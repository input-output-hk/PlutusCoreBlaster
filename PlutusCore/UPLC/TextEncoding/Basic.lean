import PlutusCore.Parser.Basic
import PlutusCore.UPLC.Term

/-!
## UPLC Text Encoding - Full Parser

Parses the standard textual representation of UPLC programs as found in `.uplc` files.

### Grammar summary
```
program      ::= "(" "program" version term ")"
version      ::= nat "." nat "." nat
term         ::= var
               | "(" "lam"     name term ")"
               | "[" term term+ "]"
               | "(" "con"     builtin-type const-val ")"
               | "(" "builtin" builtin-fun ")"
               | "(" "constr"  nat term* ")"
               | "(" "case"    term term* ")"
               | "(" "delay"   term ")"
               | "(" "force"   term ")"
               | "(" "error"   ")"
builtin-type ::= "integer" | "bytestring" | "string" | "bool" | "unit" | "data"
               | "(" "list" builtin-type ")"
               | "(" "pair" builtin-type builtin-type ")"
const-val    ::= integer-literal          -- for type integer
               | "True" | "False"         -- for type bool
               | "#" hexdigits            -- for type bytestring
               | '"' chars '"'            -- for type string
               | "()"                     -- for type unit
               | "[" (const-val ",")* "]" -- for list types
               | "(" const-val "," const-val ")" -- for pair types
               | data-val                 -- for type data
data-val     ::= "(" "Constr" integer "[" data-val* "]" ")"
               | "(" "Map"    "[" ("(" data-val "," data-val ")")* "]" ")"
               | "(" "List"   "[" data-val* "]" ")"
               | "I" integer
               | "B" "#" hexdigits
```
-/

namespace PlutusCore.UPLC.TextEncoding

namespace Internal

open PlutusCore.ByteString (ByteString)
open PlutusCore.Crypto.BLS12_381.G1 (BLS12_381_G1_Element bls12_381_G1_uncompress)
open PlutusCore.Crypto.BLS12_381.G2 (BLS12_381_G2_Element bls12_381_G2_uncompress)
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)
open PlutusCore.Parser
open PlutusCore.UPLC.Term

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

def hexCharVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

def hexPairsToChars : List Char → List Char
  | h1 :: h2 :: rest => Char.ofNat (hexCharVal h1 * 16 + hexCharVal h2) :: hexPairsToChars rest
  | _ => []

/-- Parses a '#' character. -/
def parseHashMark : Parser Unit := do _ ← char '#'

/-- Parses a "0x" prefix. -/
def parse0xPrefix : Parser Unit := do
  _ ← char '0'
  _ ← char 'x' <|> char 'X'

/-- Parse a prefixed hex byte string into a `ByteString`.
    Each pair of hex digits encodes one byte. -/
def parseHexByteString (pref : Parser Unit) : Parser ByteString := do
  _ ← pref
  let hexStr ← takeWhile (fun c =>
    c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F'))
  if hexStr.length % 2 != 0 then
    fail s!"bytestring hex must have even number of digits, got {hexStr.length}"
  return { data := String.mk (hexPairsToChars hexStr.data) }

/-- Parses a '#' prefixed bytestring. -/
def parseHashMarkPrefixedByteString := parseHexByteString parseHashMark
/-- Parses a '0x' prefixed bytestring. -/
def parse0xPrefixedByteString       := parseHexByteString parse0xPrefix

/-- Replaces characters in the 0xD800-0xDFFF range with 0xFFFD, to mimic
    the behavior of Plutus Core.
    (see remark at: https://github.com/IntersectMBO/plutus/blob/master/plutus-core/plutus-core/src/PlutusCore/Parser/Builtin.hs#L61) -/
def compensateForTextPack (c : Char) : Char :=
  if '\uD800' ≤ c && c ≤ '\uDFFF'
    then '\uFFFD'
    else c

/-- Parses character literals in the form of '\000..', where the unicode code point
    is expressed in base 10. Expects the char '\' to be already consumed and `d` to
    contain the relevant lookahed. -/
def parseDecimalCharCode (d : List Char) : Parser Char := fun s =>
  let digits := List.takeWhile Char.isDigit d
  if List.length digits == 0
    then .error { message := "expected decimal digits", pos := s.pos }
    else
      let val := List.foldl (· * 10 + ·) 0 (((· - Char.toNat '0') ∘ Char.toNat) <$> digits)
      if Nat.blt 0x10FFFF val
        then .error { message := s!"unicode escape out of range: {val}", pos := s.pos }
        else
          let result := Char.ofNat val |> compensateForTextPack
          -- each digit is 1 byte long
          .ok (result, { s with pos := s.pos + ⟨digits.length⟩ })

/-- Parses character literals in the form of '\o000.', where the unicode code point
    is expressed in base 8. Expects the chars '\o' to be already consumed and `o` to
    contain the relevant lookahed. -/
def parseOctalCharCode (o : List Char) : Parser Char := fun s =>
  let digits := List.takeWhile (λ c => c ≥ '0' && c ≤ '7') o
  if List.length digits == 0
    then .error { message := "expected octal digits", pos := s.pos }
    else
      let val := List.foldl (· * 8 + ·) 0 (((· - Char.toNat '0') ∘ Char.toNat) <$> digits)
      if Nat.blt 0x10FFFF val
        then .error { message := s!"unicode escape out of range: {val}", pos := s.pos }
        else
          let result := Char.ofNat val |> compensateForTextPack
          -- each digit is 1 byte long
          .ok (result, { s with pos := s.pos + ⟨digits.length⟩ })

/-- Parses character literals in the form of '\x000.', where the unicode code point
    is expressed in base 16. Expects the chars '\x' to be already consumed and `h` to
    contain the relevant lookahed. -/
def parseHexCharCode (h : List Char) : Parser Char := fun s =>
  let digits := List.takeWhile (λ c => (c ≥ '0' && c ≤ '9') || (c ≥ 'a' && c ≤ 'f') || (c ≥ 'A' && c ≤ 'F')) h
  if List.length digits == 0
    then .error { message := "expected hex digits", pos := s.pos }
    else
      let val := List.foldl (· * 16 + ·) 0 (fHex <$> digits)
      if Nat.blt 0x10FFFF val
        then .error { message := s!"unicode escape out of range: {val}", pos := s.pos }
        else
          let result := Char.ofNat val |> compensateForTextPack
          -- each digit is 1 byte long
          .ok (result, { s with pos := s.pos + ⟨digits.length⟩ })
 where
  fHex (c : Char) : Nat :=
         if c ≥ '0' && c ≤ '9' then Char.toNat c - Char.toNat '0'
    else if c ≥ 'a' && c ≤ 'f' then Char.toNat c - Char.toNat 'a' + 10
    else if c ≥ 'A' && c ≤ 'F' then Char.toNat c - Char.toNat 'A' + 10
    else 0

/-- Parses a control character escape sequence. Expects '\^c' to
    be already consumed, where `c` is passed in as an argument. -/
def controlCharParsed (c : Char) : Parser Char := fun s =>
  match c with
  | '@'  => .ok ('\u0000', s)
  | '['  => .ok ('\u001B', s)
  | '\\' => .ok ('\u001C', s)
  | ']'  => .ok ('\u001D', s)
  | '^'  => .ok ('\u001E', s)
  | '_'  => .ok ('\u001F', s)
  | _    =>
    if 'A' ≤ c && c ≤ 'Z'
      then .ok (Char.ofNat (Char.toNat c - 64), s)
      else .error { message := "unrecognized control-character escape", pos := s.pos }

/-- Parses a character literal according to the Plutus Core implementation.
    (see:
      - PlutusCore: https://github.com/IntersectMBO/plutus/blob/master/plutus-core/plutus-core/src/PlutusCore/Parser/Builtin.hs#L61
      - Megaparsec: https://github.com/mrkkrp/megaparsec/blob/master/Text/Megaparsec/Char/Lexer.hs#L342
      - Specification: https://www.haskell.org/definition/haskell2010.pdf#section.2.6
    ) -/
partial def parseLitChar : Parser Char := fun s => do
  match lookAhead 10 s with
  | .error e                                => .error e
  | .ok ([]                            , _) => .error { message := "no more chars", pos := s.pos }
  | .ok ('\\'                     :: [], _) => .error { message := "unterminated escape sequence", pos := s.pos }
  | .ok ('\\' :: 'a'               :: _, _) => .ok ('\u0007',         { s with pos := s.pos + ⟨2⟩ })
  | .ok ('\\' :: 'b'               :: _, _) => .ok ('\u0008',         { s with pos := s.pos + ⟨2⟩ })
  | .ok ('\\' :: 't'               :: _, _) => .ok ('\u0009',         { s with pos := s.pos + ⟨2⟩ })
  | .ok ('\\' :: 'n'               :: _, _) => .ok ('\u000A',         { s with pos := s.pos + ⟨2⟩ })
  | .ok ('\\' :: 'v'               :: _, _) => .ok ('\u000B',         { s with pos := s.pos + ⟨2⟩ })
  | .ok ('\\' :: 'f'               :: _, _) => .ok ('\u000C',         { s with pos := s.pos + ⟨2⟩ })
  | .ok ('\\' :: 'r'               :: _, _) => .ok ('\u000D',         { s with pos := s.pos + ⟨2⟩ })
  | .ok ('\\' :: '\\'              :: _, _) => .ok ('\\'    ,         { s with pos := s.pos + ⟨2⟩ })
  | .ok ('\\' :: '\"'              :: _, _) => .ok ('\"'    ,         { s with pos := s.pos + ⟨2⟩ })
  | .ok ('\\' :: '\''              :: _, _) => .ok ('\''    ,         { s with pos := s.pos + ⟨2⟩ })
  | .ok ('\\' :: '&'               :: _, _) => parseLitChar           { s with pos := s.pos + ⟨2⟩ } -- null escape: the Haskell implementation accepts it and just consumes
  | .ok ('\\' :: 'o'               :: o, _) => parseOctalCharCode o   { s with pos := s.pos + ⟨2⟩ }
  | .ok ('\\' :: 'x'               :: h, _) => parseHexCharCode   h   { s with pos := s.pos + ⟨2⟩ }
  | .ok ('\\' :: '^' :: c          :: _, _) => controlCharParsed  c   { s with pos := s.pos + ⟨3⟩ }
  | .ok ('\\' :: 'N' :: 'U' :: 'L' :: _, _) => .ok ('\u0000',         { s with pos := s.pos + ⟨4⟩ })
  | .ok ('\\' :: 'S' :: 'O' :: 'H' :: _, _) => .ok ('\u0001',         { s with pos := s.pos + ⟨4⟩ })
  | .ok ('\\' :: 'S' :: 'T' :: 'X' :: _, _) => .ok ('\u0002',         { s with pos := s.pos + ⟨4⟩ })
  | .ok ('\\' :: 'E' :: 'T' :: 'X' :: _, _) => .ok ('\u0003',         { s with pos := s.pos + ⟨4⟩ })
  | .ok ('\\' :: 'E' :: 'O' :: 'T' :: _, _) => .ok ('\u0004',         { s with pos := s.pos + ⟨4⟩ })
  | .ok ('\\' :: 'E' :: 'N' :: 'Q' :: _, _) => .ok ('\u0005',         { s with pos := s.pos + ⟨4⟩ })
  | .ok ('\\' :: 'A' :: 'C' :: 'K' :: _, _) => .ok ('\u0006',         { s with pos := s.pos + ⟨4⟩ })
  | .ok ('\\' :: 'B' :: 'E' :: 'L' :: _, _) => .ok ('\u0007',         { s with pos := s.pos + ⟨4⟩ })
  | .ok ('\\' :: 'B' :: 'S'        :: _, _) => .ok ('\u0008',         { s with pos := s.pos + ⟨3⟩ })
  | .ok ('\\' :: 'H' :: 'T'        :: _, _) => .ok ('\u0009',         { s with pos := s.pos + ⟨3⟩ })
  | .ok ('\\' :: 'L' :: 'F'        :: _, _) => .ok ('\u000A',         { s with pos := s.pos + ⟨3⟩ })
  | .ok ('\\' :: 'V' :: 'T'        :: _, _) => .ok ('\u000B',         { s with pos := s.pos + ⟨3⟩ })
  | .ok ('\\' :: 'F' :: 'F'        :: _, _) => .ok ('\u000C',         { s with pos := s.pos + ⟨3⟩ })
  | .ok ('\\' :: 'C' :: 'R'        :: _, _) => .ok ('\u000D',         { s with pos := s.pos + ⟨3⟩ })
  | .ok ('\\' :: 'S' :: 'O'        :: _, _) => .ok ('\u000E',         { s with pos := s.pos + ⟨3⟩ })
  | .ok ('\\' :: 'S' :: 'I'        :: _, _) => .ok ('\u000F',         { s with pos := s.pos + ⟨3⟩ })
  | .ok ('\\' :: 'D' :: 'L' :: 'E' :: _, _) => .ok ('\u0010',         { s with pos := s.pos + ⟨4⟩ })
  | .ok ('\\' :: 'D' :: 'C' :: '1' :: _, _) => .ok ('\u0011',         { s with pos := s.pos + ⟨4⟩ })
  | .ok ('\\' :: 'D' :: 'C' :: '2' :: _, _) => .ok ('\u0012',         { s with pos := s.pos + ⟨4⟩ })
  | .ok ('\\' :: 'D' :: 'C' :: '3' :: _, _) => .ok ('\u0013',         { s with pos := s.pos + ⟨4⟩ })
  | .ok ('\\' :: 'D' :: 'C' :: '4' :: _, _) => .ok ('\u0014',         { s with pos := s.pos + ⟨4⟩ })
  | .ok ('\\' :: 'N' :: 'A' :: 'K' :: _, _) => .ok ('\u0015',         { s with pos := s.pos + ⟨4⟩ })
  | .ok ('\\' :: 'S' :: 'Y' :: 'N' :: _, _) => .ok ('\u0016',         { s with pos := s.pos + ⟨4⟩ })
  | .ok ('\\' :: 'E' :: 'T' :: 'B' :: _, _) => .ok ('\u0017',         { s with pos := s.pos + ⟨4⟩ })
  | .ok ('\\' :: 'C' :: 'A' :: 'N' :: _, _) => .ok ('\u0018',         { s with pos := s.pos + ⟨4⟩ })
  | .ok ('\\' :: 'E' :: 'M'        :: _, _) => .ok ('\u0019',         { s with pos := s.pos + ⟨3⟩ })
  | .ok ('\\' :: 'S' :: 'U' :: 'B' :: _, _) => .ok ('\u001A',         { s with pos := s.pos + ⟨4⟩ })
  | .ok ('\\' :: 'E' :: 'S' :: 'C' :: _, _) => .ok ('\u001B',         { s with pos := s.pos + ⟨4⟩ })
  | .ok ('\\' :: 'F' :: 'S'        :: _, _) => .ok ('\u001C',         { s with pos := s.pos + ⟨3⟩ })
  | .ok ('\\' :: 'G' :: 'S'        :: _, _) => .ok ('\u001D',         { s with pos := s.pos + ⟨3⟩ })
  | .ok ('\\' :: 'R' :: 'S'        :: _, _) => .ok ('\u001E',         { s with pos := s.pos + ⟨3⟩ })
  | .ok ('\\' :: 'U' :: 'S'        :: _, _) => .ok ('\u001F',         { s with pos := s.pos + ⟨3⟩ })
  | .ok ('\\' :: 'S' :: 'P'        :: _, _) => .ok ('\u0020',         { s with pos := s.pos + ⟨3⟩ })
  | .ok ('\\' :: 'D' :: 'E' :: 'L' :: _, _) => .ok ('\u007F',         { s with pos := s.pos + ⟨4⟩ })
  | .ok ('\\'                      :: d, _) => parseDecimalCharCode d { s with pos := s.pos + ⟨1⟩ }
  | .ok (c                         :: _, _) => .ok (c       ,         { s with pos := s.input.next s.pos })

/-- Parses a string literal, expects the string to be terminated by '"', but does
    not consume it. -/
partial def parseStringChars : Parser (List Char) :=
  let rec loop (acc : List Char) : Parser (List Char) := do
    match ← peek with
    | .none      => fail "unterminated string literal"
    | .some '"'  => return (List.reverse acc) -- stop, leave '"' unconsumed
    | .some _    =>
        let c ← parseLitChar
        loop (c :: acc)
  loop []

/-- Parse a double-quoted string with basic escape sequences. -/
def parseQuotedString : Parser String := do
  _ ← char '"'
  let chars ← parseStringChars
  _ ← char '"'
  return String.mk chars

def parseBls12_381_G1_element : Parser BLS12_381_G1_Element := fun s =>
  match parse0xPrefixedByteString s with
  | .error e        => .error e
  | .ok (bytes, s') =>
      match bls12_381_G1_uncompress bytes with
      | .error e => .error { message := e, pos := s.pos }
      | .ok g1   => .ok (g1, s')

def parseBls12_381_G2_element : Parser BLS12_381_G2_Element := fun s =>
  match parse0xPrefixedByteString s with
  | .error e        => .error e
  | .ok (bytes, s') =>
      match bls12_381_G2_uncompress bytes with
      | .error e => .error { message := e, pos := s.pos }
      | .ok g2   => .ok (g2, s')

-- ---------------------------------------------------------------------------
-- BuiltinType parser
-- ---------------------------------------------------------------------------

/-- Parses an atomic type. -/
def parseAtomicType : Parser BuiltinType := do
    let name ← identifier
    match name with
    | "integer"              => return .AtomicType .TypeInteger
    | "bytestring"           => return .AtomicType .TypeByteString
    | "string"               => return .AtomicType .TypeString
    | "bool"                 => return .AtomicType .TypeBool
    | "unit"                 => return .AtomicType .TypeUnit
    | "data"                 => return .AtomicType .TypeData
    | "bls12_381_G1_element" => return .AtomicType .TypeBls12_381_G1_element
    | "bls12_381_G2_element" => return .AtomicType .TypeBls12_381_G2_element
    | other                  => fail s!"unknown builtin type '{other}'"

mutual
  /-- Parse a `BuiltinType`.
      - Atomic: `integer`, `bytestring`, `string`, `bool`, `unit`, `data`, `bls12_381_G1_element` and `bls12_381_G2_element`
      - List:   `(list T)`     - parenthesised with one type argument
      - Pair:   `(pair T U)`   - parenthesised with two type arguments -/
  partial def parseBuiltinType : Parser BuiltinType :=
    ws *> (parseTypeOperator <|> parseAtomicType)

  /-- Parses `list` and `pair` types. -/
  partial def parseTypeOperator : Parser BuiltinType :=
    parens $ do
      let name ← identifier
      match name with
      | "list" => return .TypeOperator (.TypeList (← parseBuiltinType))
      | "pair" =>
          let t1 ← parseBuiltinType
          let t2 ← parseBuiltinType
          return .TypeOperator (.TypePair t1 t2)
      | other  => fail s!"unknown type '{other}'"

end

-- ---------------------------------------------------------------------------
-- BuiltinFun parser
-- ---------------------------------------------------------------------------

-- Pure lookup table: no Parser type involved, so no Nonempty/partial issues.
def builtinFunOfName? (name : String) : Option BuiltinFun :=
  match name with
  | "addInteger"                      => some .AddInteger
  | "subtractInteger"                 => some .SubtractInteger
  | "multiplyInteger"                 => some .MultiplyInteger
  | "divideInteger"                   => some .DivideInteger
  | "quotientInteger"                 => some .QuotientInteger
  | "remainderInteger"                => some .RemainderInteger
  | "modInteger"                      => some .ModInteger
  | "equalsInteger"                   => some .EqualsInteger
  | "lessThanInteger"                 => some .LessThanInteger
  | "lessThanEqualsInteger"           => some .LessThanEqualsInteger
  | "appendByteString"                => some .AppendByteString
  | "consByteString"                  => some .ConsByteString
  | "sliceByteString"                 => some .SliceByteString
  | "lengthOfByteString"              => some .LengthOfByteString
  | "indexByteString"                 => some .IndexByteString
  | "equalsByteString"                => some .EqualsByteString
  | "lessThanByteString"              => some .LessThanByteString
  | "lessThanEqualsByteString"        => some .LessThanEqualsByteString
  | "sha2_256"                        => some .Sha2_256
  | "sha3_256"                        => some .Sha3_256
  | "blake2b_256"                     => some .Blake2b_256
  | "verifyEd25519Signature"          => some .VerifyEd25519Signature
  | "appendString"                    => some .AppendString
  | "equalsString"                    => some .EqualsString
  | "encodeUtf8"                      => some .EncodeUtf8
  | "decodeUtf8"                      => some .DecodeUtf8
  | "ifThenElse"                      => some .IfThenElse
  | "chooseUnit"                      => some .ChooseUnit
  | "trace"                           => some .Trace
  | "fstPair"                         => some .FstPair
  | "sndPair"                         => some .SndPair
  | "chooseList"                      => some .ChooseList
  | "mkCons"                          => some .MkCons
  | "headList"                        => some .HeadList
  | "tailList"                        => some .TailList
  | "nullList"                        => some .NullList
  | "chooseData"                      => some .ChooseData
  | "constrData"                      => some .ConstrData
  | "mapData"                         => some .MapData
  | "listData"                        => some .ListData
  | "iData"                           => some .IData
  | "bData"                           => some .BData
  | "unConstrData"                    => some .UnConstrData
  | "unMapData"                       => some .UnMapData
  | "unListData"                      => some .UnListData
  | "unIData"                         => some .UnIData
  | "unBData"                         => some .UnBData
  | "equalsData"                      => some .EqualsData
  | "mkPairData"                      => some .MkPairData
  | "mkNilData"                       => some .MkNilData
  | "mkNilPairData"                   => some .MkNilPairData
  | "serialiseData"                   => some .SerializeData
  | "verifyEcdsaSecp256k1Signature"   => some .VerifyEcdsaSecp256k1Signature
  | "verifySchnorrSecp256k1Signature" => some .VerifySchnorrSecp256k1Signature
  | "bls12_381_G1_add"                => some .Bls12_381_G1_add
  | "bls12_381_G1_neg"                => some .Bls12_381_G1_neg
  | "bls12_381_G1_scalarMul"          => some .Bls12_381_G1_scalarMul
  | "bls12_381_G1_equal"              => some .Bls12_381_G1_equal
  | "bls12_381_G1_hashToGroup"        => some .Bls12_381_G1_hashToGroup
  | "bls12_381_G1_compress"           => some .Bls12_381_G1_compress
  | "bls12_381_G1_uncompress"         => some .Bls12_381_G1_uncompress
  | "bls12_381_G2_add"                => some .Bls12_381_G2_add
  | "bls12_381_G2_neg"                => some .Bls12_381_G2_neg
  | "bls12_381_G2_scalarMul"          => some .Bls12_381_G2_scalarMul
  | "bls12_381_G2_equal"              => some .Bls12_381_G2_equal
  | "bls12_381_G2_hashToGroup"        => some .Bls12_381_G2_hashToGroup
  | "bls12_381_G2_compress"           => some .Bls12_381_G2_compress
  | "bls12_381_G2_uncompress"         => some .Bls12_381_G2_uncompress
  | "bls12_381_G1_multiScalarMul"     => some .Bls12_381_G1_multiScalarMul
  | "bls12_381_G2_multiScalarMul"     => some .Bls12_381_G2_multiScalarMul
  | "bls12_381_millerLoop"            => some .Bls12_381_millerLoop
  | "bls12_381_mulMlResult"           => some .Bls12_381_mulMlResult
  | "bls12_381_finalVerify"           => some .Bls12_381_finalVerify
  | "keccak_256"                      => some .Keccak_256
  | "blake2b_224"                     => some .Blake2b_224
  | "integerToByteString"             => some .IntegerToByteString
  | "byteStringToInteger"             => some .ByteStringToInteger
  | "andByteString"                   => some .AndByteString
  | "orByteString"                    => some .OrByteString
  | "xorByteString"                   => some .XorByteString
  | "complementByteString"            => some .ComplementByteString
  | "readBit"                         => some .ReadBit
  | "writeBits"                       => some .WriteBits
  | "replicateByte"                   => some .ReplicateByte
  | "shiftByteString"                 => some .ShiftByteString
  | "rotateByteString"                => some .RotateByteString
  | "countSetBits"                    => some .CountSetBits
  | "findFirstSetBit"                 => some .FindFirstSetBit
  | "ripemd_160"                      => some .Ripemd_160
  | "expModInteger"                   => some .ExpModInteger
  | "dropList"                        => some .DropList
  | _                                 => none

/-- Parse a builtin function name. -/
def parseBuiltinFun : Parser BuiltinFun := do
  let name ← identifier
  match builtinFunOfName? name with
  | some f => return f
  | none   => fail s!"unknown builtin function '{name}'"

-- ---------------------------------------------------------------------------
-- Data parser
-- ---------------------------------------------------------------------------

mutual
  /-- Parse a `Data` value.

      Handles both the parenthesised forms `(Constr N [...])`, `(Map [...])`,
      `(List [...])`, `(I N)`, `(B #HEX)` and the bare forms `Constr N [...]`,
      `Map [...]`, `List [...]`, `I N`, `B #HEX` that appear inside nested
      positions in conformance test files. -/
  partial def parseData : Parser Data :=
    ws *> (parseDataParen <|> parseDataBare)

  /-- Parenthesised form: `(kw ...)`. -/
  partial def parseDataParen : Parser Data :=
    parens (ws *> parseDataBare)

  /-- Bare form: keyword followed by its arguments. -/
  partial def parseDataBare : Parser Data := do
    let kw ← identifier
    ws
    match kw with
    | "Constr" =>
        let idx    ← signedInt
        ws
        let fields ← brackets (sepBy parseData (ws *> char ',' *> ws))
        return .Constr idx fields
    | "Map" =>
        let pairs ← brackets (sepBy parseDataPair (ws *> char ',' *> ws))
        return .Map pairs
    | "List" =>
        let elems ← brackets (sepBy parseData (ws *> char ',' *> ws))
        return .List elems
    | "I" => return .I (← signedInt)
    | "B" => return .B (← parseHashMarkPrefixedByteString)
    | other => fail s!"unknown Data value '{other}'"

  /-- Parse one `(D, D)` pair inside a `Map`. -/
  partial def parseDataPair : Parser (Data × Data) :=
    parens do
      let d1 ← parseData
      ws
      _ ← char ','
      let d2 ← parseData
      ws
      return (d1, d2)
end

-- ---------------------------------------------------------------------------
-- Const parser (type-directed)
-- ---------------------------------------------------------------------------

mutual
  /-- Parse a constant value according to its `BuiltinType`. -/
  partial def parseConstVal : BuiltinType → Parser Const
    | .AtomicType .TypeInteger              => .Integer    <$> signedInt
    | .AtomicType .TypeByteString           => .ByteString <$> parseHashMarkPrefixedByteString
    | .AtomicType .TypeString               => .String     <$> parseQuotedString
    | .AtomicType .TypeBool                 => do
        let w ← identifier
        match w with
        | "True"  => return .Bool true
        | "False" => return .Bool false
        | other   => fail s!"expected 'True' or 'False', got '{other}'"
    | .AtomicType .TypeUnit                 => (λ _ => .Unit) <$> (char '(' *> ws <* char ')')
    | .AtomicType .TypeData                 => .Data <$> parseData
    | .AtomicType .TypeBls12_381_G1_element => .Bls12_381_G1_element <$> parseBls12_381_G1_element
    | .AtomicType .TypeBls12_381_G2_element => .Bls12_381_G2_element <$> parseBls12_381_G2_element
    | .AtomicType .TypeBls12_381_MlResult   => fail "cannot parse bls12_381_MlResult"
    | .TypeOperator (.TypeList elemTy)      => parseConstList elemTy
    | .TypeOperator (.TypePair t1 t2)       => parseConstPair t1 t2

  /-- Parse `[v, v, ...]` as a list constant. -/
  partial def parseConstList (elemTy : BuiltinType) : Parser Const := do
    let elems ← brackets (sepBy (ws *> parseConstVal elemTy) (ws *> char ',' *> ws))
    match elemTy with
    | .AtomicType .TypeData =>
        let dataElems ← elems.mapM $ fun
          | .Data d => pure d
          | _       => fail "data expected"
        return .ConstDataList dataElems
    | .TypeOperator (.TypePair (.AtomicType .TypeData) (.AtomicType .TypeData)) =>
        -- (list (pair data data)) → ConstPairDataList
        let pairElems ← elems.mapM $ fun
          | .PairData p => pure p
          | _ => fail "pair data expected"
        return .ConstPairDataList pairElems
    | _ => return .ConstList elems

  /-- Parse `(v, v)` as a pair constant. -/
  partial def parseConstPair (t1 t2 : BuiltinType) : Parser Const :=
    parens do
      let v1 ← ws *> parseConstVal t1
      ws
      _ ← char ','
      let v2 ← ws *> parseConstVal t2
      ws
      match v1, v2 with
      | .Data d1, .Data d2 => return .PairData (d1, d2)
      | _, _               => return .Pair (v1, v2)
end

/-- Parse a full `con` constant: type annotation then value. -/
def parseCon : Parser Const := do
  let ty ← parseBuiltinType
  ws
  parseConstVal ty

-- ---------------------------------------------------------------------------
-- Term parser
-- ---------------------------------------------------------------------------

mutual
  /-- Parse a UPLC `Term`. -/
  -- Dispatch on the first non-whitespace character to avoid peek lookup issues.
  partial def parseTerm (v : Version) : Parser Term := fun s =>
    match (ws : Parser Unit) s with
    | .error e => .error e
    | .ok (_, s') =>
      if s'.pos == s'.input.endPos then
        .error { message := "expected term, got end of input", pos := s'.pos }
      else match s'.input.get s'.pos with
        | '[' => parseApply v s'
        | '(' => parseParenTerm v s'
        | _   => parseVar s'

  /-- `[t0 t1 … tn]` - multi-application, left-associative,
                        a minimum of two expressions must be present
      `[f x y z]` desugars to `Apply (Apply (Apply f x) y) z`. -/
  partial def parseApply (v : Version) : Parser Term :=
    brackets do
      let t0 ← parseTerm v
      let ts ← many1 (parseTerm v)
      return ts.foldl .Apply t0

  /-- `(keyword ...)` - dispatches on the keyword. -/
  partial def parseParenTerm (v : Version) : Parser Term :=
    parens do
      let kw ← identifier
      ws
      match kw with
      | "lam"     =>
          let name ← varName
          let body ← parseTerm v
          return .Lam name body
      | "con"     => .Const   <$> parseCon
      | "builtin" => .Builtin <$> parseBuiltinFun
      | "constr"  =>
          if v < .Version 1 1 0 then fail "'constr' can't be used before 1.1.0"
          let tag  ← nat
          if 18446744073709551616 ≤ tag then fail "tag cannot exceed 2^64 - 1"
          let args ← many (parseTerm v)
          return .Constr tag args
      | "case"    =>
          if v < .Version 1 1 0 then fail "'case' can't be used before 1.1.0"
          let scrut ← parseTerm v
          let alts  ← many (parseTerm v)
          return .Case scrut alts
      | "delay"   => .Delay <$> parseTerm v
      | "force"   => .Force <$> parseTerm v
      | "error"   => return .Error
      | other     => fail s!"unknown term keyword '{other}'"

  /-- A bare identifier is a variable. -/
  partial def parseVar : Parser Term := .Var <$> varName

end

-- ---------------------------------------------------------------------------
-- Version and Program parsers
-- ---------------------------------------------------------------------------

/-- Parse a complete UPLC `Program`: `(program N.N.N term)`. -/
def parseProgram : Parser Program :=
  parens do
    let kw ← identifier
    if kw != "program" then fail s!"expected 'program', got '{kw}'"
    ws
    let major ← nat
    _ ← char '.'
    let minor ← nat
    _ ← char '.'
    let patch ← nat
    let v := .Version major minor patch
    let t ← parseTerm v
    return .Program v t

-- ---------------------------------------------------------------------------
-- Public entry points
-- ---------------------------------------------------------------------------

/-- Parse a UPLC `Term` from a string, with a human-readable error on failure. -/
def termFromString (v : Version) (s : String) : Except String Term :=
  match run (parseTerm v) s with
  | .ok p    => .ok p
  | .error e => .error s!"parse error at byte {e.pos.byteIdx}: {e.message}"

/-- Parse a UPLC `Term` from a string, returning `none` on failure. -/
def termFromString? (v : Version) (s : String) : Option Term :=
  runOption (parseTerm v) s

/-- Parse a UPLC `Program` from a string, with a human-readable error on failure. -/
def programFromString (s : String) : Except String Program :=
  match run parseProgram s with
  | .ok p    => .ok p
  | .error e => .error s!"parse error at byte {e.pos.byteIdx}: {e.message}"

/-- Parse a UPLC `Program` from a string, returning `none` on failure. -/
def programFromString? (s : String) : Option Program :=
  runOption parseProgram s

end Internal

export Internal
  (
    termFromString
    termFromString?
    programFromString
    programFromString?
  )

end PlutusCore.UPLC.TextEncoding
