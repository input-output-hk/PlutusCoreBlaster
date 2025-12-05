import Lean

import PlutusCore.Cbor

import PlutusCore.UPLC.FlatEncoding
import PlutusCore.UPLC.Term

namespace PlutusCore.UPLC.ScriptEncoding

open PlutusCore.Cbor (decodeLargeBytestring)

open PlutusCore.UPLC.Term
open PlutusCore.UPLC.FlatEncoding (decodeProgramFromByteString)

namespace Internal

open Lean Elab Command Term Meta

/-- Converts a single hexadecimal "digit" to its decimal value. -/
def hexDigitValue : Char → Option Nat
  | '0'       => .some  0
  | '1'       => .some  1
  | '2'       => .some  2
  | '3'       => .some  3
  | '4'       => .some  4
  | '5'       => .some  5
  | '6'       => .some  6
  | '7'       => .some  7
  | '8'       => .some  8
  | '9'       => .some  9
  | 'a' | 'A' => .some 10
  | 'b' | 'B' => .some 11
  | 'c' | 'C' => .some 12
  | 'd' | 'D' => .some 13
  | 'e' | 'E' => .some 14
  | 'f' | 'F' => .some 15
  | _   => .none

/-- Convert a sequence of hexadecimal digits to their base 256 representation (bytestring). -/
partial def hexStringToString : List Char -> List Char → Option (List Char)
  | h₁ :: h₂ :: t, acc =>
      match hexDigitValue h₁, hexDigitValue h₂ with
      | .some h, .some l => hexStringToString t (Char.ofNat (16 * h + l) :: acc)
      | _      , _       => .none
  | []           , acc => .some (List.reverse acc)
  | _            , _   => .none

/-- Helper function to simplify adding error messages to computations resulting in `Option` values. -/
def Option.toExcept {ε α : Type} (a : Option α) (e : ε) : Except ε α := Option.getD (Option.map .ok a) (.error e)

/-- Helper function to simplify handling of errors in a compile-time context. -/
def Except.orDie! {α : Type} [Inhabited α] : Except String α → α
  | .ok    a => a
  | .error e => panic! e

/-- Helper function that encapsulates the generic macro versions of decoding a string. -/
def fromStringTermElaborator {α} [ToExpr α] (fn : String → Except String α) : TermElab := fun stx _ => do
  let input  := stx[1]
  let some s := input.isStrLit? | throwErrorAt input m!"string literal expected as input"
  match fn s with
  | .ok    r   => pure (toExpr r)
  | .error msg => throwErrorAt input msg

/-- Decodes an UPLC program from it's single-cbor-encoded hexadecimal representation. -/
def singleCborEncodedScriptFromHex? (s : String) : Except String Program := do
  let hexDecoded       ← Option.toExcept (hexStringToString s.data [])             "Could not hexdecode input!"
  let (_, decodedCbor) ← Option.toExcept (decodeLargeBytestring ⟨hexDecoded⟩)      "Could not cbor decode input!"
  let program          ← Option.toExcept (decodeProgramFromByteString decodedCbor) "Could not decode program!"
  return program

/-- Decodes an UPLC program from it's single-cbor-encoded hexadecimal representation.
    Panics if the script cannot be decoded. -/
def singleCborEncodedScriptFromHex! (s : String) : Program := Except.orDie! (singleCborEncodedScriptFromHex? s)

/-- Macro version of singleCborEncodedScriptFromHex.
    Implemented as a term elaborator, generates the program as a Lean term. -/
syntax (name := singleCborEncodedScriptFromHexMacro) "singleCborEncodedScriptFromHexM" str : term

@[term_elab singleCborEncodedScriptFromHexMacro]
def elabSingleCborEncodedScriptFromHexM : TermElab := fromStringTermElaborator singleCborEncodedScriptFromHex?

/-- Decodes an UPLC program from it's double-cbor-encoded hexadecimal representation. -/
def doubleCborEncodedScriptFromHex? (s : String) : Except String Program := do
  let hexDecoded        ← Option.toExcept (hexStringToString s.data [])              "Could not hexdecode input!"
  let (_, decodedCbor₁) ← Option.toExcept (decodeLargeBytestring ⟨hexDecoded⟩)       "Could not cbor decode input (first pass)!"
  let (_, decodedCbor₂) ← Option.toExcept (decodeLargeBytestring decodedCbor₁)       "Could not cbor decode input (second pass)!"
  let program           ← Option.toExcept (decodeProgramFromByteString decodedCbor₂) "Could not decode program!"
  return program

/-- Decodes an UPLC program from it's double-cbor-encoded hexadecimal representation.
    Panics if the script cannot be decoded. -/
def doubleCborEncodedScriptFromHex! (s : String) : Program := Except.orDie! (doubleCborEncodedScriptFromHex? s)

/-- Macro version of doubleCborEncodedScriptFromHex.
    Implemented as a term elaborator, generates the program as a Lean term. -/
syntax (name := doubleCborEncodedScriptFromHexMacro) "doubleCborEncodedScriptFromHexM" str : term

@[term_elab doubleCborEncodedScriptFromHexMacro]
def elabDoubleCborEncodedScriptFromHexM : TermElab := fromStringTermElaborator doubleCborEncodedScriptFromHex?

/-- Decodes an UPLC program from it's raw flat representation. -/
def flatEncodedScriptFromBytestring? (b : String) : Except String Program :=
  Option.toExcept (decodeProgramFromByteString b) "Could not decode program!"

/-- Decodes an UPLC program from it's raw flat representation.
    Panics if the script cannot be decoded. -/
def flatEncodedScriptFromBytestring! (b : String) : Program := Except.orDie! (flatEncodedScriptFromBytestring? b)

/-- Macro version of flatEncodedScriptFromByteString.
    Implemented as a term elaborator, generates the program as a Lean term. -/
syntax (name := flatEncodedScriptFromBytestringMacro) "flatEncodedScriptFromBytestringM" str : term

@[term_elab flatEncodedScriptFromBytestringMacro]
def elabFlatEncodedScriptFromBytestringM : TermElab := fromStringTermElaborator flatEncodedScriptFromBytestring?

/-- Decodes an UPLC program from it's flat hexadecimal representation. -/
def flatEncodedScriptFromHex? (s : String) : Except String Program := do
  let hexDecoded ← Option.toExcept (hexStringToString s.data [])              "Could not hexdecode input!"
  let program    ← Option.toExcept (decodeProgramFromByteString ⟨hexDecoded⟩) "Could not decode program!"
  return program

/-- Decodes an UPLC program from it's flat hexadecimal representation.
    Panics if the script cannot be decoded. -/
def flatEncodedScriptFromHex! (s : String) : Program := Except.orDie! (flatEncodedScriptFromHex? s)

/-- Macro version of flatEncodedScriptFromHex.
    Implemented as a term elaborator, generates the program as a Lean term. -/
syntax (name := flatEncodedScriptFromHexMacro) "flatEncodedScriptFromHexM" str : term

@[term_elab flatEncodedScriptFromHexMacro]
def elabFlatEncodedScriptFromHexM : TermElab := fromStringTermElaborator flatEncodedScriptFromHex?

/-- Syntax for importing flat UPLC files -/
syntax (name := import_flat_uplc) "#import_flat_uplc" str ident : command

/-- Elaboration for the #import_flat_uplc command -/
@[command_elab import_flat_uplc]
def importFlatUplcImp : CommandElab := fun stx => do
  let decl ← withoutModifyingEnv $ runTermElabM fun _ => do
    let progExpr ← parseUplcFile stx
    let t        ← inferType progExpr
    return Declaration.defnDecl {
             name        := ← validVariableName stx[2],
             levelParams := [],
             type        := t,
             value       := progExpr,
             hints       := .abbrev,
             safety      := .safe
           }
  liftCoreM <| addAndCompile <| decl

 where
  /-- Extracts a valid variable name from syntax -/
  validVariableName (stx : Syntax) : TermElabM Name := do
    return stx.getId

  /-- Extracts a filename string from syntax -/
  validFilename (f : Syntax) : TermElabM String := do
    let some s := f.isStrLit? | throwErrorAt f m!"string literal expected for filename"
    return s

  /-- Parses a UPLC file and returns the resulting expression -/
  parseUplcFile (stx : Syntax) : TermElabM Expr := do
    let filename ← validFilename stx[1]
    -- Read file content
    let content ← liftM $ do
      let path := System.FilePath.mk filename
      IO.FS.readFile path
    match decodeProgramFromByteString content with
    | .some p =>
        logInfo s!"Successfully decoded '{filename}'"
        return (toExpr p)
    | .none =>
        throwError s!"Decoding error in '{filename}'"


end Internal

export Internal
  (
    singleCborEncodedScriptFromHex!
    doubleCborEncodedScriptFromHex!
    flatEncodedScriptFromBytestring!
    flatEncodedScriptFromHex!
  )

end PlutusCore.UPLC.ScriptEncoding
