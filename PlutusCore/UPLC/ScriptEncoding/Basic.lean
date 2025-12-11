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

/--
Imports a UPLC program from a file at compile time.

Syntax: `#import_uplc <format> <filepath> <identifier>`

Supported formats: `textual` (stub), `flat`, `flat_hex`, `single_cbor_hex`, `double_cbor_hex`

Example:
```lean4
#import_uplc flat "scripts/validator.flat" myValidator
```
-/
syntax (name := import_uplc) "#import_uplc" ident str ident : command

/-- Elaboration for the #import_uplc command -/
@[command_elab import_uplc]
def importUplcImp : CommandElab := fun stx => do
  let decl ← withoutModifyingEnv $ runTermElabM fun _ => do
    let progExpr ← parseUplcFile stx
    let t        ← inferType progExpr
    return Declaration.defnDecl {
             name        := ← validVariableName stx[3],
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

  /-- Extracts the format identifier from syntax -/
  getFormat (stx : Syntax) : TermElabM Name := do
    return stx.getId

  /-- Extracts a filename string from syntax -/
  validFilename (f : Syntax) : TermElabM String := do
    let some s := f.isStrLit? | throwErrorAt f m!"string literal expected for filename"
    return s

  /-- Tries to decode content with all formats and returns the first one that succeeds -/
  findWorkingFormat (content : String) : Option Name :=
    -- Try flat
    if (decodeProgramFromByteString content).isSome then
      some `flat
    -- Try flat_hex
    else if (flatEncodedScriptFromHex? content).isOk then
      some `flat_hex
    -- Try single_cbor_hex
    else if (singleCborEncodedScriptFromHex? content).isOk then
      some `single_cbor_hex
    -- Try double_cbor_hex
    else if (doubleCborEncodedScriptFromHex? content).isOk then
      some `double_cbor_hex
    else
      none

  /-- Formats a list of format names as a suggestion string -/
  formatSuggestions (formats : List Name) : String :=
    let formatName (n : Name) : String := n.toString (escape := false)
    match formats with
    | []     => ""
    | [f]    => s!"Did you mean '{formatName f}'?"
    | [f, g] => s!"Did you mean '{formatName f}' or '{formatName g}'?"
    | _      => s!"Did you mean one of: {", ".intercalate (formats.map formatName)}?"

  /-- Creates an error message with format suggestions for decoding failures -/
  decodingErrorWithSuggestion (content : String) (excludeFormat : Name) (filename : String) (errorMsg? : Option String := none) : String :=
    let suggestion := match findWorkingFormat content with
      | some fmt => if fmt != excludeFormat then formatSuggestions [fmt] else ""
      | none => ""
    let baseMsg := match errorMsg? with
      | some msg => s!"Decoding error in '{filename}': {msg}"
      | none => s!"Decoding error in '{filename}'"
    if suggestion.isEmpty then baseMsg else s!"{baseMsg}. {suggestion}"

  /-- Parses a textual UPLC file and returns the resulting expression (STUB) -/
  parseTextualUplc (filename : String) : TermElabM Expr := do
    throwError s!"Textual UPLC parser not yet implemented for '{filename}'"

  /-- Parses a flat-encoded UPLC file and returns the resulting expression -/
  parseFlatUplc (filename : String) : TermElabM Expr := do
    -- Read file content
    let content ← liftM $ do
      let path := System.FilePath.mk filename
      IO.FS.readFile path
    match decodeProgramFromByteString content with
    | .some p =>
        logInfo s!"Successfully decoded '{filename}'"
        return (toExpr p)
    | .none =>
        throwError (decodingErrorWithSuggestion content `flat filename)

  /-- Parses a flat hex-encoded UPLC file and returns the resulting expression -/
  parseFlatHexUplc (filename : String) : TermElabM Expr := do
    let content ← liftM $ do
      let path := System.FilePath.mk filename
      IO.FS.readFile path
    match flatEncodedScriptFromHex? content with
    | .ok p =>
        logInfo s!"Successfully decoded flat hex '{filename}'"
        return (toExpr p)
    | .error msg =>
        throwError (decodingErrorWithSuggestion content `flat_hex filename (some msg))

  /-- Parses a single CBOR hex-encoded UPLC file and returns the resulting expression -/
  parseSingleCborHexUplc (filename : String) : TermElabM Expr := do
    let content ← liftM $ do
      let path := System.FilePath.mk filename
      IO.FS.readFile path
    match singleCborEncodedScriptFromHex? content with
    | .ok p =>
        logInfo s!"Successfully decoded single CBOR hex '{filename}'"
        return (toExpr p)
    | .error msg =>
        throwError (decodingErrorWithSuggestion content `single_cbor_hex filename (some msg))

  /-- Parses a double CBOR hex-encoded UPLC file and returns the resulting expression -/
  parseDoubleCborHexUplc (filename : String) : TermElabM Expr := do
    let content ← liftM $ do
      let path := System.FilePath.mk filename
      IO.FS.readFile path
    match doubleCborEncodedScriptFromHex? content with
    | .ok p =>
        logInfo s!"Successfully decoded double CBOR hex '{filename}'"
        return (toExpr p)
    | .error msg =>
        throwError (decodingErrorWithSuggestion content `double_cbor_hex filename (some msg))

  /-- Parses a UPLC file and returns the resulting expression based on format -/
  parseUplcFile (stx : Syntax) : TermElabM Expr := do
    let format   ← getFormat stx[1]
    let filename ← validFilename stx[2]
    match format with
    | `textual         => parseTextualUplc filename
    | `flat            => parseFlatUplc filename
    | `flat_hex        => parseFlatHexUplc filename
    | `single_cbor_hex => parseSingleCborHexUplc filename
    | `double_cbor_hex => parseDoubleCborHexUplc filename
    | _                => throwErrorAt stx[1] m!"unsupported format '{format}', expected 'textual', 'flat', 'flat_hex', 'single_cbor_hex', or 'double_cbor_hex'"


end Internal

export Internal
  (
    singleCborEncodedScriptFromHex!
    doubleCborEncodedScriptFromHex!
    flatEncodedScriptFromBytestring!
    flatEncodedScriptFromHex!
  )

end PlutusCore.UPLC.ScriptEncoding
