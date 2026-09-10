import Lean

import PlutusCore.Cbor
import PlutusCore.UPLC.FlatEncoding
import PlutusCore.UPLC.PlutusScript
import PlutusCore.UPLC.Term
import PlutusCore.UPLC.TextEncoding

namespace PlutusCore.UPLC.ScriptEncoding

open FlatEncoding (decodeProgramFromByteArray)
open PlutusCore.Cbor (decodeLargeBytestring)
open PlutusCore.UPLC.TextEncoding (programFromString)
open PlutusScript
open Term

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

/-- Convert a sequence of hexadecimal digits to the corresponding `ByteArray`.
    Each pair of hex digits becomes one byte. Returns `.none` if the input has
    an odd length or contains a non-hex character. -/
partial def hexStringToByteArray (s : String) : Option ByteArray :=
  go s.data []
where
  go : List Char → List UInt8 → Option ByteArray
  | h₁ :: h₂ :: t, acc =>
      match hexDigitValue h₁, hexDigitValue h₂ with
      | .some h, .some l => go t ((16 * h + l).toUInt8 :: acc)
      | _      , _       => .none
  | []           , acc => .some acc.reverse.toByteArray
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
  let bytes            ← Option.toExcept (hexStringToByteArray s)                 "Could not hexdecode input!"
  let (_, decodedCbor) ← Option.toExcept (decodeLargeBytestring bytes)            "Could not cbor decode input!"
  let program          ← Option.toExcept (decodeProgramFromByteArray decodedCbor) "Could not decode program!"
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
  let bytes             ← Option.toExcept (hexStringToByteArray s)                  "Could not hexdecode input!"
  let (_, decodedCbor₁) ← Option.toExcept (decodeLargeBytestring bytes)             "Could not cbor decode input (first pass)!"
  let (_, decodedCbor₂) ← Option.toExcept (decodeLargeBytestring decodedCbor₁)      "Could not cbor decode input (second pass)!"
  let program           ← Option.toExcept (decodeProgramFromByteArray decodedCbor₂) "Could not decode program!"
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
def flatEncodedScriptFromByteArray? (b : ByteArray) : Except String Program :=
  Option.toExcept (decodeProgramFromByteArray b) "Could not decode program!"

/-- Decodes an UPLC program from it's raw flat representation.
    Panics if the script cannot be decoded. -/
def flatEncodedScriptFromByteArray! (b : ByteArray) : Program := Except.orDie! (flatEncodedScriptFromByteArray? b)

/-- Decodes an UPLC program from it's flat hexadecimal representation. -/
def flatEncodedScriptFromHex? (s : String) : Except String Program := do
  let bytes   ← Option.toExcept (hexStringToByteArray s)           "Could not hexdecode input!"
  let program ← Option.toExcept (decodeProgramFromByteArray bytes) "Could not decode program!"
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
Imports a UPLC program from a file at compile time and returns a `PlutusScript` instance

Syntax: `#import_uplc <identifier> <lang> <format> <filepath>`

Supported formats: `textual`, `flat`, `flat_hex`, `single_cbor_hex`, `double_cbor_hex`
Supported plutus ledger language: `PlutusV1`, `PlutusV2`, `PlutusV3`

Example:
```lean4
#import_uplc myValidator PlutusV2 flat "scripts/validator.flat"
```
-/
syntax (name := import_uplc) "#import_uplc" ident ident ident str : command

/-- Cached representations of a file's contents.
    Binary formats need raw bytes; textual/hex formats need UTF-8 text.
    Whichever representation a parser already read is reused; the other is
    loaded lazily by the format-suggestion helper if needed. -/
structure FileContents where
  path : System.FilePath
  text : Option String     := .none
  bin  : Option ByteArray  := .none

/-- Returns the UTF-8 text of the file, reading it if not already loaded. -/
def FileContents.getText (fc : FileContents) : IO (FileContents × String) :=
  match fc.text with
  | some t => pure (fc, t)
  | none   => do
      let t ← IO.FS.readFile fc.path
      pure ({ fc with text := some t }, t)

/-- Returns the raw byte contents of the file, reading it if not already loaded. -/
def FileContents.getBin (fc : FileContents) : IO (FileContents × ByteArray) :=
  match fc.bin with
  | some b => pure (fc, b)
  | none   => do
      let b ← IO.FS.readBinFile fc.path
      pure ({ fc with bin := some b }, b)

/-- Elaboration for the #import_uplc command -/
@[command_elab import_uplc]
def importUplcImp : CommandElab := fun stx => do
  let decl ← withoutModifyingEnv $ runTermElabM fun _ => do
    let progExpr ← parseUplcFile stx
    let t        ← inferType progExpr
    return Declaration.defnDecl {
             name        := ← validVariableName stx[1],
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

  /-- Extracts the plutus language from syntax -/
  validLang (stx : Syntax) : TermElabM Expr := do
   match stx.getId with
   | `PlutusV1 => mkConst ``PlutusLanguage.PlutusV1
   | `PlutusV2 => mkConst ``PlutusLanguage.PlutusV2
   | `PlutusV3 => mkConst ``PlutusLanguage.PlutusV3
   | n => throwErrorAt stx s!"Unsupported plutus ledeger language {n}"

  /-- Extracts a filename string from syntax -/
  validFilename (f : Syntax) : TermElabM String := do
    let some s := f.isStrLit? | throwErrorAt f m!"string literal expected for filename"
    return s

  /-- Tries to decode the file's contents in every supported format and returns
      the first one that succeeds. Lazily loads either the textual or the binary
      representation depending on what each format needs, reusing whatever
      representation the caller already loaded. -/
  findWorkingFormat (fc : FileContents) : IO (Option Name) := do
    -- Try textual (needs text)
    let (fc, text) ← fc.getText
    if (programFromString text).isOk then return some `textual
    -- Try flat (needs binary)
    let (_, bin) ← fc.getBin
    if (decodeProgramFromByteArray bin).isSome then return some `flat
    let trimmed := text.trim
    -- Try flat_hex (needs text)
    if (flatEncodedScriptFromHex? trimmed).isOk then return some `flat_hex
    -- Try single_cbor_hex (needs text)
    if (singleCborEncodedScriptFromHex? trimmed).isOk then return some `single_cbor_hex
    -- Try double_cbor_hex (needs text)
    if (doubleCborEncodedScriptFromHex? trimmed).isOk then return some `double_cbor_hex
    return none

  /-- Formats a format name as a suggestion string -/
  formatSuggestion (format : Name) : String :=
    let formatName := format.toString (escape := false)
    s!"Did you mean '{formatName}'?"

  /-- Creates an error message with format suggestions for decoding failures -/
  decodingErrorWithSuggestion (fc : FileContents) (excludeFormat : Name) (errorMsg? : Option String := none) : TermElabM String := do
    let alt? ← (findWorkingFormat fc).toBaseIO
    let suggestion := match alt? with
      | .ok (some fmt) => if fmt != excludeFormat then formatSuggestion fmt else ""
      | _ => ""
    let baseMsg := match errorMsg? with
      | some msg => s!"Decoding error in '{fc.path}': {msg}"
      | none     => s!"Decoding error in '{fc.path}'"
    return if suggestion.isEmpty then baseMsg else s!"{baseMsg}. {suggestion}"

  /-- Parses a textual UPLC file and returns the resulting expression -/
  parseTextualUplc (filename : String) : TermElabM Expr := do
    let path := System.FilePath.mk filename
    let content ← liftM <| IO.FS.readFile path
    match programFromString content with
    | .ok p =>
        logInfo s!"Successfully decoded textual '{filename}'"
        return (toExpr p)
    | .error msg =>
        let fc : FileContents := { path, text := some content }
        let msg' ← decodingErrorWithSuggestion fc `textual (some msg)
        throwError msg'

  /-- Parses a flat-encoded UPLC file and returns the resulting expression -/
  parseFlatUplc (filename : String) : TermElabM Expr := do
    let path := System.FilePath.mk filename
    let bytes ← liftM <| IO.FS.readBinFile path
    match decodeProgramFromByteArray bytes with
    | .some p =>
        logInfo s!"Successfully decoded flat '{filename}'"
        return (toExpr p)
    | .none =>
        let fc : FileContents := { path, bin := some bytes }
        let msg' ← decodingErrorWithSuggestion fc `flat
        throwError msg'

  /-- Parses a flat hex-encoded UPLC file and returns the resulting expression -/
  parseFlatHexUplc (filename : String) : TermElabM Expr := do
    let path := System.FilePath.mk filename
    let content ← liftM <| IO.FS.readFile path
    let content' := String.trim content
    match flatEncodedScriptFromHex? content' with
    | .ok p =>
        logInfo s!"Successfully decoded flat hex '{filename}'"
        return (toExpr p)
    | .error msg =>
        let fc : FileContents := { path, text := some content }
        let msg' ← decodingErrorWithSuggestion fc `flat_hex (some msg)
        throwError msg'

  /-- Parses a single CBOR hex-encoded UPLC file and returns the resulting expression -/
  parseSingleCborHexUplc (filename : String) : TermElabM Expr := do
    let path := System.FilePath.mk filename
    let content ← liftM <| IO.FS.readFile path
    let content' := String.trim content
    match singleCborEncodedScriptFromHex? content' with
    | .ok p =>
        logInfo s!"Successfully decoded single CBOR hex '{filename}'"
        return (toExpr p)
    | .error msg =>
        let fc : FileContents := { path, text := some content }
        let msg' ← decodingErrorWithSuggestion fc `single_cbor_hex (some msg)
        throwError msg'

  /-- Parses a double CBOR hex-encoded UPLC file and returns the resulting expression -/
  parseDoubleCborHexUplc (filename : String) : TermElabM Expr := do
    let path := System.FilePath.mk filename
    let content ← liftM <| IO.FS.readFile path
    let content' := String.trim content
    match doubleCborEncodedScriptFromHex? content' with
    | .ok p =>
        logInfo s!"Successfully decoded double CBOR hex '{filename}'"
        return (toExpr p)
    | .error msg =>
        let fc : FileContents := { path, text := some content }
        let msg' ← decodingErrorWithSuggestion fc `double_cbor_hex (some msg)
        throwError msg'

  /-- Parses a UPLC file and returns the resulting expression based on format -/
  parseUplcFile (stx : Syntax) : TermElabM Expr := do
    let lang ← validLang stx[2]
    let format ← getFormat stx[3]
    let filename ← validFilename stx[4]
    let uplc ←
      match format with
      | `textual         => parseTextualUplc filename
      | `flat            => parseFlatUplc filename
      | `flat_hex        => parseFlatHexUplc filename
      | `single_cbor_hex => parseSingleCborHexUplc filename
      | `double_cbor_hex => parseDoubleCborHexUplc filename
      | _                => throwErrorAt stx[3] m!"unsupported format '{format}', expected 'textual', 'flat', 'flat_hex', 'single_cbor_hex', or 'double_cbor_hex'"
    return mkApp2 (mkConst ``PlutusScript.mk) lang uplc


end Internal

export Internal
  ( singleCborEncodedScriptFromHex!
    doubleCborEncodedScriptFromHex!
    flatEncodedScriptFromByteArray!
    flatEncodedScriptFromHex!
  )

end PlutusCore.UPLC.ScriptEncoding
