import PlutusCore.ByteString.Basic

namespace PlutusCore.String
open PlutusCore.ByteString

/-! ## Formalisation for PlutusCore String representation and builtin functions. -/

namespace PlutusCore.StringInternal
-- We here use the Lean4 String representation

/-! ## Builtin String functions. -/

/-- Return an empty String -/
def emptyString : String := ""

/-- Given two Strings `[u₁, ..., uₘ]` and `[v₁, ..., vₙ]` return `[u₁, ..., uₘ, v₁, ..., vₙ]` -/
def appendString (s1 : String) (s2 : String) : String := s1 ++ s2

def equalsString (s1 : String) (s2 : String) : Bool := s1 == s2

/-- Coverts String to ByteString using utf8 encoding -/
def encodeUtf8 (s : String) : ByteString := s.toUTF8

/-- Decodes a ByteString to String using utf8 decoding.
    An error is triggered when the ByteString is not uft8 encoded.
-/
def decodeUtf8 (bs : ByteString) : Except String String :=
 if h : String.validateUTF8 bs
 then pure (String.fromUTF8 bs h)
 else throw "decodeUtf8: invalid ByteString"

end PlutusCore.StringInternal

export PlutusCore.StringInternal
  ( -- builtin functions
    appendString
    decodeUtf8
    emptyString
    encodeUtf8
    equalsString
  )

end PlutusCore.String

