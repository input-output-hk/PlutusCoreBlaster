namespace PlutusCore.UPLC.CekValue

def tryCatchSome (f : Except String α) (k : α → β) : Option β :=
  match f with
  | Except.ok r => some (k r)
  | Except.error _ => none

 end PlutusCore.UPLC.CekValue
