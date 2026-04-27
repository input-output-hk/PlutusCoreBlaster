/-!
## Parser Combinators

A simple monadic parser combinator library for use in UPLC text parsing.
-/

namespace PlutusCore.Parser

namespace Internal

/-- The state threaded through all parsers: the full input string and current position. -/
structure ParseState where
  input : String
  pos   : String.Pos
  deriving Repr

/-- A parse error: a human-readable message and the position where it occurred. -/
structure ParseError where
  message : String
  pos     : String.Pos
  deriving Repr

/-- Core parser type: a function from state to either an error or a value with new state. -/
def Parser (α : Type) : Type :=
  ParseState → Except ParseError (α × ParseState)

-- ---------------------------------------------------------------------------
-- Monad instances
-- ---------------------------------------------------------------------------

instance : Monad Parser where
  pure a s    := .ok (a, s)
  bind p f s  :=
    match p s with
    | .error e    => .error e
    | .ok (a, s') => f a s'

instance : MonadExcept ParseError Parser where
  throw e      := fun _ => .error e
  tryCatch p h := fun s =>
    match p s with
    | .error e => h e s   -- restores original state on failure (full backtracking)
    | ok       => ok

-- ---------------------------------------------------------------------------
-- Primitive parsers
-- ---------------------------------------------------------------------------

/-- Fail with a message at the current position. -/
def fail (msg : String) : Parser α :=
  fun s => .error { message := msg, pos := s.pos }

/-- Every `Parser α` is inhabited (by the always-failing parser),
    which is required for `partial def`s inside `mutual` blocks. -/
instance : Inhabited (Parser α) := ⟨fail ""⟩

/-- Return the next character without consuming it; `none` at end of input. -/
def peek : Parser (Option Char) :=
  fun s =>
    if s.pos ≥ s.input.endPos then .ok (none, s)
    else .ok (some (s.input.get s.pos), s)

/-- Return the next maximum `n` characters without consuming them. -/
def lookAhead (n : Nat) : Parser (List Char) :=
  fun s =>
    let startOffset := String.offsetOfPos s.input s.pos
    .ok (s.input.data |> List.drop startOffset |> List.take n, s)

/-- `satisfy pred` consumes and returns the next `Char` if `pred` holds. -/
def satisfy (pred : Char → Bool) (description : String := "character") : Parser Char :=
  fun s =>
    if s.pos ≥ s.input.endPos then
      .error { message := s!"expected {description}, got end of input", pos := s.pos }
    else
      let c := s.input.get s.pos
      if pred c then
        .ok (c, { s with pos := s.input.next s.pos })
      else
        .error { message := s!"unexpected '{c}', expected {description}", pos := s.pos }

/-- Consume a specific character. -/
def char (c : Char) : Parser Char :=
  satisfy (· == c) s!"'{c}'"

/-- Consume the exact string `str`. -/
def string (str : String) : Parser String :=
  fun s =>
    let len   := str.utf8ByteSize
    let slice := s.input.extract s.pos ⟨s.pos.byteIdx + len⟩
    if slice == str then
      .ok (str, { s with pos := ⟨s.pos.byteIdx + len⟩ })
    else
      .error { message := s!"expected \"{str}\"", pos := s.pos }

/-- Try `p`; on failure restore original state and try `q`. -/
def orElse (p : Parser α) (q : Unit → Parser α) : Parser α :=
  fun s =>
    match p s with
    | .error _ => q () s
    | ok       => ok

instance : OrElse (Parser α) where
  orElse := orElse

-- ---------------------------------------------------------------------------
-- Whitespace and comments
-- ---------------------------------------------------------------------------

/-- Advance past the current line (stops after `\n` or at end of input). -/
partial def skipLine (s : String) (pos : String.Pos) : String.Pos :=
  if pos ≥ s.endPos then pos
  else if s.get pos == '\n' then s.next pos
  else skipLine s (s.next pos)

/-- Skip whitespace and `--` line comments. -/
partial def skipSpace (s : String) (pos : String.Pos) : String.Pos :=
  if pos ≥ s.endPos then pos
  else
    let c := s.get pos
    if c.isWhitespace then skipSpace s (s.next pos)
    else if c == '-' then
      let next := s.next pos
      if next < s.endPos && s.get next == '-' then
        skipSpace s (skipLine s (s.next next))
      else pos
    else pos

/-- Skip zero or more whitespace characters and `--` line comments. -/
def ws : Parser Unit :=
  fun s => .ok ((), { s with pos := skipSpace s.input s.pos })

-- ---------------------------------------------------------------------------
-- Combinators
-- ---------------------------------------------------------------------------

/-- `many p` runs `p` zero or more times and collects the results.
    Stops as soon as `p` fails; does not consume input on the failing attempt. -/
partial def many (p : Parser α) : Parser (List α) := fun s =>
  let rec loop (acc : List α) (s : ParseState) : Except ParseError (List α × ParseState) :=
    match p s with
    | .error _    => .ok (List.reverse acc, s)
    | .ok (a, s') => loop (a :: acc) s'
  loop [] s

/-- `many1 p` runs `p` one or more times. -/
def many1 (p : Parser α) : Parser (List α) := do
  let x  ← p
  let xs ← many p
  return x :: xs

/-- `sepBy p sep` parses zero or more `p` separated by `sep`. -/
def sepBy (p : Parser α) (sep : Parser Unit) : Parser (List α) :=
  (do
    let x  ← p
    let xs ← many (sep *> p)
    return x :: xs)
  <|> pure []

/-- Parse `open`, then `p`, then `close`; return the value from `p`. -/
def between (open' close' : Parser Unit) (p : Parser α) : Parser α := do
  open'
  let a ← p
  close'
  return a

/-- Parse `p` surrounded by `(` `)`, with optional inner whitespace. -/
def parens (p : Parser α) : Parser α :=
  ws *> between (char '(' *> ws) (ws *> char ')' *> pure ()) p

/-- Parse `p` surrounded by `[` `]`, with optional inner whitespace. -/
def brackets (p : Parser α) : Parser α :=
  ws *> between (char '[' *> ws) (ws *> char ']' *> pure ()) p

/-- Read characters while `pred` holds (zero or more). -/
partial def takeWhile (pred : Char → Bool) : Parser String := fun s =>
  let rec go (pos : String.Pos) : String.Pos :=
    if pos ≥ s.input.endPos then pos
    else if pred (s.input.get pos) then go (s.input.next pos)
    else pos
  let endPos := go s.pos
  .ok (s.input.extract s.pos endPos, { s with pos := endPos })

/-- Read a non-empty identifier: letters, digits, `_`. -/
def identifier : Parser String := do
  let s ← takeWhile (λ c => c.isAlphanum || c == '_')
  if s.isEmpty then fail "expected identifier"
  else return s

/-- Read a non-empty variable name.
    Note: the specification declares valid variable names as `[a-zA-Z][a-zA-Z0-9_']*(-[0-9])?`,
          however we opted in to allow every non-whitespace character, excluding
          characters that serve as delimiters in the UPLC grammar (`(`, `)`, `[`, `]`, `,`, `"`, `#`, `.`). -/
def varName : Parser String := do
  let s ← takeWhile notExcludedChar
  if s.isEmpty then fail "expected variable name"
  return s
 where
  notExcludedChar (c : Char) := !c.isWhitespace &&
    c != '(' && c != ')' && c != ']' && c != '[' && c != ',' && c != '"' && c != '#' && c != '.'

-- ---------------------------------------------------------------------------
-- Numeric parsers
-- ---------------------------------------------------------------------------

/-- Parse one or more decimal digits as a `Nat`. -/
def nat : Parser Nat := do
  let s ← takeWhile Char.isDigit
  match s.toNat? with
  | some n => return n
  | none   => fail "expected decimal number"

/-- Parse a signed decimal integer (optional leading `-`). -/
def signedInt : Parser Int := do
  let neg ← (char '-' *> pure true) <|> (char '+' *> pure false) <|> pure false
  let n   ← nat
  return if neg then -Int.ofNat n else Int.ofNat n

-- ---------------------------------------------------------------------------
-- Running a parser
-- ---------------------------------------------------------------------------

/-- Run `p` on the full string `input`, requiring all input is consumed
    (modulo trailing whitespace and comments). -/
def run (p : Parser α) (input : String) : Except ParseError α :=
  let init : ParseState := { input, pos := 0 }
  match p init with
  | .error e => .error e
  | .ok (a, s') =>
    match ws s' with
    | .error e => .error e
    | .ok (_, s'') =>
      if s''.pos ≥ s''.input.endPos then .ok a
      else .error { message := s!"unexpected input at byte {s''.pos.byteIdx}", pos := s''.pos }

/-- Run `p` on `input`; return `none` on any parse failure. -/
def runOption (p : Parser α) (input : String) : Option α :=
  match run p input with
  | .ok a    => some a
  | .error _ => none

end Internal

export Internal
  (
    -- Types
    Parser
    -- Functions
    brackets
    char
    fail
    identifier
    lookAhead
    many
    many1
    nat
    parens
    peek
    run
    runOption
    sepBy
    signedInt
    takeWhile
    varName
    ws
  )

end PlutusCore.Parser
