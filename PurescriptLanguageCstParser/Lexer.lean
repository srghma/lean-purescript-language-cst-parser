module
public import PurescriptLanguageCstParser.Types
public import PurescriptLanguageCstParser.Errors
public import PurescriptLanguageCstParser.Layout
public import PurescriptLanguageCstParser.Range
import NonEmpty.StringSlice
import NonEmpty.String

open PurescriptLanguageCstParser.Types
open PurescriptLanguageCstParser.Errors
open PurescriptLanguageCstParser.Layout
open NonEmpty.String
open NonEmpty.StringSlice

namespace PurescriptLanguageCstParser.Lexer

/-! ### Lexer State -/

structure LexState where
  input : String.Slice
  deriving Inhabited, BEq

inductive LexResult (e : Type) (α : Type) where
  | ok    (val : α) (nextState : LexState)
  | error (err : e) (nextState : LexState)

-- instance {e α : Type} [Inhabited α] : Inhabited (LexResult e α) where
--   default := .ok default default

def Lex (e : Type) (α : Type) := LexState → LexResult e α

namespace Lex

variable {e α β : Type}

@[inline] def run (l : Lex e α) (st : LexState) : LexResult e α := l st

protected def pure (val : α) : Lex e α := fun s => .ok val s

protected def bind (l : Lex e α) (f : α → Lex e β) : Lex e β := fun s =>
  match l s with
  | .ok val s' => f val s'
  | .error err s' => .error err s'

protected def map (f : α → β) (l : Lex e α) : Lex e β := fun s =>
  match l s with
  | .ok val s' => .ok (f val) s'
  | .error err s' => .error err s'

/-- Backtracks only if no input was consumed by the first parser. Propagates the original error if no backtrack occurs. -/
protected def orElse (l1 l2 : Lex e α) : Lex e α := fun s =>
  match l1 s with
  | .error err1 s' => if s'.input == s.input then l2 s else .error err1 s'
  | .ok val s' => .ok val s'

/-- Safely constructs a `NonEmptyStringSlice`, returning a legitimate lexer error on empty. -/
def extractNonEmpty (slice : String.Slice) (expected : String) : Lex ParseError NonEmptyStringSlice := fun s =>
  match NonEmptyStringSlice.fromSlice? slice with
  | some nes => .ok nes s
  | none => .error (ParseError.LexExpected expected "empty string") s

end Lex

instance : Monad (Lex e) where
  pure := Lex.pure
  bind := Lex.bind
  map  := Lex.map

instance : MonadExceptOf e (Lex e) where
  throw err := fun s => .error err s
  tryCatch l h := fun s =>
    match l s with
    | .error err s' => (h err) s'
    | .ok val s' => .ok val s'

/-! ### Low-level primitive scanners -/

@[inline] def isAtEnd (s : LexState) : Bool :=
  s.input.isEmpty

def peek : Lex ParseError Char := fun s =>
  match s.input.front? with
  | some c => .ok c s
  | none => .error (ParseError.LexExpected "character" "EOF") s

def advance : Lex e Unit := fun s =>
  .ok () { s with input := s.input.drop 1 }

def satisfy (expected : String) (p : Char → Bool) : Lex ParseError Char := do
  let c ← peek
  if p c then
    advance
    pure c
  else
    throw (ParseError.LexExpected expected c.toString)

def takeWhile (p : Char → Bool) : Lex ParseError Unit := fun s =>
  .ok () { s with input := s.input.dropWhile p }

/-! ### Purescript Token Parsers -/

def isIdentChar (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c == '_' || c == '\''

/-- Slices an identifier directly using pointers to avoid intermediate concatenation. -/
def parseProper : Lex ParseError NonEmptyStringSlice := fun s =>
  match s.input.front? with
  | some c =>
    if c.isUpper then
      let afterFirst := s.input.startPos.nextn 1
      let rest := s.input.sliceFrom afterFirst
      let stop := String.Slice.Pos.ofSliceFrom (p₀ := afterFirst) (rest.skipPrefixWhile isIdentChar)
      let tokenSlice := s.input.sliceTo stop
      let nextInput := s.input.sliceFrom stop
      match NonEmptyStringSlice.fromSlice? tokenSlice with
      | some val => .ok val { s with input := nextInput }
      | none => .error (ParseError.LexExpected "proper name" "empty string") s
    else
      .error (ParseError.LexExpected "proper name" "uppercase letter") s
  | none =>
    .error (ParseError.LexExpected "proper name" "uppercase letter") s

def parseIdent : Lex ParseError NonEmptyStringSlice := fun s =>
  match s.input.front? with
  | some c =>
    if c.isLower || c == '_' then
      let afterFirst := s.input.startPos.nextn 1
      let rest := s.input.sliceFrom afterFirst
      let stop := String.Slice.Pos.ofSliceFrom (p₀ := afterFirst) (rest.skipPrefixWhile isIdentChar)
      let tokenSlice := s.input.sliceTo stop
      let nextInput := s.input.sliceFrom stop
      match NonEmptyStringSlice.fromSlice? tokenSlice with
      | some val => .ok val { s with input := nextInput }
      | none => .error (ParseError.LexExpected "ident" "empty string") s
    else
      .error (ParseError.LexExpected "ident" "lowercase or underscore") s
  | none =>
    .error (ParseError.LexExpected "ident" "lowercase or underscore") s

def parseHole : Lex ParseError Token := do
  let _ ← satisfy "question mark" (· == '?')
  let name ← (fun s =>
    match parseIdent s with
    | .ok val s' => .ok val s'
    | .error _ _ => parseProper s)
  pure (.Hole name.toNonEmptyString)

def parseStringLiteral : Lex ParseError Token := fun s =>
  match s.input.front? with
  | some '"' =>
    let rest := s.input.drop 1
    let stop := rest.skipPrefixWhile (· != '"')
    if h : stop = rest.endPos then
      .error (ParseError.LexExpected "closing quote" "EOF") s
    else
      let val := (rest.sliceTo stop).copy
      .ok (.String val val) { s with input := rest.sliceFrom (stop.next h) }
  | _ =>
    .error (ParseError.LexExpected "opening quote" "char") s

def parseNumericLiteral : Lex ParseError Token := fun s =>
  let stop := s.input.skipPrefixWhile Char.isDigit
  let digits := s.input.sliceTo stop
  if digits.isEmpty then
    .error (ParseError.LexExpected "digit" "none") s
  else
    match NonEmptyStringSlice.fromSlice? digits with
    | some val => .ok (.Int val.toNonEmptyString (.SmallInt 0)) { s with input := s.input.sliceFrom stop }
    | none => .error (ParseError.LexExpected "number" "empty string") s

/-! ### Main Lexing Logic -/

def token : Lex ParseError Token := fun s =>
  match parseHole s with
  | .ok v s' => .ok v s'
  | .error _ _ =>
  match parseStringLiteral s with
  | .ok v s' => .ok v s'
  | .error _ _ =>
  match parseNumericLiteral s with
  | .ok v s' => .ok v s'
  | .error _ _ =>
  match parseIdent s with
  | .ok v s' => .ok (.LowerName none v.toNonEmptyString) s'
  | .error _ _ =>
  match parseProper s with
  | .ok v s' => .ok (.UpperName none v.toNonEmptyString) s'
  | .error e s' => .error e s'

def bumpText (pos : SourcePos) (colOffset : Nat) (str : String) : SourcePos :=
  let rec go (line : Nat) (column : Nat) (cs : List Char) : SourcePos :=
    match cs with
    | [] => { line := line.toUSize, column := (column + colOffset).toUSize }
    | '\n' :: rest => go (line + 1) 0 rest
    | '\r' :: '\n' :: rest => go (line + 1) 0 rest
    | '\r' :: rest => go line (column + 1) rest
    | _ :: rest => go line (column + 1) rest
  go pos.line.toNat pos.column.toNat str.toList

def bumpToken (pos : SourcePos) (tok : Token) : SourcePos :=
  match tok with
  | .LeftParen | .RightParen | .LeftBrace | .RightBrace | .LeftSquare | .RightSquare
  | .Equals | .Pipe | .Tick | .Dot | .Comma | .Underscore | .Backslash | .At =>
    { pos with column := pos.column + 1 }
  | .LowerName _ n | .UpperName _ n | .Operator _ n | .Hole n =>
    { pos with column := pos.column + n.toString.length.toUSize }
  | .String raw _ => bumpText pos 1 raw
  | .Int raw _ | .Number raw _ => { pos with column := pos.column + raw.toString.length.toUSize }
  | _ => pos

partial def lexWithState (st : LexState) (sp : SourcePos) (acc : Array Token) : Array Token :=
  if isAtEnd st then acc
  else
    match token st with
    | .ok tok st' =>
      lexWithState st' (bumpToken sp tok) (acc.push tok)
    | .error _ st' =>
      lexWithState { st' with input := st'.input.drop 1 } sp acc

def lex (str : String) : Array Token :=
  lexWithState ⟨str.toSlice⟩ { line := 0, column := 0 } #[]

end PurescriptLanguageCstParser.Lexer
