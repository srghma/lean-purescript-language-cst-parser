module

public import PurescriptLanguageCstParser.TokenStream
public import PurescriptLanguageCstParser.Errors

@[expose] public section

open PurescriptLanguageCstParser.Types
open PurescriptLanguageCstParser.Errors
open PurescriptLanguageCstParser.TokenStream

namespace PurescriptLanguageCstParser.Parser.Monad

structure PositionedError where
  position : SourcePos
  error : ParseError
  deriving Repr, BEq

structure ParserState where
  consumed : Bool
  errors : Array PositionedError
  stream : TokenStream
  deriving Repr

instance : Inhabited PositionedError where
  default := { position := { line := 0, column := 0 }, error := .UnexpectedEof }

instance : Inhabited ParserState where
  default := { consumed := false, errors := #[], stream := TokenStream.TokenEOF { line := 0, column := 0 } #[] }

def initialParserState (stream : TokenStream) : ParserState :=
  { consumed := false, errors := #[], stream }

inductive ParserResult (α : Type) where
  | ParseFail (error : PositionedError) (state : ParserState)
  | ParseSucc (value : α) (state : ParserState)

instance [Inhabited α] : Inhabited (ParserResult α) where
  default := .ParseSucc default default

structure Parser (α : Type) where
  run : ParserState → ParserResult α

def defer {α : Type} (k : Unit → Parser α) : Parser α :=
  { run := fun state => (k ()).run state }

def fromParserResult {α : Type} : ParserResult α → Except PositionedError (α × Array PositionedError)
  | .ParseFail error _ => .error error
  | .ParseSucc value state => .ok (value, state.errors)

def runParser' {α : Type} (state : ParserState) (p : Parser α) : ParserResult α :=
  p.run state

def runParser {α : Type} (stream : TokenStream) (p : Parser α) : Except PositionedError (α × Array PositionedError) :=
  fromParserResult (runParser' (initialParserState stream) p)

def appendConsumed (state1 state2 : ParserState) : ParserState :=
  if state1.consumed then
    { state2 with consumed := true }
  else
    state2

instance : Functor Parser where
  map f p := { run := fun state =>
      match p.run state with
      | .ParseFail err st => .ParseFail err st
      | .ParseSucc a st => .ParseSucc (f a) st }

instance : Pure Parser where
  pure a := { run := fun state => .ParseSucc a state }

instance : Bind Parser where
  bind p f := { run := fun state =>
      match p.run state with
      | .ParseFail err st => .ParseFail err st
      | .ParseSucc a st =>
          match f a |>.run (appendConsumed state st) with
          | .ParseFail err st' => .ParseFail err st'
          | .ParseSucc b st' => .ParseSucc b st' }

instance : Monad Parser where
  map := Functor.map
  pure := Pure.pure
  bind := Bind.bind

instance {α : Type} : OrElse (Parser α) where
  orElse := fun p1 p2 =>
    { run := fun state =>
        if state.consumed then
          match p1.run { state with consumed := false } with
          | .ParseFail err st =>
              if st.consumed then
                .ParseFail err st
              else
                (p2 ()).run state
          | .ParseSucc a st => .ParseSucc a st
        else
          match p1.run state with
          | .ParseFail err st =>
              if st.consumed then
                .ParseFail err st
              else
                (p2 ()).run state
          | .ParseSucc a st => .ParseSucc a st }

def fail {α : Type} (error : PositionedError) : Parser α :=
  { run := fun state => .ParseFail error state }

def tryP {α : Type} (p : Parser α) : Parser α :=
  { run := fun state =>
      match p.run state with
      | .ParseFail error st => .ParseFail error { st with consumed := state.consumed }
      | .ParseSucc a st => .ParseSucc a st }

def lookAhead {α : Type} (p : Parser α) : Parser α :=
  { run := fun state =>
      match p.run state with
      | .ParseFail error _ => .ParseFail error state
      | .ParseSucc a _ => .ParseSucc a state }

def take {α : Type} (k : SourceToken → Except ParseError α) : Parser α :=
  { run := fun state =>
      match state.stream with
      | TokenStream.TokenError pos error _ _ => .ParseFail { position := pos, error } state
      | TokenStream.TokenEOF pos _ => .ParseFail { position := pos, error := .UnexpectedEof } state
      | TokenStream.TokenCons tok _ next _ =>
          match k tok with
          | .error error => .ParseFail { position := tok.range.start, error } state
          | .ok a => .ParseSucc a { state with consumed := true, stream := next } }

def eof : Parser (SourcePos × Array (Comment LineFeed)) :=
  { run := fun state =>
      match state.stream with
      | TokenStream.TokenError pos error _ _ => .ParseFail { position := pos, error } state
      | TokenStream.TokenEOF pos comments => .ParseSucc (pos, comments) { state with consumed := true }
      | TokenStream.TokenCons tok _ _ _ => .ParseFail { position := tok.range.start, error := .ExpectedEof tok.value } state }

partial def many {α : Type} (p : Parser α) : Parser (Array α) :=
  { run := fun state =>
      let rec go (acc : Array α) (st : ParserState) : ParserResult (Array α) :=
        let st' := if st.consumed then { st with consumed := false } else st
        match p.run st' with
        | .ParseFail err st'' =>
            if st''.consumed then
              .ParseFail err st''
            else
              .ParseSucc acc.reverse st
        | .ParseSucc a st'' =>
            go (acc.push a) (appendConsumed st st'')
      go #[] state }

def optional {α : Type} (p : Parser α) : Parser (Option α) :=
  (some <$> p) <|> (pure (none : Option α))

def recover {α : Type} (k : PositionedError → TokenStream → Option (α × TokenStream)) (p : Parser α) : Parser α :=
  { run := fun state =>
      match p.run { state with consumed := false } with
      | .ParseFail err st =>
          match k err state.stream with
          | none => .ParseFail err { st with consumed := state.consumed }
          | some (a, stream) =>
              .ParseSucc a { consumed := true, errors := st.errors.push err, stream }
      | .ParseSucc a st => .ParseSucc a st }

end PurescriptLanguageCstParser.Parser.Monad
