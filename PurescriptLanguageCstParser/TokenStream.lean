module

public import PurescriptLanguageCstParser.Types
public import PurescriptLanguageCstParser.Errors
public import PurescriptLanguageCstParser.Layout

@[expose] public section

open PurescriptLanguageCstParser.Types
open PurescriptLanguageCstParser.Errors
open PurescriptLanguageCstParser.Layout

namespace PurescriptLanguageCstParser.TokenStream

inductive TokenStream where
  | TokenEOF (pos : SourcePos) (comments : Array (Comment LineFeed))
  | TokenError (pos : SourcePos) (error : ParseError) (next : Option TokenStream) (stk : LayoutStack)
  | TokenCons (tok : SourceToken) (nextPos : SourcePos) (next : TokenStream) (stk : LayoutStack)
  deriving Repr

abbrev TokenStep := TokenStream

open TokenStream

def step (stream : TokenStream) : TokenStep := stream

def consTokens (tokens : Array (SourceToken × LayoutStack)) (rest : SourcePos × TokenStream) : SourcePos × TokenStream :=
  tokens.foldr
    (fun (tok, stk) (pos, next) =>
      (tok.range.start, TokenCons tok pos next stk))
    rest

def layoutStack : TokenStream → LayoutStack
  | TokenEOF _ _ => []
  | TokenError _ _ _ stk => stk
  | TokenCons _ _ _ stk => stk

partial def unwindLayout (pos : SourcePos) (eof : TokenStream) : LayoutStack → TokenStream
  | [] => step eof
  | (pos', lyt) :: tl =>
      if _h : isIndented lyt then
        TokenCons (lytToken pos (Token.LayoutEnd pos'.column)) pos (unwindLayout pos eof tl) tl
      else
        match lyt with
        | .LytRoot => step eof
        | _ => unwindLayout pos eof tl

def currentIndentColumn (stream : TokenStream) : Int :=
  match stream with
  | TokenError _ _ _ stk =>
      match currentIndent stk with
      | some p => Int.ofNat p.column.toNat
      | none => 0
  | TokenEOF _ _ => 0
  | TokenCons { value := Token.LayoutEnd col, .. } _ _ _ => Int.ofNat col.toNat
  | TokenCons _ _ _ stk =>
      match currentIndent stk with
      | some p => Int.ofNat p.column.toNat
      | none => 0

end PurescriptLanguageCstParser.TokenStream
