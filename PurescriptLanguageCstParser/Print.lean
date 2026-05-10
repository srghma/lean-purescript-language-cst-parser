module

public import PurescriptLanguageCstParser.Types.PType
public import NonEmpty.ArrayUtil

@[expose] public section

namespace PurescriptLanguageCstParser.Print

open PurescriptLanguageCstParser.Types

inductive TokenOption
  | ShowLayout
  | HideLayout
  deriving Repr, BEq, Inhabited

def printLineFeed : LineFeed → String
  | .LF => "\n"
  | .CRLF => "\r\n"

def power (s : String) (n : USize) : String :=
  let rec go (acc : String) (k : USize) : String :=
    if h : k = 0 then
      acc
    else
      go (acc ++ s) (k - 1)
  termination_by k.toNat
  decreasing_by
    simp_wf
    have h_ne : k.toNat ≠ 0 := by
      intro h0
      apply h
      apply USize.toNat_inj.1
      rw [h0, USize.toNat_zero]
    rw [USize.toNat_sub_of_le]
    · simp [USize.toNat_one]
      omega
    · apply USize.le_iff_toNat_le.2
      simp [USize.toNat_one]
      omega
  go "" n

def printComment {l : Type} (k : l → String) : Comment l → String
  | .Comment str => str.toString
  | .Space n => power " " n
  | .Line l n => power (k l) n

def printQualified (moduleName : Option ModuleName) (name : String) : String :=
  match moduleName with
  | none => name
  | some mn => mn.toString ++ "." ++ name

def printTokenWithOption (option : TokenOption) : Token → String
  | .LeftParen => "("
  | .RightParen => ")"
  | .LeftBrace => "{"
  | .RightBrace => "}"
  | .LeftSquare => "["
  | .RightSquare => "]"
  | .LeftArrow style => match style with | .ASCII => "<-" | .Unicode => "←"
  | .RightArrow style => match style with | .ASCII => "->" | .Unicode => "→"
  | .RightFatArrow style => match style with | .ASCII => "=>" | .Unicode => "⇒"
  | .DoubleColon style => match style with | .ASCII => "::" | .Unicode => "∷"
  | .Forall style => match style with | .ASCII => "forall" | .Unicode => "∀"
  | .Equals => "="
  | .Pipe => "|"
  | .Tick => "`"
  | .Dot => "."
  | .Comma => ","
  | .Underscore => "_"
  | .Backslash => "\\"
  | .At => "@"
  | .LowerName moduleName name => printQualified moduleName name.toString
  | .UpperName moduleName name => printQualified moduleName name.toString
  | .Operator moduleName name => printQualified moduleName name.toString
  | .SymbolName moduleName name => printQualified moduleName ("(" ++ name.toString ++ ")")
  | .SymbolArrow style => match style with | .ASCII => "(->)" | .Unicode => "(→)"
  | .Hole name => "?" ++ name.toString
  | .Char raw _ => "'" ++ raw ++ "'"
  | .String raw _ => "\"" ++ raw ++ "\""
  | .RawString raw => "\"\"\"" ++ raw ++ "\"\"\""
  | .Int raw _ => raw
  | .Number raw _ => raw
  | .LayoutStart _ => match option with | .ShowLayout => "{" | .HideLayout => ""
  | .LayoutSep _ => match option with | .ShowLayout => ";" | .HideLayout => ""
  | .LayoutEnd _ => match option with | .ShowLayout => "}" | .HideLayout => ""

def printToken : Token → String := printTokenWithOption .HideLayout

def printCommentWithoutLine : CommentWithoutLine → String
  | .Comment str => str.toString
  | .Space n => "".pushn ' ' n.toNat

def printSourceTokenWithOption (option : TokenOption) (tok : SourceToken) : String :=
  let leading := NonEmpty.ArrayUtil.foldMap (· ++ ·) (printComment printLineFeed) "" tok.leadingComments
  let value := printTokenWithOption option tok.value
  let trailing := NonEmpty.ArrayUtil.foldMap (· ++ ·) printCommentWithoutLine "" tok.trailingComments
  leading ++ value ++ trailing

def printSourceToken : SourceToken → String := printSourceTokenWithOption .HideLayout

end PurescriptLanguageCstParser.Print
