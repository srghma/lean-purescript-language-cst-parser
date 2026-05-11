module

public import PurescriptLanguageCstParser.Types.PType.Basic
public import PurescriptLanguageCstParser.Print
@[expose] public section

open PurescriptLanguageCstParser.Types
open PurescriptLanguageCstParser.Print

namespace PurescriptLanguageCstParser.Errors

def printTokenError : Token → String
  | .LeftParen => "'('"
  | .RightParen => "')'"
  | .LeftBrace => "'{'"
  | .RightBrace => "'}'"
  | .LeftSquare => "'['"
  | .RightSquare => "']'"
  | .LeftArrow style => match style with | .ASCII => "'<-'" | .Unicode => "'←'"
  | .RightArrow style => match style with | .ASCII => "'->'" | .Unicode => "'→'"
  | .RightFatArrow style => match style with | .ASCII => "'=>'" | .Unicode => "'⇒'"
  | .DoubleColon style => match style with | .ASCII => "'::'" | .Unicode => "'∷'"
  | .Forall style => match style with | .ASCII => "forall" | .Unicode => "'∀'"
  | .Equals => "'='"
  | .Pipe => "'|'"
  | .Tick => "`"
  | .Dot => "."
  | .Comma => "','"
  | .Underscore => "'_'"
  | .Backslash => "'\\'"
  | .At => "'@'"
  | .LowerName moduleName name => "identifier " ++ printQualified moduleName name.toString
  | .UpperName moduleName name => "proper identifier " ++ printQualified moduleName name.toString
  | .Operator moduleName name => "operator " ++ printQualified moduleName name.toString
  | .SymbolName moduleName name => "symbol " ++ printQualified moduleName name.toString
  | .SymbolArrow style => match style with | .ASCII => "(->)" | .Unicode => "(→)"
  | .Hole name => "hole ?" ++ name.toString
  | .Char raw _ => "char literal '" ++ raw ++ "'"
  | .String _raw _ => "string literal"
  | .RawString _ => "raw string literal"
  | .Int raw _ => "int literal " ++ raw
  | .Number raw _ => "number literal " ++ raw
  | .LayoutStart _ => "start of indented block"
  | .LayoutSep _ => "new indented block item"
  | .LayoutEnd _ => "end of indented block"

inductive ParseError where
  | UnexpectedEof
  | ExpectedEof (tok : Token)
  | UnexpectedToken (tok : Token)
  | ExpectedToken (expected saw : Token)
  | ExpectedClass (cls : String) (tok : Token)
  | LexExpected (expected : String) (saw : String)
  | LexInvalidCharEscape (s : String)
  | LexCharEscapeOutOfRange (s : String)
  | LexHexOutOfRange (s : String)
  | LexIntOutOfRange (s : String)
  | LexNumberOutOfRange (s : String)
  deriving Repr, BEq

structure RecoveredError where
  error : ParseError
  position : SourcePos
  tokens : Array SourceToken
  deriving Repr, BEq

def printParseError : ParseError → String
  | .UnexpectedEof => "Unexpected end of file"
  | .ExpectedEof tok => "Expected end of file, saw " ++ printTokenError tok
  | .UnexpectedToken tok => "Unexpected " ++ printTokenError tok
  | .ExpectedToken tok saw => "Expected " ++ printTokenError tok ++ ", saw " ++ printTokenError saw
  | .ExpectedClass cls saw => "Expected " ++ cls ++ ", saw " ++ printTokenError saw
  | .LexExpected str saw => "Expected " ++ str ++ ", saw " ++ saw
  | .LexInvalidCharEscape str => "Invalid character escape " ++ str
  | .LexCharEscapeOutOfRange str => "Character escape out of range " ++ str
  | .LexHexOutOfRange str => "Hex integer out of range 0x" ++ str
  | .LexIntOutOfRange str => "Int out of range " ++ str
  | .LexNumberOutOfRange str => "Number out of range " ++ str


end PurescriptLanguageCstParser.Errors
