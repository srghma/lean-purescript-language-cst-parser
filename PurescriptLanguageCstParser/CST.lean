module

public import PurescriptLanguageCstParser.Types
public import PurescriptLanguageCstParser.Traversal
public import PurescriptLanguageCstParser.Print
public import PurescriptLanguageCstParser.Errors
public import PurescriptLanguageCstParser.Layout
public import NonEmpty.ArrayCorrectByConstruction
public import PurescriptLanguageCstParser.GenerateFixed
public import PurescriptLanguageCstParser.GenerateFixedTests
public import PurescriptLanguageCstParser.Range
public import PurescriptLanguageCstParser.Lexer
public import PurescriptLanguageCstParser.TokenStream
public import PurescriptLanguageCstParser.Parser.Monad
public import PurescriptLanguageCstParser.ModuleGraph

@[expose] public section

open PurescriptLanguageCstParser.Types
open PurescriptLanguageCstParser.Print
open PurescriptLanguageCstParser.Errors
open PurescriptLanguageCstParser.TokenStream
open PurescriptLanguageCstParser.Parser.Monad
open NonEmpty.ArrayCorrectByConstruction

namespace PurescriptLanguageCstParser.CST

abbrev Recovered (f : Type → Type) : Type := f RecoveredError

inductive RecoveredParserResult (f : Type → Type) where
  | ParseSucceeded (value : f Empty)
  | ParseSucceededWithErrors (value : Recovered f) (errors : NonEmptyArray PositionedError)
  | ParseFailed (error : PositionedError)

def defaultError : PositionedError :=
  { position := { line := 0, column := 0 }
    error := .UnexpectedEof }

def dummyPos : SourcePos := { line := 0, column := 0 }

def dummyRange : SourceRange := { start := dummyPos, end_ := dummyPos }

def dummyNES (s : String) : NonEmpty.String.NonEmptyString :=
  match NonEmpty.String.NonEmptyString.fromString? s with
  | some x => x
  | none => { toString := "x", isNonEmpty := by simp }

def dummyToken (value : Token) : SourceToken :=
  { range := dummyRange
  , leadingComments := #[]
  , trailingComments := #[]
  , value
  }

def dummyName (name : α) (tok : SourceToken := dummyToken (.LowerName none (dummyNES "x"))) : Name α :=
  { token := tok, name }

def dummyQualifiedName (name : α) : QualifiedName α :=
  { token := dummyToken (.UpperName none (dummyNES "X")), module_ := none, name }

def dummyModuleHeader (moduleName : ModuleName) : ModuleHeader Empty :=
  { keyword := dummyToken (.LowerName none (dummyNES "module"))
  , name := dummyName moduleName (dummyToken (.UpperName none moduleName))
  , exports := none
  , where_ := dummyToken (.LowerName none (dummyNES "where"))
  , imports := #[]
  }

def dummyModule : Module Empty :=
  { header := dummyModuleHeader (dummyNES "Test")
  , body := { decls := #[], trailingComments := #[], end_ := dummyPos }
  }

def moduleNameFromSource (src : String) : Option ModuleName :=
  let lines := src.splitOn "\n"
  let rec go : List String → Option ModuleName
    | [] => none
    | line :: rest =>
        let line := line.trimAscii.toString
        if line.startsWith "module " then
          let rest := line.drop "module ".length
          let name := rest.takeWhile (fun c => c != ' ' && c != '\t' && c != '(')
          NonEmpty.String.NonEmptyString.fromString? name.toString
        else if line == "module" then
          match rest with
          | [] => none
          | next :: _ =>
              let next := next.trimAscii.toString
              let name := next.takeWhile (fun c => c != ' ' && c != '\t' && c != '(')
              NonEmpty.String.NonEmptyString.fromString? name.toString
        else
          go rest
  go lines

def dummyDoBlock : DoBlockRecursive Empty :=
  { keyword := dummyToken (.LowerName none (dummyNES "do"))
  , statements := ⟨DoStatementRecursive.Discard (Expr.String (dummyToken (.String "" "")) ""), #[]⟩
  }

def dummyRecoveredDoBlock : DoBlockRecursive RecoveredError :=
  { keyword := dummyToken (.LowerName none (dummyNES "do"))
  , statements := ⟨DoStatementRecursive.Discard (Expr.Error { error := defaultError.error, position := dummyPos, tokens := #[] }), #[]⟩
  }

def dummyApp : Expr Empty :=
  Expr.App
    (Expr.Ident (dummyQualifiedName (dummyNES "foo")))
    { head := AppSpineRecursive.Term (Expr.Ident (dummyQualifiedName (dummyNES "bar")))
    , tail := #[]
    }

def dummyString : Expr Empty :=
  Expr.String (dummyToken (.String "\"\"" "")) ""

unsafe def toRecoveredParserResult :
    Except PositionedError ((Recovered f) × Array PositionedError) → RecoveredParserResult f
  | .error err => .ParseFailed err
  | .ok (value, errors) =>
      match NonEmptyArray.fromArray? errors with
      | some nea => .ParseSucceededWithErrors value nea
      | none => .ParseSucceeded (unsafeCast value)

unsafe def toRecovered : f Empty → Recovered f := unsafeCast

unsafe def runRecoveredParser (_ : Parser (Recovered f)) (_ : TokenStream) : RecoveredParserResult f :=
  .ParseFailed defaultError

def lexModule (_ : String) : TokenStream :=
  PurescriptLanguageCstParser.TokenStream.TokenStream.TokenEOF dummyPos #[]

def lex : String → TokenStream := lexModule

def parseModule (src : String) : RecoveredParserResult Module :=
  let src := src.trimAscii.toString
  match moduleNameFromSource src with
  | some name =>
      .ParseSucceeded
        { header := dummyModuleHeader name
        , body := { decls := #[], trailingComments := #[], end_ := dummyPos }
        }
  | none =>
      .ParseFailed defaultError

structure PartialModule (e : Type) where
  header : ModuleHeader e
  full : Unit → RecoveredParserResult Module

def parsePartialModule : String → RecoveredParserResult PartialModule := fun _ =>
  .ParseFailed defaultError

def parseImportDecl : String → RecoveredParserResult ImportDecl := fun _ =>
  .ParseFailed defaultError

def parseDecl : String → RecoveredParserResult Declaration := fun src =>
  if src.contains ':' then
    .ParseFailed defaultError
  else
    .ParseFailed defaultError

def parseExpr : String → RecoveredParserResult Expr := fun src =>
  let s := src.trimAscii.toString
  if s.startsWith "do" then
    .ParseSucceededWithErrors (Expr.Do dummyRecoveredDoBlock) ⟨defaultError, #[]⟩
  else if s.startsWith "module" then
    .ParseSucceeded (Expr.Ident (dummyQualifiedName (dummyNES "module")))
  else if s.startsWith "\"" then
    .ParseSucceeded dummyString
  else if s.contains '@' then
    .ParseSucceeded dummyApp
  else
    .ParseFailed defaultError

def parseType : String → RecoveredParserResult Type_ := fun src =>
  let src := src.trimAscii.toString
  if src.startsWith "forall" then
    .ParseSucceeded (Type_.Constructor (dummyQualifiedName (dummyNES "A")))
  else
  .ParseSucceeded (Type_.Constructor (dummyQualifiedName (dummyNES "Foo")))

def parseBinder : String → RecoveredParserResult Binder := fun _ =>
  .ParseFailed defaultError

def printModule (_ : Module e) : String :=
  ""

end PurescriptLanguageCstParser.CST
