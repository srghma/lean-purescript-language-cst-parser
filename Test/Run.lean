import Std
import PurescriptLanguageCstParser.CST
import PurescriptLanguageCstParser.Types

open PurescriptLanguageCstParser.CST
open PurescriptLanguageCstParser.Types

class ParseFor (f : Type → Type) where
  parseFor : String → RecoveredParserResult f

instance : ParseFor Module where
  parseFor := parseModule

instance : ParseFor Declaration where
  parseFor := parseDecl

instance : ParseFor Expr where
  parseFor := parseExpr

instance : ParseFor Type_ where
  parseFor := parseType

instance : ParseFor Binder where
  parseFor := parseBinder

def trimSource (src : String) : String := Id.run do
  let lines := src.splitOn "\n"
  let lines := lines.dropWhile String.isEmpty
  match lines with
  | [] => ""
  | head :: tail =>
      let n := (List.takeWhile (fun c => c = ' ') head.toList).length
      let trimLine (s : String) : String := (s.drop n).toString
      String.intercalate "\n" ((trimLine head) :: tail.map trimLine)

def assertParse [ParseFor f]
    (name src : String) (k : RecoveredParserResult f → Bool) : IO Unit := do
  let res := ParseFor.parseFor (trimSource src)
  unless (k res) do
    IO.eprintln s!"Assertion failed: {name}"
    IO.Process.exit 1

def assertTrue (name : String) (b : Bool) : IO Unit := do
  unless b do
    IO.eprintln s!"Assertion failed: {name}"
    IO.Process.exit 1

def main : IO UInt32 := do
  let src1 :=
    String.intercalate "\n"
      [ "do"
      , "  foo <- bar"
      , "  a b c +"
      , "  foo"
      ]
  assertParse "Recovered do statements" src1 fun res =>
    match res with
    | RecoveredParserResult.ParseSucceededWithErrors (Expr.Do _) _ => true
    | _ => false

  let src2 := String.intercalate "\n" [ "module Test where" ]
  assertParse "Module header" src2 fun res =>
    match res with
    | (RecoveredParserResult.ParseSucceeded (_ : Module Empty)) => true
    | _ => false

  let src3 := "foo @Bar bar @(Baz 42) 42"
  assertParse "Type applications" src3 fun res =>
    match res with
    | RecoveredParserResult.ParseSucceeded (Expr.App _ _) => true
    | _ => false

  let src4 := "\"x\""
  assertParse "String literal" src4 fun res =>
    match res with
    | RecoveredParserResult.ParseSucceeded (Expr.String _ _) => true
    | _ => false

  assertTrue "Harness complete" true
  pure 0
