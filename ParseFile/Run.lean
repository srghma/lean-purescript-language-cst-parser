import Std
import PurescriptLanguageCstParser.CST
import PurescriptLanguageCstParser.Errors
import PurescriptLanguageCstParser.Lexer
import PurescriptLanguageCstParser.Parser.Monad
import PurescriptLanguageCstParser.Print
import PurescriptLanguageCstParser.TokenStream
import PurescriptLanguageCstParser.Types

open PurescriptLanguageCstParser.CST
open PurescriptLanguageCstParser.Errors
open PurescriptLanguageCstParser.Lexer
open PurescriptLanguageCstParser.Print
open PurescriptLanguageCstParser.TokenStream
open PurescriptLanguageCstParser.Types

def skipArgDash (args : List String) : List String :=
  match args with
  | "--" :: rest => rest
  | _ => args

def printPositionedError (e : PurescriptLanguageCstParser.Parser.Monad.PositionedError) : String :=
  s!"[{e.position.line + 1}:{e.position.column + 1}] {printParseError e.error}"

partial def tokenStreamToArray : TokenStream → Except ParseError (Array SourceToken)
  | TokenStream.TokenEOF _ _ => .ok #[]
  | TokenStream.TokenError _ err _ _ => .error err
  | TokenStream.TokenCons tok _ next _ => do
      let rest ← tokenStreamToArray next
      pure (rest.push tok)

def emitTokens (contents : String) : IO Unit := do
  match tokenStreamToArray (lexModule contents) with
  | .ok tokens =>
      for tok in tokens do
        IO.println (printSourceTokenWithOption .ShowLayout tok)
  | .error err =>
      IO.eprintln (printParseError err)

def main (args : List String) : IO UInt32 := do
  let args := skipArgDash args
  match args with
  | [] =>
      IO.println "File path required"
      pure 0
  | fileName :: _ => do
      let contents ← IO.FS.readFile fileName
      let showTokens := args.contains "--tokens" || args.contains "-t"
      if showTokens then
        emitTokens contents

      match parseModule contents with
      | RecoveredParserResult.ParseSucceeded _ =>
          IO.println "Parse succeeded."
      | RecoveredParserResult.ParseSucceededWithErrors _ errs =>
          IO.println "Parse succeeded with errors."
          for err in errs do
            IO.eprintln (printPositionedError err)
      | RecoveredParserResult.ParseFailed err =>
          IO.println "Parse failed."
          IO.eprintln (printPositionedError err)

      pure 0
