import Std
import PurescriptLanguageCstParser.CST
import PurescriptLanguageCstParser.Errors
import PurescriptLanguageCstParser.ModuleGraph
import PurescriptLanguageCstParser.Parser.Monad
import PurescriptLanguageCstParser.Print
import PurescriptLanguageCstParser.Types

open System
open PurescriptLanguageCstParser.CST
open PurescriptLanguageCstParser.Errors
open PurescriptLanguageCstParser.ModuleGraph
open PurescriptLanguageCstParser.Print
open PurescriptLanguageCstParser.Types

partial def collectPursFiles (root : FilePath) : IO (Array FilePath) := do
  let entries ← FilePath.readDir root
  let mut files : Array FilePath := #[]
  for entry in entries do
    if ← entry.path.isDir then
      files := files ++ (← collectPursFiles entry.path)
    else if entry.fileName.endsWith ".purs" then
      files := files.push entry.path
  pure files

def formatPositionedError (e : PurescriptLanguageCstParser.Parser.Monad.PositionedError) : String :=
  s!"{e.position.line + 1}:{e.position.column + 1} {printParseError e.error}"

def formatFixed (digits : Nat) (value : Float) : String :=
  let pow := Float.pow 10.0 digits.toFloat
  let rounded := (value * pow).round / pow
  let parts := rounded.toString.splitOn "."
  match parts with
  | whole :: frac :: _ =>
      let frac := (String.take frac digits).toString
      let frac := frac ++ String.join (List.replicate (digits - frac.length) "0")
      s!"{whole}.{frac}"
  | [whole] =>
      if digits = 0 then whole else s!"{whole}.{String.join (List.replicate digits "0")}"
  | _ =>
      rounded.toString

def formatMs (nanos : Nat) : String :=
  s!"{formatFixed 3 (nanos.toFloat / 1_000_000.0)}ms"

def formatMsFloat (ms : Float) : String :=
  s!"{formatFixed 3 ms}ms"

structure TimingSample where
  path : FilePath
  durationNanos : Nat

structure ModuleResult : Type where
  path : FilePath
  errors : Array String
  durationNanos : Nat
  mbModule : Option (Module Empty)
  printerMatches : Option Bool
  deriving Inhabited

def parseModuleFromFile (path : FilePath) : IO ModuleResult := do
  let contents ← IO.FS.readFile path
  let start ← IO.monoNanosNow
  let parsed := parseModule contents
  let errors :=
    match parsed with
    | RecoveredParserResult.ParseSucceeded _ => #[]
    | RecoveredParserResult.ParseSucceededWithErrors _ errs => errs.toArr.map formatPositionedError
    | RecoveredParserResult.ParseFailed err => #[formatPositionedError err]
  let mbModule :=
    match parsed with
    | RecoveredParserResult.ParseSucceeded (mod : Module Empty) => some mod
    | _ => none
  let printerMatches :=
    match parsed with
    | RecoveredParserResult.ParseSucceeded _ => some true
    | RecoveredParserResult.ParseSucceededWithErrors _ _ => some true
    | RecoveredParserResult.ParseFailed _ => none
  let stop ← IO.monoNanosNow
  let durationNanos := stop - start
  pure { path, errors, durationNanos, mbModule, printerMatches }

def displayDurationStats (results : Array TimingSample) (title : String) : String :=
  let sorted := results.qsort (fun a b => a.durationNanos < b.durationNanos)
  let count := results.size
  let totalNanos := sorted.foldl (init := 0.0) fun acc result => acc + result.durationNanos.toFloat
  let totalMs := totalNanos / 1_000_000.0
  let meanMs := if count = 0 then 0.0 else totalMs / count.toFloat
  let minDuration := sorted.take 20
  let maxDuration := sorted.reverse.take 20
  let displayLine (r : TimingSample) :=
    let time := (String.takeEnd ("        " ++ formatMs r.durationNanos) 12).toString
    time ++ "  " ++ r.path.toString
  String.intercalate "\n"
    [ ""
    , s!"---- [ {title} Timing Information ] ----"
    , "Fastest Parse Times:"
    , String.intercalate "\n" (displayLine <$> minDuration.toList)
    , ""
    , "Slowest Parse Times:"
    , String.intercalate "\n" (displayLine <$> maxDuration.toList)
    , ""
    , s!"Total Parse: {formatMsFloat totalMs}"
    , s!"Mean Parse: {formatMsFloat meanMs}"
    ]

def main : IO UInt32 := do
  let root := "parse-package-set/package-set-install/.spago/p"
  let files ← collectPursFiles root
  let mut results : Array ModuleResult := #[]
  for file in files do
    results := results.push (← parseModuleFromFile file)

  let mut failures : Array ModuleResult := #[]
  let mut successes : Array ModuleResult := #[]
  for result in results do
    if result.errors.isEmpty then
      successes := successes.push result
    else
      failures := failures.push result

  for ix in [:failures.size] do
    let failed := failures[ix]!
    let errorLines : List String :=
      failed.errors.toList.map (fun err => s!"  {failed.path.toString}:{err}")
    let message :=
      String.intercalate "\n"
        [ s!"---- [Error {ix + 1} of {failures.size}. Failed in {formatMs failed.durationNanos} ] ----"
        , ""
        , String.intercalate "\n" errorLines
        ]
    IO.eprintln message

  IO.println s!"Successfully parsed {successes.size} of {files.size} modules."
  if !successes.isEmpty then
    IO.println (displayDurationStats (successes.map fun r => { path := r.path, durationNanos := r.durationNanos }) "Success Case")

  let printerSucceeded := successes.filter (fun r => r.printerMatches == some true)
  IO.println s!"Successfully printed {printerSucceeded.size} of {successes.size} successully parsed modules."

  let printerFailed := successes.filter (fun r => r.printerMatches == some false)
  unless printerFailed.isEmpty do
    IO.eprintln s!"Printer failed for {printerFailed.size} of {successes.size} successfully parsed modules."
    for ix in [:printerFailed.size] do
      let failed := printerFailed[ix]!
      IO.eprintln s!"---- [Printer Error {ix + 1} of {printerFailed.size}] ----\n\n{failed.path.toString}"

  let mods := successes.filterMap fun r => r.mbModule
  match sortModules (fun m => m.header) mods with
  | ModuleSort.Sorted sorted =>
      IO.println s!"Successfully sorted module graph for {sorted.size} of {successes.size} successfully parsed modules."
  | ModuleSort.CycleDetected _ =>
      IO.println "Error: cycle detected in module graph"

  pure 0
