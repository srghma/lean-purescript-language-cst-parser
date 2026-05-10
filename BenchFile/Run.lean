import Std
import PurescriptLanguageCstParser.CST

open PurescriptLanguageCstParser.CST

def skipArgDash (args : List String) : List String :=
  match args with
  | "--" :: rest => rest
  | _ => args

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

structure BenchStats where
  mean : Float
  stddev : Float
  min : Float
  max : Float

def computeStats (durations : Array Float) : BenchStats :=
  if durations.size = 0 then
    { mean := 0.0, stddev := 0.0, min := 0.0, max := 0.0 }
  else
    let count := durations.size.toFloat
    let sum := durations.foldMap (· + ·) id 0.0
    let mean := sum / count
    let variance :=
      durations.foldl (init := 0.0) fun acc d =>
        let delta := d - mean
        acc + delta * delta / count
    let first := durations[0]!
    let min := durations.foldl Float.min first
    let max := durations.foldl Float.max first
    { mean, stddev := Float.sqrt variance, min, max }

def benchParseModule (contents : String) : IO BenchStats := do
  let mut durations : Array Float := #[]
  let checksum : IO.Ref Nat ← IO.mkRef (0 : Nat)
  for _ in [:100] do
    let start ← IO.monoNanosNow
    let parsed := parseModule contents
    let delta : Nat :=
      match parsed with
      | RecoveredParserResult.ParseSucceeded _ => 0
      | RecoveredParserResult.ParseSucceededWithErrors _ _ => 1
      | RecoveredParserResult.ParseFailed _ => 2
    let current ← checksum.get
    checksum.set (current + delta)
    let stop ← IO.monoNanosNow
    durations := durations.push ((stop - start).toFloat / 1_000_000.0)
  let _ ← checksum.get
  pure (computeStats durations)

def main (args : List String) : IO UInt32 := do
  let args := skipArgDash args
  match args with
  | [] =>
      IO.println "File path required"
      pure 0
  | fileName :: _ => do
      let contents ← IO.FS.readFile fileName
      IO.println s!"Benchmarking {fileName}"
      let stats ← benchParseModule contents
      IO.println s!"mean   = {formatFixed 2 stats.mean} ms"
      IO.println s!"stddev = {formatFixed 2 stats.stddev} ms"
      IO.println s!"min    = {formatFixed 2 stats.min} ms"
      IO.println s!"max    = {formatFixed 2 stats.max} ms"
      pure 0
