module

prelude
import Std

namespace PurescriptLanguageCstParser.Exec

def run (cmd : String) (args : Array String) : IO UInt32 := do
  let output ← IO.Process.output { cmd, args }
  if output.exitCode == 0 then
    if !output.stdout.isEmpty then
      IO.print output.stdout
    pure 0
  else
    if !output.stdout.isEmpty then
      IO.print output.stdout
    if !output.stderr.isEmpty then
      IO.eprint output.stderr
    pure output.exitCode

def runSpago (args : Array String) : IO UInt32 :=
  run "spago" args

def runNode (args : Array String) : IO UInt32 :=
  run "node" args

end PurescriptLanguageCstParser.Exec
