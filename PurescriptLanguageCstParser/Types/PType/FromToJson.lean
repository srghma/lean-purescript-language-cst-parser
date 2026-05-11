module

public import PurescriptLanguageCstParser.Types.PType.Basic
public import Lean.Data.Json
@[expose] public section
namespace PurescriptLanguageCstParser.Types

open Lean
open NonEmpty.String

instance : FromJson ModuleName where
  fromJson? j := do
    let str ← j.getStr?
    match NonEmptyString.fromString? str with
    | some n => pure n
    | none => throw "TypeMismatch ModuleName (empty string)"

instance : ToJson ModuleName where
  toJson n := toJson n.toString

instance : FromJson Ident where
  fromJson? j := do
    let str ← j.getStr?
    match NonEmptyString.fromString? str with
    | some n => pure n
    | none => throw "TypeMismatch Ident (empty string)"

instance : ToJson Ident where
  toJson n := toJson n.toString

instance : FromJson Proper where
  fromJson? j := do
    let str ← j.getStr?
    match NonEmptyString.fromString? str with
    | some n => pure n
    | none => throw "TypeMismatch Proper (empty string)"

instance : ToJson Proper where
  toJson n := toJson n.toString

instance : FromJson SourcePos where
  fromJson? j := do
    let line ← j.getObjValAs? USize "line"
    let column ← j.getObjValAs? USize "column"
    pure { line, column }

instance : ToJson SourcePos where
  toJson p := Json.mkObj [("line", toJson p.line), ("column", toJson p.column)]

end PurescriptLanguageCstParser.Types
