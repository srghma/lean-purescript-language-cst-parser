module

public import PurescriptLanguageCstParser.Types

@[expose] public section

open PurescriptLanguageCstParser.Types

namespace PurescriptLanguageCstParser.ModuleGraph

abbrev Graph (a : Type) := Array (a × Array a)

def moduleGraph {e a : Type} (k : a → ModuleHeader e) (xs : Array a) : Graph ModuleName :=
  xs.map fun a =>
    let h := k a
    let name := h.name.name
    let imports := h.imports.map fun i => i.module_.name
    (name, imports)

inductive ModuleSort (a : Type) where
  | Sorted (mods : Array a)
  | CycleDetected (mods : Array a)
  deriving Repr

def lookup {a : Type} [BEq a] (g : Graph a) (k : a) : Array a :=
  match g.find? (fun p => p.1 == k) with
  | some p => p.2
  | none => #[]

def removeKey {a : Type} [BEq a] (g : Graph a) (k : a) : Graph a :=
  g.filter (fun p => p.1 != k)

def addRoot {a : Type} [BEq a] (roots : List a) (k : a) : List a :=
  if roots.contains k then roots else k :: roots

partial def topoSort {a : Type} [BEq a] (g : Graph a) : Except (Array a) (Array a) :=
  let rec go (remaining : Graph a) (roots : List a) (sorted : List a) : Except (Array a) (Array a) :=
    match roots with
    | [] =>
        if remaining.isEmpty then
          .ok sorted.reverse.toArray
        else
          .error (remaining.map Prod.fst)
    | curr :: roots' =>
        let deps := lookup remaining curr
        let remaining' := removeKey remaining curr
        let roots'' := deps.foldl (fun acc dep => addRoot acc dep) roots'
        go remaining' roots'' (curr :: sorted)
  let roots := g.foldl (fun acc p => if p.2.isEmpty then p.1 :: acc else acc) []
  go g roots []

def lookupKnown {a : Type} [BEq a] (known : Array (ModuleName × a)) (name : ModuleName) : Option a :=
  match known.find? (fun p => p.1 == name) with
  | some p => some p.2
  | none => none

def sortModules {e a : Type} [BEq a]
    (k : a → ModuleHeader e) (xs : Array a) : ModuleSort a :=
  let graph := moduleGraph k xs
  let known : Array (ModuleName × a) := xs.map (fun a => ((k a).name.name, a))
  let lookupModule (names : Array ModuleName) : Array a :=
    names.filterMap (fun name => lookupKnown known name)
  match topoSort graph with
  | .ok sorted => .Sorted (lookupModule sorted)
  | .error cycle => .CycleDetected (lookupModule cycle)

end PurescriptLanguageCstParser.ModuleGraph
