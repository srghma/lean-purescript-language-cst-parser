module

-- `generate_fixed` – derives a fixed-point `inductive` (or `structure`) from a
-- functor-shaped inductive by declaring the recursive-position substitutions
-- explicitly with `fill`.
--
-- ── Non-mutual ────────────────────────────────────────────────────────────────
--   generate_fixed inductive Tree (a : Type) from TreeF
--     fill r with (Tree a)
--     deriving Repr, BEq
--
-- ── Mutual (inside `generate_fixed_mutual … end_generate_fixed_mutual` which is like `mutual … end` but `mutual` doesnt allow to use custom keywords) ───────────────────────────
--   generate_fixed_mutual
--     generate_fixed inductive Expr from Expr2F
--       fill e with Expr
--       fill s with Stmt
--     generate_fixed inductive Stmt from StmtF
--       fill e with Expr
--       fill s with Stmt
--   end_generate_fixed_mutual

import Lean
public import Lean.Elab.Command

section
open Lean Meta Elab Command Term

--------------------------------------------------------------------------------
-- Syntax categories
--------------------------------------------------------------------------------

-- A single substitution clause, e.g. `fill r with (Tree a)`.
declare_syntax_cat fillClause
declare_syntax_cat fixed_kind
syntax "inductive" : fixed_kind
syntax "structure" : fixed_kind
syntax "fill" ident "with" term : fillClause

--------------------------------------------------------------------------------
-- Syntax-level identifier substitution
--------------------------------------------------------------------------------

meta partial def substIdent (paramName : Name) (replacement : Syntax) : Syntax → Syntax
  | s@(.ident _ _ n _) =>
      let n' := n.eraseMacroScopes
      if n' == paramName || (n'.isStr && n'.getString! == paramName.toString) then
        replacement
      else
        s
  | .node info kind args =>
      .node info kind (args.map (substIdent paramName replacement))
  | other => other

--------------------------------------------------------------------------------
-- Build the constructor list for a fixed-point inductive
--------------------------------------------------------------------------------

/-- For each constructor of `functorName`, peel its Pi-type, skip the
    `iv.numParams` type-parameter binders, delab each field type, apply
    the `fills` substitutions, and return bracketedBinder syntax. -/
meta def buildCtors (functorName : Name) (fills : Array (Name × Syntax)) (resultType : Term)
    : CommandElabM (Array (TSyntax ``Lean.Parser.Command.ctor)) := do
  let env ← getEnv
  let some ci := env.find? functorName
    | throwError "generate_fixed: unknown inductive '{functorName}'"
  let iv := ci.inductiveVal!
  let mut result : Array (TSyntax ``Lean.Parser.Command.ctor) := #[]
  for ctorName in iv.ctors do
    let ctorCi ← getConstInfo ctorName
    match ctorCi with
    | .ctorInfo cv =>
      let fieldBinders ← liftTermElabM <|
          forallTelescope cv.type fun xs _ => do
            -- xs[0..numParams-1] are the functor's own type params; skip them.
            let fieldXs := xs.extract iv.numParams xs.size
            let mut binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
            for fx in fieldXs do
              let decl ← fx.fvarId!.getDecl
              let fType ← inferType fx
              let fTypeStx ← PrettyPrinter.delab fType
              let mut fTypeSubst : Term := ⟨fTypeStx⟩
              for (p, repl) in fills do
                fTypeSubst := ⟨substIdent p repl fTypeSubst⟩
              let fId : Ident := mkIdent decl.userName
              let b : TSyntax ``Lean.Parser.Term.bracketedBinder ← `(bracketedBinder| ($fId : $fTypeSubst))
              binders := binders.push b
            return binders
      let ctorIdent := mkIdent ctorName.eraseMacroScopes.getString!.toName
      let ctor ←
        if fieldBinders.isEmpty then
          `(Lean.Parser.Command.ctor| | $ctorIdent:ident : $resultType)
        else
          `(Lean.Parser.Command.ctor| | $ctorIdent:ident $fieldBinders* : $resultType)
      result := result.push ctor
    | _ => throwError "generate_fixed: expected constructor info for '{ctorName}'"
  return result

--------------------------------------------------------------------------------
-- Build the field list for a fixed-point structure
--------------------------------------------------------------------------------

/-- Like `buildCtors` but produces `structField` syntax (no parentheses). -/
meta def buildStructFields (functorName : Name) (fills : Array (Name × Syntax))
    : CommandElabM (Array Syntax) := do
  let env ← getEnv
  let some ci := env.find? functorName
    | throwError "generate_fixed: unknown '{functorName}'"
  let iv := ci.inductiveVal!
  let some ctorName := iv.ctors[0]?
    | throwError "generate_fixed: '{functorName}' has no constructors"
  let ctorCi ← getConstInfo ctorName
  match ctorCi with
  | .ctorInfo cv =>
    liftTermElabM <|
        forallTelescope cv.type fun xs _ => do
          let fieldXs := xs.extract iv.numParams xs.size
          let mut result : Array Syntax := #[]
          for fx in fieldXs do
            let decl ← fx.fvarId!.getDecl
            let fType ← inferType fx
            let fTypeStx ← PrettyPrinter.delab fType
            let mut fTypeSubst : Term := ⟨fTypeStx⟩
            for (p, repl) in fills do
              fTypeSubst := ⟨substIdent p repl fTypeSubst⟩
            let fId : Ident := mkIdent decl.userName
            -- structSimpleBinder: `name : type`
            let field : Syntax ← `(Lean.Parser.Command.structSimpleBinder| $fId:ident : $fTypeSubst)
            result := result.push field
          return result
  | _ => throwError "generate_fixed: expected constructor info for '{ctorName}'"

--------------------------------------------------------------------------------
-- Elaborator
--------------------------------------------------------------------------------

meta def getParamIds (params : Array Syntax) : Array Ident := Id.run do
  let mut ids : Array Ident := #[]
  for p in params do
    if p.isIdent then
      ids := ids.push ⟨p⟩
    else
      let args := p.getArgs
      if args.size >= 2 then
        let names := args[1]!
        for n in names.getArgs do
          if n.isIdent then
            ids := ids.push ⟨n⟩
          else if n.getArgs.size > 0 && n[0]!.isIdent then
            ids := ids.push ⟨n[0]!⟩
  return ids

meta partial def findSepBy (s : Syntax) : Option Syntax :=
  if s.getArgs.any (·.getKind == ``Lean.Parser.Command.derivingClass) then some s
  else if s.getNumArgs > 0 then s.getArgs.findSome? findSepBy
  else none

meta def generateFixedSyntax (stx : Syntax) : CommandElabM Syntax := do
  -- [0]: mods, [1]: "generate_fixed", [2]: kw, [3]: name, [4]: params, [5]: "from", [6]: functor, [7]: fills, [8]: deriving?
  let mods : TSyntax ``Lean.Parser.Command.declModifiers := ⟨stx[0]⟩
  -- [1] is the keyword ("generate_fixed" or "generate_fixed?")
  let kw          := stx[2]
  let fixName     : Ident := ⟨stx[3]⟩
  let params      : Array (TSyntax [`ident, `Lean.Parser.Term.hole, `Lean.Parser.Term.bracketedBinder]) :=
    stx[4].getArgs.map TSyntax.mk
  let functorName : Ident := ⟨stx[6]⟩
  let fillClauses := stx[7].getArgs
  let deriving?   := stx[8]

  let fName ← resolveGlobalConstNoOverload functorName
  let env ← getEnv
  let ci ← getConstInfo fName
  if !ci.isInductive then
    throwErrorAt functorName m!"generate_fixed: `{fName}` is not an inductive type"
  let iv := ci.inductiveVal!

  let mut functorParamNames : Array Name := #[]
  let mut type := ci.type
  for _ in [:iv.numParams] do
    match type with
    | .forallE name _ body _ =>
      functorParamNames := functorParamNames.push name
      type := body
    | _ => break

  let fills : Array (Name × Syntax) ← fillClauses.mapM fun fc => do
    -- fc is a `fillClause` node: "fill" ident "with" term
    let pId  : Ident := ⟨fc[1]⟩
    let pName := pId.getId
    if !functorParamNames.contains pName then
       let paramsStr := ", ".intercalate (functorParamNames.toList.map (·.toString))
       throwErrorAt pId m!"generate_fixed: functor `{fName}` does not have a parameter named `{pName}`. Available parameters: `[{paramsStr}]`"
    let repl : Syntax := fc[3]
    return (pName, repl)

  let isStruct ←
    if kw.isNone then
      pure (Lean.isStructure env fName)
    else
      let k := kw[0]
      if k.isToken "inductive" then pure false
      else if k.isToken "structure" then pure true
      else throwErrorAt k "generate_fixed: expected 'inductive' or 'structure'"

  let ids : Array (TSyntax `Lean.Parser.Command.derivingClass) :=
    match findSepBy stx[8] with
    | some cn => cn.getSepArgs.map TSyntax.mk
    | none => #[]

  if !isStruct then
    let paramNames := getParamIds params
    let resultType : Term ← `(term| $fixName $paramNames*)
    let ctors ← buildCtors fName fills resultType
    if ids.isEmpty then
      `(command| $mods:declModifiers inductive $fixName $[$params]* : Type where $[$ctors]*)
    else
      `(command| $mods:declModifiers inductive $fixName $[$params]* : Type where $[$ctors]* deriving $[$ids],*)
  else
    let sfields ← buildStructFields fName fills
    let sfieldsCast : Array (TSyntax [`Lean.Parser.Command.structExplicitBinder, `Lean.Parser.Command.structImplicitBinder, `Lean.Parser.Command.structInstBinder, `Lean.Parser.Command.structSimpleBinder]) :=
      sfields.map TSyntax.mk
    if ids.isEmpty then
      `(command| $mods:declModifiers structure $fixName $[$params]* where $[$sfieldsCast]*)
    else
      `(command| $mods:declModifiers structure $fixName $[$params]* where $[$sfieldsCast]* deriving $[$ids],*)

syntax (name := generateFixed) declModifiers "generate_fixed" (fixed_kind)? ident bracketedBinder*
     "from" ident fillClause*
     (ppLine Lean.Parser.Command.optDeriving)? : command

syntax (name := generateFixedTrace) declModifiers "generate_fixed?" (fixed_kind)? ident bracketedBinder*
     "from" ident fillClause*
     (ppLine Lean.Parser.Command.optDeriving)? : command

meta partial def stripInfo (s : Syntax) : Syntax :=
  match s with
  | .node _ kind args => .node .none kind (args.map stripInfo)
  | .ident _ preresolved name preresolved' => .ident .none preresolved name preresolved'
  | .atom _ val => .atom .none val
  | _ => s

@[command_elab generateFixed]
public meta def elabGenerateFixed : CommandElab := fun stx => do
  let cmd ← generateFixedSyntax stx
  trace[Meta.debug] "generate_fixed expansion:\n{cmd}"
  elabCommand cmd

@[command_elab generateFixedTrace]
public meta def elabGenerateFixedTrace : CommandElab := fun stx => do
  let cmd ← generateFixedSyntax stx
  logInfo m!"generate_fixed expansion:\n{stripInfo cmd}"
  trace[Meta.debug] "generate_fixed expansion:\n{cmd}"
  elabCommand cmd

meta def elabGenerateFixedMutual (trace : Bool) (cmds : Array Syntax) : CommandElabM Unit := do
  let mut expanded : Array (TSyntax `command) := #[]
  for cmd in cmds do
    let cmd ← liftMacroM <| expandMacros cmd
    if cmd.getKind == ``generateFixed || cmd.getKind == ``generateFixedTrace then
      let exp ← generateFixedSyntax cmd
      expanded := expanded.push ⟨exp⟩
    else
      expanded := expanded.push ⟨cmd⟩
  let mutualCmd ← `(command| mutual $[$expanded]* end)
  if trace then
    logInfo m!"generate_fixed_mutual expansion:\n{stripInfo mutualCmd}"
  trace[Meta.debug] "generate_fixed_mutual expansion:\n{mutualCmd}"
  elabCommand mutualCmd

syntax (name := generateFixedMutual) declModifiers "generate_fixed_mutual" command+ "end_generate_fixed_mutual" : command
syntax (name := generateFixedMutualTrace) declModifiers "generate_fixed_mutual?" command+ "end_generate_fixed_mutual" : command

@[command_elab generateFixedMutual]
public meta def elabGenerateFixedMutualCommand : CommandElab := fun stx => do
  let cmds := stx[2].getArgs
  elabGenerateFixedMutual false cmds

@[command_elab generateFixedMutualTrace]
public meta def elabGenerateFixedMutualTraceCommand : CommandElab := fun stx => do
  let cmds := stx[2].getArgs
  elabGenerateFixedMutual true cmds

end
