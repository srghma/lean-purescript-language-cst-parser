module

public import PurescriptLanguageCstParser.Types

namespace PurescriptLanguageCstParser.Layout
open PurescriptLanguageCstParser.Types
@[expose] public section

inductive LayoutDelim
  | LytRoot
  | LytTopDecl
  | LytTopDeclHead
  | LytDeclGuard
  | LytCase
  | LytCaseBinders
  | LytCaseGuard
  | LytLambdaBinders
  | LytParen
  | LytBrace
  | LytSquare
  | LytIf
  | LytThen
  | LytProperty
  | LytForall
  | LytTick
  | LytLet
  | LytLetStmt
  | LytWhere
  | LytOf
  | LytDo
  | LytAdo
  deriving Repr, BEq

abbrev LayoutStack := List (SourcePos × LayoutDelim)

/--
Checks if a layout delimiter introduces an indented context (i.e., follows the offside rule).
For example, `where`, `let`, `do`, and `of` blocks are indented.

Example:
`isIndented .LytWhere` => `true`
`isIndented .LytParen` => `false`
-/
def isIndented : LayoutDelim → Bool
  | .LytLet => true
  | .LytLetStmt => true
  | .LytWhere => true
  | .LytOf => true
  | .LytDo => true
  | .LytAdo => true
  | _ => false

/--
Finds the indentation position of the nearest indented context in the stack.
The stack is searched from top to bottom (head to tail).

Example:
`currentIndent [(pos, .LytWhere), (rootPos, .LytRoot)]` => `some pos`
`currentIndent [(rootPos, .LytRoot)]` => `none`
-/
def currentIndent (stk : LayoutStack) : Option SourcePos :=
  match stk with
  | (pos, lyt) :: rest =>
    if isIndented lyt then some pos else currentIndent rest
  | [] => none

/--
Checks if the current position is at the top-level of a module declaration.
In Purescript, this is true if the stack starts with a `LytWhere` followed by `LytRoot`
and the current column matches the `where` column.

Example:
`isTopDecl { column := 1, .. } [( { column := 1, .. }, .LytWhere), (_, .LytRoot)]` => `true`
-/
def isTopDecl (tokPos : SourcePos) (stk : LayoutStack) : Bool :=
  match stk with
  | (lytPos, LayoutDelim.LytWhere) :: (_, LayoutDelim.LytRoot) :: _ =>
    tokPos.column == lytPos.column
  | _ => false

/--
Helper function to create a `SourceToken` with an empty range and no comments.
Used primarily for generating layout-related tokens like `LayoutStart`, `LayoutSep`, and `LayoutEnd`.

Example:
`lytToken pos (.LayoutSep 1)` => A SourceToken at `pos` with value `LayoutSep 1`.
-/
def lytToken (pos : SourcePos) (value : Token) : SourceToken :=
  { range := { start := pos, end_ := pos }
    leadingComments := #[]
    trailingComments := #[]
    value := value }

/--
The internal state used during layout insertion.
* `stk`: The current layout stack (delimiters and their starting positions).
* `acc`: The accumulated tokens along with the stack state at the time of insertion.
-/
structure LayoutState where
  stk : LayoutStack
  acc : Array (SourceToken × LayoutStack)
  deriving Repr

/--
Pushes a token into the state's accumulator.
The current stack is paired with the token to assist the parser in recovery.

Example:
`insertToken tok state` => `state` with `tok` added to `acc`.
-/
def insertToken (token : SourceToken) (state : LayoutState) : LayoutState :=
  { state with acc := state.acc.push (token, state.stk) }

/--
Pushes a new delimiter and its starting position onto the layout stack.

Example:
`pushStack pos .LytDo state` => `state` with `(pos, .LytDo)` at the head of `stk`.
-/
def pushStack (lytPos : SourcePos) (lyt : LayoutDelim) (state : LayoutState) : LayoutState :=
  { state with stk := (lytPos, lyt) :: state.stk }

/--
Pops the top element of the stack if it matches the given predicate.

Example:
`popStack (· == .LytProperty) state` => `state` with top element removed if it was `.LytProperty`.
-/
def popStack (p : LayoutDelim → Bool) (state : LayoutState) : LayoutState :=
  match state.stk with
  | (_, lyt) :: rest => if p lyt then { state with stk := rest } else state
  | _ => state

/--
The main entry point for the layout insertion algorithm.
Processes a `SourceToken` from the lexer and generates any necessary layout markers
(like `LayoutStart`, `LayoutSep`, or `LayoutEnd`) based on the indentation level and current stack.

* `src`: The current token being processed.
* `nextPos`: The starting position of the next token in the stream.
* `stack`: The current layout stack.

Returns a pair containing the updated `LayoutStack` and an `Array` of tokens to be
emitted (including the original `src` and any generated layout tokens).

Example:
If `src` is at a new line with the same indentation as the current block,
it will emit a `LayoutSep` before the token itself.
-/
def insertLayout (src : SourceToken) (nextPos : SourcePos) (stack : LayoutStack) : (LayoutStack × Array (SourceToken × LayoutStack)) :=
  let tokPos := src.range.start

  let rec collapse' (p : SourcePos → LayoutDelim → Bool) (state : LayoutState) : LayoutState :=
    let rec go (stk : LayoutStack) (acc : Array (SourceToken × LayoutStack)) : LayoutState :=
      match stk with
      | (lytPos, lyt) :: rest =>
        if p lytPos lyt then
          let newAcc := if isIndented lyt then
            acc.push (lytToken tokPos (Token.LayoutEnd lytPos.column), rest)
          else acc
          go rest newAcc
        else { stk := stk, acc := acc }
      | _ => { stk := stk, acc := acc }
    go state.stk state.acc

  let insertSep (state : LayoutState) : LayoutState :=
    match state.stk with
    | (lytPos, .LytTopDecl) :: rest =>
      if tokPos.column == lytPos.column && tokPos.line != lytPos.line then
        insertToken (lytToken tokPos (Token.LayoutSep tokPos.column)) { state with stk := rest }
      else state
    | (lytPos, .LytTopDeclHead) :: rest =>
      if tokPos.column == lytPos.column && tokPos.line != lytPos.line then
        insertToken (lytToken tokPos (Token.LayoutSep tokPos.column)) { state with stk := rest }
      else state
    | (lytPos, lyt) :: _ =>
      if isIndented lyt && tokPos.column == lytPos.column && tokPos.line != lytPos.line then
        if lyt == .LytOf then
          insertToken (lytToken tokPos (Token.LayoutSep tokPos.column)) (pushStack tokPos .LytCaseBinders state)
        else
          insertToken (lytToken tokPos (Token.LayoutSep tokPos.column)) state
      else state
    | _ => state

  let insertDefault (state : LayoutState) : LayoutState :=
    let state' := collapse' (fun lytPos lyt => isIndented lyt && tokPos.column < lytPos.column) state
    let state'' := insertSep state'
    insertToken src state''

  let insertStart (lyt : LayoutDelim) (state : LayoutState) : LayoutState :=
    let found := state.stk.find? (fun (_, l) => isIndented l)
    match found with
    | some (pos, _) =>
      if nextPos.column <= pos.column then state
      else
        let state' := pushStack nextPos lyt state
        insertToken (lytToken nextPos (Token.LayoutStart nextPos.column)) state'
    | _ =>
      let state' := pushStack nextPos lyt state
      insertToken (lytToken nextPos (Token.LayoutStart nextPos.column)) state'

  let insertEnd (indent : USize) (state : LayoutState) : LayoutState :=
    insertToken (lytToken tokPos (Token.LayoutEnd indent)) state

  let insertKwProperty (k : LayoutState → LayoutState) (state : LayoutState) : LayoutState :=
    let state' := insertDefault state
    match state'.stk with
    | (_, .LytProperty) :: rest => { state' with stk := rest }
    | _ => k state'

  let insert (state : LayoutState) : LayoutState :=
    match src.value with
    | .LowerName optMod s =>
      match optMod, s.toString with
      | none, "data" =>
        let state' := insertDefault state
        if isTopDecl tokPos state'.stk then
          pushStack tokPos .LytTopDecl state'
        else
          popStack (fun lyt => lyt == LayoutDelim.LytProperty) state'
      | none, "class" =>
        let state' := insertDefault state
        if isTopDecl tokPos state'.stk then
          pushStack tokPos .LytTopDeclHead state'
        else
          popStack (fun lyt => lyt == LayoutDelim.LytProperty) state'
      | none, "where" =>
        match state.stk with
        | (_, .LytTopDeclHead) :: rest =>
          let state' := { state with stk := rest }
          let state'' := insertToken src state'
          insertStart .LytWhere state''
        | (_, .LytProperty) :: rest =>
          let state' := { state with stk := rest }
          insertToken src state'
        | _ =>
          let state' := collapse' (fun lytPos lyt => if lyt == LayoutDelim.LytDo then true else (isIndented lyt && tokPos.column <= lytPos.column)) state
          let state'' := insertToken src state'
          insertStart .LytWhere state''
      | none, "in" =>
        let state' := collapse' (fun _ lyt => if lyt == LayoutDelim.LytLet || lyt == LayoutDelim.LytAdo then false else isIndented lyt) state
        match state'.stk with
        | (pos1, .LytLetStmt) :: (pos2, .LytAdo) :: rest =>
          let state' := { state' with stk := rest }
          let state'' := insertEnd pos1.column state'
          let state''' := insertEnd pos2.column state''
          insertToken src state'''
        | (pos1, lyt) :: rest =>
          if isIndented lyt then
            let state' := { state' with stk := rest }
            let state'' := insertEnd pos1.column state'
            insertToken src state''
          else
            let state' := insertDefault state'
            popStack (fun lyt => lyt == LayoutDelim.LytProperty) state'
        | _ =>
          let state' := insertDefault state'
          popStack (fun lyt => lyt == LayoutDelim.LytProperty) state'
      | none, "let" =>
        insertKwProperty (fun state' =>
          match state'.stk with
          | (p, .LytDo) :: _ =>
            if p.column == tokPos.column then insertStart .LytLetStmt state'
            else insertStart .LytLet state'
          | (p, .LytAdo) :: _ =>
            if p.column == tokPos.column then insertStart .LytLetStmt state'
            else insertStart .LytLet state'
          | _ =>
            insertStart .LytLet state'
        ) state
      | none, "case" =>
        insertKwProperty (pushStack tokPos .LytCase) state
      | none, "of" =>
        let state' := collapse' (fun _ lyt => isIndented lyt) state
        match state'.stk with
        | (_, .LytCase) :: rest =>
          let state' := { state' with stk := rest }
          let state'' := insertToken src state'
          let state''' := insertStart .LytOf state''
          pushStack nextPos .LytCaseBinders state'''
        | _ =>
          let state' := insertDefault state'
          popStack (fun lyt => lyt == LayoutDelim.LytProperty) state'
      | none, "if" =>
        insertKwProperty (pushStack tokPos .LytIf) state
      | none, "then" =>
        let state' := collapse' (fun _ lyt => isIndented lyt) state
        match state'.stk with
        | (_, .LytIf) :: rest =>
          let state' := { state with stk := rest }
          let state'' := insertToken src state'
          pushStack tokPos .LytThen state''
        | _ =>
          let state' := insertDefault state'
          popStack (fun lyt => lyt == LayoutDelim.LytProperty) state'
      | none, "else" =>
        let state' := collapse' (fun _ lyt => isIndented lyt) state
        match state'.stk with
        | (_, .LytThen) :: rest =>
          let state' := { state with stk := rest }
          insertToken src state'
        | _ =>
          let state' := collapse' (fun lytPos lyt => isIndented lyt && tokPos.column <= lytPos.column) state
          if isTopDecl tokPos state'.stk then
            insertToken src state'
          else
            let state' := insertSep state'
            let state'' := insertToken src state'
            popStack (fun lyt => lyt == LayoutDelim.LytProperty) state''
      | _, "do" =>
        insertKwProperty (insertStart .LytDo) state
      | _, "ado" =>
        insertKwProperty (insertStart .LytAdo) state
      | none, _ =>
        let state' := insertDefault state
        popStack (fun lyt => lyt == LayoutDelim.LytProperty) state'
      | some _, _ =>
        insertDefault state

    | .Forall _ =>
      insertKwProperty (pushStack tokPos .LytForall) state

    | .Backslash =>
      let state' := insertDefault state
      pushStack tokPos .LytLambdaBinders state'

    | .RightArrow _ =>
      let state' := collapse' (fun lytPos lyt => if lyt == LayoutDelim.LytDo then true else if lyt == LayoutDelim.LytOf then false else (isIndented lyt && tokPos.column <= lytPos.column)) state
      let state'' := popStack (fun lyt => lyt == LayoutDelim.LytCaseBinders || lyt == LayoutDelim.LytCaseGuard || lyt == LayoutDelim.LytLambdaBinders) state'
      insertToken src state''

    | .Equals =>
      let state' := collapse' (fun _ lyt => lyt == LayoutDelim.LytWhere || lyt == LayoutDelim.LytLet || lyt == LayoutDelim.LytLetStmt) state
      match state'.stk with
      | (_, .LytDeclGuard) :: rest =>
        let state' := { state' with stk := rest }
        insertToken src state'
      | _ =>
        insertDefault state'

    | .Pipe =>
      let state' := collapse' (fun lytPos lyt => isIndented lyt && tokPos.column <= lytPos.column) state
      match state'.stk with
      | (_, .LytOf) :: _ =>
        pushStack tokPos .LytCaseGuard (insertToken src state')
      | (_, .LytLet) :: _ =>
        pushStack tokPos .LytDeclGuard (insertToken src state')
      | (_, .LytLetStmt) :: _ =>
        pushStack tokPos .LytDeclGuard (insertToken src state')
      | (_, .LytWhere) :: _ =>
        pushStack tokPos .LytDeclGuard (insertToken src state')
      | _ =>
        insertDefault state'

    | .Tick =>
      let state' := collapse' (fun _ lyt => isIndented lyt) state
      match state'.stk with
      | (_, .LytTick) :: rest =>
        let state' := { state' with stk := rest }
        insertToken src state'
      | _ =>
        let state' := collapse' (fun lytPos lyt => isIndented lyt && tokPos.column <= lytPos.column) state
        let state'' := insertSep state'
        let state''' := insertToken src state''
        pushStack tokPos .LytTick state'''

    | .Comma =>
      let state' := collapse' (fun _ lyt => isIndented lyt) state
      match state'.stk with
      | (_, LayoutDelim.LytBrace) :: _ =>
        insertToken src (pushStack tokPos .LytProperty state')
      | _ =>
        insertToken src state'

    | .Dot =>
      let state' := insertDefault state
      match state'.stk with
      | (_, .LytForall) :: rest => { state' with stk := rest }
      | _ => pushStack tokPos .LytProperty state'

    | .LeftParen =>
      let state' := insertDefault state
      pushStack tokPos .LytParen state'

    | .LeftBrace =>
      let state' := insertDefault state
      let state'' := pushStack tokPos .LytBrace state'
      pushStack tokPos .LytProperty state''

    | .LeftSquare =>
      let state' := insertDefault state
      pushStack tokPos .LytSquare state'

    | .RightParen =>
      let state' := collapse' (fun _ lyt => isIndented lyt) state
      let state'' := popStack (fun lyt => lyt == LayoutDelim.LytParen) state'
      insertToken src state''

    | .RightBrace =>
      let state' := collapse' (fun _ lyt => isIndented lyt) state
      let state'' := popStack (fun lyt => lyt == LayoutDelim.LytProperty) state'
      let state''' := popStack (fun lyt => lyt == LayoutDelim.LytBrace) state''
      insertToken src state'''

    | .RightSquare =>
      let state' := collapse' (fun _ lyt => isIndented lyt) state
      let state'' := popStack (fun lyt => lyt == LayoutDelim.LytSquare) state'
      insertToken src state''

    | .String _ _ | .RawString _ =>
      let state' := insertDefault state
      popStack (fun lyt => lyt == LayoutDelim.LytProperty) state'

    | .Operator _ _ =>
      let state' := collapse' (fun lytPos lyt => isIndented lyt && tokPos.column <= lytPos.column) state
      let state'' := insertSep state'
      insertToken src state''

    | _ =>
      insertDefault state

  let finalState := insert { stk := stack, acc := #[] }
  (finalState.stk, finalState.acc)
end
end PurescriptLanguageCstParser.Layout
