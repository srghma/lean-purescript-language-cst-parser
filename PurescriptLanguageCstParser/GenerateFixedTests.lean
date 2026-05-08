module

import PurescriptLanguageCstParser.GenerateFixed

-- ---------------------------------------------------------------------------
-- Test 1 : Tree  (payload param `a`, recursive param `r`)
-- ---------------------------------------------------------------------------

namespace Test1

inductive TreeF (a r : Type) where
  | leaf (val : a)
  | node (left right : r)
  deriving Repr, BEq

/--
info:
generate_fixed expansion:
inductive Tree (a : Type) : Type where
  | leaf (val : a) : Tree a
  | node (left : (Tree a)) (right : (Tree a)) : Tree a
  deriving Repr, BEq
-/
#guard_msgs in
generate_fixed? Tree (a : Type) from TreeF
  fill r with (Tree a)
  deriving Repr, BEq

/--
info:
private inductive Test1.Tree : Type → Type
number of parameters: 1
constructors:
_private.PurescriptLanguageCstParser.GenerateFixedTests.0.Test1.Tree.leaf : {a : Type} → a → Tree a
_private.PurescriptLanguageCstParser.GenerateFixedTests.0.Test1.Tree.node : {a : Type} → Tree a → Tree a → Tree a
 -/
#guard_msgs in
#print Tree

def exTree : Tree Nat :=
  .node (.leaf 1) (.node (.leaf 2) (.leaf 3))

/--
info:
_private.PurescriptLanguageCstParser.GenerateFixedTests.0.Test1.Tree.node
  (_private.PurescriptLanguageCstParser.GenerateFixedTests.0.Test1.Tree.leaf 1)
  (_private.PurescriptLanguageCstParser.GenerateFixedTests.0.Test1.Tree.node
    (_private.PurescriptLanguageCstParser.GenerateFixedTests.0.Test1.Tree.leaf 2)
    (_private.PurescriptLanguageCstParser.GenerateFixedTests.0.Test1.Tree.leaf 3))
-/
#guard_msgs in
#eval exTree

end Test1

-- ---------------------------------------------------------------------------
-- Test 2 : Expr (recursive param `e`, with `Int` literals)
-- ---------------------------------------------------------------------------

namespace Test2

inductive ExprF (e : Type) where
  | num (val : Int)
  | add (l r : e)
  | mul (l r : e)
  | neg (inner : e)
  deriving Repr, BEq

/--
info:
generate_fixed expansion:
public inductive Expr : Type where
  | num (val : Int) : Expr
  | add (l : Expr) (r : Expr) : Expr
  | mul (l : Expr) (r : Expr) : Expr
  | neg (inner : Expr) : Expr
  deriving Repr, BEq-/
#guard_msgs in
public generate_fixed? Expr from ExprF
  fill e with Expr
  deriving Repr, BEq

/--
info:
inductive Test2.Expr : Type
number of parameters: 0
constructors:
Test2.Expr.num : Int → Expr
Test2.Expr.add : Expr → Expr → Expr
Test2.Expr.mul : Expr → Expr → Expr
Test2.Expr.neg : Expr → Expr
 -/
#guard_msgs in
#print Expr

def exExpr : Expr :=
  .add (.num 1) (.mul (.num 2) (.neg (.num 3)))

/--
info: Test2.Expr.add (Test2.Expr.num 1) (Test2.Expr.mul (Test2.Expr.num 2) (Test2.Expr.neg (Test2.Expr.num 3)))
-/
#guard_msgs in
#eval exExpr

end Test2

-- ---------------------------------------------------------------------------
-- Test 3 : Mutual recursion (Expr and Stmt)
-- ---------------------------------------------------------------------------

namespace Test3

inductive ExprF (e s : Type) where
  | num (val : Int)
  | add (l r : e)
  | ifE (cond : s) (thenE elseE : e)
  deriving Repr, BEq

inductive StmtF (e s : Type) where
  | assign (name : String) (val : e)
  | seq (l r : s)
  | whileS (cond : e) (body : s)
  deriving Repr, BEq

/--
info:
generate_fixed_mutual expansion:
mutual
  public inductive Expr : Type where
    | num (val : Int) : Expr
    | add (l : Expr) (r : Expr) : Expr
    | ifE (cond : Stmt) (thenE : Expr) (elseE : Expr) : Expr
  public inductive Stmt : Type where
    | assign (name : String) (val : Expr) : Stmt
    | seq (l : Stmt) (r : Stmt) : Stmt
    | whileS (cond : Expr) (body : Stmt) : Stmt
end
-/
#guard_msgs in
generate_fixed_mutual?
  public generate_fixed Expr from ExprF
    fill e with Expr
    fill s with Stmt

  public generate_fixed Stmt from StmtF
    fill e with Expr
    fill s with Stmt
end_generate_fixed_mutual

/--
info:
inductive Test3.Expr : Type
number of parameters: 0
constructors:
Test3.Expr.num : Int → Expr
Test3.Expr.add : Expr → Expr → Expr
Test3.Expr.ifE : Stmt → Expr → Expr → Expr
-/
#guard_msgs in
#print Expr

/--
info:
inductive Test3.Stmt : Type
number of parameters: 0
constructors:
Test3.Stmt.assign : String → Expr → Stmt
Test3.Stmt.seq : Stmt → Stmt → Stmt
Test3.Stmt.whileS : Expr → Stmt → Stmt
-/
#guard_msgs in
#print Stmt

def exStmt : Stmt :=
  .whileS
    (.add (.num 1) (.num 2))
    (.assign "x"
      (.ifE
        (.seq (.assign "skip" (.num 0)) (.assign "skip" (.num 0)))
        (.num 0)
        (.num 1)))

/--
info:
Test3.Stmt.whileS
  (Test3.Expr.add (Test3.Expr.num 1) (Test3.Expr.num 2))
  (Test3.Stmt.assign
    "x"
    (Test3.Expr.ifE
      (Test3.Stmt.seq (Test3.Stmt.assign "skip" (Test3.Expr.num 0)) (Test3.Stmt.assign "skip" (Test3.Expr.num 0)))
      (Test3.Expr.num 0)
      (Test3.Expr.num 1)))
-/
#guard_msgs in
#eval exStmt

end Test3

-- ---------------------------------------------------------------------------
-- Test 4 : RoseTree  (recursive parameter nested inside `List`)
-- ---------------------------------------------------------------------------

namespace Test4

inductive RoseTreeF (a r : Type) where
  | node (val : a) (children : List r)
  deriving Repr, BEq

-- `fill r with (RoseTree a)` rewrites `List r` → `List (RoseTree a)` because
-- `substIdent` walks into the `List r` application and replaces the `r` leaf.
/--
info:
generate_fixed expansion:
public inductive RoseTree (a : Type) : Type where
  | node (val : a) (children : List (RoseTree a)) : RoseTree a
  deriving Repr, BEq
-/
#guard_msgs in
public generate_fixed? RoseTree (a : Type) from RoseTreeF
  fill r with (RoseTree a)
  deriving Repr, BEq

-- or can
-- public generate_fixed inductive RoseTree (x : Type) from RoseTreeF
--   fill r with (RoseTree x)
--   fill a with x
--   deriving Repr, BEq


/--
info:
inductive Test4.RoseTree : Type → Type
number of parameters: 1
constructors:
Test4.RoseTree.node : {a : Type} → a → List (RoseTree a) → RoseTree a
 -/
#guard_msgs in
#print RoseTree

def exRoseTree : RoseTree String :=
  .node "root" [.node "child1" [], .node "child2" [.node "grandchild" []]]

/--
info: Test4.RoseTree.node
  "root"
  [Test4.RoseTree.node "child1" [], Test4.RoseTree.node "child2" [Test4.RoseTree.node "grandchild" []]]
-/
#guard_msgs in
#eval exRoseTree

end Test4

-- ---------------------------------------------------------------------------
-- Test 5 : Mutual inductive + structure
-- ---------------------------------------------------------------------------

namespace Test5

inductive ExprF (error e m : Type) where
  | num      (n : Int)
  | add      (l r : e)
  | metadata (meta_ : m)
  | err      (e : error)
  deriving Repr, BEq

structure MetadataF (error e m : Type) where
  expr     : e
  meta_     : m
  hasError : Option error
  deriving Repr, BEq

set_option linter.unusedVariables false in -- FIXME: why error is not used?

/--
info:
generate_fixed_mutual expansion:
mutual
  public structure Metadata (error : Type) where
    expr : Expr error
    meta_ : Metadata error
    hasError : Option error
    deriving Repr, BEq
  public inductive Expr (error : Type) : Type where
    | num (n : Int) : Expr error
    | add (l : Expr error) (r : Expr error) : Expr error
    | metadata (meta_ : Metadata error) : Expr error
    | err (e : error) : Expr error
    deriving Repr, BEq
end
-/
#guard_msgs in
generate_fixed_mutual?
  public generate_fixed Metadata (error : Type) from MetadataF
    fill e with (Expr error)
    fill m with (Metadata error)
    -- fill error with error
    deriving Repr, BEq

  public generate_fixed Expr (error : Type) from ExprF
    fill e with (Expr error)
    fill m with (Metadata error)
    -- fill error with error
    deriving Repr, BEq
end_generate_fixed_mutual

/-- info:
inductive Test5.Expr : Type → Type
number of parameters: 1
constructors:
Test5.Expr.num : {error : Type} → Int → Expr error
Test5.Expr.add : {error : Type} → Expr error → Expr error → Expr error
Test5.Expr.metadata : {error : Type} → Metadata error → Expr error
Test5.Expr.err : {error : Type} → error → Expr error
 -/
#guard_msgs in
#print Expr

/-- info:
structure Test5.Metadata (error : Type) : Type
number of parameters: 1
fields:
  Test5.Metadata.expr : Expr error
  Test5.Metadata.meta_ : Metadata error
  Test5.Metadata.hasError : Option error
constructor:
  Test5.Metadata.mk {error : Type} (expr : Expr error) (meta_ : Metadata error) (hasError : Option error) :
    Metadata error
 -/
#guard_msgs in
#print Metadata

def ex5 : Expr String := .add (.num 1) (.err "oops")

/--
info: Test5.Expr.add (Test5.Expr.num 1) (Test5.Expr.err "oops")
-/
#guard_msgs in
#eval ex5

end Test5

-- ---------------------------------------------------------------------------
-- Test 6 : Mixed declarations in generate_fixed_mutual
-- ---------------------------------------------------------------------------

namespace Test6

inductive ExprF (e : Type) where
  | num (n : Int)
  | add (l r : e)
  deriving Repr

/--
info: generate_fixed_mutual expansion:
mutual
  public inductive Expr : Type where
    | num (n : Int) : Expr
    | add (l : Expr) (r : Expr) : Expr
  public inductive ExprTag where
    | lit
    | bin
end
-/
#guard_msgs in
generate_fixed_mutual?
  public generate_fixed Expr from ExprF -- also test that can export
    fill e with Expr

  public inductive ExprTag where -- also test that can export
    | lit
    | bin
end_generate_fixed_mutual

deriving instance Repr, BEq for Expr
deriving instance Repr, BEq for ExprTag

/-- info:
inductive Test6.Expr : Type
number of parameters: 0
constructors:
Test6.Expr.num : Int → Expr
Test6.Expr.add : Expr → Expr → Expr
 -/
#guard_msgs in
#print Expr
/-- info:
inductive Test6.ExprTag : Type
number of parameters: 0
constructors:
Test6.ExprTag.lit : ExprTag
Test6.ExprTag.bin : ExprTag
 -/
#guard_msgs in
#print ExprTag

end Test6

-- ---------------------------------------------------------------------------
-- Test 7 : Debug output with `?`
-- ---------------------------------------------------------------------------

namespace Test7

inductive SimpleF (e : Type) where
  | baseS
  | recS (inner : e)
  deriving Repr

/--
info: generate_fixed expansion:
inductive Simple : Type where
  | baseS : Simple
  | recS (inner : Simple) : Simple
-/
#guard_msgs in
generate_fixed? Simple from SimpleF
  fill e with Simple

inductive ExprF (e s : Type) where
  | baseE
  | recE (inner : s)

inductive StmtF (e s : Type) where
  | baseSt
  | recSt (inner : e)

/--
info: generate_fixed_mutual expansion:
mutual
  public inductive Expr : Type where
    | baseE : Expr
    | recE (inner : Stmt) : Expr
  public inductive Stmt : Type where
    | baseSt : Stmt
    | recSt (inner : Expr) : Stmt
end
-/
#guard_msgs in
generate_fixed_mutual?
  public generate_fixed Expr from ExprF
    fill e with Expr
    fill s with Stmt
  public generate_fixed Stmt from StmtF
    fill e with Expr
    fill s with Stmt
end_generate_fixed_mutual

/--
error: generate_fixed: functor `_private.PurescriptLanguageCstParser.GenerateFixedTests.0.Test7.ExprF` does not have a parameter named `nonExistent`. Available parameters: `[e, s]`
-/
#guard_msgs(error) in
generate_fixed ExprFail from ExprF
  fill nonExistent with Unit

/--
error: Constructor field `s` of `Test7.ExprFail2.recE` contains universe level metavariables at the expression
  Sort ?u.4
in its type
  Sort ?u.4
-/
#guard_msgs(error) in
public generate_fixed ExprFail2 from ExprF
  fill e with Unit

end Test7
