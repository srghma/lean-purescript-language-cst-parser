module

import NonEmpty.ArrayCorrectByConstruction
import NonEmpty.String
import Aesop
public import PurescriptLanguageCstParser.Types.PType.Basic
meta import PurescriptLanguageCstParser.GenerateFixed

@[expose] public section

@[simp] theorem Array.sizeOf_attach_elem [SizeOf α] (arr : Array α) (x : { x // x ∈ arr }) :
    sizeOf x.val < sizeOf arr := by
  let ⟨val, h⟩ := x
  obtain ⟨i, hi, hval⟩ := Array.mem_iff_getElem.mp h
  subst hval
  have h1 := Array.sizeOf_getElem arr i hi
  omega

namespace PurescriptLanguageCstParser.Types

open NonEmpty.ArrayCorrectByConstruction
open NonEmpty.String
open PurescriptLanguageCstParser.Types

inductive DataMembers
  | All (token : SourceToken)
  | Enumerated (separated : Delimited (Name Proper))
  deriving Repr, BEq

inductive Export (e : Type)
  | Value (name : Name Ident)
  | Op (name : Name Operator)
  | Type_ (name : Name Proper) (optionMembers : Option DataMembers)
  | TypeOp (token : SourceToken) (name : Name Operator)
  | Class (token : SourceToken) (name : Name Proper)
  | Module (token : SourceToken) (name : Name ModuleName)
  | Error (data : e)
  deriving Repr, BEq

namespace Export

@[always_inline, simp] def map (f : α → β) (e : Export α) : Export β :=
  match e with
  | .Value n        => .Value n
  | .Op n           => .Op n
  | .Type_ n m      => .Type_ n m
  | .TypeOp t n     => .TypeOp t n
  | .Class t n      => .Class t n
  | .Module t n     => .Module t n
  | .Error d        => .Error (f d)

@[simp] theorem id_map (e : Export α) : (e.map id) = e := by
  cases e <;> rfl

@[simp] theorem comp_map (f : α → β) (g : β → γ) (e : Export α) : (e.map (g ∘ f)) = (e.map f |>.map g) := by
  cases e <;> rfl

@[simp] theorem map_id_fun : map (id : α → α) = id := by funext e; exact id_map e

@[simp] theorem map_comp_fun (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext e; exact comp_map f g e

@[always_inline, simp] def mapM [Applicative m] (f : α → m β) (e : Export α) : m (Export β) :=
  match e with
  | .Error d => .Error <$> f d
  | .Value n        => pure (.Value n)
  | .Op n           => pure (.Op n)
  | .Type_ n m      => pure (.Type_ n m)
  | .TypeOp t n     => pure (.TypeOp t n)
  | .Class t n      => pure (.Class t n)
  | .Module t n     => pure (.Module t n)

end Export

@[always_inline] instance : Functor Export where
  map := Export.map

instance : LawfulFunctor Export where
  map_const := rfl
  id_map e := Export.id_map e
  comp_map f g e := Export.comp_map f g e

---------------------------------------------------------------------------------------------------------
structure DataHead (e : Type) where
  keyword : SourceToken
  name : Name Proper
  parameters : Array (TypeVarBinding (Name Ident) (Type_ e))
  deriving Repr, BEq

namespace DataHead

@[always_inline, simp] def map (f : α → β) (h : DataHead α) : DataHead β :=
  { h with parameters := h.parameters.map (Functor.map (Functor.map f)) }

@[simp] theorem id_map (h : DataHead α) : (h.map id) = h := by
  cases h; aesop

@[simp] theorem comp_map (f : α → β) (g : β → γ) (h : DataHead α) : (h.map (g ∘ f)) = (h.map f |>.map g) := by
  cases h; aesop

@[simp] theorem map_id_fun : map (id : α → α) = id := by funext h; exact id_map h

@[simp] theorem map_comp_fun (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext h; exact comp_map f g h

instance : Functor DataHead where map := map
instance : LawfulFunctor DataHead where
  map_const := rfl
  id_map := id_map
  comp_map := comp_map

@[always_inline, simp] def mapM [Monad m] (f : α → m β) (h : DataHead α) : m (DataHead β) :=
  DataHead.mk h.keyword h.name <$> h.parameters.mapM (TypeVarBinding.mapM (Type_.mapM f))

end DataHead

@[always_inline] instance : Functor DataHead where
  map := DataHead.map

instance : LawfulFunctor DataHead where
  map_const := rfl
  id_map e := DataHead.id_map e
  comp_map f g e := DataHead.comp_map f g e

structure DataCtor (e : Type) where
  name : Name Proper
  parameters : Array (Type_ e)
  deriving Repr, BEq

namespace DataCtor

@[always_inline, simp] def map (f : α → β) (c : DataCtor α) : DataCtor β :=
  { c with parameters := c.parameters.map (Functor.map f) }

@[simp] theorem id_map (c : DataCtor α) : (c.map id) = c := by
  cases c; aesop

@[simp] theorem comp_map (f : α → β) (g : β → γ) (c : DataCtor α) : (c.map (g ∘ f)) = (c.map f |>.map g) := by
  cases c; aesop

@[simp] theorem map_id_fun : map (id : α → α) = id := by funext c; exact id_map c

@[simp] theorem map_comp_fun (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext c; exact comp_map f g c

instance : Functor DataCtor where map := map
instance : LawfulFunctor DataCtor where
  map_const := rfl
  id_map := id_map
  comp_map := comp_map

@[always_inline, simp] def mapM [Monad m] (f : α → m β) (c : DataCtor α) : m (DataCtor β) := do
  let params ← c.parameters.mapM (Type_.mapM f)
  pure { c with parameters := params }

end DataCtor

@[always_inline] instance : Functor DataCtor where
  map := DataCtor.map

instance : LawfulFunctor DataCtor where
  map_const := rfl
  id_map e := DataCtor.id_map e
  comp_map f g e := DataCtor.comp_map f g e

inductive ClassFundep
  | Determined (token : SourceToken) (names : NonEmptyArray (Name Ident))
  | Determines (left : NonEmptyArray (Name Ident)) (token : SourceToken) (right : NonEmptyArray (Name Ident))
  deriving Repr, BEq

structure ClassHead (e : Type) where
  keyword : SourceToken
  typeConstraint : Option (OneOrDelimited (Type_ e) × SourceToken)
  name : Name Proper
  parameters : Array (TypeVarBinding (Name Ident) (Type_ e))
  fundependencies : Option (SourceToken × Separated ClassFundep)
  deriving Repr, BEq

namespace ClassHead

@[always_inline, simp] def map (f : α → β) (h : ClassHead α) : ClassHead β :=
  { h with
    typeConstraint := h.typeConstraint.map (fun (o, t) => (Functor.map (Functor.map f) o, t))
    parameters := h.parameters.map (Functor.map (Functor.map f))
  }

@[simp] theorem id_map (h : ClassHead α) : (h.map id) = h := by
  cases h; aesop

@[simp] theorem comp_map (f : α → β) (g : β → γ) (h : ClassHead α) : (h.map (g ∘ f)) = (h.map f |>.map g) := by
  cases h; aesop

@[simp] theorem map_id_fun : map (id : α → α) = id := by funext h; exact id_map h

@[simp] theorem map_comp_fun (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext h; exact comp_map f g h

instance : Functor ClassHead where map := map
instance : LawfulFunctor ClassHead where
  map_const := rfl
  id_map := id_map
  comp_map := comp_map

@[always_inline, simp] def mapM [Monad m] (f : α → m β) (h : ClassHead α) : m (ClassHead β) := do
  let tc ← h.typeConstraint.mapM (fun (o, t) => (·, t) <$> o.mapM (Type_.mapM f))
  let params ← h.parameters.mapM (TypeVarBinding.mapM (Type_.mapM f))
  pure { h with typeConstraint := tc, parameters := params }

end ClassHead


structure InstanceHead (e : Type) where
  keyword : SourceToken
  name : Option (Name Ident × SourceToken)
  constraints : Option (OneOrDelimited (Type_ e) × SourceToken)
  className : QualifiedName Proper
  types : Array (Type_ e)
  deriving Repr, BEq

namespace InstanceHead

@[always_inline, simp] def map (f : α → β) (h : InstanceHead α) : InstanceHead β :=
  { h with
    constraints := h.constraints.map (fun (o, t) => (Functor.map (Functor.map f) o, t))
    types := h.types.map (Functor.map f)
  }

@[simp] theorem id_map (h : InstanceHead α) : (h.map id) = h := by
  cases h; aesop

@[simp] theorem comp_map (f : α → β) (g : β → γ) (h : InstanceHead α) : (h.map (g ∘ f)) = (h.map f |>.map g) := by
  cases h; aesop

@[simp] theorem map_id_fun : map (id : α → α) = id := by funext h; exact id_map h

@[simp] theorem map_comp_fun (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext h; exact comp_map f g h

instance : Functor InstanceHead where map := map
instance : LawfulFunctor InstanceHead where
  map_const := rfl
  id_map := id_map
  comp_map := comp_map

@[always_inline, simp] def mapM [Monad m] (f : α → m β) (h : InstanceHead α) : m (InstanceHead β) := do
  let tc ← h.constraints.mapM (fun (o, t) => (·, t) <$> o.mapM (Type_.mapM f))
  let tys ← h.types.mapM (Type_.mapM f)
  pure { h with constraints := tc, types := tys }

end InstanceHead


inductive RecordLabeled (a : Type)
  | Pun (name : Name Ident)
  | Field (label : Name Label) (separator : SourceToken) (value : a)
  deriving Repr, BEq

-- #print RecordLabeled._sizeOf_1
-- #print RecordLabeled.Pun.sizeOf_spec
-- #print RecordLabeled.Field.sizeOf_spec

namespace RecordLabeled

@[always_inline, simp] def map (f : α → β) (r : RecordLabeled α) : RecordLabeled β :=
  match r with
  | .Pun n         => .Pun n
  | .Field l sep v => .Field l sep (f v)

@[simp] theorem id_map (r : RecordLabeled α) : (r.map id) = r := by
  cases r <;> rfl

@[simp] theorem comp_map (f : α → β) (g : β → γ) (r : RecordLabeled α) : (r.map (g ∘ f)) = (r.map f |>.map g) := by
  cases r <;> rfl

theorem map_id' (r : RecordLabeled α) (f : α → α) (hf : ∀ x, f x = x) : r.map f = r := by
  cases r <;> simp only [map, Field.injEq, true_and]
  simp_all only

theorem map_comp' (r : RecordLabeled α) (f : α → β) (g : β → γ) (h : α → γ) (hh : ∀ x, h x = g (f x)) :
  r.map h = (r.map f).map g := by
  cases r <;> simp only [map, hh]

@[simp] theorem functor_map_id : map (id : α → α) = id := by funext e; exact id_map e

@[simp] theorem functor_map_comp (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext e; exact comp_map f g e

theorem sizeOf_field_value [SizeOf α]
    (l : Name Label) (sep : SourceToken) (v : α) :
    sizeOf v < sizeOf (RecordLabeled.Field l sep v) := by
  rw [RecordLabeled.Field.sizeOf_spec]; omega

-- The real issue is that `field.map (fun b_in => map f b_in)` passes `b_in` as a lambda argument, and Lean generates a termination goal for every possible `b_in` — including the impossible `Pun` case where the function is never actually called.
-- The solution: add a `Membership` instance for `RecordLabeled` and a `sizeOf_attach_elem` lemma
instance : Membership α (RecordLabeled α) where
  mem r a := match r with
    | .Pun _     => False
    | .Field _ _ v => a = v

@[simp] theorem mem_def (a : α) (r : RecordLabeled α) :
    a ∈ r ↔ match r with | .Pun _ => False | .Field _ _ v => a = v := Iff.rfl

@[simp] theorem sizeOf_attach_elem [SizeOf α] (r : RecordLabeled α)
    (x : { x // x ∈ r }) : sizeOf x.val < sizeOf r := by
  obtain ⟨val, property⟩ := x
  cases r with
  | Pun n => exact absurd property (by simp only [mem_def, not_false_eq_true])
  | Field l sep v =>
    simp only [mem_def] at property
    subst property
    rw [RecordLabeled.Field.sizeOf_spec]
    grind only

def attach (r : RecordLabeled α) : RecordLabeled { x // x ∈ r } :=
  match r with
  | .Pun n     => .Pun n
  | .Field l sep v => .Field l sep ⟨v, by simp only [mem_def]⟩

@[simp] theorem attach_map (r : RecordLabeled α) (f : α → β) :
    r.attach.map (fun x => f x.val) = r.map f := by
  cases r <;> rfl

@[simp] theorem attach_map_val (r : RecordLabeled α) :
    r.attach.map (fun x => x.val) = r := by
  cases r <;> rfl

@[always_inline, simp] def mapM [Applicative m] (f : α → m β) (r : RecordLabeled α) : m (RecordLabeled β) := match r with | .Pun n => pure (.Pun n) | .Field l sep v => .Field l sep <$> f v

end RecordLabeled

@[always_inline] instance : Functor RecordLabeled where
  map := RecordLabeled.map

instance : LawfulFunctor RecordLabeled where
  map_const := rfl
  id_map r := RecordLabeled.id_map r
  comp_map f g r := RecordLabeled.comp_map f g r

inductive BinderF (e binder_e : Type)
  | Wildcard (token : SourceToken)
  | Var (name : Name Ident)
  | Named (name : Name Ident) (token : SourceToken) (binder : binder_e)
  | Constructor (name : QualifiedName Proper) (args : Array binder_e)
  | Boolean (token : SourceToken) (val : Bool)
  | Char (token : SourceToken) (val : Char)
  | String (token : SourceToken) (val : String)
  | Int (prefix_ : Option SourceToken) (token : SourceToken) (val : IntValue)
  | Number (prefix_ : Option SourceToken) (token : SourceToken) (val : Float)
  | Array (items : Delimited binder_e)
  | Record (fields : Delimited (RecordLabeled binder_e))
  | Parens (wrapped : Wrapped binder_e)
  | Typed (binder : binder_e) (token : SourceToken) (type_ : Type_ e)
  | Op (first : binder_e) (ops : NonEmptyArray (QualifiedName Operator × binder_e))
  | Error (data : e)
  deriving Repr, BEq

namespace BinderF

@[always_inline, simp] def map_all (f : e → e') (f_binder : binder_e → binder_e') (b : BinderF e binder_e) : BinderF e' binder_e' :=
  match b with
  | Wildcard t => Wildcard t
  | Var n => Var n
  | Named n t b' => Named n t (f_binder b')
  | Constructor n args => Constructor n (args.map f_binder)
  | Boolean t v => Boolean t v
  | Char t v => Char t v
  | String t v => String t v
  | Int p t v => Int p t v
  | Number p t v => Number p t v
  | Array items => Array (items.map f_binder)
  | Record fields => Record (fields.map (Functor.map f_binder))
  | Parens w => Parens (w.map f_binder)
  | Typed b_e t t_ => Typed (f_binder b_e) t (t_.map f)
  | Op first ops => Op (f_binder first) (ops.map (fun (o, b) => (o, f_binder b)))
  | Error d => Error (f d)

@[simp] theorem map_all_id (b : BinderF e binder_e) : b.map_all id id = b := by
  cases b <;> simp only [Array.map_id_fun, Array.map_id_fun', Delimited.map, NonEmptyArray.map, Separated.map_id_fun, Type_.map_id, Wrapped.map, functor_map_id, id_eq, id_map, map_all]

@[simp] theorem map_all_comp
  (f1 : e1 → e2) (f2 : e2 → e3) (g1 : binder_e1 → binder_e2) (g2 : binder_e2 → binder_e3)
  (b : BinderF e1 binder_e1) :
  b.map_all (f2 ∘ f1) (g2 ∘ g1) = (b.map_all f1 g1).map_all f2 g2 := by
  cases b <;> simp only [map_all, Function.comp_apply, Array.map_map, Delimited.map, Separated.map_comp_fun, Option.map_eq_map, Option.map_map, functor_map_comp, Wrapped.map, Type_.map_comp, NonEmptyArray.map, Op.injEq, NonEmptyArray.mk.injEq, Array.map_inj_left, implies_true, and_self]

@[always_inline, simp] def map_binder_e (f : binder_e → binder_e') (b : BinderF e binder_e) : BinderF e binder_e' :=
  b.map_all id f

@[always_inline, simp] def map_e (f : e → e') (b : BinderF e binder_e) : BinderF e' binder_e :=
  b.map_all f id

@[simp] theorem map_e_id (b : BinderF e binder_e) : b.map_e id = b := by
  rw [map_e, map_all_id]

@[simp] theorem map_e_comp (f : e1 → e2) (g : e2 → e3) (b : BinderF e1 binder_e) : b.map_e (g ∘ f) = (b.map_e f).map_e g := by
  rw [map_e, map_e, map_e, ← map_all_comp f g id id]
  rfl

@[simp] theorem map_binder_e_id (b : BinderF e binder_e) : b.map_binder_e id = b := by
  rw [map_binder_e, map_all_id]

@[simp] theorem map_binder_e_comp (f : binder_e1 → binder_e2) (g : binder_e2 → binder_e3) (b : BinderF e binder_e1) : b.map_binder_e (g ∘ f) = (b.map_binder_e f).map_binder_e g := by
  rw [map_binder_e, map_binder_e, map_binder_e, ← map_all_comp id id f g]
  rfl

@[always_inline, simp] def mapM_all [Monad m] (f : e → m e') (f_binder : binder_e → m binder_e') (b : BinderF e binder_e) : m (BinderF e' binder_e') :=
  match b with
  | Wildcard t => pure (Wildcard t)
  | Var n => pure (Var n)
  | Named n t b' => Named n t <$> f_binder b'
  | Constructor n args => Constructor n <$> args.mapM f_binder
  | Boolean t v => pure (Boolean t v)
  | Char t v => pure (Char t v)
  | String t v => pure (String t v)
  | Int p t v => pure (Int p t v)
  | Number p t v => pure (Number p t v)
  | Array items => Array <$> items.mapM f_binder
  | Record fields => Record <$> fields.mapM (RecordLabeled.mapM f_binder)
  | Parens w => Parens <$> w.mapM f_binder
  | Typed b_e t t_ => Typed <$> f_binder b_e <*> pure t <*> t_.mapM f
  | Op first ops => Op <$> f_binder first <*> ops.mapM (fun (o, b') => do pure (o, ← f_binder b'))
  | Error d => Error <$> f d

end BinderF

/--
info:
generate_fixed expansion:
inductive Binder (e : Type) : Type where
  | Wildcard (token : SourceToken) : Binder e
  | Var (name : Name Ident) : Binder e
  | Named (name : Name Ident) (token : SourceToken) (binder : (Binder e)) : Binder e
  | Constructor (name : QualifiedName Proper) (args : Array (Binder e)) : Binder e
  | Boolean (token : SourceToken) (val : Bool) : Binder e
  | Char (token : SourceToken) (val : Char) : Binder e
  | String (token : SourceToken) (val : String) : Binder e
  | Int (prefix_ : Option SourceToken) (token : SourceToken) (val : IntValue) : Binder e
  | Number (prefix_ : Option SourceToken) (token : SourceToken) (val : Float) : Binder e
  | Array (items : Delimited (Binder e)) : Binder e
  | Record (fields : Delimited (RecordLabeled (Binder e))) : Binder e
  | Parens (wrapped : Wrapped (Binder e)) : Binder e
  | Typed (binder : (Binder e)) (token : SourceToken) (type_ : Type_ e) : Binder e
  | Op (first : (Binder e)) (ops : NonEmptyArray (QualifiedName Operator × (Binder e))) : Binder e
  | Error (data : e) : Binder e
  deriving Repr, BEq
-/
#guard_msgs in
generate_fixed? Binder (e : Type) from BinderF
  fill binder_e with (Binder e)
  deriving Repr, BEq

namespace Binder

@[simp] theorem Named.sizeOf_binder [SizeOf e] (n : Name Ident) (t : SourceToken) (b : Binder e) :
    sizeOf b < sizeOf (Binder.Named n t b) := by
  simp only [Named.sizeOf_spec]; omega

@[simp] theorem Constructor.sizeOf_binder_arr [SizeOf e] (n : QualifiedName Proper) (args : _root_.Array (Binder e)) (i : Nat) (h : i < args.size) :
    sizeOf args[i] < sizeOf (Binder.Constructor n args) := by
  simp only [Constructor.sizeOf_spec]
  have := Array.sizeOf_getElem args i h
  omega

@[simp] theorem Typed.sizeOf_binder [SizeOf e] (b : Binder e) (t : SourceToken) (t_ : Type_ e) :
    sizeOf b < sizeOf (Binder.Typed b t t_) := by
  simp only [Typed.sizeOf_spec]; omega

@[simp] theorem Op.sizeOf_first [SizeOf e] (first : Binder e) (ops : NonEmptyArray (QualifiedName Operator × Binder e)) :
    sizeOf first < sizeOf (Op first ops) := by
  simp only [Op.sizeOf_spec]; omega

mutual
  def map (f : e1 → e2) (b : Binder e1) : Binder e2 :=
    match b with
      | .Wildcard t         => .Wildcard t
      | .Var n              => .Var n
      | .Named n t b        => .Named n t (map f b)
      | .Constructor n args => .Constructor n (args.attach.map (fun ⟨b, _hmem⟩ => map f b))
      | .Boolean t v        => .Boolean t v
      | .Char t v           => .Char t v
      | .String t v => .String t v
      | .Int p t v          => .Int p t v
      | .Number p t v       => .Number p t v
      | .Array items        => .Array (mapDelimited f items)
      | .Record fields      => .Record (mapDelimitedRecordLabeled f fields)
      | .Parens w           => .Parens (mapWrapped f w)
      | .Typed b t t_       => .Typed (map f b) t (t_.map f)
      | .Op first ops       => .Op (map f first) (ops.attach.map (fun ⟨⟨n, b⟩, _hmem⟩ => (n, map f b)))
      | .Error d            => .Error (f d)
  termination_by sizeOf b
  decreasing_by
    all_goals (simp_all only [Array.sizeOf_spec, Constructor.sizeOf_spec, Named.sizeOf_spec, Nat.lt_add_left_iff_pos, Nat.lt_add_one, Op.sizeOf_spec, Parens.sizeOf_spec, Record.sizeOf_spec, Typed.sizeOf_spec]; simp_wf; try omega)
    · have := Array.sizeOf_lt_of_mem _hmem; omega
    · have := NonEmptyArray.sizeOf_lt_of_mem _hmem; simp only [Prod.mk.sizeOf_spec, gt_iff_lt] at *; omega

  def mapDelimited (f : e1 → e2) (d : Delimited (Binder e1)) : Delimited (Binder e2) :=
    match d with
    | .mk w => .mk (mapWrappedOptionSeparated f w)
  termination_by sizeOf d
  decreasing_by all_goals (simp_all only [Delimited.mk.sizeOf_spec, Nat.lt_add_left_iff_pos, Nat.lt_add_one])

  def mapWrappedOptionSeparated (f : e1 → e2) (w : Wrapped (Option (Separated (Binder e1)))) : Wrapped (Option (Separated (Binder e2))) :=
    { w with value := mapOptionSeparated f w.value }
  termination_by sizeOf w
  decreasing_by all_goals (simp_all only [Wrapped.sizeOf_value])

  def mapOptionSeparated (f : e1 → e2) (o : Option (Separated (Binder e1))) : Option (Separated (Binder e2)) :=
    match o with
    | none => none
    | some s => some (mapSeparated f s)
  termination_by sizeOf o
  decreasing_by all_goals (simp_all only [Option.some.sizeOf_spec, Nat.lt_add_left_iff_pos, Nat.lt_add_one])

  def mapSeparated (f : e1 → e2) (s : Separated (Binder e1)) : Separated (Binder e2) :=
    { head := map f s.head, tail := s.tail.attach.map (fun ⟨⟨tok, b⟩, _hmem⟩ => (tok, map f b)) }
  termination_by sizeOf s
  decreasing_by
    simp_wf
    obtain ⟨i, hi, h⟩ := Array.mem_iff_getElem.mp _hmem
    have : b = s.tail[i].2 := by simp only [h]
    rw [this]
    exact s.sizeOf_tail_get i hi

  def mapDelimitedRecordLabeled (f : e1 → e2) (fields : Delimited (RecordLabeled (Binder e1))) : Delimited (RecordLabeled (Binder e2)) :=
    match fields with
    | .mk w => .mk (mapWrappedOptionSeparatedRecordLabeled f w)
  termination_by sizeOf fields
  decreasing_by all_goals (simp_all only [Delimited.mk.sizeOf_spec, Nat.lt_add_left_iff_pos, Nat.lt_add_one])

  def mapWrappedOptionSeparatedRecordLabeled (f : e1 → e2) (w : Wrapped (Option (Separated (RecordLabeled (Binder e1))))) : Wrapped (Option (Separated (RecordLabeled (Binder e2)))) :=
    { w with value := mapOptionSeparatedRecordLabeled f w.value }
  termination_by sizeOf w
  decreasing_by all_goals (simp_all only [Wrapped.sizeOf_value])

  def mapOptionSeparatedRecordLabeled (f : e1 → e2) (o : Option (Separated (RecordLabeled (Binder e1)))) : Option (Separated (RecordLabeled (Binder e2))) :=
    match o with
    | none => none
    | some s => some (mapSeparatedRecordLabeled f s)
  termination_by sizeOf o
  decreasing_by all_goals (simp_all only [Option.some.sizeOf_spec, Nat.lt_add_left_iff_pos, Nat.lt_add_one])

  def mapSeparatedRecordLabeled (f : e1 → e2) (s : Separated (RecordLabeled (Binder e1))) : Separated (RecordLabeled (Binder e2)) :=
    { head := mapRecordLabeled f s.head, tail := s.tail.attach.map (fun ⟨⟨tok, rl⟩, _hmem⟩ => (tok, mapRecordLabeled f rl)) }
  termination_by sizeOf s
  decreasing_by
    simp_wf
    obtain ⟨i, hi, h⟩ := Array.mem_iff_getElem.mp _hmem
    have : rl = (s.tail[i]).2 := by simp only [h]
    rw [this]
    exact s.sizeOf_tail_get i hi

  def mapRecordLabeled (f : e1 → e2) (rl : RecordLabeled (Binder e1)) : RecordLabeled (Binder e2) :=
    match rl with
    | .Pun n => .Pun n
    | .Field l sep v => .Field l sep (map f v)
  termination_by sizeOf rl
  decreasing_by
    simp_wf
    grind only

  def mapWrapped (f : e1 → e2) (w : Wrapped (Binder e1)) : Wrapped (Binder e2) :=
    { w with value := map f w.value }
  termination_by sizeOf w
  decreasing_by all_goals (simp_all only [Wrapped.sizeOf_value])
end


mutual
  @[simp] theorem map_id (binder : Binder e) : map id binder = binder := by
    match binder with
    | .Wildcard t => simp only [map]
    | .Var n => simp only [map]
    | .Named n t child =>
        have ih := map_id child
        simpa only [map] using congrArg (Binder.Named n t) ih
    | .Constructor n args =>
        simp only [map]
        congr
        ext i hi₁ hi₂ : 1
        · simp_all only [Array.size_map, Array.size_attach]
        · simpa only [Array.getElem_map, Array.getElem_attach] using map_id args[i]
    | .Boolean t v => simp only [map]
    | .Char t v => simp only [map]
    | .String t v => simp only [map]
    | .Int p t v => simp only [map]
    | .Number p t v => simp only [map]
    | .Array (.mk ⟨open_, none, close⟩) =>
        simp only [map, mapDelimited, mapWrappedOptionSeparated, mapOptionSeparated]
    | .Array (.mk ⟨open_, some s, close⟩) =>
        have hs : mapSeparated id s = s := by
          simp only [mapSeparated]
          congr
          · simpa only using map_id s.head
          ext i hi₁ hi₂ : 1
          · simp_all only [Array.size_map, Array.size_attach]
          · ext : 1
            · simp_all only [Array.getElem_map, Array.getElem_attach]
            · simpa only [Array.getElem_map, Array.getElem_attach] using map_id (s.tail[i]'hi₂).2
        simp only [map, mapDelimited, mapWrappedOptionSeparated, mapOptionSeparated, hs]
    | .Record (.mk ⟨open_, none, close⟩) =>
        simp only [map, mapDelimitedRecordLabeled, mapWrappedOptionSeparatedRecordLabeled, mapOptionSeparatedRecordLabeled]
    | .Record (.mk ⟨open_, some s, close⟩) =>
        have hs : mapSeparatedRecordLabeled id s = s := by
          cases s with
          | mk head tail =>
              have hhead : mapRecordLabeled id head = head := mapRecordLabeled_id head
              simp only [mapSeparatedRecordLabeled, hhead]
              congr
              ext i hi₁ hi₂ : 1
              · simp_all only [Array.size_map, Array.size_attach]
              · ext : 1
                · simp_all only [Array.getElem_map, Array.getElem_attach]
                · have htail : mapRecordLabeled id (tail[i]'hi₂).2 = (tail[i]'hi₂).2 := mapRecordLabeled_id (tail[i]'hi₂).2
                  simpa only [Array.getElem_map, Array.getElem_attach] using htail
        simp only [map, mapDelimitedRecordLabeled, mapWrappedOptionSeparatedRecordLabeled, mapOptionSeparatedRecordLabeled, hs]
    | .Parens ⟨open_, value, close⟩ =>
        have ih := map_id value
        simpa only [map, mapWrapped] using congrArg (fun v => Binder.Parens { open_ := open_, value := v, close := close }) ih
    | .Typed child t t_ =>
        have ih := map_id child
        simpa only [map, Type_.map_id] using congrArg (fun v => Binder.Typed v t t_) ih
    | .Op first ops =>
        have ihFirst := map_id first
        cases ops with
        | mk head tail =>
            cases head with
            | mk op child =>
                have ihHead := map_id child
                have htailMap : tail.map (fun p => (p.1, map id p.2)) = tail := by
                  ext i hi₁ hi₂ : 1
                  · simp_all only [Array.size_map]
                  · ext : 1
                    · simp_all only [Array.getElem_map]
                    · simpa only [Array.getElem_map] using map_id (tail[i]'hi₂).2
                have htail : tail.attach.map (fun ⟨p, _⟩ => (p.1, map id p.2)) = tail := by
                  ext i hi₁ hi₂ : 1
                  · simp_all only [Array.size_map, Array.size_attach]
                  · ext : 1
                    · simp_all only [Array.getElem_map, Array.getElem_attach]
                    · simpa only [Array.getElem_map, Array.getElem_attach] using map_id (tail[i]'hi₂).2
                have hOpsMap :
                    NonEmptyArray.map (fun p => (p.1, map id p.2)) ⟨(op, child), tail⟩ =
                      ⟨(op, child), tail⟩ := by
                  simp only [NonEmptyArray.map, ihHead, htailMap]
                have hOpsAttach :
                    (⟨(op, child), tail⟩ : NonEmptyArray (QualifiedName Operator × Binder e)).attach.map
                        (fun ⟨p, _⟩ => (p.1, map id p.2)) =
                      ⟨(op, child), tail⟩ := by
                  exact (NonEmptyArray.attach_map ⟨(op, child), tail⟩ (fun p => (p.1, map id p.2))).trans hOpsMap
                simpa only [map, ihFirst] using congrArg (Binder.Op first) hOpsAttach
    | .Error d => simp only [map, id_eq]
  termination_by sizeOf binder
  decreasing_by
    all_goals (simp_all only [Array.sizeOf_spec, Constructor.sizeOf_spec, Named.sizeOf_spec,
      Op.sizeOf_spec, Parens.sizeOf_spec, Record.sizeOf_spec, Typed.sizeOf_spec,
      Delimited.mk.sizeOf_spec]; simp_wf; try omega)
    · simpa only [Constructor.sizeOf_spec] using Binder.Constructor.sizeOf_binder_arr n args i hi₂
    · have h1 : sizeOf s.head < sizeOf s := Separated.sizeOf_head s
      have _h2 : sizeOf s < sizeOf (Wrapped.mk open_ (some s) close) := by
        have h3 : sizeOf (some s) < sizeOf (Wrapped.mk open_ (some s) close) := Wrapped.sizeOf_value (Wrapped.mk open_ (some s) close)
        simp only [Option.some.sizeOf_spec] at h3
        omega
      omega
    · have h1 : sizeOf (s.tail[i]'hi₂).2 < sizeOf s := Separated.sizeOf_tail_get s i hi₂
      have _h2 : sizeOf s < sizeOf (Wrapped.mk open_ (some s) close) := by
        have h3 : sizeOf (some s) < sizeOf (Wrapped.mk open_ (some s) close) := Wrapped.sizeOf_value (Wrapped.mk open_ (some s) close)
        simp only [Option.some.sizeOf_spec] at h3
        omega
      omega
    · have h1 : sizeOf tail[i].snd < sizeOf ({ head := head, tail := tail } : Separated (RecordLabeled (Binder _))) := by
        simpa only [Separated.mk.sizeOf_spec] using
          Separated.sizeOf_tail_get
            ({ head := head, tail := tail } : Separated (RecordLabeled (Binder _))) i hi₂
      have h2 : sizeOf ({ head := head, tail := tail } : Separated (RecordLabeled (Binder _))) <
          sizeOf (Wrapped.mk open_ (some ({ head := head, tail := tail } : Separated (RecordLabeled (Binder _)))) close) := by
        have h3 :
            sizeOf (some ({ head := head, tail := tail } : Separated (RecordLabeled (Binder _)))) <
              sizeOf (Wrapped.mk open_ (some ({ head := head, tail := tail } : Separated (RecordLabeled (Binder _)))) close) :=
          Wrapped.sizeOf_value (Wrapped.mk open_ (some ({ head := head, tail := tail } : Separated (RecordLabeled (Binder _)))) close)
        simp only [Option.some.sizeOf_spec] at h3
        omega
      have h3 :
          sizeOf (Wrapped.mk open_ (some ({ head := head, tail := tail } : Separated (RecordLabeled (Binder _)))) close) <
            sizeOf (Record (Delimited.mk { open_ := open_, value := some { head := head, tail := tail }, close := close })) := by
        simp only [Record.sizeOf_spec, Delimited.mk.sizeOf_spec]
        omega
      simpa only [Record.sizeOf_spec, Delimited.mk.sizeOf_spec] using Nat.lt_trans h1 (Nat.lt_trans h2 h3)
    · cases hpair : tail[i]'hi₂ with
      | mk fst snd =>
          have hget := Array.sizeOf_getElem tail i hi₂
          simp only [hpair, Prod.mk.sizeOf_spec] at hget ⊢
          clear hi₁
          omega
    · clear hi₁ htailMap
      have htail : sizeOf tail < sizeOf ({ head := (op, child), tail := tail } : NonEmptyArray (QualifiedName Operator × Binder e)) := by
        change sizeOf tail < 1 + sizeOf (op, child) + sizeOf tail
        omega
      have hops : sizeOf ({ head := (op, child), tail := tail } : NonEmptyArray (QualifiedName Operator × Binder e)) <
          sizeOf (first.Op { head := (op, child), tail := tail }) := by
        simp only [Op.sizeOf_spec]
        omega
      have hpair : sizeOf tail[i].snd < sizeOf tail := by
        have hget := Array.sizeOf_getElem tail i hi₂
        match hpair : tail[i] with
        | (fst, snd) =>
            simp only [hpair, Prod.mk.sizeOf_spec] at hget ⊢
            omega
      simpa only [Op.sizeOf_spec] using Nat.lt_trans hpair (Nat.lt_trans htail hops)

  @[simp] theorem mapRecordLabeled_id (rl : RecordLabeled (Binder e)) : mapRecordLabeled id rl = rl := by
    match rl with
    | .Pun n => simp only [mapRecordLabeled]
    | .Field l sep v =>
        have ih := map_id v
        simpa only [mapRecordLabeled] using congrArg (RecordLabeled.Field l sep) ih
  termination_by sizeOf rl
  decreasing_by
    simp_wf
    omega
end

@[simp] theorem mapSeparated_id (s : Separated (Binder e)) : mapSeparated id s = s := by
  simp only [mapSeparated, map_id]
  congr
  ext i hi₁ hi₂ : 1
  · simp_all only [Array.size_map, Array.size_attach]
  · ext : 1
    · simp_all only [Array.getElem_map, Array.getElem_attach]
    · simp_all only [Array.getElem_map, Array.getElem_attach]

@[simp] theorem mapSeparatedRecordLabeled_id (s : Separated (RecordLabeled (Binder e))) : mapSeparatedRecordLabeled id s = s := by
  simp only [mapSeparatedRecordLabeled, mapRecordLabeled_id]
  congr
  ext i hi₁ hi₂ : 1
  · simp_all only [Array.size_map, Array.size_attach]
  · ext : 1
    · simp_all only [Array.getElem_map, Array.getElem_attach]
    · simp_all only [Array.getElem_map, Array.getElem_attach]

@[simp] theorem mapOptionSeparated_id (o : Option (Separated (Binder e))) : mapOptionSeparated id o = o := by
  cases o <;> simp only [mapOptionSeparated, mapSeparated_id]

@[simp] theorem mapWrappedOptionSeparated_id (w : Wrapped (Option (Separated (Binder e)))) : mapWrappedOptionSeparated id w = w := by
  cases w
  simp only [mapWrappedOptionSeparated, mapOptionSeparated_id]

@[simp] theorem mapDelimited_id (d : Delimited (Binder e)) : mapDelimited id d = d := by
  cases d
  simp only [mapDelimited, mapWrappedOptionSeparated_id]

@[simp] theorem mapWrapped_id (w : Wrapped (Binder e)) : mapWrapped id w = w := by
  cases w
  simp only [mapWrapped, map_id]

@[simp] theorem mapOptionSeparatedRecordLabeled_id (o : Option (Separated (RecordLabeled (Binder e)))) :
    mapOptionSeparatedRecordLabeled id o = o := by
  cases o <;> simp only [mapOptionSeparatedRecordLabeled, mapSeparatedRecordLabeled_id]

@[simp] theorem mapWrappedOptionSeparatedRecordLabeled_id
    (w : Wrapped (Option (Separated (RecordLabeled (Binder e))))) :
    mapWrappedOptionSeparatedRecordLabeled id w = w := by
  cases w
  simp only [mapWrappedOptionSeparatedRecordLabeled, mapOptionSeparatedRecordLabeled_id]

@[simp] theorem mapDelimitedRecordLabeled_id (d : Delimited (RecordLabeled (Binder e))) :
    mapDelimitedRecordLabeled id d = d := by
  cases d
  simp only [mapDelimitedRecordLabeled, mapWrappedOptionSeparatedRecordLabeled_id]

@[simp] theorem mapArray_eq (g : e → f) (arr : _root_.Array (Binder e)) :
    arr.map (map g) = arr.attach.map (fun ⟨b, _⟩ => map g b) := by
  simp only [Array.map_subtype, Array.unattach_attach]

mutual
  @[simp] theorem map_comp (f : e1 → e2) (g : e2 → e3) (b : Binder e1) : map (g ∘ f) b = map g (map f b) := by
    match b with
    | .Wildcard _ => simp only [map]
    | .Var _ => simp only [map]
    | .Named n t b =>
        have ih := map_comp f g b
        simpa only [map, Function.comp_apply] using congrArg (Binder.Named n t) ih
    | .Constructor n args =>
        have hargs : args.map (map (g ∘ f)) = (args.map (map f)).map (map g) := by
          apply Array.ext
          · simp only [Array.size_map]
          · intro i hi₁ hi₂
            simp only [Array.getElem_map]
            have hi : i < args.size := by simpa only [Array.size_map] using hi₂
            simpa only [Function.comp_apply] using map_comp f g (args[i]'hi)
        simpa only [map, Array.map_subtype, Array.unattach_attach, Array.map_map, Function.comp_apply] using
          congrArg (Binder.Constructor n) hargs
    | .Boolean _ _ => simp only [map]
    | .Char _ _ => simp only [map]
    | .String _ _ => simp only [map]
    | .Int _ _ _ => simp only [map]
    | .Number _ _ _ => simp only [map]
    | .Array items =>
        simpa only [map] using congrArg Binder.Array (mapDelimited_comp f g items)
    | .Record fields =>
        simpa only [map] using congrArg Binder.Record (mapDelimitedRecordLabeled_comp f g fields)
    | .Parens w =>
        simpa only [map] using congrArg Binder.Parens (mapWrapped_comp f g w)
    | .Typed b t t_ =>
        have ih := map_comp f g b
        simpa only [map, Function.comp_apply, Type_.map_comp] using congrArg (fun v => Binder.Typed v t (Type_.map (g ∘ f) t_)) ih
    | .Op first ops =>
        have ihFirst := map_comp f g first
        cases ops with
        | mk head tail =>
            cases head with
            | mk op child =>
                have ihHead := map_comp f g child
                have htailMap :
                    tail.map (fun p => (p.1, map (g ∘ f) p.2)) =
                      (tail.map (fun p => (p.1, map f p.2))).map (fun p => (p.1, map g p.2)) := by
                  apply Array.ext
                  · simp only [Array.size_map]
                  · intro i hi₁ hi₂
                    simp only [Array.getElem_map]
                    ext : 1
                    · rfl
                    · have hi : i < tail.size := by simpa only [Array.size_map] using hi₂
                      simpa only [Function.comp_apply] using map_comp f g ((tail[i]'hi).2)
                have hOpsMap :
                    NonEmptyArray.map (fun p => (p.1, map (g ∘ f) p.2)) ⟨(op, child), tail⟩ =
                      NonEmptyArray.map (fun p => (p.1, map g p.2))
                        (NonEmptyArray.map (fun p => (p.1, map f p.2)) ⟨(op, child), tail⟩) := by
                  simp only [NonEmptyArray.map, ihHead, htailMap]
                let ops' : NonEmptyArray (QualifiedName Operator × Binder e1) := ⟨(op, child), tail⟩
                have hInner :
                    NonEmptyArray.map (fun x => (x.1.fst, map f x.1.snd)) ops'.attach =
                      NonEmptyArray.map (fun p => (p.1, map f p.2)) ops' := by
                  simpa only [NonEmptyArray.map, NonEmptyArray.mk.injEq, Prod.mk.injEq] using
                    (NonEmptyArray.attach_map ops' (fun p => (p.1, map f p.2)))
                have hOpsAttach :
                    NonEmptyArray.map (fun x => (x.1.fst, map (g ∘ f) x.1.snd)) ops'.attach =
                      NonEmptyArray.map (fun x => (x.1.fst, map g x.1.snd))
                        (NonEmptyArray.map (fun x => (x.1.fst, map f x.1.snd)) ops'.attach).attach := by
                  rw [hInner]
                  exact (NonEmptyArray.attach_map ops' (fun p => (p.1, map (g ∘ f) p.2))).trans <|
                    hOpsMap.trans <|
                      (NonEmptyArray.attach_map (NonEmptyArray.map (fun p => (p.1, map f p.2)) ops')
                        (fun p => (p.1, map g p.2))).symm
                simpa only [map, Function.comp_apply, ihFirst, ops'] using
                  congrArg (Binder.Op (map g (map f first))) hOpsAttach
    | .Error _ => simp only [map, Function.comp_apply]
  termination_by sizeOf b
  decreasing_by
    · simpa only [Named.sizeOf_spec] using Binder.Named.sizeOf_binder n t b
    · have hi : i < args.size := by simpa only [Array.size_map, Array.size_attach] using hi₂
      simpa only [Constructor.sizeOf_spec] using Binder.Constructor.sizeOf_binder_arr n args i hi
    · simp only [Array.sizeOf_spec]
      omega
    · simp only [Record.sizeOf_spec]
      omega
    · simp only [Parens.sizeOf_spec]
      omega
    · simpa only [Typed.sizeOf_spec] using Binder.Typed.sizeOf_binder b t t_
    · simpa only [Op.sizeOf_spec] using Binder.Op.sizeOf_first first ops
    · have hpair : sizeOf child < sizeOf (op, child) := by
        simp only [Prod.mk.sizeOf_spec]
        omega
      have hhead : sizeOf (op, child) < sizeOf ({ head := (op, child), tail := tail } : NonEmptyArray (QualifiedName Operator × Binder e1)) := by
        change sizeOf (op, child) < 1 + sizeOf (op, child) + sizeOf tail
        omega
      have hops : sizeOf ({ head := (op, child), tail := tail } : NonEmptyArray (QualifiedName Operator × Binder e1)) <
          sizeOf (first.Op { head := (op, child), tail := tail }) := by
        simp only [Op.sizeOf_spec]
        omega
      simpa only [Op.sizeOf_spec] using Nat.lt_trans hpair (Nat.lt_trans hhead hops)
    · clear hi₁
      have htail : sizeOf tail < sizeOf ({ head := (op, child), tail := tail } : NonEmptyArray (QualifiedName Operator × Binder e1)) := by
        change sizeOf tail < 1 + sizeOf (op, child) + sizeOf tail
        omega
      have hops : sizeOf ({ head := (op, child), tail := tail } : NonEmptyArray (QualifiedName Operator × Binder e1)) <
          sizeOf (first.Op { head := (op, child), tail := tail }) := by
        simp only [Op.sizeOf_spec]
        omega
      have hpair : sizeOf tail[i].snd < sizeOf tail := by
        have hi : i < tail.size := by simpa only [Array.size_map] using hi₂
        have hget := Array.sizeOf_getElem tail i hi
        match hpair : tail[i] with
        | (fst, snd) =>
            simp only [hpair, Prod.mk.sizeOf_spec] at hget ⊢
            omega
      simpa only [Op.sizeOf_spec] using Nat.lt_trans hpair (Nat.lt_trans htail hops)

  @[simp] theorem mapDelimited_comp (f : e1 → e2) (g : e2 → e3) (d : Delimited (Binder e1)) :
      mapDelimited (g ∘ f) d = mapDelimited g (mapDelimited f d) := by
    match d with
    | .mk w => simpa only [mapDelimited] using congrArg Delimited.mk (mapWrappedOptionSeparated_comp f g w)
  termination_by sizeOf d
  decreasing_by
    simp only [Delimited.mk.sizeOf_spec]
    omega

  @[simp] theorem mapWrappedOptionSeparated_comp (f : e1 → e2) (g : e2 → e3)
      (w : Wrapped (Option (Separated (Binder e1)))) :
      mapWrappedOptionSeparated (g ∘ f) w = mapWrappedOptionSeparated g (mapWrappedOptionSeparated f w) := by
    cases w with
    | mk open_ value close =>
        simp only [mapWrappedOptionSeparated, Wrapped.mk.injEq]
        constructor
        · trivial
        constructor
        · exact mapOptionSeparated_comp f g value
        · trivial
  termination_by sizeOf w
  decreasing_by
    simpa only [Wrapped.mk.sizeOf_spec] using
      (Wrapped.sizeOf_value
        ({ open_ := open_, value := value, close := close } :
          Wrapped (Option (Separated (Binder e1)))))

  @[simp] theorem mapOptionSeparated_comp (f : e1 → e2) (g : e2 → e3) (o : Option (Separated (Binder e1))) :
      mapOptionSeparated (g ∘ f) o = mapOptionSeparated g (mapOptionSeparated f o) := by
    match o with
    | none => simp only [mapOptionSeparated]
    | some s => simpa only [mapOptionSeparated] using congrArg some (mapSeparated_comp f g s)
  termination_by sizeOf o
  decreasing_by
    simp only [Option.some.sizeOf_spec]
    omega

  @[simp] theorem mapSeparated_comp (f : e1 → e2) (g : e2 → e3) (s : Separated (Binder e1)) :
      mapSeparated (g ∘ f) s = mapSeparated g (mapSeparated f s) := by
    cases s with
    | mk head tail =>
        simp only [mapSeparated, Separated.mk.injEq]
        constructor
        · exact map_comp f g head
        · apply Array.ext
          · simp only [Array.size_map, Array.size_attach]
          · intro i hi₁ hi₂
            simp only [Array.getElem_map, Array.getElem_attach]
            ext : 1
            · rfl
            · have hi : i < tail.size := by simpa only [Array.size_map, Array.size_attach] using hi₂
              simpa only [Function.comp_apply] using map_comp f g (tail[i]'hi).2
  termination_by sizeOf s
  decreasing_by
    · simpa only [Separated.mk.sizeOf_spec] using
      Separated.sizeOf_head ({ head := head, tail := tail } : Separated (Binder e1))
    · have hi : i < tail.size := by simpa only [Array.size_map, Array.size_attach] using hi₂
      simpa only [Separated.mk.sizeOf_spec, gt_iff_lt] using
        Separated.sizeOf_tail_get ({ head := head, tail := tail } : Separated (Binder e1)) i hi

  @[simp] theorem mapDelimitedRecordLabeled_comp (f : e1 → e2) (g : e2 → e3) (d : Delimited (RecordLabeled (Binder e1))) :
      mapDelimitedRecordLabeled (g ∘ f) d = mapDelimitedRecordLabeled g (mapDelimitedRecordLabeled f d) := by
    match d with
    | .mk w => simpa only [mapDelimitedRecordLabeled] using congrArg Delimited.mk (mapWrappedOptionSeparatedRecordLabeled_comp f g w)
  termination_by sizeOf d
  decreasing_by
    simp only [Delimited.mk.sizeOf_spec]
    omega

  @[simp] theorem mapWrappedOptionSeparatedRecordLabeled_comp (f : e1 → e2) (g : e2 → e3)
      (w : Wrapped (Option (Separated (RecordLabeled (Binder e1))))) :
      mapWrappedOptionSeparatedRecordLabeled (g ∘ f) w =
        mapWrappedOptionSeparatedRecordLabeled g (mapWrappedOptionSeparatedRecordLabeled f w) := by
    cases w with
    | mk open_ value close =>
        simp only [mapWrappedOptionSeparatedRecordLabeled, Wrapped.mk.injEq]
        constructor
        · trivial
        constructor
        · exact mapOptionSeparatedRecordLabeled_comp f g value
        · trivial
  termination_by sizeOf w
  decreasing_by
    simpa only [Wrapped.mk.sizeOf_spec] using
      (Wrapped.sizeOf_value
        ({ open_ := open_, value := value, close := close } :
          Wrapped (Option (Separated (RecordLabeled (Binder e1))))))

  @[simp] theorem mapOptionSeparatedRecordLabeled_comp (f : e1 → e2) (g : e2 → e3)
      (o : Option (Separated (RecordLabeled (Binder e1)))) :
      mapOptionSeparatedRecordLabeled (g ∘ f) o =
        mapOptionSeparatedRecordLabeled g (mapOptionSeparatedRecordLabeled f o) := by
    match o with
    | none => simp only [mapOptionSeparatedRecordLabeled]
    | some s => simpa only [mapOptionSeparatedRecordLabeled] using congrArg some (mapSeparatedRecordLabeled_comp f g s)
  termination_by sizeOf o
  decreasing_by
    simp only [Option.some.sizeOf_spec]
    omega

  @[simp] theorem mapSeparatedRecordLabeled_comp (f : e1 → e2) (g : e2 → e3) (s : Separated (RecordLabeled (Binder e1))) :
      mapSeparatedRecordLabeled (g ∘ f) s = mapSeparatedRecordLabeled g (mapSeparatedRecordLabeled f s) := by
    cases s with
    | mk head tail =>
        simp only [mapSeparatedRecordLabeled, Separated.mk.injEq]
        constructor
        · exact mapRecordLabeled_comp f g head
        · apply Array.ext
          · simp only [Array.size_map, Array.size_attach]
          · intro i hi₁ hi₂
            simp only [Array.getElem_map, Array.getElem_attach]
            ext : 1
            · rfl
            · have hi : i < tail.size := by simpa only [Array.size_map, Array.size_attach] using hi₂
              simpa only [Function.comp_apply] using mapRecordLabeled_comp f g (tail[i]'hi).2
  termination_by sizeOf s
  decreasing_by
    · simpa only [Separated.mk.sizeOf_spec] using
      Separated.sizeOf_head ({ head := head, tail := tail } : Separated (RecordLabeled (Binder e1)))
    · have hi : i < tail.size := by simpa only [Array.size_map, Array.size_attach] using hi₂
      simpa only [Separated.mk.sizeOf_spec, gt_iff_lt] using
        Separated.sizeOf_tail_get
          ({ head := head, tail := tail } : Separated (RecordLabeled (Binder e1))) i hi

  @[simp] theorem mapRecordLabeled_comp (f : e1 → e2) (g : e2 → e3) (rl : RecordLabeled (Binder e1)) :
      mapRecordLabeled (g ∘ f) rl = mapRecordLabeled g (mapRecordLabeled f rl) := by
    match rl with
    | .Pun _ => simp only [mapRecordLabeled]
    | .Field l sep v =>
        have ih := map_comp f g v
        simpa only [mapRecordLabeled, Function.comp_apply] using congrArg (RecordLabeled.Field l sep) ih
  termination_by sizeOf rl
  decreasing_by
    simp_wf
    omega

  @[simp] theorem mapWrapped_comp (f : e1 → e2) (g : e2 → e3) (w : Wrapped (Binder e1)) :
      mapWrapped (g ∘ f) w = mapWrapped g (mapWrapped f w) := by
    cases w with
    | mk open_ value close =>
        simpa only [mapWrapped] using
          congrArg (fun v => Wrapped.mk open_ v close) (map_comp f g value)
  termination_by sizeOf w
  decreasing_by
    simpa only [Wrapped.mk.sizeOf_spec] using
      (Wrapped.sizeOf_value
        ({ open_ := open_, value := value, close := close } : Wrapped (Binder e1)))
end

instance : Functor Binder where map := map
instance : LawfulFunctor Binder where
  map_const := rfl
  id_map := map_id
  comp_map := map_comp


mutual
  @[simp] def mapM [Monad m] (f : e1 → m e2) (b : Binder e1) : m (Binder e2) :=
    match b with
      | .Wildcard t         => pure (.Wildcard t)
      | .Var n              => pure (.Var n)
      | .Named n t b        => .Named n t <$> mapM f b
      | .Constructor n args => .Constructor n <$> args.attach.mapM (fun ⟨b, _hmem⟩ => mapM f b)
      | .Boolean t v        => pure (.Boolean t v)
      | .Char t v           => pure (.Char t v)
      | .String t v => pure (.String t v)
      | .Int p t v          => pure (.Int p t v)
      | .Number p t v       => pure (.Number p t v)
      | .Array items        => .Array <$> mapMDelimited f items
      | .Record fields      => .Record <$> mapMDelimitedRecordLabeled f fields
      | .Parens w           => .Parens <$> mapMWrapped f w
      | .Typed b t t_       => .Typed <$> mapM f b <*> pure t <*> Type_.mapM f t_
      | .Op first ops       => .Op <$> mapM f first <*> ops.attach.mapM (fun ⟨⟨n, b⟩, _hmem⟩ => do pure (n, ← mapM f b))
      | .Error d            => .Error <$> f d
  termination_by sizeOf b
  decreasing_by
    all_goals (simp_all only [Array.sizeOf_spec, Constructor.sizeOf_spec, Named.sizeOf_spec, Nat.lt_add_left_iff_pos, Nat.lt_add_one, Op.sizeOf_spec, Parens.sizeOf_spec, Record.sizeOf_spec, Typed.sizeOf_spec]; simp_wf; try omega)
    · have := Array.sizeOf_lt_of_mem _hmem; omega
    · have := NonEmptyArray.sizeOf_lt_of_mem _hmem; simp only [Prod.mk.sizeOf_spec, gt_iff_lt] at *; omega

  @[simp] def mapMDelimited [Monad m] (f : e1 → m e2) (d : Delimited (Binder e1)) : m (Delimited (Binder e2)) :=
    match d with
    | .mk w => .mk <$> mapMWrappedOptionSeparated f w
  termination_by sizeOf d
  decreasing_by all_goals (simp_all only [Delimited.mk.sizeOf_spec, Nat.lt_add_left_iff_pos, Nat.lt_add_one])

  @[simp] def mapMWrappedOptionSeparated [Monad m] (f : e1 → m e2) (w : Wrapped (Option (Separated (Binder e1)))) : m (Wrapped (Option (Separated (Binder e2)))) := do
    let val ← mapMOptionSeparated f w.value
    pure { w with value := val }
  termination_by sizeOf w
  decreasing_by all_goals (simp_all only [Wrapped.sizeOf_value])

  @[simp] def mapMOptionSeparated [Monad m] (f : e1 → m e2) (o : Option (Separated (Binder e1))) : m (Option (Separated (Binder e2))) :=
    match o with
    | none => pure none
    | some s => some <$> mapMSeparated f s
  termination_by sizeOf o
  decreasing_by all_goals (simp_all only [Option.some.sizeOf_spec, Nat.lt_add_left_iff_pos, Nat.lt_add_one])

  @[simp] def mapMSeparated [Monad m] (f : e1 → m e2) (s : Separated (Binder e1)) : m (Separated (Binder e2)) := do
    let head ← mapM f s.head
    let tail ← s.tail.attach.mapM (fun ⟨⟨tok, b⟩, _hmem⟩ => do pure (tok, ← mapM f b))
    pure { head := head, tail := tail }
  termination_by sizeOf s
  decreasing_by
    simp_wf
    obtain ⟨i, hi, h⟩ := Array.mem_iff_getElem.mp _hmem
    have : b = s.tail[i].2 := by simp only [h]
    rw [this]
    exact s.sizeOf_tail_get i hi

  @[simp] def mapMDelimitedRecordLabeled [Monad m] (f : e1 → m e2) (fields : Delimited (RecordLabeled (Binder e1))) : m (Delimited (RecordLabeled (Binder e2))) :=
    match fields with
    | .mk w => .mk <$> mapMWrappedOptionSeparatedRecordLabeled f w
  termination_by sizeOf fields
  decreasing_by all_goals (simp_all only [Delimited.mk.sizeOf_spec, Nat.lt_add_left_iff_pos, Nat.lt_add_one])

  @[simp] def mapMWrappedOptionSeparatedRecordLabeled [Monad m] (f : e1 → m e2) (w : Wrapped (Option (Separated (RecordLabeled (Binder e1))))) : m (Wrapped (Option (Separated (RecordLabeled (Binder e2))))) := do
    let val ← mapMOptionSeparatedRecordLabeled f w.value
    pure { w with value := val }
  termination_by sizeOf w
  decreasing_by all_goals (simp_all only [Wrapped.sizeOf_value])

  @[simp] def mapMOptionSeparatedRecordLabeled [Monad m] (f : e1 → m e2) (o : Option (Separated (RecordLabeled (Binder e1)))) : m (Option (Separated (RecordLabeled (Binder e2)))) :=
    match o with
    | none => pure none
    | some s => some <$> mapMSeparatedRecordLabeled f s
  termination_by sizeOf o
  decreasing_by all_goals (simp_all only [Option.some.sizeOf_spec, Nat.lt_add_left_iff_pos, Nat.lt_add_one])

  @[simp] def mapMSeparatedRecordLabeled [Monad m] (f : e1 → m e2) (s : Separated (RecordLabeled (Binder e1))) : m (Separated (RecordLabeled (Binder e2))) := do
    let head ← mapMRecordLabeled f s.head
    let tail ← s.tail.attach.mapM (fun ⟨⟨tok, rl⟩, _hmem⟩ => do pure (tok, ← mapMRecordLabeled f rl))
    pure { head := head, tail := tail }
  termination_by sizeOf s
  decreasing_by
    simp_wf
    obtain ⟨i, hi, h⟩ := Array.mem_iff_getElem.mp _hmem
    have : rl = (s.tail[i]).2 := by simp only [h]
    rw [this]
    exact s.sizeOf_tail_get i hi

  @[simp] def mapMRecordLabeled [Monad m] (f : e1 → m e2) (rl : RecordLabeled (Binder e1)) : m (RecordLabeled (Binder e2)) :=
    match rl with
    | .Pun n => pure (.Pun n)
    | .Field l sep v => .Field l sep <$> mapM f v
  termination_by sizeOf rl
  decreasing_by
    simp_wf
    grind only

  @[simp] def mapMWrapped [Monad m] (f : e1 → m e2) (w : Wrapped (Binder e1)) : m (Wrapped (Binder e2)) := do
    let val ← mapM f w.value
    pure { w with value := val }
  termination_by sizeOf w
  decreasing_by all_goals (simp_all only [Wrapped.sizeOf_value])
end

end Binder

structure AndToken (α : Type) where
  value : α
  token : SourceToken
  deriving Repr, BEq

namespace AndToken

@[always_inline, simp] def map (f : α → β) (a : AndToken α) : AndToken β :=
  { a with value := f a.value }

@[simp] theorem id_map (a : AndToken α) : (a.map id) = a := rfl

@[simp] theorem comp_map (f : α → β) (g : β → γ) (a : AndToken α) : (a.map (g ∘ f)) = (a.map f |>.map g) := rfl

@[simp] theorem functor_map_id : map (id : α → α) = id := by funext e; exact id_map e

@[simp] theorem functor_map_comp (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext e; exact comp_map f g e

@[always_inline, simp] def mapM [Monad m] (f : α → m β) (a : AndToken α) : m (AndToken β) := do
  let v ← f a.value
  pure { a with value := v }

end AndToken
--
@[always_inline] instance : Functor AndToken where
  map := AndToken.map

instance : LawfulFunctor AndToken where
  map_const := rfl
  id_map := AndToken.id_map
  comp_map := AndToken.comp_map

inductive AppSpineF (e expr_e : Type)
  | Type_ (token : SourceToken) (type_ : Type_ e)
  | Term (expr : expr_e)
  deriving Repr, BEq

namespace AppSpineF

@[always_inline, simp] def map_all (f : e1 → e2) (f_expr : α → β) (s : AppSpineF e1 α) : AppSpineF e2 β :=
  match s with
  | .Term e => .Term (f_expr e)
  | .Type_ t ty => .Type_ t (ty.map f)

@[simp] theorem map_all_id (s : AppSpineF e α) : s.map_all id id = s := by
  match s with
  | .Term e => simp only [map_all, id_eq]
  | .Type_ t ty => simp only [map_all, Type_.map_id]

@[simp] theorem map_all_comp (f : e1 → e2) (g : e2 → e3) (f_expr : α → β) (g_expr : β → γ) (s : AppSpineF e1 α) :
  s.map_all (g ∘ f) (g_expr ∘ f_expr) = (s.map_all f f_expr).map_all g g_expr := by
  match s with
  | .Term e => simp only [map_all, Function.comp_apply]
  | .Type_ t ty => simp only [map_all, Type_.map_comp]

@[always_inline, simp] def map_expr_e (f : α → β) (s : AppSpineF e α) : AppSpineF e β :=
  s.map_all id f

@[always_inline, simp] def map_e (f : e1 → e2) (s : AppSpineF e1 α) : AppSpineF e2 α :=
  s.map_all f id

instance : Functor (AppSpineF e) where map := map_expr_e
instance : LawfulFunctor (AppSpineF e) where
  map_const := rfl
  id_map := map_all_id
  comp_map := map_all_comp id id

@[always_inline, simp] def mapM_all [Monad m] (f : e1 → m e2) (f_expr : α → m β) (s : AppSpineF e1 α) : m (AppSpineF e2 β) :=
  match s with
  | .Term e => .Term <$> f_expr e
  | .Type_ t ty => .Type_ t <$> ty.mapM f

end AppSpineF
--
inductive RecordUpdateF (expr_e self : Type)
  | Leaf (label : Name Label) (token : SourceToken) (expr : expr_e)
  | Branch (label : Name Label) (updates : DelimitedNonEmpty self)
  deriving Repr, BEq

-- namespace RecordUpdateF

-- @[simp] theorem sizeOf_Leaf [SizeOf α] (l t expr) :
--   sizeOf (RecordUpdateF.Leaf (expr_e := α) l t expr) = 1 + sizeOf l + sizeOf t + sizeOf expr :=
--   RecordUpdateF.Leaf.sizeOf_spec l t expr

-- @[simp] theorem sizeOf_Branch [SizeOf α] (l updates) :
--   sizeOf (RecordUpdateF.Branch (expr_e := α) l updates) = 1 + sizeOf l + sizeOf updates :=
--   RecordUpdateF.Branch.sizeOf_spec l updates

-- @[inline] def map_all [SizeOf α] (f_expr : α → β) (u : RecordUpdateF α) : RecordUpdateF β :=
--   match u with
--   | .Leaf label token expr => .Leaf label token (f_expr expr)
--   | .Branch label updates  => .Branch label (updates.attach.map (fun x => x.val.map_all f_expr))
-- termination_by sizeOf u
-- decreasing_by
--   simp_wf
--   have := DelimitedNonEmpty.sizeOf_attach_elem updates x
--   omega

-- @[simp] theorem map_all_id (u : RecordUpdateF α) : map_all id u = u := by
--   match u with
--   | .Leaf label token expr => simp only [map_all, id_eq]
--   | .Branch label updates =>
--     simp only [map_all, Branch.injEq, true_and]
--     have h : (fun x : { x // x ∈ updates } => x.val.map_all id) = (fun x => x.val) := by
--       funext x; exact map_all_id x.val
--     rw [h, DelimitedNonEmpty.attach_map_val]
-- termination_by sizeOf u
-- decreasing_by
--   simp_wf
--   have := DelimitedNonEmpty.sizeOf_attach_elem updates x
--   omega

-- @[simp] theorem map_all_comp (f_expr : α → β) (g_expr : β → γ) (u : RecordUpdateF α) :
--   map_all (g_expr ∘ f_expr) u = map_all g_expr (map_all f_expr u) := by
--   match u with
--   | .Leaf label token expr => simp only [map_all, Function.comp_apply]
--   | .Branch label updates =>
--     simp only [map_all, Branch.injEq, true_and]
--     have h : (fun x : { x // x ∈ updates } => x.val.map_all (g_expr ∘ f_expr)) = (fun x => (x.val.map_all f_expr).map_all g_expr) := by
--       funext x; exact map_all_comp f_expr g_expr x.val
--     rw [h]
--     rw [DelimitedNonEmpty.attach_map]
--     rw [← DelimitedNonEmpty.comp_map]
--     rfl
-- termination_by sizeOf u
-- decreasing_by
--   simp_wf
--   have := DelimitedNonEmpty.sizeOf_attach_elem updates x
--   omega

-- @[always_inline, inline] def map_expr_e [SizeOf α] (f : α → β) (u : RecordUpdateF α) : RecordUpdateF β :=
--   u.map_all f

-- @[always_inline, inline] def map_e [SizeOf α] (_f : e1 → e2) (u : RecordUpdateF α) : RecordUpdateF α :=
--   u

-- @[simp] theorem map_expr_e_id (u : RecordUpdateF α) : map_expr_e id u = u := map_all_id u
-- @[simp] theorem map_expr_e_comp (f : α → β) (g : β → γ) (u : RecordUpdateF α) : map_expr_e (g ∘ f) u = map_expr_e g (map_expr_e f u) := map_all_comp f g u
-- @[simp] theorem map_e_id (u : RecordUpdateF α) : map_e (id : e → e) u = u := rfl
-- @[simp] theorem map_e_comp (f : e1 → e2) (g : e2 → e3) (u : RecordUpdateF α) : map_e (g ∘ f) u = map_e g (map_e f u) := rfl

-- instance : Functor RecordUpdateF where map := map_expr_e
-- instance : LawfulFunctor RecordUpdateF where
--   map_const := rfl
--   id_map := map_expr_e_id
--   comp_map := map_expr_e_comp

-- end RecordUpdateF

structure RecordAccessorF (expr_e : Type) where
  expr : expr_e
  dot : SourceToken
  path : Separated (Name Label)
  deriving Repr, BEq

namespace RecordAccessorF

@[always_inline, simp] def map (f : α → β) (a : RecordAccessorF α) : RecordAccessorF β :=
  { a with expr := f a.expr }

@[simp] theorem id_map (a : RecordAccessorF α) : (a.map id) = a := by
  cases a; aesop

@[simp] theorem comp_map (f : α → β) (g : β → γ) (a : RecordAccessorF α) : (a.map (g ∘ f)) = (a.map f |>.map g) := by
  cases a; aesop

@[simp] theorem map_id_fun : map (id : α → α) = id := by funext a; exact id_map a

@[simp] theorem map_comp_fun (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext a; exact comp_map f g a

instance : Functor RecordAccessorF where map := map
instance : LawfulFunctor RecordAccessorF where
  map_const := rfl
  id_map := id_map
  comp_map := comp_map

@[always_inline, simp] def mapM [Monad m] (f : α → m β) (a : RecordAccessorF α) : m (RecordAccessorF β) := do
  let e ← f a.expr
  pure { a with expr := e }

end RecordAccessorF

structure LambdaF (e expr_e : Type) where
  symbol : SourceToken
  binders : NonEmptyArray (Binder e)
  arrow : SourceToken
  body : expr_e
  deriving Repr, BEq

namespace LambdaF

@[always_inline, simp] def map_all (f : e1 → e2) (f_expr : α → β) (l : LambdaF e1 α) : LambdaF e2 β :=
  { symbol := l.symbol
    binders := l.binders.map (fun b => b.map f)
    arrow := l.arrow
    body := f_expr l.body
  }

@[simp] theorem map_all_id (l : LambdaF e α) : l.map_all id id = l := by
  cases l; simp only [map_all, NonEmptyArray.map, Binder.map_id, Array.map_id_fun', id_eq]

@[simp] theorem map_all_comp (f : e1 → e2) (g : e2 → e3) (f_expr : α → β) (g_expr : β → γ) (l : LambdaF e1 α) :
  l.map_all (g ∘ f) (g_expr ∘ f_expr) = (l.map_all f f_expr).map_all g g_expr := by
  cases l; simp only [map_all, NonEmptyArray.map, Binder.map_comp, Function.comp_apply,
    Array.map_map, mk.injEq, NonEmptyArray.mk.injEq, Array.map_inj_left, implies_true, and_self]

@[always_inline, simp] def map_expr_e (f : α → β) (l : LambdaF e α) : LambdaF e β :=
  l.map_all id f

@[always_inline, simp] def map_e (f : e1 → e2) (l : LambdaF e1 α) : LambdaF e2 α :=
  l.map_all f id

@[always_inline, simp] def mapM_all [Monad m] (f : e1 → m e2) (f_expr : α → m β) (l : LambdaF e1 α) : m (LambdaF e2 β) := do
  let binders ← l.binders.mapM (fun b => b.mapM f)
  let body ← f_expr l.body
  pure { symbol := l.symbol, binders := binders, arrow := l.arrow, body := body }

end LambdaF

structure IfThenElseF (expr_e : Type) where
  keyword : SourceToken
  cond : expr_e
  then_ : SourceToken
  true_ : expr_e
  else_ : SourceToken
  false_ : expr_e
  deriving Repr, BEq

namespace IfThenElseF

@[always_inline, simp] def map (f : α → β) (i : IfThenElseF α) : IfThenElseF β :=
  { i with cond := f i.cond, true_ := f i.true_, false_ := f i.false_ }

@[simp] theorem id_map (i : IfThenElseF α) : (i.map id) = i := by
  cases i; aesop

@[simp] theorem comp_map (f : α → β) (g : β → γ) (i : IfThenElseF α) : (i.map (g ∘ f)) = (i.map f |>.map g) := by
  cases i; aesop

@[simp] theorem map_id_fun : map (id : α → α) = id := by funext i; exact id_map i

@[simp] theorem map_comp_fun (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext i; exact comp_map f g i

instance : Functor IfThenElseF where map := map
instance : LawfulFunctor IfThenElseF where
  map_const := rfl
  id_map := id_map
  comp_map := comp_map

@[always_inline, simp] def mapM [Monad m] (f : α → m β) (i : IfThenElseF α) : m (IfThenElseF β) := do
  let cond ← f i.cond
  let true_ ← f i.true_
  let false_ ← f i.false_
  pure { i with cond := cond, true_ := true_, false_ := false_ }

end IfThenElseF

structure PatternGuardF (e expr_e : Type) where
  binder : Option (Binder e × SourceToken)
  expr : expr_e
  deriving Repr, BEq

namespace PatternGuardF

@[always_inline, simp] def map_all (f : e1 → e2) (f_expr : α → β) (p : PatternGuardF e1 α) : PatternGuardF e2 β :=
  { binder := p.binder.map (fun (b, t) => (b.map f, t))
    expr := f_expr p.expr
  }

@[simp] theorem map_all_id (p : PatternGuardF e α) : p.map_all id id = p := by
  match p with
  | { binder, expr } => simp only [map_all, Binder.map_id, Option.map_id_fun', id_eq]

@[simp] theorem map_all_comp (f : e1 → e2) (g : e2 → e3) (f_expr : α → β) (g_expr : β → γ) (p : PatternGuardF e1 α) :
  p.map_all (g ∘ f) (g_expr ∘ f_expr) = (p.map_all f f_expr).map_all g g_expr := by
  match p with
  | { binder, expr } =>
    simp only [map_all, Binder.map_comp, Function.comp_apply, Option.map_map, mk.injEq, and_true]
    apply congrArg (Option.map · binder); funext x; simp only [Function.comp_apply]

@[always_inline, simp] def map_expr_e (f : α → β) (p : PatternGuardF e α) : PatternGuardF e β :=
  p.map_all id f

@[always_inline, simp] def map_e (f : e1 → e2) (p : PatternGuardF e1 α) : PatternGuardF e2 α :=
  p.map_all f id

instance : Functor (PatternGuardF e) where map := map_expr_e
instance : LawfulFunctor (PatternGuardF e) where
  map_const := rfl
  id_map := map_all_id
  comp_map f g x := map_all_comp id id f g x

@[always_inline, simp] def mapM_all [Monad m] (f : e1 → m e2) (f_expr : α → m β) (p : PatternGuardF e1 α) : m (PatternGuardF e2 β) := do
  let binder ← p.binder.mapM (fun (b, t) => do pure (← b.mapM f, t))
  let expr ← f_expr p.expr
  pure { binder := binder, expr := expr }

end PatternGuardF

-- ```mermaid
-- graph TD
--     LB[LetBindingF] -->|Pattern| W[WhereF]
--     LB -->|Name| VBF[ValueBindingFieldsF]
--
--     VBF -->|guarded| G[GuardedF]
--
--     G -->|Unconditional| W
--     G -->|Guarded| GE[GuardedExprF]
--
--     GE -->|where_| W
--
--     W -->|bindings| LB
--
--     subgraph "The Mutual Cycle"
--     LB
--     VBF
--     G
--     GE
--     W
--     end
-- ```

-- 1. GuardExpr depends only on Where
structure GuardedExprF (patternGuard_e where_e : Type) where
  bar        : SourceToken
  patterns   : Separated patternGuard_e
  separator  : SourceToken
  where_     : where_e
  deriving Repr, BEq

namespace GuardedExprF

@[always_inline, simp] def map_all
  (f_patternGuard : patternGuard_e → patternGuard_e') (f_where : where_e → where_e')
  (g : GuardedExprF patternGuard_e where_e) : GuardedExprF patternGuard_e' where_e' :=
  { bar := g.bar
    patterns := g.patterns.map f_patternGuard
    separator := g.separator
    where_ := f_where g.where_
  }

@[simp] theorem map_all_id (g : GuardedExprF patternGuard_e where_e) : g.map_all id id = g := by
  match g with
  | { bar, patterns, separator, where_ } => simp only [map_all, Separated.map_id_fun, id_eq]

@[simp] theorem map_all_comp
  (f_patternGuard : patternGuard_e1 → patternGuard_e2) (g_patternGuard : patternGuard_e2 → patternGuard_e3)
  (f_where : where_e1 → where_e2) (g_where : where_e2 → where_e3)
  (ge : GuardedExprF patternGuard_e1 where_e1) :
  ge.map_all (g_patternGuard ∘ f_patternGuard) (g_where ∘ f_where) = (ge.map_all f_patternGuard f_where).map_all g_patternGuard g_where := by
  match ge with
  | { bar, patterns, separator, where_ } =>
    simp only [map_all, Separated.map_comp_fun, Function.comp_apply]

@[always_inline, simp] def mapM_all [Monad m]
  (f_patternGuard : patternGuard_e → m patternGuard_e') (f_where : where_e → m where_e')
  (g : GuardedExprF patternGuard_e where_e) : m (GuardedExprF patternGuard_e' where_e') := do
  let patterns ← g.patterns.mapM f_patternGuard
  let where_ ← f_where g.where_
  pure { bar := g.bar, patterns := patterns, separator := g.separator, where_ := where_ }

end GuardedExprF

-- 2. Guarded depends on Where and GuardExpr
inductive GuardedF (where_e guardedExpr_e : Type) where
  | Unconditional (token : SourceToken) (where_ : where_e)
  | Guarded (branches : NonEmptyArray guardedExpr_e)
  deriving Repr, BEq

namespace GuardedF

@[always_inline, simp] def map_all
  (f_where : where_e → where_e') (f_guardedExpr : guardedExpr_e → guardedExpr_e')
  (g : GuardedF where_e guardedExpr_e) : GuardedF where_e' guardedExpr_e' :=
  match g with
  | Unconditional t w => Unconditional t (f_where w)
  | Guarded b => Guarded (b.map f_guardedExpr)

@[simp] theorem map_all_id (g : GuardedF where_e guardedExpr_e) : g.map_all id id = g := by
  match g with
  | Unconditional t w => simp only [map_all, id_eq]
  | Guarded b => simp only [map_all, NonEmptyArray.map, id_eq, Array.map_id_fun]

@[simp] theorem map_all_comp
  (f_where : where_e1 → where_e2) (g_where : where_e2 → where_e3)
  (f_guardedExpr : guardedExpr_e1 → guardedExpr_e2) (g_guardedExpr : guardedExpr_e2 → guardedExpr_e3)
  (gr : GuardedF where_e1 guardedExpr_e1) :
  gr.map_all (g_where ∘ f_where) (g_guardedExpr ∘ f_guardedExpr) = (gr.map_all f_where f_guardedExpr).map_all g_where g_guardedExpr := by
  match gr with
  | Unconditional t w => simp only [map_all, Function.comp_apply]
  | Guarded b => simp only [map_all, NonEmptyArray.map, Function.comp_apply, Array.map_map]

@[always_inline, simp] def mapM_all [Monad m]
  (f_where : where_e → m where_e') (f_guardedExpr : guardedExpr_e → m guardedExpr_e')
  (g : GuardedF where_e guardedExpr_e) : m (GuardedF where_e' guardedExpr_e') :=
  match g with
  | Unconditional t w => Unconditional t <$> f_where w
  | Guarded b => Guarded <$> b.mapM f_guardedExpr

end GuardedF

-- 3. ValueBindingFields depends on Guarded
structure ValueBindingFieldsF (e guardedExpr_e : Type) where
  name    : Name Ident
  binders : Array (Binder e)
  guarded : guardedExpr_e
  deriving Repr, BEq

namespace ValueBindingFieldsF

@[always_inline, simp] def map_all
  (f : e → e') (f_guardedExpr : guardedExpr_e → guardedExpr_e')
  (v : ValueBindingFieldsF e guardedExpr_e) : ValueBindingFieldsF e' guardedExpr_e' :=
  { name := v.name
    binders := v.binders.map (fun b => b.map f)
    guarded := f_guardedExpr v.guarded
  }

@[simp] theorem map_all_id (v : ValueBindingFieldsF e guardedExpr_e) : v.map_all id id = v := by
  match v with
  | { name, binders, guarded } => simp only [map_all, Binder.map_id, Array.map_id_fun', id_eq]

@[simp] theorem map_all_comp
  (f : e1 → e2) (g : e2 → e3) (f_guardedExpr : guardedExpr_e1 → guardedExpr_e2) (g_guardedExpr : guardedExpr_e2 → guardedExpr_e3)
  (v : ValueBindingFieldsF e1 guardedExpr_e1) :
  v.map_all (g ∘ f) (g_guardedExpr ∘ f_guardedExpr) = (v.map_all f f_guardedExpr).map_all g g_guardedExpr := by
  match v with
  | { name, binders, guarded } => simp only [map_all, Binder.map_comp, Function.comp_apply,
    Array.map_map, mk.injEq, Array.map_inj_left, implies_true, and_self]

@[always_inline, simp] def mapM_all [Monad m]
  (f : e → m e') (f_guardedExpr : guardedExpr_e → m guardedExpr_e')
  (v : ValueBindingFieldsF e guardedExpr_e) : m (ValueBindingFieldsF e' guardedExpr_e') := do
  let binders ← v.binders.mapM (fun b => b.mapM f)
  let guarded ← f_guardedExpr v.guarded
  pure { name := v.name, binders := binders, guarded := guarded }
end ValueBindingFieldsF

-- 4. Where depends on the list of Bindings
structure WhereF (expr_e letBinding_e : Type) where
  expr     : expr_e
  bindings : Option (SourceToken × NonEmptyArray letBinding_e)
  deriving Repr, BEq

namespace WhereF

@[always_inline, simp] def map_all
  (f_expr : expr_e → expr_e') (f_letBinding : letBinding_e → letBinding_e')
  (w : WhereF expr_e letBinding_e) : WhereF expr_e' letBinding_e' :=
  { expr := f_expr w.expr
    bindings := w.bindings.map (fun (t, b) => (t, b.map f_letBinding))
  }

@[simp] theorem map_all_id (w : WhereF expr_e letBinding_e) : w.map_all id id = w := by
  match w with
  | { expr, bindings } => simp only [map_all, id_eq, NonEmptyArray.map, Array.map_id_fun,
    Option.map_id_fun']

@[simp] theorem map_all_comp
  (f_expr : expr_e1 → expr_e2) (g_expr : expr_e2 → expr_e3)
  (f_letBinding : letBinding_e1 → letBinding_e2) (g_letBinding : letBinding_e2 → letBinding_e3)
  (w : WhereF expr_e1 letBinding_e1) :
  w.map_all (g_expr ∘ f_expr) (g_letBinding ∘ f_letBinding) = (w.map_all f_expr f_letBinding).map_all g_expr g_letBinding := by
  match w with
  | { expr, bindings } =>
    simp_all only [map_all, Function.comp_apply, NonEmptyArray.map, Option.map_map, mk.injEq, true_and]
    ext a : 1
    simp_all only [Option.map_eq_some_iff, Prod.exists, Function.comp_apply, Array.map_map]

@[always_inline, simp] def mapM_all [Monad m]
  (f_expr : expr_e → m expr_e') (f_letBinding : letBinding_e → m letBinding_e')
  (w : WhereF expr_e letBinding_e) : m (WhereF expr_e' letBinding_e') := do
  let expr ← f_expr w.expr
  let bindings ← w.bindings.mapM (fun (t, b) => do pure (t, ← b.mapM f_letBinding))
  pure { expr := expr, bindings := bindings }

end WhereF

-- 5. LetBinding is the "Sum" of the complex
inductive LetBindingF (e valueBindingFields_e where_e : Type) where
  | Signature (labeled : Labeled (Name Ident) (Type_ e))
  | Name (fields : valueBindingFields_e)
  | Pattern (binder : Binder e) (token : SourceToken) (where_ : where_e)
  | Error (data : e)
  deriving Repr, BEq

namespace LetBindingF

@[always_inline, simp] def map_all
  (f : e → e') (f_valueBindingFields : valueBindingFields_e → valueBindingFields_e') (f_where : where_e → where_e')
  (b : LetBindingF e valueBindingFields_e where_e) : LetBindingF e' valueBindingFields_e' where_e' :=
  match b with
  | Signature l => Signature (l.map_value (fun t => t.map f))
  | Name fields => Name (f_valueBindingFields fields)
  | Pattern b' t w => Pattern (b'.map f) t (f_where w)
  | Error d => Error (f d)

@[simp] theorem map_all_id (b : LetBindingF e valueBindingFields_e where_e) : b.map_all id id id = b := by
  match b with
  | Signature l =>
    simp_all only [map_all, Signature.injEq]
    simp_all only [Type_.map_id]
    rfl
  | Name fields => simp only [map_all, id_eq]
  | Pattern b' t w => simp only [map_all, Binder.map_id, id_eq]
  | Error d => simp only [map_all, id_eq]

@[simp] theorem map_all_comp
  (f : e1 → e2) (g : e2 → e3)
  (f_valueBindingFields : valueBindingFields_e1 → valueBindingFields_e2) (g_valueBindingFields : valueBindingFields_e2 → valueBindingFields_e3)
  (f_where : where_e1 → where_e2) (g_where : where_e2 → where_e3)
  (lb : LetBindingF e1 valueBindingFields_e1 where_e1) :
  lb.map_all (g ∘ f) (g_valueBindingFields ∘ f_valueBindingFields) (g_where ∘ f_where) = (lb.map_all f f_valueBindingFields f_where).map_all g g_valueBindingFields g_where := by
  match lb with
  | Signature l => simp only [map_all, Type_.map_comp]; exact congrArg Signature (Labeled.map_value_comp _ _ _)
  | Name fields => simp only [map_all, Function.comp_apply]
  | Pattern b' t w => simp only [map_all, Binder.map_comp, Function.comp_apply]
  | Error d => simp only [map_all, Function.comp_apply]

@[always_inline, simp] def mapM_all [Monad m]
  (f : e → m e') (f_valueBindingFields : valueBindingFields_e → m valueBindingFields_e') (f_where : where_e → m where_e')
  (b : LetBindingF e valueBindingFields_e where_e) : m (LetBindingF e' valueBindingFields_e' where_e') :=
  match b with
  | Signature l => Signature <$> l.mapM_value (fun t => t.mapM f)
  | Name fields => Name <$> f_valueBindingFields fields
  | Pattern b' t w => Pattern <$> b'.mapM f <*> pure t <*> f_where w
  | Error d => Error <$> f d

end LetBindingF

structure CaseOfF (e expr_e guardedRecursive_e : Type) where
  keyword : SourceToken
  head : Separated expr_e
  of : SourceToken
  branches : NonEmptyArray (Separated (Binder e) × guardedRecursive_e)
  deriving Repr, BEq

namespace CaseOfF

@[always_inline, simp] def map_all
  (f : e → e') (f_expr : expr_e → expr_e') (f_guardedRecursive : guardedRecursive_e → guardedRecursive_e')
  (c : CaseOfF e expr_e guardedRecursive_e) : CaseOfF e' expr_e' guardedRecursive_e' :=
  { keyword := c.keyword
    head := c.head.map f_expr
    of := c.of
    branches := c.branches.map (fun (b, g) => (b.map (fun b' => b'.map f), f_guardedRecursive g))
  }

@[simp] theorem map_all_id (c : CaseOfF e expr_e guardedRecursive_e) : c.map_all id id id = c := by
  match c with
  | { keyword, head, of, branches } => simp only [map_all, Separated.map, id_eq, Array.map_id_fun',
    NonEmptyArray.map, Binder.map_id]

@[simp] theorem map_all_comp
  (f : e1 → e2) (g : e2 → e3) (f_expr : expr_e1 → expr_e2) (g_expr : expr_e2 → expr_e3)
  (f_guardedRecursive : guardedRecursive_e1 → guardedRecursive_e2) (g_guardedRecursive : guardedRecursive_e2 → guardedRecursive_e3)
  (c : CaseOfF e1 expr_e1 guardedRecursive_e1) :
  c.map_all (g ∘ f) (g_expr ∘ f_expr) (g_guardedRecursive ∘ f_guardedRecursive) = (c.map_all f f_expr f_guardedRecursive).map_all g g_expr g_guardedRecursive := by
  match c with
  | { keyword, head, of, branches } => simp only [map_all, Separated.map, Function.comp_apply,
    NonEmptyArray.map, Binder.map_comp, Array.map_map, mk.injEq, Separated.mk.injEq,
    Array.map_inj_left, implies_true, and_self, NonEmptyArray.mk.injEq, Prod.mk.injEq]

@[always_inline, simp] def mapM_all [Monad m]
  (f : e → m e') (f_expr : expr_e → m expr_e') (f_guardedRecursive : guardedRecursive_e → m guardedRecursive_e')
  (c : CaseOfF e expr_e guardedRecursive_e) : m (CaseOfF e' expr_e' guardedRecursive_e') := do
  let head ← c.head.mapM f_expr
  let branches ← c.branches.mapM (fun (b, g) => do pure (← b.mapM (fun b' => b'.mapM f), ← f_guardedRecursive g))
  pure { keyword := c.keyword, head := head, of := c.of, branches := branches }
end CaseOfF

structure LetInF (expr_e letBindingRecursive_e : Type) where
  keyword : SourceToken
  bindings : NonEmptyArray letBindingRecursive_e
  in_ : SourceToken
  body : expr_e
  deriving Repr, BEq

namespace LetInF

@[always_inline, simp] def map_all
  (f_expr : expr_e → expr_e') (f_letBindingRecursive : letBindingRecursive_e → letBindingRecursive_e')
  (l : LetInF expr_e letBindingRecursive_e) : LetInF expr_e' letBindingRecursive_e' :=
  { keyword := l.keyword
    bindings := l.bindings.map f_letBindingRecursive
    in_ := l.in_
    body := f_expr l.body
  }

@[simp] theorem map_all_id (l : LetInF expr_e letBindingRecursive_e) : l.map_all id id = l := by
  match l with
  | { keyword, bindings, in_, body } => simp only [map_all, NonEmptyArray.map, id_eq,
    Array.map_id_fun]

@[simp] theorem map_all_comp
  (f_expr : expr_e1 → expr_e2) (g_expr : expr_e2 → expr_e3)
  (f_letBindingRecursive : letBindingRecursive_e1 → letBindingRecursive_e2) (g_letBindingRecursive : letBindingRecursive_e2 → letBindingRecursive_e3)
  (l : LetInF expr_e1 letBindingRecursive_e1) :
  l.map_all (g_expr ∘ f_expr) (g_letBindingRecursive ∘ f_letBindingRecursive) = (l.map_all f_expr f_letBindingRecursive).map_all g_expr g_letBindingRecursive := by
  match l with
  | { keyword, bindings, in_, body } => simp only [map_all, NonEmptyArray.map, Function.comp_apply,
    Array.map_map]

@[always_inline, simp] def mapM_all [Monad m]
  (f_expr : expr_e → m expr_e') (f_letBindingRecursive : letBindingRecursive_e → m letBindingRecursive_e')
  (l : LetInF expr_e letBindingRecursive_e) : m (LetInF expr_e' letBindingRecursive_e') := do
  let bindings ← l.bindings.mapM f_letBindingRecursive
  let body ← f_expr l.body
  pure { keyword := l.keyword, bindings := bindings, in_ := l.in_, body := body }

end LetInF

inductive DoStatementF (e expr_e letBindingRecursive_e : Type)
  | Let (token : SourceToken) (bindings : NonEmptyArray letBindingRecursive_e)
  | Discard (expr : expr_e)
  | Bind (binder : Binder e) (token : SourceToken) (expr : expr_e)
  | Error (data : e)
  deriving Repr, BEq

namespace DoStatementF

@[always_inline, simp] def map_all
  (f : e → e') (f_expr : expr_e → expr_e') (f_letBindingRecursive : letBindingRecursive_e → letBindingRecursive_e')
  (s : DoStatementF e expr_e letBindingRecursive_e) : DoStatementF e' expr_e' letBindingRecursive_e' :=
  match s with
  | Let t b => Let t (b.map f_letBindingRecursive)
  | Discard expr => Discard (f_expr expr)
  | Bind b t expr => Bind (b.map f) t (f_expr expr)
  | Error d => Error (f d)

@[simp] theorem map_all_id (s : DoStatementF e expr_e letBindingRecursive_e) : s.map_all id id id = s := by
  match s with
  | Let t b => simp only [map_all, NonEmptyArray.map, id_eq, Array.map_id_fun]
  | Discard expr => simp only [map_all, id_eq]
  | Bind b' t expr => simp only [map_all, Binder.map_id, id_eq]
  | Error d => simp only [map_all, id_eq]

@[simp] theorem map_all_comp
  (f : e1 → e2) (g : e2 → e3) (f_expr : expr_e1 → expr_e2) (g_expr : expr_e2 → expr_e3)
  (f_letBindingRecursive : letBindingRecursive_e1 → letBindingRecursive_e2) (g_letBindingRecursive : letBindingRecursive_e2 → letBindingRecursive_e3)
  (s : DoStatementF e1 expr_e1 letBindingRecursive_e1) :
  s.map_all (g ∘ f) (g_expr ∘ f_expr) (g_letBindingRecursive ∘ f_letBindingRecursive) = (s.map_all f f_expr f_letBindingRecursive).map_all g g_expr g_letBindingRecursive := by
  match s with
  | Let t b => simp only [map_all, NonEmptyArray.map, Function.comp_apply, Array.map_map]
  | Discard expr => simp only [map_all, Function.comp_apply]
  | Bind b' t expr => simp only [map_all, Binder.map_comp, Function.comp_apply]
  | Error d => simp only [map_all, Function.comp_apply]

@[always_inline, simp] def mapM_all [Monad m]
  (f : e → m e') (f_expr : expr_e → m expr_e') (f_letBindingRecursive : letBindingRecursive_e → m letBindingRecursive_e')
  (s : DoStatementF e expr_e letBindingRecursive_e) : m (DoStatementF e' expr_e' letBindingRecursive_e') :=
  match s with
  | Let t b => Let t <$> b.mapM f_letBindingRecursive
  | Discard expr => Discard <$> f_expr expr
  | Bind b t expr => Bind <$> b.mapM f <*> pure t <*> f_expr expr
  | Error d => Error <$> f d
end DoStatementF

structure DoBlockF (doStatement_e : Type) where
  keyword : SourceToken
  statements : NonEmptyArray doStatement_e
  deriving Repr, BEq

namespace DoBlockF

@[always_inline, simp] def map_all
  (f_doStatement : doStatement_e → doStatement_e')
  (b : DoBlockF doStatement_e) : DoBlockF doStatement_e' :=
  { keyword := b.keyword
    statements := b.statements.map f_doStatement
  }

@[simp] theorem map_all_id (b : DoBlockF doStatement_e) : b.map_all id = b := by
  match b with
  | { keyword, statements } => simp only [map_all, NonEmptyArray.map, id_eq, Array.map_id_fun]

@[simp] theorem map_all_comp
  (f_doStatement : doStatement_e1 → doStatement_e2) (g_doStatement : doStatement_e2 → doStatement_e3)
  (b : DoBlockF doStatement_e1) :
  b.map_all (g_doStatement ∘ f_doStatement) = (b.map_all f_doStatement).map_all g_doStatement := by
  match b with
  | { keyword, statements } => simp only [map_all, NonEmptyArray.map, Function.comp_apply,
    Array.map_map]

@[always_inline, simp] def mapM_all [Monad m]
  (f_doStatement : doStatement_e → m doStatement_e')
  (b : DoBlockF doStatement_e) : m (DoBlockF doStatement_e') := do
  let statements ← b.statements.mapM f_doStatement
  pure { keyword := b.keyword, statements := statements }
end DoBlockF

structure AdoBlockF (expr_e doStatement_e : Type) where
  keyword : SourceToken
  statements : Array doStatement_e
  in_ : SourceToken
  result : expr_e
  deriving Repr, BEq

namespace AdoBlockF

@[always_inline, simp] def map_all
  (f_expr : expr_e → expr_e') (f_doStatement : doStatement_e → doStatement_e')
  (b : AdoBlockF expr_e doStatement_e) : AdoBlockF expr_e' doStatement_e' :=
  { keyword := b.keyword
    statements := b.statements.map f_doStatement
    in_ := b.in_
    result := f_expr b.result
  }

@[simp] theorem map_all_id (b : AdoBlockF expr_e doStatement_e) : b.map_all id id = b := by
  match b with
  | { keyword, statements, in_, result } => simp only [map_all, Array.map_id_fun, id_eq]

@[simp] theorem map_all_comp
  (f_expr : expr_e1 → expr_e2) (g_expr : expr_e2 → expr_e3)
  (f_doStatement : doStatement_e1 → doStatement_e2) (g_doStatement : doStatement_e2 → doStatement_e3)
  (b : AdoBlockF expr_e1 doStatement_e1) :
  b.map_all (g_expr ∘ f_expr) (g_doStatement ∘ f_doStatement) = (b.map_all f_expr f_doStatement).map_all g_expr g_doStatement := by
  match b with
  | { keyword, statements, in_, result } => simp only [map_all, Function.comp_apply, Array.map_map]

@[always_inline, simp] def mapM_all [Monad m]
  (f_expr : expr_e → m expr_e') (f_doStatement : doStatement_e → m doStatement_e')
  (b : AdoBlockF expr_e doStatement_e) : m (AdoBlockF expr_e' doStatement_e') := do
  let statements ← b.statements.mapM f_doStatement
  let result ← f_expr b.result
  pure { keyword := b.keyword, statements := statements, in_ := b.in_, result := result }
end AdoBlockF

inductive ExprF (e expr_e doBlock adoBlock guardedRecursive_e letBindingRecursive_e recordAccessor_e recordUpdate_e appSpine_e lambda_e ifThenElse_e caseOf_e letIn_e : Type)
  | Hole (name : Name Ident)
  | Section (token : SourceToken)
  | Ident (name : QualifiedName Ident)
  | Constructor (name : QualifiedName Proper)
  | Boolean (token : SourceToken) (val : Bool)
  | Char (token : SourceToken) (val : Char)
  | String (token : SourceToken) (val : String)
  | Int (token : SourceToken) (val : IntValue)
  | Number (token : SourceToken) (val : Float)
  | Array (items : Delimited expr_e)
  | Record (fields : Delimited (RecordLabeled expr_e))
  | Parens (wrapped : Wrapped expr_e)
  | Typed (expr : expr_e) (token : SourceToken) (type_ : Type_ e)
  | Infix (head : expr_e) (tail : NonEmptyArray (Wrapped expr_e × expr_e))
  | Op (head : expr_e) (ops : NonEmptyArray (QualifiedName Operator × expr_e))
  | OpName (name : QualifiedName Operator)
  | Negate (token : SourceToken) (expr : expr_e)
  | RecordAccessor (data : recordAccessor_e)
  | RecordUpdate (expr : expr_e) (updates : DelimitedNonEmpty recordUpdate_e)
  | App (fn : expr_e) (args : NonEmptyArray appSpine_e)
  | Lambda (data : lambda_e)
  | If (data : ifThenElse_e)
  | Case (data : caseOf_e)
  | Let (data : letIn_e)
  | Do (data : doBlock)
  | Ado (data : adoBlock)
  | Error (data : e)
  deriving Repr, BEq

namespace ExprF

set_option linter.unusedVariables false in
@[always_inline, simp] def map_all
  (f : e → e')
  (f_expr : expr_e → expr_e')
  (f_doBlock : doBlock → doBlock')
  (f_adoBlock : adoBlock → adoBlock')
  (f_guardedRecursive : guardedRecursive_e → guardedRecursive_e')
  (f_letBindingRecursive : letBindingRecursive_e → letBindingRecursive_e')
  (f_recordAccessor : recordAccessor_e → recordAccessor_e')
  (f_recordUpdate : recordUpdate_e → recordUpdate_e')
  (f_appSpine : appSpine_e → appSpine_e')
  (f_lambda : lambda_e → lambda_e')
  (f_ifThenElse : ifThenElse_e → ifThenElse_e')
  (f_caseOf : caseOf_e → caseOf_e')
  (f_letIn : letIn_e → letIn_e')
  (expr : ExprF e expr_e doBlock adoBlock guardedRecursive_e letBindingRecursive_e recordAccessor_e recordUpdate_e appSpine_e lambda_e ifThenElse_e caseOf_e letIn_e) : ExprF e' expr_e' doBlock' adoBlock' guardedRecursive_e' letBindingRecursive_e' recordAccessor_e' recordUpdate_e' appSpine_e' lambda_e' ifThenElse_e' caseOf_e' letIn_e' :=
  match expr with
  | Hole n => Hole n
  | Section t => Section t
  | Ident n => Ident n
  | Constructor n => Constructor n
  | Boolean t v => Boolean t v
  | Char t v => Char t v
  | String t v => String t v
  | Int t v => Int t v
  | Number t v => Number t v
  | Array items => Array (items.map f_expr)
  | Record fields => Record (fields.map (fun r => r.map f_expr))
  | Parens wrapped => Parens (wrapped.map f_expr)
  | Typed e' t ty => Typed (f_expr e') t (ty.map f)
  | Infix h t => Infix (f_expr h) (t.map (fun (w, e') => (w.map f_expr, f_expr e')))
  | Op h o => Op (f_expr h) (o.map (fun (n, e') => (n, f_expr e')))
  | OpName n => OpName n
  | Negate t e' => Negate t (f_expr e')
  | RecordAccessor data => RecordAccessor (f_recordAccessor data)
  | RecordUpdate e' updates => RecordUpdate (f_expr e') (updates.map f_recordUpdate)
  | App fn args => App (f_expr fn) (args.map f_appSpine)
  | Lambda data => Lambda (f_lambda data)
  | If data => If (f_ifThenElse data)
  | Case data => Case (f_caseOf data)
  | Let data => Let (f_letIn data)
  | Do data => Do (f_doBlock data)
  | Ado data => Ado (f_adoBlock data)
  | Error d => Error (f d)

@[simp] theorem map_all_id
  (expr : ExprF e expr_e doBlock adoBlock guardedRecursive_e letBindingRecursive_e recordAccessor_e recordUpdate_e appSpine_e lambda_e ifThenElse_e caseOf_e letIn_e) :
  expr.map_all id id id id id id id id id id id id id = expr := by
  match expr with
  | Hole n => simp only [map_all]
  | Section t => simp only [map_all]
  | Ident n => simp only [map_all]
  | Constructor n => simp only [map_all]
  | Boolean t v => simp only [map_all]
  | Char t v => simp only [map_all]
  | String t v => simp only [map_all]
  | Int t v => simp only [map_all]
  | Number t v => simp only [map_all]
  | Array items => simp only [map_all, Delimited.map, Separated.map_id_fun, id_map]
  | Record fields =>
    simp only [map_all]
    have : (fun (r : RecordLabeled expr_e) => RecordLabeled.map (id : expr_e → expr_e) r) = id := by funext r; exact RecordLabeled.id_map r
    simp only [this, Delimited.id_map]
  | Parens wrapped => simp only [map_all, Wrapped.map, id_eq]
  | Typed e' t ty => simp only [map_all, id_eq, Type_.map_id]
  | Infix h t =>
    simp only [map_all, id_eq, NonEmptyArray.map, Infix.injEq, true_and]
    simp_all only [Wrapped.map, id_eq, Array.map_id_fun']
  | Op h o => simp only [map_all, id_eq, NonEmptyArray.map, Array.map_id_fun']
  | OpName n => simp only [map_all]
  | Negate t e' => simp only [map_all, id_eq]
  | RecordAccessor data => simp only [map_all, id_eq]
  | RecordUpdate e' updates => simp only [map_all, id_eq, DelimitedNonEmpty.id_map]
  | App fn args => simp_all only [map_all, id_eq, NonEmptyArray.map, Array.map_id_fun]
  | Lambda data => simp only [map_all, id_eq]
  | If data => simp only [map_all, id_eq]
  | Case data => simp only [map_all, id_eq]
  | Let data => simp only [map_all, id_eq]
  | Do data => simp only [map_all, id_eq]
  | Ado data => simp only [map_all, id_eq]
  | Error d => simp only [map_all, id_eq]

@[simp] theorem map_all_comp
  (f : e1 → e2) (g : e2 → e3) (f_expr : expr_e1 → expr_e2) (g_expr : expr_e2 → expr_e3)
  (f_doBlock : doBlock1 → doBlock2) (g_doBlock : doBlock2 → doBlock3)
  (f_adoBlock : adoBlock1 → adoBlock2) (g_adoBlock : adoBlock2 → adoBlock3)
  (f_guardedRecursive : guardedRecursive_e1 → guardedRecursive_e2) (g_guardedRecursive : guardedRecursive_e2 → guardedRecursive_e3)
  (f_letBindingRecursive : letBindingRecursive_e1 → letBindingRecursive_e2) (g_letBindingRecursive : letBindingRecursive_e2 → letBindingRecursive_e3)
  (f_recordAccessor : recordAccessor_e1 → recordAccessor_e2) (g_recordAccessor : recordAccessor_e2 → recordAccessor_e3)
  (f_recordUpdate : recordUpdate_e1 → recordUpdate_e2) (g_recordUpdate : recordUpdate_e2 → recordUpdate_e3)
  (f_appSpine : appSpine_e1 → appSpine_e2) (g_appSpine : appSpine_e2 → appSpine_e3)
  (f_lambda : lambda_e1 → lambda_e2) (g_lambda : lambda_e2 → lambda_e3)
  (f_ifThenElse : ifThenElse_e1 → ifThenElse_e2) (g_ifThenElse : ifThenElse_e2 → ifThenElse_e3)
  (f_caseOf : caseOf_e1 → caseOf_e2) (g_caseOf : caseOf_e2 → caseOf_e3)
  (f_letIn : letIn_e1 → letIn_e2) (g_letIn : letIn_e2 → letIn_e3)
  (expr : ExprF e1 expr_e1 doBlock1 adoBlock1 guardedRecursive_e1 letBindingRecursive_e1 recordAccessor_e1 recordUpdate_e1 appSpine_e1 lambda_e1 ifThenElse_e1 caseOf_e1 letIn_e1) :
  expr.map_all (g ∘ f) (g_expr ∘ f_expr) (g_doBlock ∘ f_doBlock) (g_adoBlock ∘ f_adoBlock) (g_guardedRecursive ∘ f_guardedRecursive) (g_letBindingRecursive ∘ f_letBindingRecursive) (g_recordAccessor ∘ f_recordAccessor) (g_recordUpdate ∘ f_recordUpdate) (g_appSpine ∘ f_appSpine) (g_lambda ∘ f_lambda) (g_ifThenElse ∘ f_ifThenElse) (g_caseOf ∘ f_caseOf) (g_letIn ∘ f_letIn) =
  (expr.map_all f f_expr f_doBlock f_adoBlock f_guardedRecursive f_letBindingRecursive f_recordAccessor f_recordUpdate f_appSpine f_lambda f_ifThenElse f_caseOf f_letIn).map_all g g_expr g_doBlock g_adoBlock g_guardedRecursive g_letBindingRecursive g_recordAccessor g_recordUpdate g_appSpine g_lambda g_ifThenElse g_caseOf g_letIn := by
  match expr with
  | Hole n => simp only [map_all]
  | Section t => simp only [map_all]
  | Ident n => simp only [map_all]
  | Constructor n => simp only [map_all]
  | Boolean t v => simp only [map_all]
  | Char t v => simp only [map_all]
  | String t v => simp only [map_all]
  | Int t v => simp only [map_all]
  | Number t v => simp only [map_all]
  | Array items => simp only [map_all, Delimited.map, Separated.map_comp_fun, comp_map,
    Option.map_eq_map, Option.map_map]
  | Record fields =>
    simp only [map_all, Delimited.map, RecordLabeled.map, Function.comp_apply,
    Option.map_eq_map, Option.map_map, Record.injEq, Delimited.mk.injEq, Wrapped.mk.injEq, and_true,
    true_and]
    ext a : 1
    simp_all only [Option.map_eq_some_iff, Separated.map, Function.comp_apply, Array.map_map]
    apply Iff.intro
    · intro a_1
      obtain ⟨w, h⟩ := a_1
      obtain ⟨left, right⟩ := h
      subst right
      simp_all only [Option.some.injEq, Separated.mk.injEq, exists_eq_left', Array.map_inj_left, Function.comp_apply,
        Prod.mk.injEq, true_and, Prod.forall]
      split
      next r n heq =>
        split
        next r_1 n_1 heq_1 =>
          simp_all only [RecordLabeled.Pun.injEq, true_and]
          intro a b a_1
          subst heq
          split
          next r_2 n heq =>
            split
            next r_3 n_2 => simp_all only [RecordLabeled.Pun.injEq]
            next r_3 l sep v => simp_all only [reduceCtorEq]
          next r_2 l sep v heq =>
            split
            next r_3 n => simp_all only [reduceCtorEq]
            next r_3 l_1 sep_1 v_1 => simp_all only [RecordLabeled.Field.injEq]
        next r_1 l sep v heq_1 => simp_all only [reduceCtorEq]
      next r l sep v heq =>
        split
        next r_1 n heq_1 => simp_all only [reduceCtorEq]
        next r_1 l_1 sep_1 v_1 heq_1 =>
          simp_all only [RecordLabeled.Field.injEq, true_and]
          intro a b a_1
          obtain ⟨left_1, right⟩ := heq
          obtain ⟨left_2, right⟩ := right
          subst left_1 left_2 right
          split
          next r_2 n heq =>
            split
            next r_3 n_1 => simp_all only [RecordLabeled.Pun.injEq]
            next r_3 l sep v => simp_all only [reduceCtorEq]
          next r_2 l sep v heq =>
            split
            next r_3 n => simp_all only [reduceCtorEq]
            next r_3 l_2 sep_2 v_2 => simp_all only [RecordLabeled.Field.injEq]
    · intro a_1
      obtain ⟨w, h⟩ := a_1
      obtain ⟨left, right⟩ := h
      subst right
      simp_all only [Option.some.injEq, Separated.mk.injEq, exists_eq_left', Array.map_inj_left, Function.comp_apply,
        Prod.mk.injEq, true_and, Prod.forall]
      split
      next r n heq =>
        simp_all only [true_and]
        intro a b a_1
        split
        next r_1 n_1 => simp_all only
        next r_1 l sep v => simp_all only
      next r l sep v heq =>
        simp_all only [true_and]
        intro a b a_1
        split
        next r_1 n => simp_all only
        next r_1 l_1 sep_1 v_1 => simp_all only
  | Parens wrapped => simp only [map_all, Wrapped.map, Function.comp_apply]
  | Typed e' t ty => simp only [map_all, Function.comp_apply, Type_.map_comp]
  | Infix h t => simp only [map_all, Function.comp_apply, NonEmptyArray.map,
    Array.map_map, Infix.injEq, NonEmptyArray.mk.injEq, Array.map_inj_left, implies_true, and_self,
    Wrapped.comp_map]
  | Op h o => simp only [map_all, Function.comp_apply, NonEmptyArray.map, Array.map_map, Op.injEq,
    NonEmptyArray.mk.injEq, Array.map_inj_left, implies_true, and_self]
  | OpName n => simp only [map_all]
  | Negate t e' => simp only [map_all, Function.comp_apply]
  | RecordAccessor data => simp only [map_all, Function.comp_apply]
  | RecordUpdate e' updates => simp only [map_all, Function.comp_apply, DelimitedNonEmpty.comp_map]
  | App fn args => simp only [map_all, Function.comp_apply, NonEmptyArray.map, Array.map_map]
  | Lambda data => simp only [map_all, Function.comp_apply]
  | If data => simp only [map_all, Function.comp_apply]
  | Case data => simp only [map_all, Function.comp_apply]
  | Let data => simp only [map_all, Function.comp_apply]
  | Do data => simp only [map_all, Function.comp_apply]
  | Ado data => simp only [map_all, Function.comp_apply]
  | Error d => simp only [map_all, Function.comp_apply]

@[always_inline, simp] def mapM_all [Monad m]
  (f : e → m e')
  (f_expr : expr_e → m expr_e')
  (f_doBlock : doBlock → m doBlock')
  (f_adoBlock : adoBlock → m adoBlock')
  (f_recordAccessor : recordAccessor_e → m recordAccessor_e')
  (f_recordUpdate : recordUpdate_e → m recordUpdate_e')
  (f_appSpine : appSpine_e → m appSpine_e')
  (f_lambda : lambda_e → m lambda_e')
  (f_ifThenElse : ifThenElse_e → m ifThenElse_e')
  (f_caseOf : caseOf_e → m caseOf_e')
  (f_letIn : letIn_e → m letIn_e')
  (expr : ExprF e expr_e doBlock adoBlock guardedRecursive_e letBindingRecursive_e recordAccessor_e recordUpdate_e appSpine_e lambda_e ifThenElse_e caseOf_e letIn_e) : m (ExprF e' expr_e' doBlock' adoBlock' guardedRecursive_e' letBindingRecursive_e' recordAccessor_e' recordUpdate_e' appSpine_e' lambda_e' ifThenElse_e' caseOf_e' letIn_e') :=
  match expr with
  | Hole n => pure (Hole n)
  | Section t => pure (Section t)
  | Ident n => pure (Ident n)
  | Constructor n => pure (Constructor n)
  | Boolean t v => pure (Boolean t v)
  | Char t v => pure (Char t v)
  | String t v => pure (String t v)
  | Int t v => pure (Int t v)
  | Number t v => pure (Number t v)
  | Array items => Array <$> items.mapM f_expr
  | Record fields => Record <$> fields.mapM (fun r => r.mapM f_expr)
  | Parens wrapped => Parens <$> wrapped.mapM f_expr
  | Typed e' t ty => Typed <$> f_expr e' <*> pure t <*> ty.mapM f
  | Infix h t => Infix <$> f_expr h <*> t.mapM (fun (w, e') => do pure (← w.mapM f_expr, ← f_expr e'))
  | Op h o => Op <$> f_expr h <*> o.mapM (fun (n, e') => do pure (n, ← f_expr e'))
  | OpName n => pure (OpName n)
  | Negate t e' => Negate t <$> f_expr e'
  | RecordAccessor data => RecordAccessor <$> f_recordAccessor data
  | RecordUpdate e' updates => RecordUpdate <$> f_expr e' <*> updates.mapM f_recordUpdate
  | App fn args => App <$> f_expr fn <*> args.mapM f_appSpine
  | Lambda data => Lambda <$> f_lambda data
  | If data => If <$> f_ifThenElse data
  | Case data => Case <$> f_caseOf data
  | Let data => Let <$> f_letIn data
  | Do data => Do <$> f_doBlock data
  | Ado data => Ado <$> f_adoBlock data
  | Error d => Error <$> f d

end ExprF

inductive Foreign (e : Type)
  | Value (labeled : Labeled (Name Ident) (Type_ e))
  | Data (keyword : SourceToken) (labeled : Labeled (Name Proper) (Type_ e))
  | Kind (keyword : SourceToken) (name : Name Proper)
  deriving Repr, BEq

namespace Foreign

@[always_inline, simp] def map (f : α → β) (o : Foreign α) : Foreign β :=
  match o with
  | .Value l => .Value (Functor.map (Functor.map f) l)
  | .Data k l => .Data k (Functor.map (Functor.map f) l)
  | .Kind k n => .Kind k n

@[simp] theorem id_map (o : Foreign α) : (o.map id) = o := by
  cases o <;> aesop

@[simp] theorem comp_map (f : α → β) (g : β → γ) (o : Foreign α) : (o.map (g ∘ f)) = (o.map f |>.map g) := by
  cases o <;> aesop

@[simp] theorem map_id_fun : map (id : α → α) = id := by funext o; exact id_map o

@[simp] theorem map_comp_fun (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext o; exact comp_map f g o

instance : Functor Foreign where map := map
instance : LawfulFunctor Foreign where
  map_const := rfl
  id_map := id_map
  comp_map := comp_map

@[always_inline, simp] def mapM [Monad m] (f : α → m β) (o : Foreign α) : m (Foreign β) :=
  match o with
  | .Value l => .Value <$> l.mapM_value (fun t => t.mapM f)
  | .Data k l => .Data k <$> l.mapM_value (fun t => t.mapM f)
  | .Kind k n => pure (.Kind k n)

end Foreign

@[always_inline] instance : Functor Foreign where
  map := Foreign.map

instance : LawfulFunctor Foreign where
  map_const := rfl
  id_map o := Foreign.id_map o
  comp_map f g o := Foreign.comp_map f g o

inductive Fixity
  | Infix
  | Infixl
  | Infixr
  deriving Repr, BEq, Ord

inductive FixityOp
  | Value (name : QualifiedName (Ident ⊕ Proper)) (token : SourceToken) (op : Name Operator)
  | Type_ (token1 : SourceToken) (name : QualifiedName Proper) (token2 : SourceToken) (op : Name Operator)
  deriving Repr, BEq

structure FixityFields where
  keyword : SourceToken × Fixity
  prec : SourceToken × USize
  operator : FixityOp
  deriving Repr, BEq

inductive Role
  | Nominal
  | Representational
  | Phantom
  deriving Repr, BEq, Ord

-----------------------------------------------------------------------------------------------------------

inductive Import (e : Type)
  | Value (name : Name Ident)
  | Op (name : Name Operator)
  | Type_ (name : Name Proper) (optionMembers : Option DataMembers)
  | TypeOp (token : SourceToken) (name : Name Operator)
  | Class (token : SourceToken) (name : Name Proper)
  | Error (data : e)
  deriving Repr, BEq

namespace Import

@[always_inline, simp] def map (f : α → β) (i : Import α) : Import β :=
  match i with
  | .Value n        => .Value n
  | .Op n           => .Op n
  | .Type_ n m      => .Type_ n m
  | .TypeOp t n     => .TypeOp t n
  | .Class t n      => .Class t n
  | .Error d        => .Error (f d)

@[simp] theorem id_map (i : Import α) : (i.map id) = i := by
  cases i <;> rfl

@[simp] theorem comp_map (f : α → β) (g : β → γ) (i : Import α) : (i.map (g ∘ f)) = (i.map f |>.map g) := by
  cases i <;> rfl

@[simp] theorem functor_map_id : map (id : α → α) = id := by funext i; exact id_map i

@[simp] theorem functor_map_comp (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext i; exact comp_map f g i

@[always_inline, simp] def mapM [Monad m] (f : α → m β) (i : Import α) : m (Import β) := match i with | .Value n => pure (.Value n) | .Op n => pure (.Op n) | .Type_ n m => pure (.Type_ n m) | .TypeOp t n => pure (.TypeOp t n) | .Class t n => pure (.Class t n) | .Error d => .Error <$> f d

end Import

@[always_inline] instance : Functor Import where
  map := Import.map

instance : LawfulFunctor Import where
  map_const := rfl
  id_map i := Import.id_map i
  comp_map f g i := Import.comp_map f g i

structure ImportDecl (e : Type) where
  keyword : SourceToken
  module_ : Name ModuleName
  importList : Option (Option SourceToken × DelimitedNonEmpty (Import e))
  qualified : Option (SourceToken × Name ModuleName)
  deriving Repr, BEq

namespace ImportDecl

@[always_inline, simp] def map (f : α → β) (i : ImportDecl α) : ImportDecl β :=
  { i with importList := i.importList.map (fun (o, d) => (o, Functor.map (Functor.map f) d)) }

@[simp] theorem id_map (i : ImportDecl α) : (i.map id) = i := by
  cases i; aesop

@[simp] theorem comp_map (f : α → β) (g : β → γ) (i : ImportDecl α) : (i.map (g ∘ f)) = (i.map f |>.map g) := by
  cases i; aesop

@[simp] theorem map_id_fun : map (id : α → α) = id := by funext i; exact id_map i

@[simp] theorem map_comp_fun (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext i; exact comp_map f g i

instance : Functor ImportDecl where map := map
instance : LawfulFunctor ImportDecl where
  map_const := rfl
  id_map := id_map
  comp_map := comp_map

def mapM [Monad m] (f : α → m β) (i : ImportDecl α) : m (ImportDecl β) := do
  let list ← i.importList.mapM (fun (o, d) => (o, ·) <$> d.mapM (Import.mapM f))
  pure { i with importList := list }

end ImportDecl

@[always_inline] instance : Functor ImportDecl where
  map := ImportDecl.map

instance : LawfulFunctor ImportDecl where
  map_const := rfl
  id_map i := ImportDecl.id_map i
  comp_map f g i := ImportDecl.comp_map f g i
-----------------------------------------------------------------------------------------------------------

structure ModuleHeader (e : Type) where
  keyword : SourceToken
  name : Name ModuleName
  exports : Option (DelimitedNonEmpty (Export e))
  where_ : SourceToken
  imports : Array (ImportDecl e)
  deriving Repr, BEq

namespace ModuleHeader

@[always_inline, simp] def map (f : α → β) (m : ModuleHeader α) : ModuleHeader β :=
  { m with
    exports := m.exports.map (Functor.map (Functor.map f))
    imports := m.imports.map (Functor.map f)
  }

@[simp] theorem id_map (m : ModuleHeader α) : (m.map id) = m := by
  cases m; aesop

@[simp] theorem comp_map (f : α → β) (g : β → γ) (m : ModuleHeader α) : (m.map (g ∘ f)) = (m.map f |>.map g) := by
  cases m; aesop

@[simp] theorem map_id_fun : map (id : α → α) = id := by funext m; exact id_map m

@[simp] theorem map_comp_fun (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext m; exact comp_map f g m

instance : Functor ModuleHeader where map := map
instance : LawfulFunctor ModuleHeader where
  map_const := rfl
  id_map := id_map
  comp_map := comp_map

@[always_inline, simp] def mapM [Monad m] (f : α → m β) (m_ : ModuleHeader α) : m (ModuleHeader β) := do
  let exps ← m_.exports.mapM (·.mapM (Export.mapM f))
  let imps ← m_.imports.mapM (ImportDecl.mapM f)
  pure { m_ with exports := exps, imports := imps }

end ModuleHeader

end PurescriptLanguageCstParser.Types
