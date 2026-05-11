module

public import NonEmpty.ArrayCorrectByConstruction
public import NonEmpty.String
import PurescriptLanguageCstParser.GenerateFixed

namespace PurescriptLanguageCstParser.Types

open NonEmpty.ArrayCorrectByConstruction
open NonEmpty.String

@[expose] public section

def ModuleName := NonEmptyString
  deriving Repr, BEq, Ord, Hashable, DecidableEq

structure SourcePos where
  line : USize
  column : USize
  deriving Repr, BEq, Ord, Inhabited, Hashable, DecidableEq

namespace SourcePos

/--
Returns true if position `a` occurs strictly before position `b` in the source text.
Comparison is performed lexicographically: first by line, then by column.
-/
def isBefore (a b : SourcePos) : Bool :=
  a.line < b.line || (a.line == b.line && a.column < b.column)

end SourcePos

structure SourceRange where
  start : SourcePos
  end_ : SourcePos
  deriving Repr, BEq, Ord, Inhabited, Hashable, DecidableEq

inductive CommentWithoutLine
  | Comment (s : NonEmptyString)
  | Space (i : USize)
  deriving Repr, BEq, Ord, Hashable, DecidableEq

inductive Comment (l : Type)
  | Comment (s : NonEmptyString)
  | Space (i : USize)
  | Line (l : l) (i : USize)
  deriving Repr, BEq, Ord, Hashable, DecidableEq

namespace Comment
-- Why full name? Bc inductive type Comment has a constructor also named Comment
@[inline_if_reduce, simp] def map (f : α → β) (c : PurescriptLanguageCstParser.Types.Comment α) : PurescriptLanguageCstParser.Types.Comment β :=
  match c with
  | .Comment s    => .Comment s
  | .Space i      => .Space i
  | .Line l i     => .Line (f l) i

@[inline_if_reduce, simp] def mapM [Monad m] (f : α → m β) (c : PurescriptLanguageCstParser.Types.Comment α) : m (PurescriptLanguageCstParser.Types.Comment β) :=
  match c with
  | .Comment s    => pure (.Comment s)
  | .Space i      => pure (.Space i)
  | .Line l i     => (.Line · i) <$> f l

@[simp] theorem id_map (c : PurescriptLanguageCstParser.Types.Comment α) : (c.map id) = c := by
  cases c with | Comment s => rfl | Space i => rfl | Line l i => rfl

@[simp] theorem comp_map (f : α → β) (g : β → γ) (c : PurescriptLanguageCstParser.Types.Comment α) : (c.map (g ∘ f)) = (c.map f |>.map g) := by
  cases c with | Comment s => rfl | Space i => rfl | Line l i => rfl

@[simp] theorem map_id_fun : map (id : α → α) = id := by funext c; exact id_map c

@[simp] theorem map_comp_fun (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext c; exact comp_map f g c

end Comment

@[always_inline] instance : Functor Comment where
  map := Comment.map

instance : LawfulFunctor Comment where
  map_const := rfl
  id_map c := Comment.id_map c
  comp_map f g c := Comment.comp_map f g c

inductive LineFeed
  | LF
  | CRLF
  deriving Repr, BEq, Ord, Hashable, DecidableEq

inductive SourceStyle
  | ASCII
  | Unicode
  deriving Repr, BEq, Ord, Hashable, DecidableEq

inductive IntValue
  | SmallInt (i : USize)
  | BigInt (s : NonEmptyString)
  | BigHex (s : NonEmptyString)
  deriving Repr, BEq, Ord, Hashable, DecidableEq

inductive Token
  | LeftParen
  | RightParen
  | LeftBrace
  | RightBrace
  | LeftSquare
  | RightSquare
  | LeftArrow (style : SourceStyle)
  | RightArrow (style : SourceStyle)
  | RightFatArrow (style : SourceStyle)
  | DoubleColon (style : SourceStyle)
  | Forall (style : SourceStyle)
  | Equals
  | Pipe
  | Tick
  | Dot
  | Comma
  | Underscore
  | Backslash
  | At
  | LowerName (module_ : Option ModuleName) (name : NonEmptyString)
  | UpperName (module_ : Option ModuleName) (name : NonEmptyString)
  | Operator (module_ : Option ModuleName) (name : NonEmptyString)
  | SymbolName (module_ : Option ModuleName) (name : NonEmptyString)
  | SymbolArrow (style : SourceStyle)
  | Hole (name : NonEmptyString)
  | Char (s : NonEmptyString) (c : Char)
  | String (s : String) (value : String)
  | RawString (s : String)
  | Int (s : NonEmptyString) (value : IntValue)
  | Number (s : NonEmptyString) (value : Float)
  | LayoutStart (i : USize)
  | LayoutSep (i : USize)
  | LayoutEnd (i : USize)
  deriving Repr, BEq --, Ord -- bc of Float

structure SourceToken where
  range : SourceRange
  leadingComments : Array (Comment LineFeed)
  trailingComments : Array CommentWithoutLine
  value : Token
  deriving Repr, BEq

namespace SourceToken

/--
Compares two tokens and returns the one that starts earlier in the source file.
If they start at the same position, the first argument is returned.
-/
def minByStart (a b : SourceToken) : SourceToken :=
  if SourcePos.isBefore a.range.start b.range.start then a else b

/--
Compares two tokens and returns the one that finishes later in the source file.
If they end at the same position, the first argument is returned.
-/
def maxByEnd (a b : SourceToken) : SourceToken :=
  if SourcePos.isBefore a.range.end_ b.range.end_ then b else a

end SourceToken

instance : SizeOf SourceToken where
  sizeOf _ := 0

def Ident := NonEmptyString
  deriving Repr, BEq, Ord, Hashable, DecidableEq

def Proper := NonEmptyString
  deriving Repr, BEq, Ord, Hashable, DecidableEq

def Label := NonEmptyString
  deriving Repr, BEq, Ord, Hashable, DecidableEq

def Operator := NonEmptyString
  deriving Repr, BEq, Ord, Hashable, DecidableEq

structure Name (α : Type) where
  token : SourceToken
  name : α
  deriving Repr, BEq

instance [SizeOf α] : SizeOf (Name α) where
  sizeOf n := 1 + sizeOf n.token + sizeOf n.name

namespace Name

@[always_inline, simp] def map (f : α → β) (n : Name α) : Name β :=
  { n with name := f n.name }

@[simp] theorem id_map (n : Name α) : (n.map id) = n := rfl

@[simp] theorem comp_map (f : α → β) (g : β → γ) (n : Name α) : (n.map (g ∘ f)) = (n.map f |>.map g) := rfl

@[simp] theorem map_id_fun : map (id : α → α) = id := by funext n; exact id_map n

@[simp] theorem map_comp_fun (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext n; exact comp_map f g n

@[simp] theorem sizeOf_name [SizeOf α] (n : Name α) : sizeOf n.name < sizeOf n := by
  cases n with | mk t name =>
  change sizeOf name < 1 + sizeOf t + sizeOf name
  omega

@[inline_if_reduce, simp] def mapM [Monad m] (f : α → m β) (n : Name α) : m (Name β) := Name.mk n.token <$> f n.name

end Name

@[always_inline] instance : Functor Name where
  map := Name.map

instance : LawfulFunctor Name where
  map_const := rfl
  id_map n := Name.id_map n
  comp_map f g n := Name.comp_map f g n

structure QualifiedName (α : Type) where
  token : SourceToken
  module_ : Option ModuleName
  name : α
  deriving Repr, BEq

namespace QualifiedName

@[always_inline, simp] def map (f : α → β) (n : QualifiedName α) : QualifiedName β :=
  { n with name := f n.name }

@[simp] theorem id_map (n : QualifiedName α) : (n.map id) = n := rfl

@[simp] theorem comp_map (f : α → β) (g : β → γ) (n : QualifiedName α) : (n.map (g ∘ f)) = (n.map f |>.map g) := rfl

@[simp] theorem map_id_fun : map (id : α → α) = id := by funext n; exact id_map n

@[simp] theorem map_comp_fun (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext n; exact comp_map f g n

@[simp] theorem sizeOf_name [SizeOf α] (n : QualifiedName α) : sizeOf n.name < sizeOf n := by
  cases n with | mk t m name =>
  change sizeOf name < 1 + sizeOf t + sizeOf m + sizeOf name
  omega

@[inline_if_reduce, simp] def mapM [Monad m] (f : α → m β) (n : QualifiedName α) : m (QualifiedName β) := QualifiedName.mk n.token n.module_ <$> f n.name

end QualifiedName

@[always_inline] instance : Functor QualifiedName where
  map := QualifiedName.map

instance : LawfulFunctor QualifiedName where
  map_const := rfl
  id_map n := QualifiedName.id_map n
  comp_map f g n := QualifiedName.comp_map f g n

structure Wrapped (α : Type) where
  open_ : SourceToken
  value : α
  close : SourceToken
  deriving Repr, BEq

namespace Wrapped

@[always_inline, simp] def map (g : α → β) (w : Wrapped α) : Wrapped β :=
  { w with value := g w.value }

@[simp] theorem id_map (w : Wrapped α) : (w.map id) = w := rfl

@[simp] theorem comp_map (g : α → β) (h : β → γ) (w : Wrapped α) : (w.map (h ∘ g)) = (w.map g |>.map h) := rfl

@[simp] theorem map_id_fun : map (id : α → α) = id := by funext w; exact id_map w

@[simp] theorem map_comp_fun (g : α → β) (h : β → γ) : map (h ∘ g) = map h ∘ map g := by funext w; exact comp_map g h w

@[simp] theorem sizeOf_value [SizeOf α] (w : Wrapped α) : sizeOf w.value < sizeOf w := by
  cases w with | mk o v c =>
  change sizeOf v < 1 + sizeOf o + sizeOf v + sizeOf c
  omega

instance : Membership α (Wrapped α) where
  mem w a := a = w.value

@[simp] theorem mem_def (a : α) (w : Wrapped α) : a ∈ w ↔ a = w.value := Iff.rfl

def attachWith (w : Wrapped α) (P : α → Prop) (H : ∀ a ∈ w, P a) : Wrapped { x // P x } :=
  { w with value := ⟨w.value, H w.value (mem_def .. |>.mpr rfl)⟩ }

def attach (w : Wrapped α) : Wrapped { x // x ∈ w } :=
  w.attachWith _ (fun _ => id)

@[simp] theorem sizeOf_attach_elem [SizeOf α] (w : Wrapped α) (x : { x // x ∈ w }) : sizeOf x.val < sizeOf w := by
  let ⟨a, h⟩ := x
  rw [mem_def] at h
  subst h
  apply sizeOf_value

@[simp] theorem attach_map (w : Wrapped α) (f : α → β) : w.attach.map (fun x => f x.val) = w.map f := rfl

@[simp] theorem attach_map_val (w : Wrapped α) : w.attach.map (fun x => x.val) = w := rfl

@[always_inline, simp] def mapM [Monad m] (f : α → m β) (w : Wrapped α) : m (Wrapped β) := Wrapped.mk w.open_ <$> f w.value <*> pure w.close

@[simp] theorem sizeOf_wrapped_mapM [SizeOf β] (w : Wrapped α) (f : α → β) :
  sizeOf (f w.value) < 1 + sizeOf w.open_ + sizeOf (f w.value) + sizeOf w.close := by
  omega

@[simp] theorem sizeOf_mapM_val [SizeOf α] [SizeOf β] (w : Wrapped α) (v : β) :
  sizeOf v < 1 + sizeOf w.open_ + sizeOf v + sizeOf w.close := by
  omega

@[simp] theorem sizeOf_mapM_result (w : Wrapped α) (v : β) :
  sizeOf v < sizeOf (Wrapped.mk w.open_ v w.close) := by
  simp only [sizeOf_default, mk.sizeOf_spec, Nat.add_zero]; omega

@[simp] theorem sizeOf_mem [SizeOf α]
    (w : Wrapped α) (a : α) (h : a ∈ w) : sizeOf a < sizeOf w := by
  rw [Wrapped.mem_def] at h; subst h; exact Wrapped.sizeOf_value w

end Wrapped

@[always_inline] instance : Functor Wrapped where
  map := Wrapped.map

instance : LawfulFunctor Wrapped where
  map_const := rfl
  id_map w := Wrapped.id_map w
  comp_map g h w := Wrapped.comp_map g h w

structure Separated (α : Type) where
  head : α
  tail : Array (SourceToken × α)
  deriving Repr, BEq

namespace Separated

@[always_inline, simp] def map (g : α → β) (s : Separated α) : Separated β := { head := g s.head, tail := s.tail.map (fun (tok, a) => (tok, g a)) }

@[always_inline, simp, inline]
def foldMap {α ω} (op : ω → ω → ω) (f : α → ω) (g : SourceToken × α → ω) (s : Separated α) : ω :=
  NonEmpty.ArrayUtil.foldMap op g (f s.head) s.tail

@[simp] theorem id_map (s : Separated α) : (s.map id) = s := by
  simp_all only [map, id_eq, Array.map_id_fun']

@[simp] theorem comp_map (g : α → β) (h : β → γ) (s : Separated α) : (s.map (h ∘ g)) = (s.map g |>.map h) := by
  funext
  simp_all only [map, Function.comp, Array.map_map, Separated.mk.injEq, Array.map_inj_left,
      implies_true, and_self]

@[simp] theorem map_id_fun : map (id : α → α) = id := by funext s; exact id_map s

@[simp] theorem map_comp_fun (g : α → β) (h : β → γ) : map (h ∘ g) = map h ∘ map g := by funext s; exact comp_map g h s

@[simp] theorem sizeOf_head [SizeOf α] (s : Separated α) : sizeOf s.head < sizeOf s := by
  cases s with | mk h t =>
  change sizeOf h < 1 + sizeOf h + sizeOf t
  omega

@[simp] theorem sizeOf_tail [SizeOf α] (s : Separated α) : sizeOf s.tail < sizeOf s := by
  cases s with | mk h t =>
  change sizeOf t < 1 + sizeOf h + sizeOf t
  omega

@[simp] theorem sizeOf_tail_elem [SizeOf α] (s : Separated α) (i : Nat) (h : i < s.tail.size) : sizeOf (s.tail[i]).2 < sizeOf s := by
  cases s with | mk head tail =>
  have h1 := Array.sizeOf_getElem tail i h
  match h2 : tail[i] with
  | (tok, a) =>
    simp only [h2, Prod.mk.sizeOf_spec] at h1
    change sizeOf a < 1 + sizeOf head + sizeOf tail
    omega

@[simp] theorem sizeOf_tail_get [SizeOf α] (s : Separated α) (i : Nat) (h : i < s.tail.size) :
    sizeOf (s.tail[i]'h).2 < sizeOf s := by
  cases s with | mk head tail =>
  have h1 := Array.sizeOf_getElem tail i h
  have h2 : sizeOf (tail[i]'h).2 < sizeOf (tail[i]'h) := by
    match tail[i]'h with
    | (tok, a) =>
      change sizeOf a < 1 + sizeOf tok + sizeOf a
      omega
  have h3 : sizeOf tail < sizeOf (Separated.mk head tail) := by
    change sizeOf tail < 1 + sizeOf head + sizeOf tail
    omega
  exact Nat.lt_trans h2 (Nat.lt_trans h1 h3)

instance : Membership α (Separated α) where
  mem s a := a = s.head ∨ ∃ tok, (tok, a) ∈ s.tail

@[simp] theorem mem_def (a : α) (s : Separated α) :
    a ∈ s ↔ a = s.head ∨ ∃ tok, (tok, a) ∈ s.tail := Iff.rfl

def attachWith (s : Separated α) (P : α → Prop) (H : ∀ a ∈ s, P a) : Separated { x // P x } :=
  { head := ⟨s.head, H s.head (mem_def .. |>.mpr (Or.inl rfl))⟩,
    tail := s.tail.attachWith (fun p => P p.2) (fun p hp => H p.2 (mem_def .. |>.mpr (Or.inr ⟨p.1, hp⟩)))
            |>.map (fun ⟨p, h⟩ => (p.1, ⟨p.2, h⟩)) }

def attach (s : Separated α) : Separated { x // x ∈ s } :=
  s.attachWith _ (fun _ => id)

@[simp] theorem sizeOf_attach_elem [SizeOf α] (s : Separated α) (x : { x // x ∈ s }) : sizeOf x.val < sizeOf s := by
  obtain ⟨val, property⟩ := x
  simp only [mem_def] at property
  cases property with
  | inl h =>
    subst h
    exact sizeOf_head s
  | inr h_1 =>
    obtain ⟨w, h⟩ := h_1
    have ⟨i, hi, heq⟩ := Array.mem_iff_getElem.mp h
    have h_size := sizeOf_tail_elem s i hi
    -- Extract the tuple element to help omega see the size
    have h_eq : sizeOf val < sizeOf s.tail[i] := by
      rw [heq]
      grind only [= Prod.mk.sizeOf_spec]
    grind only

 @[simp] theorem attach_map (s : Separated α) (f : α → β) : s.attach.map (fun x => f x.val) = s.map f := by
   cases s with | mk h t =>
   simp only [map, attach, attachWith, Array.map_attachWith, Array.map_map, mk.injEq, true_and]
   apply Array.ext
   · simp
   · intro i h1 h2
     simp only [Array.getElem_map, Array.getElem_attach, Function.comp_apply]

@[simp] theorem attach_map_val (s : Separated α) : s.attach.map (fun x => x.val) = s := by
   rw [attach_map s (fun x => x)]
   simp

@[inline_if_reduce] def mapM [Monad m] (f : α → m β) (s : Separated α) : m (Separated β) := do
  let h ← f s.head
  let t ← s.tail.mapM (fun p => Prod.mk p.1 <$> f p.2)
  pure (Separated.mk h t)

def mapM' [Monad m] (f : α → m β) (s : Separated α) :
    m { bs : Separated β // bs.tail.size = s.tail.size } := do
    let ⟨t, th⟩ ← s.tail.mapM' (fun p => Prod.mk p.1 <$> f p.2)
    let h ← f s.head
    pure (Subtype.mk (Separated.mk h t) th)

-- @[simp] theorem mapM'_eq_mapM (f : α → m β) [Monad m] (s : Separated α) :
--     mapM' f s = (fun ⟨bs, _⟩ => bs) <$> mapM f s := by
--   funext
--   simp? [mapM', Subtype.val_mk, Array.mapM'_eq_mapM]

-- @[simp] theorem mapM'_id (s : Separated α) :
--     mapM' (fun x => return x) s = return (Subtype.mk s rfl) := by
--   funext
--   simp? [mapM', Subtype.val_mk, Array.mapM'_id]

-- @[simp] theorem mapM'_comp (f : α → m β) (g : β → m γ) (s : Separated α) :
--     mapM' (g ∘ f) s = (mapM' f s).bind (fun ⟨bs, _⟩ => mapM' g bs) := by
--   funext
--   simp? [mapM', Subtype.val_mk, Array.mapM'_comp, bind_def, Functor.map]

end Separated

@[always_inline] instance : Functor Separated where
  map := Separated.map

instance : LawfulFunctor Separated where
  map_const := rfl
  id_map s := Separated.id_map s
  comp_map g h s := Separated.comp_map g h s

structure Labeled (α β : Type) where
  label : α
  separator : SourceToken
  value : β
  deriving Repr, BEq

namespace Labeled

@[always_inline] def map_all (f : α → β) (g : γ → δ) (l : Labeled α γ) : Labeled β δ := { l with label := f l.label, value := g l.value }

@[always_inline] def map_label (g : α → β) (l : Labeled α x) : Labeled β x := map_all g id l

@[always_inline] def map_value (g : β → γ) (l : Labeled α β) : Labeled α γ := map_all id g l

@[simp] theorem map_value_id (l : Labeled α β) : map_value (id : β → β) l = l := rfl
@[simp] theorem map_value_comp (g : β → γ) (h : γ → δ) (l : Labeled α β) : map_value (h ∘ g) l = map_value h (map_value g l) := rfl

@[simp] theorem map_label_id (l : Labeled α β) : map_label (id : α → α) l = l := rfl
@[simp] theorem map_label_comp (g : α → β) (h : β → γ) (l : Labeled α δ) : map_label (h ∘ g) l = map_label h (map_label g l) := rfl

@[simp] theorem sizeOf_value [SizeOf α] [SizeOf β] (l : Labeled α β) : sizeOf l.value < sizeOf l := by
  cases l with | mk l s v =>
  change sizeOf v < 1 + sizeOf l + sizeOf s + sizeOf v
  omega

@[simp] theorem map_label_id_fun : map_label (id : α → α) = (id : Labeled α β → Labeled α β) := by funext l; exact map_label_id l
@[simp] theorem map_value_id_fun : map_value (id : β → β) = (id : Labeled α β → Labeled α β) := by funext l; exact map_value_id l

@[simp] theorem map_label_comp_fun (g : α → β) (h : β → γ) :
  map_label (h ∘ g) = (map_label h ∘ map_label g : Labeled α δ → Labeled γ δ) := by funext l; exact map_label_comp g h l
@[simp] theorem map_value_comp_fun (g : β → γ) (h : γ → δ) :
  map_value (h ∘ g) = (map_value h ∘ map_value g : Labeled α β → Labeled α δ) := by funext l; exact map_value_comp g h l

@[inline_if_reduce] def mapM_all [Applicative m] (f_label : α → m β) (f_value : γ → m δ) (l : Labeled α γ) : m (Labeled β δ) :=
  Labeled.mk <$> f_label l.label <*> pure l.separator <*> f_value l.value

@[inline_if_reduce] def mapM_label [Applicative m] (f_label : α → m β) (s : Labeled α γ) : m (Labeled β γ) := mapM_all f_label pure s

@[inline_if_reduce] def mapM_value [Applicative m] (f_value : γ → m β) (s : Labeled α γ) : m (Labeled α β) := mapM_all pure f_value s

-- @[simp] theorem mapM_label_eq_mapM (f_label : α → m β) (s : Labeled α γ) : mapM_label f_label s = (fun ⟨v⟩ => v) <$> (f_label s.label *> (fun s' => (s.separator, s'.value)) <$> s.tail.mapM (fun ⟨t, v⟩ => pure (t, f_value v))) := by
--   funext
--   rfl

end Labeled

@[always_inline] instance : Functor (Labeled α) where
  map := Labeled.map_value

instance : LawfulFunctor (Labeled α) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl

structure Prefixed (α : Type) where
  prefix_ : Option SourceToken
  value : α
  deriving Repr, BEq

namespace Prefixed

@[always_inline, simp] def map (f : α → β) (p : Prefixed α) : Prefixed β := { p with value := f p.value }

@[inline_if_reduce, simp] def mapM [Monad m] (f : α → m β) (p : Prefixed α) : m (Prefixed β) :=
  Prefixed.mk p.prefix_ <$> f p.value

@[simp] theorem id_map (p : Prefixed α) : (p.map id) = p := rfl

@[simp] theorem comp_map (f : α → β) (g : β → γ) (p : Prefixed α) : (p.map (g ∘ f)) = (p.map f |>.map g) := rfl

@[simp] theorem map_id_fun : map (id : α → α) = id := by funext p; exact id_map p

@[simp] theorem map_comp_fun (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext p; exact comp_map f g p

@[simp] theorem sizeOf_value [SizeOf α] (p : Prefixed α) : sizeOf p.value < sizeOf p := by
  cases p with | mk pr v =>
  change sizeOf v < 1 + sizeOf pr + sizeOf v
  omega

end Prefixed

@[always_inline] instance : Functor Prefixed where
  map := Prefixed.map

instance : LawfulFunctor Prefixed where
  map_const := rfl
  id_map p := Prefixed.id_map p
  comp_map f g p := Prefixed.comp_map f g p

-- why not def or abbrev? will break in recursive inductive types (e.g. Expr)
inductive Delimited (α : Type)
  | mk (v : Wrapped (Option (Separated α)))
  deriving Repr, BEq

namespace Delimited

@[simp] theorem sizeOf_mk [SizeOf α] (v : Wrapped (Option (Separated α))) : sizeOf (mk v) = 1 + sizeOf v := rfl

@[always_inline, simp] def map (f : α → β) : Delimited α → Delimited β
  | .mk v => .mk { v with value := (Separated.map f) <$> v.value }

@[inline_if_reduce] def mapM [Monad m] (f : α → m β) : Delimited α → m (Delimited β)
  | .mk v => .mk <$> v.mapM (fun opt => opt.mapM (Separated.mapM f))

@[simp] theorem id_map (d : Delimited α) : map id d = d := by
  cases d with | mk v =>
  simp only [map, Separated.map_id_fun, LawfulFunctor.id_map]

@[simp] theorem comp_map (f : α → β) (g : β → γ) (d : Delimited α) : (map (g ∘ f) d) = (map g (map f d)) := by
  cases d with | mk v =>
  simp only [map, Separated.map_comp_fun, Option.map_eq_map, Option.map_map]

instance : Membership α (Delimited α) where
  mem d a := match d with | mk w => ∃ s, s ∈ w.value ∧ a ∈ s

@[simp] theorem mem_def (a : α) (d : Delimited α) :
    a ∈ d ↔ match d with | mk w => ∃ s, s ∈ w.value ∧ a ∈ s := Iff.rfl

def attachWith (d : Delimited α) (P : α → Prop) (H : ∀ a ∈ d, P a) : Delimited { x // P x } :=
  match d with
  | mk w => mk { w with value :=
      match h_val : w.value with
      | none => none
      | some s => some (s.attachWith P (fun a ha => H a (by simp_all only [mem_def, Option.mem_def, Option.some.injEq,
        Separated.mem_def, exists_eq_left', forall_eq_or_imp, forall_exists_index])))
    }

def attach (d : Delimited α) : Delimited { x // x ∈ d } :=
  d.attachWith _ (fun _ => id)

@[simp] theorem sizeOf_attach_elem [SizeOf α] (d : Delimited α) (x : { x // x ∈ d }) : sizeOf x.val < sizeOf d := by
  cases d with | mk v =>
  obtain ⟨val, property⟩ := x
  simp only [mem_def] at property
  obtain ⟨w, h_eq, h_mem⟩ := property
  have h_v := Wrapped.sizeOf_value v
  have h_some : sizeOf w < sizeOf (some w) := by
    simp only [Option.some.sizeOf_spec, Nat.lt_add_left_iff_pos, Nat.lt_add_one]
  cases h_mem with
  | inl h =>
    subst h
    have h_w := Separated.sizeOf_head w
    -- Give omega the explicit chain of inequalities
    have step1 : sizeOf (some w) ≤ sizeOf v.value := by rw [h_eq]; omega
    grind only [= mk.sizeOf_spec]
  | inr h_tail =>
    obtain ⟨w_1, h⟩ := h_tail
    have ⟨i, hi, heq⟩ := Array.mem_iff_getElem.mp h
    have h_w := Separated.sizeOf_tail_get w i hi
    -- Give omega the explicit chain of inequalities
    have step1 : sizeOf (some w) ≤ sizeOf v.value := by rw [h_eq]; omega
    grind only [= mk.sizeOf_spec]

@[simp] theorem attach_map (d : Delimited α) (f : α → β) : d.attach.map (fun x => f x.val) = d.map f := by
  cases d with | mk v =>
  simp only [map, attach, attachWith, mk.injEq, Wrapped.mk.injEq, Option.map_eq_map]
  simp_all only [and_true, true_and]
  split
  next heq => simp_all only [Option.map_none]
  next s heq =>
    simp_all only [Option.map_some, Separated.map, Option.some.injEq, Separated.mk.injEq]
    have := Separated.attach_map s f
    simp_all only [Separated.map, Separated.mk.injEq, Separated.attachWith, Array.map_attachWith,
      Array.map_map, true_and]
    obtain ⟨left, right⟩ := this
    ext i hi₁ hi₂ : 1
    · simp_all only [Array.size_map, Array.size_attach]
    · ext : 1
      · simp_all only [Array.getElem_map, Array.getElem_attach, Function.comp_apply]
      · simp_all only [Array.getElem_map, Array.getElem_attach, Function.comp_apply]

 @[simp] theorem attach_map_val (d : Delimited α) : d.attach.map (fun x => x.val) = d := by
   rw [(_ : (fun x : {x // x ∈ d} => x.val) = (fun x => id x.val))]
   · rw [attach_map, id_map]
   · rfl

end Delimited

@[always_inline] instance : Functor Delimited where
  map := Delimited.map

instance : LawfulFunctor Delimited where
  map_const := rfl
  id_map := Delimited.id_map
  comp_map := Delimited.comp_map

inductive DelimitedNonEmpty (α : Type)
  | mk (v : Wrapped (Separated α))
  deriving Repr, BEq

namespace DelimitedNonEmpty

@[always_inline, simp] def map (f : α → β) : DelimitedNonEmpty α → DelimitedNonEmpty β
  | .mk v => .mk { v with value := Separated.map f v.value }

@[inline_if_reduce] def mapM [Monad m] (f : α → m β) : DelimitedNonEmpty α → m (DelimitedNonEmpty β)
  | .mk v => .mk <$> v.mapM (Separated.mapM f)

@[simp] theorem id_map (d : DelimitedNonEmpty α) : map id d = d := by
  cases d with | mk v =>
  simp only [map, Separated.map, id_eq, Array.map_id_fun']

@[simp] theorem comp_map (f : α → β) (g : β → γ) (d : DelimitedNonEmpty α) : (map (g ∘ f) d) = (map g (map f d)) := by
  cases d with | mk v =>
  simp only [map, Separated.map, Function.comp_apply,
    Array.map_map, DelimitedNonEmpty.mk.injEq, Wrapped.mk.injEq, Separated.mk.injEq,
    Array.map_inj_left, implies_true, and_self]

@[simp] theorem sizeOf_mk [SizeOf α] (v : Wrapped (Separated α)) : sizeOf (mk v) = 1 + sizeOf v := rfl

@[simp] theorem sizeOf_v [SizeOf α] (d : DelimitedNonEmpty α) : sizeOf d.1 < sizeOf d := by
  cases d with | mk v =>
  change sizeOf v < 1 + sizeOf v
  omega

instance : Membership α (DelimitedNonEmpty α) where
  mem d a := match d with | mk w => a ∈ w.value

@[simp] theorem mem_def (a : α) (d : DelimitedNonEmpty α) :
    a ∈ d ↔ match d with | mk w => a ∈ w.value := Iff.rfl

@[simp] theorem sizeOf_attach_elem [SizeOf α] (d : DelimitedNonEmpty α) (x : { x // x ∈ d }) : sizeOf x.val < sizeOf d := by
  cases d with | mk v =>
  obtain ⟨val, property⟩ := x
  simp only [mem_def] at property
  have h_v := Wrapped.sizeOf_value v
  cases property with
  | inl h =>
    subst h
    have h_w := Separated.sizeOf_head v.value
    grind only [= mk.sizeOf_spec]
  | inr h_tail =>
    obtain ⟨w_1, h⟩ := h_tail
    have ⟨i, hi, heq⟩ := Array.mem_iff_getElem.mp h
    have h_w := Separated.sizeOf_tail_get v.value i hi
    have h_val : sizeOf val = sizeOf (v.value.tail[i]).2 := by simp only [heq]
    grind only [= mk.sizeOf_spec]

@[simp] def attachWith (d : DelimitedNonEmpty α) (P : α → Prop) (H : ∀ a ∈ d, P a) : DelimitedNonEmpty { x // P x } :=
  match d with
  | mk w => mk { w with value := w.value.attachWith P (fun a ha => H a (by simp_all only [mem_def, Separated.mem_def,
    forall_eq_or_imp, forall_exists_index])) }

@[simp] def attach (d : DelimitedNonEmpty α) : DelimitedNonEmpty { x // x ∈ d } :=
  d.attachWith _ (fun _ => id)


 @[simp] theorem attach_map (d : DelimitedNonEmpty α) (f : α → β) : d.attach.map (fun x => f x.val) = d.map f := by
   cases d with | mk v =>
   simp only [map, attach, attachWith, Separated.map, mk.injEq, Wrapped.mk.injEq,
     Separated.mk.injEq, and_true, true_and]
   cases v with | mk o val c =>
   simp only
   apply And.intro
   · rfl
   · exact (congrArg Separated.tail (Separated.attach_map val f))

 @[simp] theorem attach_map_val (d : DelimitedNonEmpty α) : d.attach.map (fun x => x.val) = d := by
   rw [attach_map d (fun x => x)]
   simp

 end DelimitedNonEmpty

instance : Functor DelimitedNonEmpty where
  map := DelimitedNonEmpty.map

instance : LawfulFunctor DelimitedNonEmpty where
  map_const := rfl
  id_map := DelimitedNonEmpty.id_map
  comp_map := DelimitedNonEmpty.comp_map

inductive OneOrDelimited (α : Type)
  | One (value : α)
  | Many (separated : DelimitedNonEmpty α)
  deriving Repr, BEq

namespace OneOrDelimited

@[always_inline, simp] def map (f : α → β) : OneOrDelimited α → OneOrDelimited β
  | .One a  => .One (f a)
  | .Many m => .Many (f <$> m)

@[inline_if_reduce] def mapM [Monad m] (f : α → m β) : OneOrDelimited α → m (OneOrDelimited β)
  | .One a  => .One <$> f a
  | .Many m => .Many <$> m.mapM f

@[simp] theorem id_map (o : OneOrDelimited α) : map id o = o := by
  cases o <;> simp_all only [map, LawfulFunctor.id_map, id_eq]

@[simp] theorem comp_map (f : α → β) (g : β → γ) (o : OneOrDelimited α) : (map (g ∘ f) o) = (map g (map f o)) := by
  cases o <;> simp_all only [map, Functor.map_map, Many.injEq, Function.comp_apply]
  rfl

end OneOrDelimited

@[always_inline] instance : Functor OneOrDelimited where
  map := OneOrDelimited.map

instance : LawfulFunctor OneOrDelimited where
  map_const := rfl
  id_map := OneOrDelimited.id_map
  comp_map := OneOrDelimited.comp_map

-- Note: the above requires Functor for DelimitedNonEmpty, defined below.

structure TokenAnd (α : Type) where
  token : SourceToken
  value : α
  deriving Repr, BEq

namespace TokenAnd

@[always_inline, simp] def map (f : α → β) (t : TokenAnd α) : TokenAnd β :=
  { t with value := f t.value }

@[inline_if_reduce, simp] def mapM [Monad m] (f : α → m β) (t : TokenAnd α) : m (TokenAnd β) :=
  TokenAnd.mk t.token <$> f t.value

@[simp] theorem id_map (t : TokenAnd α) : (t.map id) = t := rfl

@[simp] theorem comp_map (f : α → β) (g : β → γ) (t : TokenAnd α) : (t.map (g ∘ f)) = (t.map f |>.map g) := rfl

@[simp] theorem map_id_fun : map (id : α → α) = id := by funext t; exact id_map t

@[simp] theorem map_comp_fun (f : α → β) (g : β → γ) : map (g ∘ f) = map g ∘ map f := by funext t; exact comp_map f g t

@[simp] theorem sizeOf_value [SizeOf α] (t : TokenAnd α) : sizeOf t.value < sizeOf t := by
  cases t with | mk tok v =>
  change sizeOf v < 1 + sizeOf tok + sizeOf v
  omega

end TokenAnd

@[always_inline] instance : Functor TokenAnd where
  map := TokenAnd.map

instance : LawfulFunctor TokenAnd where
  map_const := rfl
  id_map t := TokenAnd.id_map t
  comp_map f g t := TokenAnd.comp_map f g t

inductive TypeVarBinding (name type_e : Type)
  | Kinded (wrapped : Wrapped (Labeled name type_e))
  | Name (name : name)
  deriving Repr, BEq

namespace TypeVarBinding

@[always_inline, simp] def map (f : α → β) : TypeVarBinding name α → TypeVarBinding name β
  | .Kinded w => .Kinded (w.map (Labeled.map_value f))
  | .Name n   => .Name n

@[inline_if_reduce] def mapM [Monad m] (f : α → m β) : TypeVarBinding name α → m (TypeVarBinding name β)
  | .Kinded w => .Kinded <$> w.mapM (Labeled.mapM_value f)
  | .Name n   => pure (.Name n)

@[simp] theorem id_map (t : TypeVarBinding name α) : (t.map id) = t := by
  cases t <;> simp only [map, Wrapped.map, Labeled.map_value_id]

@[simp] theorem comp_map (g : α → β) (h : β → γ) (t : TypeVarBinding name α) : (t.map (h ∘ g)) = (t.map g |>.map h) := by
  cases t <;> simp only [map, Wrapped.map, Labeled.map_value_comp]

@[simp] theorem map_id_fun : map (name := name) (id : α → α) = id := by
  funext t; exact id_map t

@[simp] theorem map_comp_fun (g : α → β) (h : β → γ) :
    map (name := name) (h ∘ g) = map (name := name) h ∘ map (name := name) g := by
  funext t; exact comp_map g h t

def map_name (g : a → b) : TypeVarBinding a α → TypeVarBinding b α
  | .Kinded w => .Kinded (w.map (Labeled.map_label g))
  | .Name n   => .Name (g n)

@[simp] theorem map_name_id (t : TypeVarBinding a α) : map_name (id : a → a) t = t := by
  cases t <;> simp only [map_name, Wrapped.map, Labeled.map_label_id, id_eq]

@[simp] theorem map_name_comp (ga : a → b) (gb : b → c) (t : TypeVarBinding a α) :
  map_name (gb ∘ ga) t = map_name gb (map_name ga t) := by
  cases t <;> simp only [map_name, Wrapped.map, Labeled.map_label_comp, Function.comp_apply]

@[simp] theorem sizeOf_Kinded [SizeOf name] [SizeOf α] (w : Wrapped (Labeled name α)) :
  sizeOf w < sizeOf (TypeVarBinding.Kinded (type_e := α) w) := by
  show sizeOf w < 1 + sizeOf w
  omega

@[simp] theorem sizeOf_Name [SizeOf name] [SizeOf α] (n : name) :
  sizeOf n < sizeOf (TypeVarBinding.Name (type_e := α) n) := by
  show sizeOf n < 1 + sizeOf n
  omega

end TypeVarBinding

instance : Functor (TypeVarBinding name) where
  map := TypeVarBinding.map

instance : LawfulFunctor (TypeVarBinding name) where
  map_const := rfl
  id_map t := TypeVarBinding.id_map t
  comp_map g h t := TypeVarBinding.comp_map g h t

structure Row (type_e : Type) where
  labels : Option (Separated (Labeled (Name Label) type_e))
  tail : Option (SourceToken × type_e)
  deriving Repr, BEq

namespace Row

@[simp] def map (f : type_e → type_e') : Row type_e → Row type_e'
  | { labels, tail } => {
    labels := labels.map (Separated.map (Labeled.map_value f))
    tail   := tail.map (fun (tok, t) => (tok, f t))
  }

@[inline_if_reduce] def mapM [Monad m] (f : α → m β) (r : Row α) : m (Row β) := do
  let labels ← r.labels.mapM (Separated.mapM (Labeled.mapM_value f))
  let tail ← r.tail.mapM (fun (tok, t) => (tok, ·) <$> f t)
  pure { labels, tail }

@[simp] theorem id_map (r : Row α) : (map id r) = r := by
  cases r; simp only [map, Labeled.map_value_id_fun, Separated.map_id_fun, Option.map_id, id_eq,
    Option.map_id_fun']

@[simp] theorem comp_map (f : α → β) (g : β → γ) (r : Row α) : (map (g ∘ f) r) = (map g (map f r)) := by
  cases r with | mk l t =>
  simp only [map, Labeled.map_value_comp_fun, Separated.map_comp_fun, Function.comp_apply,
    Option.map_map, mk.injEq, true_and]
  cases t <;> rfl

@[simp] theorem sizeOf_labels [SizeOf α] (r : Row α) : sizeOf r.labels < sizeOf r := by
  cases r with | mk l t =>
  change sizeOf l < 1 + sizeOf l + sizeOf t
  omega

@[simp] theorem sizeOf_tail [SizeOf α] (r : Row α) : sizeOf r.tail < sizeOf r := by
  cases r with | mk l t =>
  change sizeOf t < 1 + sizeOf l + sizeOf t
  omega

def map_e (_g : e → f) (r : Row α) : Row α :=
  r

@[simp] theorem map_e_id (r : Row α) : map_e (id : e → e) r = r := rfl

@[simp] theorem map_e_comp (ge : e → f) (gf : f → g) (r : Row α) :
  map_e (gf ∘ ge) r = map_e gf (map_e ge r) := rfl

@[simp] theorem map_comm (ge : e → f) (ga : α → β) (r : Row α) :
  (map ga) (map_e ge r) = map_e ge ((map ga) r) := rfl

end Row

instance : Functor Row where
  map := Row.map

instance : LawfulFunctor Row where
  map_const := rfl
  id_map := Row.id_map
  comp_map := Row.comp_map


-- Why? https://github.com/leanprover/lean4/issues/13465#issuecomment-4360118365 bc alternative is to wrap in inductive
local notation "inline_TypeF_Forall_Bindings" α:max => NonEmptyArray (TypeVarBinding (Prefixed (Name Ident)) α)

abbrev TypeF_Forall_Bindings (type_e : Type) := inline_TypeF_Forall_Bindings type_e

namespace TypeF_Forall_Bindings
  @[simp] def map (g : α → β) (arr : TypeF_Forall_Bindings α) : TypeF_Forall_Bindings β
    := NonEmptyArray.map (Functor.map g) arr

  @[inline_if_reduce] def mapM [Monad m] (f : α → m β) (arr : TypeF_Forall_Bindings α) : m (TypeF_Forall_Bindings β) :=
    NonEmptyArray.mapM (TypeVarBinding.mapM f) arr

  @[simp] theorem id_map (t : TypeF_Forall_Bindings α) : (map id t) = t := by
    cases t
    simp only [map, NonEmptyArray.map, LawfulFunctor.id_map, NonEmptyArray.mk.injEq, true_and]
    ext i hi₁ hi₂ : 1
    · simp_all only [Array.size_map]
    · simp_all only [Array.getElem_map, LawfulFunctor.id_map]

  @[simp] theorem comp_map (g : α → β) (h : β → γ) (t : TypeF_Forall_Bindings α) : (map (h ∘ g) t) = (map h (map g t)) := by
    cases t
    simp only [map, NonEmptyArray.map, Functor.map_map, Array.map_map, NonEmptyArray.mk.injEq,
      Array.map_inj_left, Function.comp_apply]
    apply And.intro
    · rfl
    · intro a a_1
      rfl

  @[simp] theorem sizeOf_get [SizeOf α] (t : TypeF_Forall_Bindings α) (i : Nat) (h : i < t.size) :
      sizeOf t[i] < sizeOf t := by
    apply NonEmptyArray.sizeOf_getElem

end TypeF_Forall_Bindings

-- Why? https://github.com/leanprover/lean4/issues/13465#issuecomment-4360118365 bc alternative is to wrap in inductive
local notation "inline_TypeF_Op_Ops" α:max => NonEmptyArray (QualifiedName Operator × α)

abbrev TypeF_Op_Ops (type_e : Type) := inline_TypeF_Op_Ops type_e

namespace TypeF_Op_Ops
@[simp] def map (g : α → β) (arr : TypeF_Op_Ops α) : TypeF_Op_Ops β
  := NonEmptyArray.map (fun (op, t) => (op, g t)) arr

@[inline_if_reduce] def mapM [Monad m] (f : α → m β) (arr : TypeF_Op_Ops α) : m (TypeF_Op_Ops β) :=
  NonEmptyArray.mapM (fun (op, t) => (op, ·) <$> f t) arr

@[simp] theorem id_map (t : TypeF_Op_Ops α) : (map id t) = t := by
  cases t
  simp only [map, NonEmptyArray.map, id_eq, Array.map_id_fun']

@[simp] theorem comp_map (g : α → β) (h : β → γ) (t : TypeF_Op_Ops α) : (map (h ∘ g) t) = (map h (map g t)) := by
  cases t
  simp only [map, NonEmptyArray.map, Function.comp_apply, Array.map_map, NonEmptyArray.mk.injEq,
    Array.map_inj_left, implies_true, and_self]

@[simp] theorem sizeOf_get [SizeOf α] (t : TypeF_Op_Ops α) (i : Nat) (h : i < t.size) :
    sizeOf t[i].2 < sizeOf t := by
  have h1 := NonEmptyArray.sizeOf_getElem t i h
  have h2 : sizeOf (t[i]).2 < sizeOf (t[i]) := by
    match t[i] with
    | (op, a) =>
      change sizeOf a < 1 + sizeOf op + sizeOf a
      omega
  omega
end TypeF_Op_Ops


inductive TypeF (e type_e : Type)
  | Var (name : Name Ident)
  | Constructor (name : QualifiedName Proper)
  | Wildcard (token : SourceToken)
  | Hole (name : Name Ident)
  | String (token : SourceToken) (value : String)
  | Int (prefix_ : Option SourceToken) (token : SourceToken) (value : IntValue)
  | Row (wrapped : Wrapped (Row type_e))
  | Record (wrapped : Wrapped (Row type_e))
  | Forall (open_ : SourceToken) (bindings : inline_TypeF_Forall_Bindings type_e) (close : SourceToken) (body : type_e)
  | Kinded (type_ : type_e) (sep : SourceToken) (kind : type_e)
  | App (fn : type_e) (args : NonEmptyArray type_e)
  | Op (first : type_e) (ops : inline_TypeF_Op_Ops type_e)
  | OpName (name : QualifiedName Operator)
  | Arrow (dom : type_e) (token : SourceToken) (codom : type_e)
  | ArrowName (token : SourceToken)
  | Constrained (type_ : type_e) (token : SourceToken) (body : type_e)
  | Parens (wrapped : Wrapped type_e)
  | Error (data : e)
  deriving Repr, BEq

-- #check TypeF.Kinded.sizeOf_spec
-- #check TypeF.Kinded.injEq
-- #check TypeF.Forall.sizeOf_spec
-- #check TypeF._sizeOf_1

namespace TypeF
  @[simp] def map (f : type_a -> type_b) : TypeF e type_a → TypeF e type_b
    | .Var n                    => .Var n
    | .Constructor n            => .Constructor n
    | .Wildcard t               => .Wildcard t
    | .Hole n                   => .Hole n
    | .String t v               => .String t v
    | .Int p t v                => .Int p t v
    | .Row w                    => .Row ((f <$> ·) <$> w)   -- Wrapped (Row type_e)
    | .Record w                 => .Record ((f <$> ·) <$> w)
    | .Forall o bs c body       => .Forall o (TypeF_Forall_Bindings.map f bs) c (f body)
    | .Kinded t sep k           => .Kinded (f t) sep (f k)
    | .App fn args              => .App (f fn) (args.map f)
    | .Op first ops             => .Op (f first) (TypeF_Op_Ops.map f ops)
    | .OpName n                 => .OpName n
    | .Arrow dom tok codom      => .Arrow (f dom) tok (f codom)
    | .ArrowName t              => .ArrowName t
    | .Constrained t tok body   => .Constrained (f t) tok (f body)
    | .Parens w                 => .Parens (f <$> w)  -- Wrapped type_e
    | .Error e                  => .Error e            -- e ≠ type_e, unchanged

  @[inline_if_reduce] def mapM [Monad m] (f : α → m β) : TypeF e α → m (TypeF e β)
    | .Var n                    => pure (.Var n)
    | .Constructor n            => pure (.Constructor n)
    | .Wildcard t               => pure (.Wildcard t)
    | .Hole n                   => pure (.Hole n)
    | .String t v       => pure (.String t v)
    | .Int p t v                => pure (.Int p t v)
    | .Row w                    => .Row <$> w.mapM (Row.mapM f)
    | .Record w                 => .Record <$> w.mapM (Row.mapM f)
    | .Forall o bs c body       => .Forall o <$> TypeF_Forall_Bindings.mapM f bs <*> pure c <*> f body
    | .Kinded t sep k           => .Kinded <$> f t <*> pure sep <*> f k
    | .App fn args              => .App <$> f fn <*> args.mapM f
    | .Op first ops             => .Op <$> f first <*> TypeF_Op_Ops.mapM f ops
    | .OpName n                 => pure (.OpName n)
    | .Arrow dom tok codom      => .Arrow <$> f dom <*> pure tok <*> f codom
    | .ArrowName t              => pure (.ArrowName t)
    | .Constrained t tok body   => .Constrained <$> f t <*> pure tok <*> f body
    | .Parens w                 => .Parens <$> w.mapM f
    | .Error e                  => pure (.Error e)

  @[simp] theorem sizeOf_row [SizeOf e] [SizeOf type_e] (w : Wrapped (PurescriptLanguageCstParser.Types.Row type_e)) : sizeOf w.value < sizeOf (TypeF.Row (e := e) (type_e := type_e) w) := by
    change sizeOf w.value < 1 + sizeOf w
    have := Wrapped.sizeOf_value w
    omega

  @[simp] theorem sizeOf_record [SizeOf e] [SizeOf type_e] (w : Wrapped (PurescriptLanguageCstParser.Types.Row type_e)) : sizeOf w.value < sizeOf (TypeF.Record (e := e) (type_e := type_e) w) := by
    change sizeOf w.value < 1 + sizeOf w
    have := Wrapped.sizeOf_value w
    omega

  @[simp] theorem sizeOf_forall_bindings [SizeOf e] [SizeOf type_e] (o bs c body) : sizeOf bs < sizeOf (TypeF.Forall (e := e) (type_e := type_e) o bs c body) := by
    change sizeOf bs < 1 + sizeOf o + sizeOf bs + sizeOf c + sizeOf body
    omega

  @[simp] theorem sizeOf_forall_body [SizeOf e] [SizeOf type_e] (o bs c body) : sizeOf body < sizeOf (TypeF.Forall (e := e) (type_e := type_e) o bs c body) := by
    change sizeOf body < 1 + sizeOf o + sizeOf bs + sizeOf c + sizeOf body
    omega

  @[simp] theorem sizeOf_kinded_type [SizeOf e] [SizeOf type_e] (t sep k) : sizeOf t < sizeOf (TypeF.Kinded (e := e) (type_e := type_e) t sep k) := by
    change sizeOf t < 1 + sizeOf t + sizeOf sep + sizeOf k
    omega

  @[simp] theorem sizeOf_kinded_kind [SizeOf e] [SizeOf type_e] (t sep k) : sizeOf k < sizeOf (TypeF.Kinded (e := e) (type_e := type_e) t sep k) := by
    change sizeOf k < 1 + sizeOf t + sizeOf sep + sizeOf k
    omega

  @[simp] theorem sizeOf_app_fn [SizeOf e] [SizeOf type_e] (fn args) : sizeOf fn < sizeOf (TypeF.App (e := e) (type_e := type_e) fn args) := by
    change sizeOf fn < 1 + sizeOf fn + sizeOf args
    omega

  @[simp] theorem sizeOf_app_args [SizeOf e] [SizeOf type_e] (fn args) : sizeOf args < sizeOf (TypeF.App (e := e) (type_e := type_e) fn args) := by
    change sizeOf args < 1 + sizeOf fn + sizeOf args
    omega

  @[simp] theorem sizeOf_op_first [SizeOf e] [SizeOf type_e] (first ops) : sizeOf first < sizeOf (TypeF.Op (e := e) (type_e := type_e) first ops) := by
    change sizeOf first < 1 + sizeOf first + sizeOf ops
    omega

  @[simp] theorem sizeOf_op_ops [SizeOf e] [SizeOf type_e] (first ops) : sizeOf ops < sizeOf (TypeF.Op (e := e) (type_e := type_e) first ops) := by
    change sizeOf ops < 1 + sizeOf first + sizeOf ops
    omega

  @[simp] theorem sizeOf_arrow_dom [SizeOf e] [SizeOf type_e] (d tok c) : sizeOf d < sizeOf (TypeF.Arrow (e := e) (type_e := type_e) d tok c) := by
    change sizeOf d < 1 + sizeOf d + sizeOf tok + sizeOf c
    omega

  @[simp] theorem sizeOf_arrow_codom [SizeOf e] [SizeOf type_e] (d tok c) : sizeOf c < sizeOf (TypeF.Arrow (e := e) (type_e := type_e) d tok c) := by
    change sizeOf c < 1 + sizeOf d + sizeOf tok + sizeOf c
    omega

  @[simp] theorem sizeOf_constrained_type [SizeOf e] [SizeOf type_e] (t tok b) : sizeOf t < sizeOf (TypeF.Constrained (e := e) (type_e := type_e) t tok b) := by
    change sizeOf t < 1 + sizeOf t + sizeOf tok + sizeOf b
    omega

  @[simp] theorem sizeOf_constrained_body [SizeOf e] [SizeOf type_e] (t tok b) : sizeOf b < sizeOf (TypeF.Constrained (e := e) (type_e := type_e) t tok b) := by
    change sizeOf b < 1 + sizeOf t + sizeOf tok + sizeOf b
    omega

  @[simp] theorem sizeOf_parens [SizeOf e] [SizeOf type_e] (w : Wrapped type_e) : sizeOf w.value < sizeOf (TypeF.Parens (e := e) (type_e := type_e) w) := by
    change sizeOf w.value < 1 + sizeOf w
    have := Wrapped.sizeOf_value w
    omega

  @[simp] theorem map_id (t : TypeF e α) : map (id : α → α) t = t := by
    cases t <;> simp_all only [map, id_map, id_map']
    · simp_all only [TypeF_Forall_Bindings.map, NonEmptyArray.map, id_map, id_eq, Forall.injEq, and_self, and_true,
      true_and]
      ext : 1
      · simp_all only
      · ext i hi₁ hi₂ : 1
        · simp_all only [Array.size_map]
        · simp_all only [Array.getElem_map, id_map]
    · simp_all only [id_eq]
    · simp_all only [id_eq, NonEmptyArray.map, Array.map_id_fun]
    · simp_all only [id_eq, TypeF_Op_Ops.map, NonEmptyArray.map, Array.map_id_fun']
    · simp_all only [id_eq]
    · simp_all only [id_eq]

  @[simp] theorem map_comp (g : α → β) (h : β → γ) (t : TypeF e α) :
    map (h ∘ g) t = map h (map g t) := by
    cases t
    · simp_all only [map]
    · simp_all only [map]
    · simp_all only [map]
    · simp_all only [map]
    · simp_all only [map]
    · simp_all only [map]
    · simp_all only [map, Functor.map_map, Row.injEq]
      rfl
    · simp_all only [map, Functor.map_map, Record.injEq]
      rfl
    · simp_all only [map, TypeF_Forall_Bindings.map, NonEmptyArray.map, Function.comp_apply, Functor.map_map,
      Array.map_map, Forall.injEq, NonEmptyArray.mk.injEq, Array.map_inj_left, and_self, and_true, true_and]
      apply And.intro
      · rfl
      · intro a a_1
        rfl
    · simp_all only [map, Function.comp_apply]
    · simp_all only [map, Function.comp_apply, NonEmptyArray.map, Array.map_map]
    · simp_all only [map, Function.comp_apply, TypeF_Op_Ops.map, NonEmptyArray.map, Array.map_map, Op.injEq,
      NonEmptyArray.mk.injEq, Array.map_inj_left, implies_true, and_self]
    · simp_all only [map]
    · simp_all only [map, Function.comp_apply]
    · simp_all only [map]
    · simp_all only [map, Function.comp_apply]
    · simp_all only [map, Functor.map_map, Parens.injEq]
      rfl
    · simp_all only [map]

  @[simp] def map_e (g : e → f) : TypeF e α → TypeF f α
    | .Row w => .Row { w with value := Row.map_e g w.value }
    | .Record w => .Record { w with value := Row.map_e g w.value }
    | .Error e_val => .Error (g e_val)
    -- All other cases don't contain 'e', so they are identities
    | .Var n => .Var n
    | .Constructor n => .Constructor n
    | .Wildcard t => .Wildcard t
    | .Hole n => .Hole n
    | .String t v => .String t v
    | .Int p t v => .Int p t v
    | .Forall o bs c body => .Forall o bs c body
    | .Kinded t sep k => .Kinded t sep k
    | .App fn args => .App fn args
    | .Op first ops => .Op first ops
    | .OpName n => .OpName n
    | .Arrow dom tok codom => .Arrow dom tok codom
    | .ArrowName t => .ArrowName t
    | .Constrained t tok body => .Constrained t tok body
    | .Parens w => .Parens w

  @[simp] theorem map_e_id (t : TypeF e α) : map_e (id : e → e) t = t := by
    cases t <;> simp only [map_e, id_eq, Row.map_e_id]

  @[simp] theorem map_e_comp (ge : e → f) (gf : f → g) (t : TypeF e α) :
    map_e (gf ∘ ge) t = map_e gf (map_e ge t) := by
    cases t <;> simp only [map_e, Row.map_e_comp, Function.comp_apply]

  @[simp] theorem map_map_e_comm (gf : e → f) (ga : α → β) (t : TypeF e α) :
    map ga (map_e gf t) = map_e gf (map ga t) := by
    cases t <;> rfl

  @[simp] def map_bi (ge : e → f) (ga : α → β) (t : TypeF e α) : TypeF f β :=
    map ga (map_e ge t)

  @[simp] theorem map_bi_id_id (t : TypeF e α) : map_bi (id : e → e) (id : α → α) t = t := by
    simp_all only [map_bi]
    cases t <;> simp only [map, map_e, NonEmptyArray.map, id_map, Array.map_id_fun, id_eq, Row.map_e_id, id_map, id_map']
    simp_all only [TypeF_Forall_Bindings.map, NonEmptyArray.map, id_map, Forall.injEq, and_self, and_true, true_and]
    ext : 1
    · simp_all only
    · ext i hi₁ hi₂ : 1
      · simp_all only [Array.size_map]
      · simp_all only [Array.getElem_map, id_map]
    · simp_all only [TypeF_Op_Ops.map, NonEmptyArray.map, id_eq, Array.map_id_fun']

  @[simp] theorem map_bi_comp (ge : e → f) (gf : f → g) (ga : α → β) (gb : β → γ) (t : TypeF e α) :
    map_bi (gf ∘ ge) (gb ∘ ga) t = map_bi gf gb (map_bi ge ga t) := by
    simp only [map_bi, map_comp, map_e_comp, map_map_e_comm]
end TypeF

instance : Functor (TypeF e) where
  map := TypeF.map

instance : LawfulFunctor (TypeF e) where
  map_const := rfl
  id_map t := by simp only [Functor.map, TypeF.map_id]
  comp_map g h t := by simp only [Functor.map, TypeF.map_comp]

generate_fixed Type_ (e : Type) from TypeF
  fill type_e with (Type_ e)
  deriving Repr, BEq

mutual
  def Type_.mapArray (g : e → f) (arr : Array (Type_ e)) : Array (Type_ f) :=
    arr.map (Type_.map g)
  termination_by sizeOf arr
  decreasing_by
    all_goals decreasing_trivial

  def Type_.mapNonEmpty (g : e → f) (args : NonEmptyArray (Type_ e))
      : NonEmptyArray (Type_ f) :=
    ⟨Type_.map g args.head, Type_.mapArray g args.tail⟩
  termination_by sizeOf args
  decreasing_by
    all_goals simp

  def TypeVarBinding.mapType [SizeOf name] (g : e → f)
      (binding : TypeVarBinding name (Type_ e)) : TypeVarBinding name (Type_ f) :=
    match binding with
    | .Kinded w => .Kinded { w with value := { w.value with value := Type_.map g w.value.value } }
    | .Name n   => .Name n
  termination_by sizeOf binding
  decreasing_by
    simp_wf
    have h1 := Wrapped.sizeOf_value w
    have h2 := Labeled.sizeOf_value w.value
    omega

  def TypeF_Forall_Bindings.mapTypeArray (g : e → f)
      (arr : Array (TypeVarBinding (Prefixed (Name Ident)) (Type_ e))) :
      Array (TypeVarBinding (Prefixed (Name Ident)) (Type_ f)) :=
    arr.attach.map (fun ⟨entry, _h⟩ => TypeVarBinding.mapType g entry)
  termination_by sizeOf arr
  decreasing_by
    simp_wf
    decreasing_trivial

  def TypeF_Forall_Bindings.mapType (g : e → f)
      (bs : TypeF_Forall_Bindings (Type_ e)) : TypeF_Forall_Bindings (Type_ f) :=
    ⟨TypeVarBinding.mapType g bs.head, TypeF_Forall_Bindings.mapTypeArray g bs.tail⟩
  termination_by sizeOf bs
  decreasing_by
    simp_wf
    decreasing_trivial

  def TypeF_Op_Ops.mapTypeElem (g : e → f)
      (op : QualifiedName Operator × Type_ e) : QualifiedName Operator × Type_ f :=
    (op.1, Type_.map g op.2)
  termination_by sizeOf op
  decreasing_by
    cases op
    simp
    omega

  def TypeF_Op_Ops.mapTypeArray (g : e → f)
      (arr : Array (QualifiedName Operator × Type_ e)) :
      Array (QualifiedName Operator × Type_ f) :=
    arr.map (TypeF_Op_Ops.mapTypeElem g)
  termination_by sizeOf arr
  decreasing_by
    all_goals decreasing_trivial

  def TypeF_Op_Ops.mapType (g : e → f)
      (ops : TypeF_Op_Ops (Type_ e)) : TypeF_Op_Ops (Type_ f) :=
    ⟨TypeF_Op_Ops.mapTypeElem g ops.head, TypeF_Op_Ops.mapTypeArray g ops.tail⟩
  termination_by sizeOf ops
  decreasing_by
    all_goals simp

  def Labeled.mapTypeValue [SizeOf α] (g : e → f)
      (l : Labeled α (Type_ e)) : Labeled α (Type_ f) :=
    { l with value := Type_.map g l.value }
  termination_by sizeOf l
  decreasing_by
    simp_wf

  def Separated.mapTypeTailElem [SizeOf α] (g : e → f)
      (entry : SourceToken × Labeled α (Type_ e)) :
      SourceToken × Labeled α (Type_ f) :=
    (entry.1, Labeled.mapTypeValue g entry.2)
  termination_by sizeOf entry
  decreasing_by
    cases entry
    simp
    omega

  def Separated.mapTypeTailArray [SizeOf α] (tail : Array (SourceToken × Labeled α (Type_ e)))
      (g : e → f) : Array (SourceToken × Labeled α (Type_ f)) :=
    tail.attach.map (fun ⟨entry, _h⟩ => Separated.mapTypeTailElem g entry)
  termination_by sizeOf tail
  decreasing_by
    simp_wf
    decreasing_trivial

  def Separated.mapType [SizeOf α] (g : e → f)
      (s : Separated (Labeled α (Type_ e))) : Separated (Labeled α (Type_ f)) :=
    ⟨Labeled.mapTypeValue g s.head, Separated.mapTypeTailArray s.tail g⟩
  termination_by sizeOf s
  decreasing_by
    simp_wf
    decreasing_trivial

  def Row.mapTypeTail (g : e → f)
      (tail : SourceToken × Type_ e) : SourceToken × Type_ f :=
    (tail.1, Type_.map g tail.2)
  termination_by sizeOf tail
  decreasing_by
    cases tail
    simp
    omega

  def Type_.map (g : e → f) : Type_ e → Type_ f
    | .Var n                 => .Var n
    | .Constructor n         => .Constructor n
    | .Wildcard t            => .Wildcard t
    | .Hole n                => .Hole n
    | .String t v    => .String t v
    | .Int p t v             => .Int p t v
    | .Kinded t sep k        => .Kinded (Type_.map g t) sep (Type_.map g k)
    | .Arrow d tok c         => .Arrow (Type_.map g d) tok (Type_.map g c)
    | .Constrained t tok b   => .Constrained (Type_.map g t) tok (Type_.map g b)
    | .Parens w              => .Parens { w with value := Type_.map g w.value }
    | .Error e               => .Error (g e)
    | .OpName n              => .OpName n
    | .ArrowName t           => .ArrowName t
    | .App fn args           => .App (Type_.map g fn) (Type_.mapNonEmpty g args)
    | .Forall o bs c body    => .Forall o (TypeF_Forall_Bindings.mapType g bs) c (Type_.map g body)
    | .Op first ops          => .Op (Type_.map g first) (TypeF_Op_Ops.mapType g ops)
    | .Row ⟨open_, r, close⟩ => .Row ⟨open_, Row.mapType g r, close⟩
    | .Record ⟨open_, r, close⟩ => .Record ⟨open_, Row.mapType g r, close⟩
  termination_by t => sizeOf t
  decreasing_by
    · simp_all only [Type_.Kinded.sizeOf_spec]
      omega
    · simp_all only [Type_.Kinded.sizeOf_spec, Nat.lt_add_left_iff_pos]
      omega
    · simp_all only [Type_.Arrow.sizeOf_spec]
      omega
    · simp_all only [Type_.Arrow.sizeOf_spec, Nat.lt_add_left_iff_pos]
      omega
    · simp_all only [Type_.Constrained.sizeOf_spec]
      omega
    · simp_all only [Type_.Constrained.sizeOf_spec, Nat.lt_add_left_iff_pos]
      omega
    · simp_all only [Type_.Parens.sizeOf_spec]
      have := Wrapped.sizeOf_value w
      omega
    · simp_all only [Type_.App.sizeOf_spec]
      omega
    · simp_all only [Type_.App.sizeOf_spec]
      omega
    · simp_all only [Type_.Forall.sizeOf_spec]
      omega
    · simp_all only [Type_.Forall.sizeOf_spec, Nat.lt_add_left_iff_pos]
      omega
    · simp_all only [Type_.Op.sizeOf_spec]
      omega
    · simp_all only [Type_.Op.sizeOf_spec]
      omega
    · simp_all only [Type_.Row.sizeOf_spec]
      have h : sizeOf r < sizeOf (Wrapped.mk open_ r close) := by
        simpa only [Wrapped.mk.sizeOf_spec] using (Wrapped.sizeOf_value (Wrapped.mk open_ r close))
      omega
    · simp_all only [Type_.Record.sizeOf_spec]
      have h : sizeOf r < sizeOf (Wrapped.mk open_ r close) := by
        simpa only [Wrapped.mk.sizeOf_spec] using (Wrapped.sizeOf_value (Wrapped.mk open_ r close))
      omega

  def Row.mapType (g : e → f) (r : Row (Type_ e))
      : Row (Type_ f) :=
    match r with
    | { labels := none, tail := none } => { labels := none, tail := none }
    | { labels := some labels, tail := none } =>
        { labels := some (Separated.mapType g labels), tail := none }
    | { labels := none, tail := some tail } =>
        { labels := none, tail := some (Row.mapTypeTail g tail) }
    | { labels := some labels, tail := some tail } =>
        { labels := some (Separated.mapType g labels), tail := some (Row.mapTypeTail g tail) }
  termination_by sizeOf r
  decreasing_by
    · simp_wf
      decreasing_trivial
    · simp_wf
      decreasing_trivial
    · simp_wf
      decreasing_trivial
    · simp_wf
      decreasing_trivial
end

mutual
  @[simp] def Type_.mapM [Monad m] (g : e → m f) : Type_ e → m (Type_ f)
    | .Var n                 => pure (.Var n)
    | .Constructor n         => pure (.Constructor n)
    | .Wildcard t            => pure (.Wildcard t)
    | .Hole n                => pure (.Hole n)
    | .String t v    => pure (.String t v)
    | .Int p t v             => pure (.Int p t v)
    | .Kinded t sep k        => .Kinded <$> Type_.mapM g t <*> pure sep <*> Type_.mapM g k
    | .Arrow d tok c         => .Arrow <$> Type_.mapM g d <*> pure tok <*> Type_.mapM g c
    | .Constrained t tok b   => .Constrained <$> Type_.mapM g t <*> pure tok <*> Type_.mapM g b
    | .Parens w              => .Parens <$> (Wrapped.mk w.open_ <$> Type_.mapM g w.value <*> pure w.close)
    | .Error e               => .Error <$> g e
    | .OpName n              => pure (.OpName n)
    | .ArrowName t           => pure (.ArrowName t)
    | .App fn args           => .App <$> Type_.mapM g fn <*> Type_.mapMNonEmpty g args
    | .Forall o bs c body    => .Forall o <$> TypeF_Forall_Bindings.mapMType g bs <*> pure c <*> Type_.mapM g body
    | .Op first ops          => .Op <$> Type_.mapM g first <*> TypeF_Op_Ops.mapMType g ops
    | .Row w                 => .Row <$> (Wrapped.mk w.open_ <$> Row.mapMType g w.value <*> pure w.close)
    | .Record w              => .Record <$> (Wrapped.mk w.open_ <$> Row.mapMType g w.value <*> pure w.close)
  termination_by t => sizeOf t
  decreasing_by
    · simp only [Type_.Kinded.sizeOf_spec]; omega
    · simp only [Type_.Kinded.sizeOf_spec, Nat.lt_add_left_iff_pos]; omega
    · simp only [Type_.Arrow.sizeOf_spec]; omega
    · simp only [Type_.Arrow.sizeOf_spec, Nat.lt_add_left_iff_pos]; omega
    · simp only [Type_.Constrained.sizeOf_spec]; omega
    · simp only [Type_.Constrained.sizeOf_spec, Nat.lt_add_left_iff_pos]; omega
    · simp_all only [Type_.Parens.sizeOf_spec]
      have := Wrapped.sizeOf_value w
      omega
    · simp_all only [Type_.App.sizeOf_spec]
      omega
    · simp_all only [Type_.App.sizeOf_spec]
      omega
    · simp_all only [Type_.Forall.sizeOf_spec]
      omega
    · simp_all only [Type_.Forall.sizeOf_spec, Nat.lt_add_left_iff_pos]
      omega
    · simp_all only [Type_.Op.sizeOf_spec]
      omega
    · simp_all only [Type_.Op.sizeOf_spec]
      omega
    · simp_all only [Type_.Row.sizeOf_spec]
      have := Wrapped.sizeOf_value w
      omega
    · simp_all only [Type_.Record.sizeOf_spec]
      have := Wrapped.sizeOf_value w
      omega

  def Type_.mapMArray [Monad m] (g : e → m f) (arr : Array (Type_ e)) : m (Array (Type_ f)) :=
    arr.attach.mapM (fun ⟨entry, _h⟩ => Type_.mapM g entry)
  termination_by sizeOf arr
  decreasing_by
    all_goals decreasing_trivial

  def Type_.mapMNonEmpty [Monad m] (g : e → m f) (args : NonEmptyArray (Type_ e))
      : m (NonEmptyArray (Type_ f)) := do
    let h ← Type_.mapM g args.head
    let t ← Type_.mapMArray g args.tail
    pure ⟨h, t⟩
  termination_by sizeOf args
  decreasing_by
    all_goals simp

  def TypeVarBinding.mapMType [Monad m] [SizeOf name] (g : e → m f)
      (binding : TypeVarBinding name (Type_ e)) : m (TypeVarBinding name (Type_ f)) :=
    match binding with
    | .Kinded w => .Kinded <$> (Wrapped.mk w.open_ <$> (Labeled.mk w.value.label w.value.separator <$> Type_.mapM g w.value.value) <*> pure w.close)
    | .Name n   => pure (.Name n)
  termination_by sizeOf binding
  decreasing_by
    simp_wf
    have h1 := Wrapped.sizeOf_value w
    have h2 := Labeled.sizeOf_value w.value
    omega

  def TypeF_Forall_Bindings.mapMTypeArray [Monad m] (g : e → m f)
      (arr : Array (TypeVarBinding (Prefixed (Name Ident)) (Type_ e))) :
      m (Array (TypeVarBinding (Prefixed (Name Ident)) (Type_ f))) :=
    arr.attach.mapM (fun ⟨entry, _h⟩ => TypeVarBinding.mapMType g entry)
  termination_by sizeOf arr
  decreasing_by
    simp_wf
    decreasing_trivial

  def TypeF_Forall_Bindings.mapMType [Monad m] (g : e → m f)
      (bs : TypeF_Forall_Bindings (Type_ e)) : m (TypeF_Forall_Bindings (Type_ f)) := do
    let h ← TypeVarBinding.mapMType g bs.head
    let t ← TypeF_Forall_Bindings.mapMTypeArray g bs.tail
    pure ⟨h, t⟩
  termination_by sizeOf bs
  decreasing_by
    simp_wf
    decreasing_trivial

  def TypeF_Op_Ops.mapMTypeElem [Monad m] (g : e → m f)
      (op : QualifiedName Operator × Type_ e) : m (QualifiedName Operator × Type_ f) := do
    let v ← Type_.mapM g op.2
    pure (op.1, v)
  termination_by sizeOf op
  decreasing_by
    cases op
    simp
    omega

  def TypeF_Op_Ops.mapMTypeArray [Monad m] (g : e → m f)
      (arr : Array (QualifiedName Operator × Type_ e)) :
      m (Array (QualifiedName Operator × Type_ f)) :=
    arr.attach.mapM (fun ⟨entry, _h⟩ => TypeF_Op_Ops.mapMTypeElem g entry)
  termination_by sizeOf arr
  decreasing_by
    simp_wf
    decreasing_trivial

  def TypeF_Op_Ops.mapMType [Monad m] (g : e → m f)
      (ops : TypeF_Op_Ops (Type_ e)) : m (TypeF_Op_Ops (Type_ f)) := do
    let h ← TypeF_Op_Ops.mapMTypeElem g ops.head
    let t ← TypeF_Op_Ops.mapMTypeArray g ops.tail
    pure ⟨h, t⟩
  termination_by sizeOf ops
  decreasing_by
    simp_wf
    decreasing_trivial

  def Labeled.mapMTypeValue [Monad m] [SizeOf α] (g : e → m f)
      (l : Labeled α (Type_ e)) : m (Labeled α (Type_ f)) :=
    Labeled.mk l.label l.separator <$> Type_.mapM g l.value
  termination_by sizeOf l
  decreasing_by
    simp_wf

  def Separated.mapMTypeTailElem [Monad m] [SizeOf α] (g : e → m f)
      (entry : SourceToken × Labeled α (Type_ e)) :
      m (SourceToken × Labeled α (Type_ f)) := do
    let v ← Labeled.mapMTypeValue g entry.2
    pure (entry.1, v)
  termination_by sizeOf entry
  decreasing_by
    cases entry
    simp
    omega

  def Separated.mapMTypeTailArray [Monad m] [SizeOf α] (tail : Array (SourceToken × Labeled α (Type_ e)))
      (g : e → m f) : m (Array (SourceToken × Labeled α (Type_ f))) :=
    tail.attach.mapM (fun ⟨entry, _h⟩ => Separated.mapMTypeTailElem g entry)
  termination_by sizeOf tail
  decreasing_by
    simp_wf
    decreasing_trivial

  def Separated.mapMType [Monad m] [SizeOf α] (g : e → m f)
      (s : Separated (Labeled α (Type_ e))) : m (Separated (Labeled α (Type_ f))) := do
    let h ← Labeled.mapMTypeValue g s.head
    let t ← Separated.mapMTypeTailArray s.tail g
    pure ⟨h, t⟩
  termination_by sizeOf s
  decreasing_by
    simp_wf
    decreasing_trivial

  def Row.mapMTypeTail [Monad m] (g : e → m f)
      (tail : SourceToken × Type_ e) : m (SourceToken × Type_ f) := do
    let v ← Type_.mapM g tail.2
    pure (tail.1, v)
  termination_by sizeOf tail
  decreasing_by
    cases tail
    simp
    omega

  def Row.mapMType [Monad m] (g : e → m f) (r : Row (Type_ e))
      : m (Row (Type_ f)) :=
    match r with
    | { labels := none, tail := none } => pure { labels := none, tail := none }
    | { labels := some labels, tail := none } => do
        let l ← Separated.mapMType g labels
        pure { labels := some l, tail := none }
    | { labels := none, tail := some tail } => do
        let t ← Row.mapMTypeTail g tail
        pure { labels := none, tail := some t }
    | { labels := some labels, tail := some tail } => do
        let l ← Separated.mapMType g labels
        let t ← Row.mapMTypeTail g tail
        pure { labels := some l, tail := some t }
  termination_by sizeOf r
  decreasing_by
    · simp_wf
      decreasing_trivial
    · simp_wf
      decreasing_trivial
    · simp_wf
      decreasing_trivial
    · simp_wf
      decreasing_trivial
end

mutual
  @[simp] theorem TypeVarBinding.mapType_id [SizeOf name] (b : TypeVarBinding name (Type_ e)) : TypeVarBinding.mapType id b = b := by
    cases b
    · rename_i w; cases w; rename_i o l c; cases l
      simp only [TypeVarBinding.mapType, TypeVarBinding.Kinded.injEq, Wrapped.mk.injEq, Labeled.mk.injEq, and_true, true_and]
      apply Type_.map_id
    · simp_all only [TypeVarBinding.mapType]

  @[simp] theorem TypeF_Forall_Bindings.mapTypeArray_id (arr : Array (TypeVarBinding (Prefixed (Name Ident)) (Type_ e))) : TypeF_Forall_Bindings.mapTypeArray id arr = arr := by
    simp only [TypeF_Forall_Bindings.mapTypeArray]
    apply Array.ext
    · simp only [Array.size_map, Array.size_attach]
    · intro i hi₁ hi₂
      simp only [Array.getElem_map, Array.getElem_attach]
      apply TypeVarBinding.mapType_id

  @[simp] theorem TypeF_Forall_Bindings.mapType_id (bs : TypeF_Forall_Bindings (Type_ e)) : TypeF_Forall_Bindings.mapType id bs = bs := by
    cases bs
    simp only [TypeF_Forall_Bindings.mapType, NonEmptyArray.mk.injEq]
    apply And.intro
    · apply TypeVarBinding.mapType_id
    · apply TypeF_Forall_Bindings.mapTypeArray_id

  @[simp] theorem TypeF_Op_Ops.mapTypeElem_id (op : QualifiedName Operator × Type_ e) : TypeF_Op_Ops.mapTypeElem id op = op := by
    cases op
    simp only [TypeF_Op_Ops.mapTypeElem, Prod.mk.injEq, true_and]
    apply Type_.map_id

  @[simp] theorem TypeF_Op_Ops.mapTypeArray_id (arr : Array (QualifiedName Operator × Type_ e)) : TypeF_Op_Ops.mapTypeArray id arr = arr := by
    simp only [TypeF_Op_Ops.mapTypeArray]
    apply Array.ext
    · simp only [Array.size_map]
    · intro i hi₁ hi₂
      simp only [Array.getElem_map]
      apply TypeF_Op_Ops.mapTypeElem_id

  @[simp] theorem TypeF_Op_Ops.mapType_id (ops : TypeF_Op_Ops (Type_ e)) : TypeF_Op_Ops.mapType id ops = ops := by
    cases ops
    simp only [TypeF_Op_Ops.mapType, NonEmptyArray.mk.injEq]
    apply And.intro
    · apply TypeF_Op_Ops.mapTypeElem_id
    · apply TypeF_Op_Ops.mapTypeArray_id

  @[simp] theorem Labeled.mapTypeValue_id [SizeOf α] (l : Labeled α (Type_ e)) : Labeled.mapTypeValue id l = l := by
    cases l
    simp only [Labeled.mapTypeValue, Labeled.mk.injEq, true_and]
    apply Type_.map_id

  @[simp] theorem Separated.mapTypeTailElem_id [SizeOf α] (entry : SourceToken × Labeled α (Type_ e)) : Separated.mapTypeTailElem id entry = entry := by
    cases entry
    simp only [Separated.mapTypeTailElem, Prod.mk.injEq, true_and]
    apply Labeled.mapTypeValue_id

  @[simp] theorem Separated.mapTypeTailArray_id [SizeOf α] (tail : Array (SourceToken × Labeled α (Type_ e))) : Separated.mapTypeTailArray tail id = tail := by
    simp only [Separated.mapTypeTailArray]
    apply Array.ext
    · simp only [Array.size_map, Array.size_attach]
    · intro i hi₁ hi₂
      simp only [Array.getElem_map, Array.getElem_attach]
      apply Separated.mapTypeTailElem_id

  @[simp] theorem Separated.mapType_id [SizeOf α] (s : Separated (Labeled α (Type_ e))) : Separated.mapType id s = s := by
    cases s
    simp only [Separated.mapType, Separated.mk.injEq]
    apply And.intro
    · apply Labeled.mapTypeValue_id
    · apply Separated.mapTypeTailArray_id

  @[simp] theorem Row.mapTypeTail_id (tail : SourceToken × Type_ e) : Row.mapTypeTail id tail = tail := by
    cases tail
    simp only [Row.mapTypeTail, Prod.mk.injEq, true_and]
    apply Type_.map_id

  @[simp] theorem Row.mapType_id (r : Row (Type_ e)) : Row.mapType id r = r := by
    cases r with | mk labels tail =>
      cases labels <;> cases tail
      · simp_all only [Row.mapType]
      · rename_i val
        simp only [Row.mapType, Row.mk.injEq, Option.some.injEq, true_and]
        apply Row.mapTypeTail_id
      · rename_i val
        simp only [Row.mapType, Row.mk.injEq, Option.some.injEq, and_true]
        apply Separated.mapType_id
      · rename_i val_1 val_2
        simp only [Row.mapType, Row.mk.injEq, Option.some.injEq]
        apply And.intro
        · apply Separated.mapType_id
        · apply Row.mapTypeTail_id

  @[simp] theorem Type_.mapArray_id (arr : Array (Type_ e)) : Type_.mapArray id arr = arr := by
    simp only [Type_.mapArray]
    apply Array.ext
    · simp only [Array.size_map]
    · intro i hi₁ hi₂
      simp only [Array.getElem_map]
      apply Type_.map_id

  @[simp] theorem Type_.mapNonEmpty_id (args : NonEmptyArray (Type_ e)) : Type_.mapNonEmpty id args = args := by
    cases args
    simp only [Type_.mapNonEmpty, NonEmptyArray.mk.injEq]
    apply And.intro
    · apply Type_.map_id
    · apply Type_.mapArray_id

  @[simp] theorem Type_.map_id (t : Type_ e) : Type_.map id t = t := by
    cases t
    · simp_all only [Type_.map]
    · simp_all only [Type_.map]
    · simp_all only [Type_.map]
    · simp_all only [Type_.map]
    · simp_all only [Type_.map]
    · simp_all only [Type_.map]
    · rename_i wrapped
      cases wrapped; simp only [Type_.map, Type_.Row.injEq, Wrapped.mk.injEq, and_true, true_and]
      apply Row.mapType_id
    · rename_i wrapped
      cases wrapped; simp only [Type_.map, Type_.Record.injEq, Wrapped.mk.injEq, and_true, true_and]
      apply Row.mapType_id
    · rename_i o bs c body
      simp only [Type_.map, Type_.Forall.injEq, true_and]
      apply And.intro
      · apply TypeF_Forall_Bindings.mapType_id
      · apply Type_.map_id
    · rename_i t sep k
      simp only [Type_.map, Type_.Kinded.injEq, true_and]
      apply And.intro
      · apply Type_.map_id
      · apply Type_.map_id
    · rename_i fn args
      simp only [Type_.map, Type_.App.injEq]
      apply And.intro
      · apply Type_.map_id
      · apply Type_.mapNonEmpty_id
    · rename_i first ops
      simp only [Type_.map, Type_.Op.injEq]
      apply And.intro
      · apply Type_.map_id
      · apply TypeF_Op_Ops.mapType_id
    · simp_all only [Type_.map]
    · rename_i dom tok codom
      simp only [Type_.map, Type_.Arrow.injEq, true_and]
      apply And.intro
      · apply Type_.map_id
      · apply Type_.map_id
    · simp_all only [Type_.map]
    · rename_i t tok b
      simp only [Type_.map, Type_.Constrained.injEq, true_and]
      apply And.intro
      · apply Type_.map_id
      · apply Type_.map_id
    · rename_i w
      cases w; simp only [Type_.map, Type_.Parens.injEq, Wrapped.mk.injEq, and_true, true_and]
      apply Type_.map_id
    · simp_all only [Type_.map, id_eq]
end

mutual
  @[simp] theorem TypeVarBinding.mapType_comp [SizeOf name] (ge : e → f) (gf : f → g) (b : TypeVarBinding name (Type_ e)) :
      TypeVarBinding.mapType (gf ∘ ge) b = TypeVarBinding.mapType gf (TypeVarBinding.mapType ge b) := by
    cases b
    · rename_i w; cases w; rename_i o l c; cases l
      simp only [TypeVarBinding.mapType, TypeVarBinding.Kinded.injEq, Wrapped.mk.injEq, Labeled.mk.injEq, and_true, true_and]
      apply Type_.map_comp
    · simp_all only [TypeVarBinding.mapType]

  @[simp] theorem TypeF_Forall_Bindings.mapTypeArray_comp (ge : e → f) (gf : f → g) (arr : Array (TypeVarBinding (Prefixed (Name Ident)) (Type_ e))) :
      TypeF_Forall_Bindings.mapTypeArray (gf ∘ ge) arr = TypeF_Forall_Bindings.mapTypeArray gf (TypeF_Forall_Bindings.mapTypeArray ge arr) := by
    simp only [TypeF_Forall_Bindings.mapTypeArray]
    apply Array.ext
    · simp only [Array.size_map, Array.size_attach]
    · intro i hi₁ hi₂
      simp only [Array.getElem_map, Array.getElem_attach]
      apply TypeVarBinding.mapType_comp

  @[simp] theorem TypeF_Forall_Bindings.mapType_comp (ge : e → f) (gf : f → g) (bs : TypeF_Forall_Bindings (Type_ e)) :
      TypeF_Forall_Bindings.mapType (gf ∘ ge) bs = TypeF_Forall_Bindings.mapType gf (TypeF_Forall_Bindings.mapType ge bs) := by
    cases bs
    simp only [TypeF_Forall_Bindings.mapType, NonEmptyArray.mk.injEq]
    apply And.intro
    · apply TypeVarBinding.mapType_comp
    · apply TypeF_Forall_Bindings.mapTypeArray_comp

  @[simp] theorem TypeF_Op_Ops.mapTypeElem_comp (ge : e → f) (gf : f → g) (op : QualifiedName Operator × Type_ e) :
      TypeF_Op_Ops.mapTypeElem (gf ∘ ge) op = TypeF_Op_Ops.mapTypeElem gf (TypeF_Op_Ops.mapTypeElem ge op) := by
    cases op
    simp only [TypeF_Op_Ops.mapTypeElem, Prod.mk.injEq, true_and]
    apply Type_.map_comp

  @[simp] theorem TypeF_Op_Ops.mapTypeArray_comp (ge : e → f) (gf : f → g) (arr : Array (QualifiedName Operator × Type_ e)) :
      TypeF_Op_Ops.mapTypeArray (gf ∘ ge) arr = TypeF_Op_Ops.mapTypeArray gf (TypeF_Op_Ops.mapTypeArray ge arr) := by
    simp only [TypeF_Op_Ops.mapTypeArray]
    apply Array.ext
    · simp only [Array.size_map]
    · intro i hi₁ hi₂
      simp only [Array.getElem_map]
      apply TypeF_Op_Ops.mapTypeElem_comp

  @[simp] theorem TypeF_Op_Ops.mapType_comp (ge : e → f) (gf : f → g) (ops : TypeF_Op_Ops (Type_ e)) :
      TypeF_Op_Ops.mapType (gf ∘ ge) ops = TypeF_Op_Ops.mapType gf (TypeF_Op_Ops.mapType ge ops) := by
    cases ops
    simp only [TypeF_Op_Ops.mapType, NonEmptyArray.mk.injEq]
    apply And.intro
    · apply TypeF_Op_Ops.mapTypeElem_comp
    · apply TypeF_Op_Ops.mapTypeArray_comp

  @[simp] theorem Labeled.mapTypeValue_comp [SizeOf α] (ge : e → f) (gf : f → g) (l : Labeled α (Type_ e)) :
      Labeled.mapTypeValue (gf ∘ ge) l = Labeled.mapTypeValue gf (Labeled.mapTypeValue ge l) := by
    cases l
    simp only [Labeled.mapTypeValue, Labeled.mk.injEq, true_and]
    apply Type_.map_comp

  @[simp] theorem Separated.mapTypeTailElem_comp [SizeOf α] (ge : e → f) (gf : f → g) (entry : SourceToken × Labeled α (Type_ e)) :
      Separated.mapTypeTailElem (gf ∘ ge) entry = Separated.mapTypeTailElem gf (Separated.mapTypeTailElem ge entry) := by
    cases entry
    simp only [Separated.mapTypeTailElem, Prod.mk.injEq, true_and]
    apply Labeled.mapTypeValue_comp

  @[simp] theorem Separated.mapTypeTailArray_comp [SizeOf α] (ge : e → f) (gf : f → g) (tail : Array (SourceToken × Labeled α (Type_ e))) :
      Separated.mapTypeTailArray tail (gf ∘ ge) = Separated.mapTypeTailArray (Separated.mapTypeTailArray tail ge) gf := by
    simp only [Separated.mapTypeTailArray]
    apply Array.ext
    · simp only [Array.size_map, Array.size_attach]
    · intro i hi₁ hi₂
      simp only [Array.getElem_map, Array.getElem_attach]
      apply Separated.mapTypeTailElem_comp

  @[simp] theorem Separated.mapType_comp [SizeOf α] (ge : e → f) (gf : f → g) (s : Separated (Labeled α (Type_ e))) :
      Separated.mapType (gf ∘ ge) s = Separated.mapType gf (Separated.mapType ge s) := by
    cases s
    simp only [Separated.mapType, Separated.mk.injEq]
    apply And.intro
    · apply Labeled.mapTypeValue_comp
    · apply Separated.mapTypeTailArray_comp

  @[simp] theorem Row.mapTypeTail_comp (ge : e → f) (gf : f → g) (tail : SourceToken × Type_ e) :
      Row.mapTypeTail (gf ∘ ge) tail = Row.mapTypeTail gf (Row.mapTypeTail ge tail) := by
    cases tail
    simp only [Row.mapTypeTail, Prod.mk.injEq, true_and]
    apply Type_.map_comp

  @[simp] theorem Row.mapType_comp (ge : e → f) (gf : f → g) (r : Row (Type_ e)) :
      Row.mapType (gf ∘ ge) r = Row.mapType gf (Row.mapType ge r) := by
    cases r with | mk labels tail =>
      cases labels <;> cases tail
      · simp_all only [Row.mapType]
      · rename_i val
        simp only [Row.mapType, Row.mk.injEq, Option.some.injEq, true_and]
        apply Row.mapTypeTail_comp
      · rename_i val
        simp only [Row.mapType, Row.mk.injEq, Option.some.injEq, and_true]
        apply Separated.mapType_comp
      · rename_i val_1 val_2
        simp only [Row.mapType, Row.mk.injEq, Option.some.injEq]
        apply And.intro
        · apply Separated.mapType_comp
        · apply Row.mapTypeTail_comp

  @[simp] theorem Type_.mapArray_comp (ge : e → f) (gf : f → g) (arr : Array (Type_ e)) :
      Type_.mapArray (gf ∘ ge) arr = Type_.mapArray gf (Type_.mapArray ge arr) := by
    simp only [Type_.mapArray]
    apply Array.ext
    · simp only [Array.size_map]
    · intro i hi₁ hi₂
      simp only [Array.getElem_map]
      apply Type_.map_comp

  @[simp] theorem Type_.mapNonEmpty_comp (ge : e → f) (gf : f → g) (args : NonEmptyArray (Type_ e)) :
      Type_.mapNonEmpty (gf ∘ ge) args = Type_.mapNonEmpty gf (Type_.mapNonEmpty ge args) := by
    cases args
    simp only [Type_.mapNonEmpty, NonEmptyArray.mk.injEq]
    apply And.intro
    · apply Type_.map_comp
    · apply Type_.mapArray_comp

  @[simp] theorem Type_.map_comp (ge : e → f) (gf : f → g) (t : Type_ e) :
      Type_.map (gf ∘ ge) t = Type_.map gf (Type_.map ge t) := by
    cases t
    · simp_all only [Type_.map]
    · simp_all only [Type_.map]
    · simp_all only [Type_.map]
    · simp_all only [Type_.map]
    · simp_all only [Type_.map]
    · simp_all only [Type_.map]
    · rename_i wrapped
      cases wrapped; simp only [Type_.map]
      simp_all only [Type_.Row.injEq, Wrapped.mk.injEq, and_true, true_and]
      apply Row.mapType_comp
    · rename_i wrapped
      cases wrapped; simp only [Type_.map]
      simp_all only [Type_.Record.injEq, Wrapped.mk.injEq, and_true, true_and]
      apply Row.mapType_comp
    · rename_i o bs c body
      simp only [Type_.map]
      simp_all only [Type_.Forall.injEq, true_and]
      apply And.intro
      · apply TypeF_Forall_Bindings.mapType_comp
      · apply Type_.map_comp
    · rename_i t sep k
      simp only [Type_.map]
      simp_all only [Type_.Kinded.injEq, true_and]
      apply And.intro
      · apply Type_.map_comp
      · apply Type_.map_comp
    · rename_i fn args
      simp only [Type_.map]
      simp_all only [Type_.App.injEq]
      apply And.intro
      · apply Type_.map_comp
      · apply Type_.mapNonEmpty_comp
    · rename_i first ops
      simp only [Type_.map]
      simp_all only [Type_.Op.injEq]
      apply And.intro
      · apply Type_.map_comp
      · apply TypeF_Op_Ops.mapType_comp
    · simp_all only [Type_.map]
    · rename_i dom tok codom
      simp only [Type_.map]
      simp_all only [Type_.Arrow.injEq, true_and]
      apply And.intro
      · apply Type_.map_comp
      · apply Type_.map_comp
    · simp_all only [Type_.map]
    · rename_i t tok b
      simp only [Type_.map]
      simp_all only [Type_.Constrained.injEq, true_and]
      apply And.intro
      · apply Type_.map_comp
      · apply Type_.map_comp
    · rename_i w
      cases w; simp only [Type_.map]
      simp_all only [Type_.Parens.injEq, Wrapped.mk.injEq, and_true, true_and]
      apply Type_.map_comp
    · simp_all only [Type_.map, Function.comp_apply]
end

@[simp] theorem functor_map_id [Functor f] [LawfulFunctor f] : Functor.map (id : α → α) = (id : f α → f α) := by funext x; exact LawfulFunctor.id_map x
@[simp] theorem functor_map_comp [Functor f] [LawfulFunctor f] (g : α → β) (h : β → γ) : Functor.map (h ∘ g) = (Functor.map h ∘ Functor.map g : f α → f γ) := by funext x; exact LawfulFunctor.comp_map g h x

instance : Functor Type_ where map := Type_.map

instance : LawfulFunctor Type_ where
  map_const := rfl
  id_map t := by
    simpa only using Type_.map_id t
  comp_map g h t := by
    simpa only [Functor.map] using Type_.map_comp g h t

end
end PurescriptLanguageCstParser.Types
