module

public import PurescriptLanguageCstParser.Types.PType.Basic
import Init.Data.Array.Subarray

@[expose] public section
namespace PurescriptLanguageCstParser.Range.TokenList

open PurescriptLanguageCstParser.Types

inductive TokenList
  | TokenEmpty
  | TokenCons  (token : SourceToken) (rest  : TokenList)
  | TokenWrap  (open_ : SourceToken) (inner : TokenList) (close : SourceToken)
  | TokenAppend (left : TokenList) (right : TokenList)
  | TokenArray  (tokens : Subarray SourceToken) (hnonempty : tokens.size != 0)

instance : Append TokenList where
  append a b := match a, b with
    | _, .TokenEmpty => a
    | .TokenEmpty, b => b
    | a, b           => .TokenAppend a b

def singleton (a : SourceToken)                              : TokenList := .TokenCons a .TokenEmpty

def fromArray (arr : Array SourceToken) : TokenList :=
  if _h : arr.size == 0 then .TokenEmpty
  else .TokenArray arr.toSubarray (by grind only [= Subarray.size_eq, = Array.stop_toSubarray, = Array.start_toSubarray, = Nat.min_def])

-- instance : Inhabited SourceToken where
--   default := { range := { start := ⟨0,0⟩, end_ := ⟨0,0⟩ }, leadingComments := #[], trailingComments := #[], value := .LeftParen }

-- ── Single structural traversal ─────────────────────────────────────────────
-- Everything that needs all tokens is built on this.
def TokenList.foldl (f : β → SourceToken → β) (init : β) : TokenList → β
  | .TokenEmpty      => init
  | .TokenCons a b   => foldl f (f init a) b
  | .TokenWrap a i c => f (foldl f (f init a) i) c
  | .TokenAppend a b => foldl f (foldl f init a) b
  | .TokenArray arr _ => arr.foldl f init

 def TokenList.foldMap (op : ω → ω → ω) (f : SourceToken → ω) (empty : ω) (tl : TokenList) : ω :=
   tl.foldl (fun acc t => op acc (f t)) empty

def toArray (tl : TokenList) : Array SourceToken :=
  tl.foldl (· |>.push ·) #[]

-- ── uncons ──────────────────────────────────────────────────────────────────
-- Necessarily separate from foldl: different semantics (returns rest as TokenList).
-- arr.get? is safe (returns Option); no unsafe indexing.
inductive UnconsToken
  | UnconsDone
  | UnconsMore (token : SourceToken) (rest : TokenList)

def uncons : TokenList → UnconsToken
  | .TokenEmpty         => .UnconsDone
  | .TokenCons a b      => .UnconsMore a b
  | .TokenWrap a i c    => .UnconsMore a (i ++ .TokenCons c .TokenEmpty)
  | .TokenAppend a b    =>
      match uncons a with
      | .UnconsDone          => uncons b          -- a was empty, try b
      | .UnconsMore tok rest => .UnconsMore tok (rest ++ b)
  | .TokenArray arr h =>
      match arr[0]? with
      | none     => .UnconsDone
      | some tok => .UnconsMore tok
          (if h1 : arr.size = 1 then
             .TokenEmpty
           else
             .TokenArray (arr.drop 1) (by
               rw [Subarray.size_drop]

               -- 1. Extract the mathematical fact that size ≠ 0
               have h0 : arr.size ≠ 0 := by
                 intro c
                 simp_all

               -- 2. Let omega do the math in Prop
               have hz : arr.size - 1 ≠ 0 := by omega

               -- 3. Translate back to the boolean `!= 0` goal by evaluating it
               generalize arr.size - 1 = n at hz ⊢
               cases n
               · contradiction -- if n = 0, it contradicts `hz`
               · rfl           -- if n = m + 1, `(m + 1 != 0) = true` is definitionally true
             ))
  termination_by tl => sizeOf tl


-- ── head ────────────────────────────────────────────────────────────────────
-- Shares arr.get? convention with uncons.
def head : TokenList → Option SourceToken
  | .TokenEmpty       => none
  | .TokenCons a _    => some a
  | .TokenWrap a _ _  => some a
  | .TokenAppend l _  => head l
  | .TokenArray arr _ => arr[0]?

end PurescriptLanguageCstParser.Range.TokenList
