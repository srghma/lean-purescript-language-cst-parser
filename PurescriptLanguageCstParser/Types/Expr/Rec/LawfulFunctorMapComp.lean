module

import NonEmpty.ArrayCorrectByConstruction
import NonEmpty.String
import Aesop
import PurescriptLanguageCstParser.Types.PType.Basic
public import PurescriptLanguageCstParser.Types.Expr.Leafs
public import PurescriptLanguageCstParser.Types.Expr.Rec.Basic
public import PurescriptLanguageCstParser.Types.Expr.Rec.Simp
public import PurescriptLanguageCstParser.Types.Expr.Rec.Functor
@[expose] public section
namespace PurescriptLanguageCstParser.Types

open NonEmpty.ArrayCorrectByConstruction
open NonEmpty.String
open PurescriptLanguageCstParser.Types

-- ╔══════════════════════════════════════════════════════════════════╗
-- ║  map_comp theorems                                               ║
-- ╚══════════════════════════════════════════════════════════════════╝

mutual
  theorem Expr.map_comp (f : e1 → e2) (g : e2 → e3) (expr : Expr e1) : (Expr.map (g ∘ f) expr) = (Expr.map g (Expr.map f expr)) := by
    cases expr
    · sorry -- Hole
    · sorry -- Section
    · sorry -- Ident
    · sorry -- Constructor
    · sorry -- Boolean
    · sorry -- Char
    · sorry -- NonEmptyString
    · sorry -- Int
    · sorry -- Number
    · rename_i items; sorry
    · rename_i fields; sorry
    · rename_i w; sorry
    · rename_i expr t ty; sorry
    · rename_i head tail; sorry
    · rename_i head ops; sorry
    · sorry -- OpName
    · rename_i t e'; sorry
    · rename_i data; sorry
    · rename_i expr updates; sorry
    · rename_i fn args; sorry
    · rename_i data; sorry
    · rename_i data; sorry
    · rename_i data; sorry
    · rename_i data; sorry
    · rename_i data; sorry
    · rename_i data; sorry
    · rename_i d; sorry

  theorem Expr.mapDelimited_comp (f : e1 → e2) (g : e2 → e3) (d : Delimited (Expr e1)) : Expr.mapDelimited (g ∘ f) d = Expr.mapDelimited g (Expr.mapDelimited f d) := by
    cases d; rename_i w
    cases w.value
    · sorry
    · rename_i s; sorry

  theorem Expr.mapSep_comp (f : e1 → e2) (g : e2 → e3) (s : Separated (Expr e1)) : Expr.mapSep (g ∘ f) s = Expr.mapSep g (Expr.mapSep f s) := by
    cases s; sorry

  theorem Expr.mapDelimitedRL_comp (f : e1 → e2) (g : e2 → e3) (d : Delimited (RecordLabeled (Expr e1))) : Expr.mapDelimitedRL (g ∘ f) d = Expr.mapDelimitedRL g (Expr.mapDelimitedRL f d) := by
    cases d; rename_i w
    cases w.value
    · sorry
    · rename_i s;
      sorry

  theorem Expr.mapSepRL_comp (f : e1 → e2) (g : e2 → e3) (s : Separated (RecordLabeled (Expr e1))) : Expr.mapSepRL (g ∘ f) s = Expr.mapSepRL g (Expr.mapSepRL f s) := by
    cases s; sorry

  theorem Expr.mapRL_comp (f : e1 → e2) (g : e2 → e3) (rl : RecordLabeled (Expr e1)) : Expr.mapRL (g ∘ f) rl = Expr.mapRL g (Expr.mapRL f rl) := by
    cases rl
    · sorry
    · sorry

  theorem RecordAccessorRecursive.map_comp (f : e1 → e2) (g : e2 → e3) (data : RecordAccessorRecursive e1) : (RecordAccessorRecursive.map (g ∘ f) data) = (RecordAccessorRecursive.map g (RecordAccessorRecursive.map f data)) := by
    cases data; simp only [RecordAccessorRecursive.map, RecordAccessorRecursive.mk.injEq,
      and_self, and_true]; congr 1;
    · sorry
    · sorry
    · sorry

  theorem RecordUpdateRecursive.map_comp (f : e1 → e2) (g : e2 → e3) (u : RecordUpdateRecursive e1) : (RecordUpdateRecursive.map (g ∘ f) u) = (RecordUpdateRecursive.map g (RecordUpdateRecursive.map f u)) := by
    cases u
    · sorry
    · sorry

  theorem AppSpineRecursive.map_comp (f : e1 → e2) (g : e2 → e3) (s : AppSpineRecursive e1) : (AppSpineRecursive.map (g ∘ f) s) = (AppSpineRecursive.map g (AppSpineRecursive.map f s)) := by
    cases s
    · sorry
    · sorry

  theorem LambdaRecursive.map_comp (f : e1 → e2) (g : e2 → e3) (data : LambdaRecursive e1) : (LambdaRecursive.map (g ∘ f) data) = (LambdaRecursive.map g (LambdaRecursive.map f data)) := by
    cases data; sorry

  theorem IfThenElseRecursive.map_comp (f : e1 → e2) (g : e2 → e3) (data : IfThenElseRecursive e1) : (IfThenElseRecursive.map (g ∘ f) data) = (IfThenElseRecursive.map g (IfThenElseRecursive.map f data)) := by
    cases data; sorry

  theorem CaseOfRecursive.map_comp (f : e1 → e2) (g : e2 → e3) (data : CaseOfRecursive e1) : (CaseOfRecursive.map (g ∘ f) data) = (CaseOfRecursive.map g (CaseOfRecursive.map f data)) := by
    cases data; sorry

  theorem GuardedRecursive.map_comp (f : e1 → e2) (g : e2 → e3) (guarded : GuardedRecursive e1) : (GuardedRecursive.map (g ∘ f) guarded) = (GuardedRecursive.map g (GuardedRecursive.map f guarded)) := by
    cases guarded
    · sorry
    · sorry

  theorem GuardedExprRecursive.map_comp (f : e1 → e2) (g : e2 → e3) (data : GuardedExprRecursive e1) : (GuardedExprRecursive.map (g ∘ f) data) = (GuardedExprRecursive.map g (GuardedExprRecursive.map f data)) := by
    cases data; sorry

  theorem PatternGuardRecursive.map_comp (f : e1 → e2) (g : e2 → e3) (data : PatternGuardRecursive e1) : (PatternGuardRecursive.map (g ∘ f) data) = (PatternGuardRecursive.map g (PatternGuardRecursive.map f data)) := by
    cases data; sorry

  theorem LetInRecursive.map_comp (f : e1 → e2) (g : e2 → e3) (data : LetInRecursive e1) : (LetInRecursive.map (g ∘ f) data) = (LetInRecursive.map g (LetInRecursive.map f data)) := by
    cases data; sorry

  theorem LetBindingRecursive.map_comp (f : e1 → e2) (g : e2 → e3) (b : LetBindingRecursive e1) : (LetBindingRecursive.map (g ∘ f) b) = (LetBindingRecursive.map g (LetBindingRecursive.map f b)) := by
    cases b
    · sorry
    · sorry
    · sorry
    · sorry

  theorem ValueBindingFieldsRecursive.map_comp (f : e1 → e2) (g : e2 → e3) (data : ValueBindingFieldsRecursive e1) : (ValueBindingFieldsRecursive.map (g ∘ f) data) = (ValueBindingFieldsRecursive.map g (ValueBindingFieldsRecursive.map f data)) := by
    cases data;
    sorry

  theorem WhereRecursive.map_comp (f : e1 → e2) (g : e2 → e3) (data : WhereRecursive e1) : (WhereRecursive.map (g ∘ f) data) = (WhereRecursive.map g (WhereRecursive.map f data)) := by
    cases data;
    sorry

  theorem DoBlockRecursive.map_comp (f : e1 → e2) (g : e2 → e3) (data : DoBlockRecursive e1) : (DoBlockRecursive.map (g ∘ f) data) = (DoBlockRecursive.map g (DoBlockRecursive.map f data)) := by
    cases data;
    sorry

  theorem AdoBlockRecursive.map_comp (f : e1 → e2) (g : e2 → e3) (data : AdoBlockRecursive e1) : (AdoBlockRecursive.map (g ∘ f) data) = (AdoBlockRecursive.map g (AdoBlockRecursive.map f data)) := by
    cases data;
    sorry

  theorem DoStatementRecursive.map_comp (f : e1 → e2) (g : e2 → e3) (s : DoStatementRecursive e1) : (DoStatementRecursive.map (g ∘ f) s) = (DoStatementRecursive.map g (DoStatementRecursive.map f s)) := by
    cases s
    · sorry
    · sorry
    · sorry
    · sorry
end

end PurescriptLanguageCstParser.Types
