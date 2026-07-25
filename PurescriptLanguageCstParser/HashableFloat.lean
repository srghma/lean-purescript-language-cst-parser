module

public import Batteries.Data.Float.Basic

structure HashableFloat where
  val : Float
  noNaN : val ≠ Float.nan
  noNegZero : val ≠ (-0.0 : Float)

instance : Hashable Float := ⟨λ f => hash f.toBits⟩

instance : LawfulHashable Float := ⟨λ f => sorry⟩ -- todo: prove that if not NaN or -0.0 then float is hashable
