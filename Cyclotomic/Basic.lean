import Mathlib

variable {K : Type*} [Field K] [Fintype K] {p f n : ℕ} [Fact p.Prime]
  (hK : Fintype.card K = p^f) (hn : (p^f).Coprime n)

open Polynomial ZMod

theorem foo {P : K[X]} (hP : P ∣ cyclotomic n K) (hPirr : Irreducible P) :
    orderOf (unitOfCoprime _ hn) ≤ P.natDegree := by
    sorry


theorem bar {P : K[X]} (hP : P ∣ cyclotomic n K) (hPirr : Irreducible P) :
    P.natDegree ≤ orderOf (unitOfCoprime _ hn) := by
    sorry

theorem final {P : K[X]} (hP : P ∣ cyclotomic n K) (hPirr : Irreducible P) :
    P.natDegree = orderOf (unitOfCoprime _ hn) := by
