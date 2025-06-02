import Mathlib

variable {K : Type*} [Field K] [Fintype K]
variable {p f n : ℕ} [hp : Fact p.Prime]

(hK : Fintype.card K = p^f)
(hn : (p^f).Coprime n)

open Polynomial ZMod
open Prime

include hK

theorem foo {P : K[X]} (hP : P ∣ cyclotomic n K) (hPirr : Irreducible P) :
    orderOf (unitOfCoprime _ hn) = P.natDegree := by

  classical
  let Q := normalize P

  let hQmo : Monic Q := by
    apply P.monic_normalize hPirr.ne_zero

  let L := AdjoinRoot Q

  have : Module.Finite K L := hQmo.finite_adjoinRoot
  have : Finite L := Module.finite_of_finite K

  have : Fact (Irreducible Q) := by
    have qIrr : Irreducible Q := by
      suffices Irreducible P by
        apply Associated.irreducible (p:=P)
        apply associated_normalize P
        exact this
      exact hPirr
    exact ⟨qIrr⟩

  have hQ : Q ∣ cyclotomic n K := by
    apply dvd_trans (b:=P)
    rw[normalize_dvd_iff]
    exact hP

  let ζ' := AdjoinRoot.root Q

  have n0 : NeZero (n : L) := by
      suffices NeZero (n : K) by
        simpa using NeZero.of_injective (algebraMap K (AdjoinRoot Q)).injective
      have hf : 0 < f := by
        apply Nat.pos_of_ne_zero
        intro hf
        simp [hf] at hK
        rw [Fintype.card_eq_one_iff] at hK
        obtain ⟨x, hx⟩ := hK
        have : (0 : K) ≠ 1 := by
          exact zero_ne_one' K
        have : (0 : K) = 1 := by
          rw [hx 0, hx 1]
        contradiction
      have : CharP K p := by
        rw [CharP.charP_iff_prime_eq_zero hp.1]
        have hf1 : f ≠ 0 := by
          exact Nat.ne_zero_of_lt hf
        simpa [hf1, hK] using Nat.cast_card_eq_zero K
      apply NeZero.of_not_dvd K (p := p)
      rw [← Nat.Prime.coprime_iff_not_dvd hp.1]
      exact (Nat.coprime_pow_left_iff hf _ _).mp hn

  have hζ' : IsPrimitiveRoot ζ' n := by
    rw [← isRoot_cyclotomic_iff]
    exact IsRoot.dvd
      (AdjoinRoot.isRoot_root Q)
      (by simpa using Polynomial.map_dvd (algebraMap K L) hQ)

  have hζ0 : ζ' ≠ 0 := by
    apply IsPrimitiveRoot.ne_zero (hζ')
    exact (NeZero.of_neZero_natCast (h := n0)).ne

  let ζ := Units.mk0 ζ' hζ0

  have hζ : IsPrimitiveRoot ζ n := by
    exact IsPrimitiveRoot.coe_units_iff.mp hζ'

  let pB := AdjoinRoot.powerBasis this.elim.ne_zero

  have hDeg : P.natDegree = Q.natDegree := by
    apply P.natDegree_eq_of_degree_eq
    rw[P.degree_normalize]

  rw [hDeg]

  rw [← AdjoinRoot.powerBasis_dim this.elim.ne_zero, ← pB.finrank,← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]

  apply dvd_antisymm

  ---P1
  rw [orderOf_dvd_iff_pow_eq_one]
  set φ := (FiniteField.frobeniusAlgEquivOfAlgebraic K L)
  have : (φ ^ orderOf φ) ζ' = ζ' := by simp [pow_orderOf_eq_one φ]
  simp only [AlgEquiv.coe_pow, φ, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, pow_iterate, hK] at this
  ext
  set o := orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic K (AdjoinRoot Q))
  simp
  norm_cast
  rw [← Nat.cast_one, ZMod.eq_iff_modEq_nat, IsPrimitiveRoot.eq_orderOf hζ]
  have : ζ ^ (p^f) ^ o = ζ := by
    ext
    simpa
  nth_rewrite 2 [← pow_one ζ] at this
  exact pow_eq_pow_iff_modEq.mp this

  ---P2
  rw [orderOf_dvd_iff_pow_eq_one]
  apply AlgEquiv.coe_algHom_injective
  apply pB.algHom_ext
  simp [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, hK, pB]
  set φ := (FiniteField.frobeniusAlgEquivOfAlgebraic K L)
  have : (φ ^ orderOf φ) ζ' = ζ' := by simp [pow_orderOf_eq_one φ]
  simp only [AlgEquiv.coe_pow, φ, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, pow_iterate, hK] at this
  suffices ζ ^ (p^f) ^ orderOf (unitOfCoprime (p^f) hn) = ζ by
    exact Units.eq_iff.2 this
  nth_rewrite 2 [← pow_one ζ]
  rw [pow_eq_pow_iff_modEq, ← IsPrimitiveRoot.eq_orderOf hζ, ← ZMod.eq_iff_modEq_nat]
  have : (unitOfCoprime (p^f) hn) ^ (orderOf ((unitOfCoprime (p^f) hn))) = 1 := by
    exact pow_orderOf_eq_one (unitOfCoprime (p^f) hn)
  simp [← Units.eq_iff] at this
  push_cast
  exact this
