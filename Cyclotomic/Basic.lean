import Mathlib

variable {K : Type*} [Field K] [Fintype K]
variable {p f n : ℕ} [hp : Fact p.Prime]

(hK : Fintype.card K = p^f)
(hn : (p^f).Coprime n)
(hn0 : n ≠ 0)

open Polynomial ZMod

include hK hn0

---r est l'ordre de q modulo n dans (ZMod n)
---on démontre d'abord que r divise le degrée de P, où P est un polynôme irréductible dans Fq[X]
---divisant le n-ième polynôme cyclotomique (vu dans Fq)
theorem foo {P : K[X]} (hP : P ∣ cyclotomic n K) (hPirr : Irreducible P) (hPmo : P.Monic) :
    orderOf (unitOfCoprime _ hn) ∣ P.natDegree := by

---on montre que P est irréductible (c'est notre hypothèse)
  have : Fact (Irreducible P) := ⟨hPirr⟩

--on se place dans un corps avec une racine de P
  let L := AdjoinRoot P

--on récupère que ce corps est fini et cyclique sur K (Fq)
  have : Module.Finite K L := hPmo.finite_adjoinRoot
  have : Finite L := Module.finite_of_finite K

--on récupère la racine que l'on a ajoutée
  let ζ' := AdjoinRoot.root P


--on mont quel ζ' est une racine primitive n-ième de l'unité
  have hζ' : IsPrimitiveRoot ζ' n := by
    have : NeZero (n : L) := by
      suffices NeZero (n : K) by
        simpa using NeZero.of_injective (algebraMap K (AdjoinRoot P)).injective
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
    ---on réécrit l'objectif en "ζ' est une racine d'un polynôme cyclotomique"
    rw [← isRoot_cyclotomic_iff]
    ---On a tous ce qu'il faut : ζ' est racine de P et P divise un polynôme cyclotomique par hypothèse
    exact IsRoot.dvd
      (AdjoinRoot.isRoot_root P)
      ---On doit montrer que P | cyclomotic n L (dans L[X])
      ---donc on précise à Lean de changer le type de P et cyclomotic n K pour les mettre dans L
      (by simpa using Polynomial.map_dvd (algebraMap K L) hP)

---on montre que ζ' est différent de zero
  have hζ0 : ζ' ≠ 0 := by
    apply IsPrimitiveRoot.ne_zero (hζ')
    exact hn0
  let ζ := Units.mk0 ζ' hζ0
  have hζ : IsPrimitiveRoot ζ n := by
    exact IsPrimitiveRoot.coe_units_iff.mp hζ'
---on introduit la base de L sur K
  let pB := AdjoinRoot.powerBasis hPirr.ne_zero
---On réécrit l'objectif, on passe de P.natDegree au degree de l'extension L sur K
  rw [← AdjoinRoot.powerBasis_dim hPirr.ne_zero, ← pB.finrank, ←
    FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]
---on introduit le Frobenius
  set φ := (FiniteField.frobeniusAlgEquivOfAlgebraic K L)

  have : (φ ^ orderOf φ) ζ' = ζ' := by simp [pow_orderOf_eq_one φ]
  simp only [AlgEquiv.coe_pow, φ, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, pow_iterate, hK] at this

  rw [orderOf_dvd_iff_pow_eq_one]
  ext
  set o := orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic K (AdjoinRoot P))
  simp
  norm_cast
  rw [← Nat.cast_one, ZMod.eq_iff_modEq_nat, IsPrimitiveRoot.eq_orderOf hζ]
  have H : ζ ^ (p ^ f) ^ o = ζ := by
    ext
    simpa
  nth_rewrite 2 [← pow_one ζ] at H
  exact pow_eq_pow_iff_modEq.mp H

theorem bar {P : K[X]} (hP : P ∣ cyclotomic n K) (hPirr : Irreducible P) (hPmo : P.Monic) :
    P.natDegree ∣ orderOf (unitOfCoprime _ hn) := by

---on montre que P est irréductible (c'est notre hypothèse)
  have : Fact (Irreducible P) := ⟨hPirr⟩

--on se place dans un corps avec une racine de P
  let L := AdjoinRoot P

--on récupère que ce corps est fini et cyclique sur K (Fq)
  have : Module.Finite K L := hPmo.finite_adjoinRoot
  have : Finite L := Module.finite_of_finite K

--on récupère la racine que l'on a ajoutée
  let ζ' := AdjoinRoot.root P


--on mont quel ζ' est une racine primitive n-ième de l'unité
  have hζ' : IsPrimitiveRoot ζ' n := by
    have : NeZero (n : L) := by
      suffices NeZero (n : K) by
        simpa using NeZero.of_injective (algebraMap K (AdjoinRoot P)).injective
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
    ---on réécrit l'objectif en "ζ' est une racine d'un polynôme cyclotomique"
    rw [← isRoot_cyclotomic_iff]
    ---On a tous ce qu'il faut : ζ' est racine de P et P divise un polynôme cyclotomique par hypothèse
    exact IsRoot.dvd
      (AdjoinRoot.isRoot_root P)
      ---On doit montrer que P | cyclomotic n L (dans L[X])
      ---donc on précise à Lean de changer le type de P et cyclomotic n K pour les mettre dans L
      (by simpa using Polynomial.map_dvd (algebraMap K L) hP)

---on montre que ζ' est différent de zero
  have hζ0 : ζ' ≠ 0 := by
    apply IsPrimitiveRoot.ne_zero (hζ')
    exact hn0
  let ζ := Units.mk0 ζ' hζ0
  have hζ : IsPrimitiveRoot ζ n := by
    exact IsPrimitiveRoot.coe_units_iff.mp hζ'
---on introduit la base de L sur K
  let pB := AdjoinRoot.powerBasis hPirr.ne_zero
---On réécrit l'objectif, on passe de P.natDegree au degree de l'extension L sur K
  rw [← AdjoinRoot.powerBasis_dim hPirr.ne_zero, ← pB.finrank, ←
    FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, orderOf_dvd_iff_pow_eq_one]
  apply AlgEquiv.coe_algHom_injective
  apply pB.algHom_ext
  simp [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, hK, pB]

---on introduit le Frobenius
  set φ := (FiniteField.frobeniusAlgEquivOfAlgebraic K L)

  have : (φ ^ orderOf φ) ζ' = ζ' := by simp [pow_orderOf_eq_one φ]
  simp only [AlgEquiv.coe_pow, φ, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, pow_iterate, hK] at this
  suffices ζ ^ (p ^ f) ^ orderOf (unitOfCoprime (p ^ f) hn) = ζ by
    exact Units.eq_iff.2 this
  nth_rewrite 2 [← pow_one ζ]
  rw [pow_eq_pow_iff_modEq, ← IsPrimitiveRoot.eq_orderOf hζ, ← ZMod.eq_iff_modEq_nat]
  have : (unitOfCoprime (p ^ f) hn) ^ (orderOf ((unitOfCoprime (p ^ f) hn))) = 1 := by
    exact pow_orderOf_eq_one (unitOfCoprime (p ^ f) hn)
  simp [← Units.eq_iff] at this
  push_cast
  exact this
