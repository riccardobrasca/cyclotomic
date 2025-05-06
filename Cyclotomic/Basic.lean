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
  have hcycl := FiniteField.instIsCyclicAlgEquivOfFinite K L

--on récupère la racine que l'on a ajoutée
  let ζ' := AdjoinRoot.root P


--on mont quel ζ' est une racine primitive n-ième de l'unité
  have hζ' : IsPrimitiveRoot ζ' n := by
    have : NeZero (n : L) := by
      sorry
      ---rw[neZero_iff]
      ---apply NeZero.of_not_dvd

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

---on introduit la base de L sur K
  let pB := AdjoinRoot.powerBasis hPirr.ne_zero
---On réécrit l'objectif, on passe de P.natDegree au degree de l'extension L sur K
  rw [← AdjoinRoot.powerBasis_dim hPirr.ne_zero, ← pB.finrank, ←
    FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]
---on introduit le Frobenius
  let φ := (FiniteField.frobeniusAlgEquivOfAlgebraic K L)

  have : (φ ^ orderOf φ) ζ' = ζ' := by simp [pow_orderOf_eq_one φ]
  simp only [AlgEquiv.coe_pow, φ, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, pow_iterate, hK] at this
  nth_rewrite 2 [← pow_one ζ'] at this

  rw [orderOf_dvd_iff_pow_eq_one]
  ext
  apply hζ.zmodEquivZPowers.injective
  sorry
