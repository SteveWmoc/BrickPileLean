import BrickPileLean.BostConnes.FiniteTimeEvolution
import Mathlib.Topology.Algebra.StarSubalgebra

namespace BrickPileLean
namespace BostConnes

noncomputable section

/-- The diagonal time isometry, upgraded to an isometric equivalence with inverse `U_{-t}`. -/
def timeLinearIsometryEquiv (S : Finset ℕ) (t : ℝ) :
    FiniteHilbertSpace S ≃ₗᵢ[ℂ] FiniteHilbertSpace S :=
  LinearIsometryEquiv.ofLinearIsometry
    (timeIsometry S t)
    (timeIsometry S (-t)).toLinearMap
    (by
      apply LinearMap.ext
      intro x
      have h := congrArg (fun f : FiniteOperator S => f x)
        (timeOperator_neg_comp_timeOperator S (-t))
      simpa [timeOperator] using h)
    (by
      apply LinearMap.ext
      intro x
      have h := congrArg (fun f : FiniteOperator S => f x)
        (timeOperator_neg_comp_timeOperator S t)
      simpa [timeOperator] using h)

@[simp] theorem timeLinearIsometryEquiv_apply
    {S : Finset ℕ} (t : ℝ) (x : FiniteHilbertSpace S) :
    timeLinearIsometryEquiv S t x = timeIsometry S t x :=
  rfl

@[simp] theorem timeLinearIsometryEquiv_symm_apply
    {S : Finset ℕ} (t : ℝ) (x : FiniteHilbertSpace S) :
    (timeLinearIsometryEquiv S t).symm x = timeIsometry S (-t) x :=
  rfl

@[simp] theorem timeLinearIsometryEquiv_symm (S : Finset ℕ) (t : ℝ) :
    (timeLinearIsometryEquiv S t).symm = timeLinearIsometryEquiv S (-t) := by
  ext x
  simp

/-- The isometric equivalences form the expected one-parameter group. -/
theorem timeLinearIsometryEquiv_add (S : Finset ℕ) (t u : ℝ) :
    timeLinearIsometryEquiv S (t + u) =
      (timeLinearIsometryEquiv S u).trans (timeLinearIsometryEquiv S t) := by
  apply LinearIsometryEquiv.ext
  intro x
  have h := congrArg (fun f : FiniteOperator S => f x) (timeOperator_add S t u)
  simpa [timeOperator] using h

/-- Conjugation by `U_t` as a star-algebra automorphism of all bounded operators. -/
def ambientTimeStarAlgEquiv (S : Finset ℕ) (t : ℝ) :
    FiniteOperator S ≃⋆ₐ[ℂ] FiniteOperator S :=
  (timeLinearIsometryEquiv S t).conjStarAlgEquiv

@[simp] theorem ambientTimeStarAlgEquiv_apply
    {S : Finset ℕ} (t : ℝ) (a : FiniteOperator S) :
    ambientTimeStarAlgEquiv S t a = ambientTimeEvolution S t a := by
  rfl

@[simp] theorem ambientTimeStarAlgEquiv_symm (S : Finset ℕ) (t : ℝ) :
    (ambientTimeStarAlgEquiv S t).symm = ambientTimeStarAlgEquiv S (-t) := by
  simp [ambientTimeStarAlgEquiv]

/-- The ambient automorphisms form the same one-parameter group. -/
theorem ambientTimeStarAlgEquiv_add (S : Finset ℕ) (t u : ℝ) :
    ambientTimeStarAlgEquiv S (t + u) =
      (ambientTimeStarAlgEquiv S u).trans (ambientTimeStarAlgEquiv S t) := by
  change (timeLinearIsometryEquiv S (t + u)).conjStarAlgEquiv =
    (timeLinearIsometryEquiv S u).conjStarAlgEquiv.trans
      (timeLinearIsometryEquiv S t).conjStarAlgEquiv
  rw [timeLinearIsometryEquiv_add,
    LinearIsometryEquiv.conjStarAlgEquiv_trans]

/-- The ambient time automorphism is norm-topology continuous. -/
theorem continuous_ambientTimeStarAlgEquiv (S : Finset ℕ) (t : ℝ) :
    Continuous (ambientTimeStarAlgEquiv S t) := by
  have h : Continuous (fun a : FiniteOperator S =>
      timeOperator S t * a * timeOperator S (-t)) :=
    (continuous_const.mul continuous_id).mul continuous_const
  change Continuous (fun a : FiniteOperator S => ambientTimeStarAlgEquiv S t a)
  have heq :
      (fun a : FiniteOperator S => ambientTimeStarAlgEquiv S t a) =
        fun a : FiniteOperator S => timeOperator S t * a * timeOperator S (-t) := by
    funext a
    exact ambientTimeStarAlgEquiv_apply t a
  rw [heq]
  exact h

/-- Conjugation by `U_t` preserves the finite Toeplitz algebra. -/
theorem ambientTimeStarAlgEquiv_map_finiteToeplitz_le
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (t : ℝ) :
    StarSubalgebra.map (ambientTimeStarAlgEquiv S t).toStarAlgHom
        (finiteToeplitzAlgebra hS) ≤
      finiteToeplitzAlgebra hS := by
  let A0 : StarSubalgebra ℂ (FiniteOperator S) :=
    StarAlgebra.adjoin ℂ (primeShiftSet hS)
  change StarSubalgebra.map (ambientTimeStarAlgEquiv S t).toStarAlgHom A0.topologicalClosure ≤
    A0.topologicalClosure
  calc
    StarSubalgebra.map (ambientTimeStarAlgEquiv S t).toStarAlgHom A0.topologicalClosure ≤
        (StarSubalgebra.map (ambientTimeStarAlgEquiv S t).toStarAlgHom A0).topologicalClosure :=
      StarSubalgebra.map_topologicalClosure_le A0 _
        (continuous_ambientTimeStarAlgEquiv S t)
    _ ≤ A0.topologicalClosure := by
      apply StarSubalgebra.topologicalClosure_minimal
      · rw [StarSubalgebra.map_le_iff_le_comap]
        apply StarAlgebra.adjoin_le
        rintro _ ⟨p, rfl⟩
        change ambientTimeStarAlgEquiv S t
            (shiftOperator hS (primeSemigroupElement S p)) ∈ A0.topologicalClosure
        rw [ambientTimeStarAlgEquiv_apply, ambientTimeEvolution_shift]
        apply A0.topologicalClosure.smul_mem
        · exact StarSubalgebra.le_topologicalClosure A0
            (StarAlgebra.subset_adjoin ℂ (primeShiftSet hS) ⟨p, rfl⟩)
      · exact StarSubalgebra.isClosed_topologicalClosure A0

/-- Every element of the finite Toeplitz algebra stays in it under time evolution. -/
theorem ambientTimeEvolution_mem_finiteToeplitzAlgebra
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (t : ℝ)
    {a : FiniteOperator S} (ha : a ∈ finiteToeplitzAlgebra hS) :
    ambientTimeEvolution S t a ∈ finiteToeplitzAlgebra hS := by
  have hmap := ambientTimeStarAlgEquiv_map_finiteToeplitz_le hS t
  apply hmap
  rw [StarSubalgebra.mem_map]
  exact ⟨a, ha, by simp⟩

/-- The time evolution restricted to the finite Toeplitz algebra as a star-algebra homomorphism. -/
def finiteTimeEvolutionHom
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (t : ℝ) :
    finiteToeplitzAlgebra hS →⋆ₐ[ℂ] finiteToeplitzAlgebra hS :=
  StarAlgHom.codRestrict
    ((ambientTimeStarAlgEquiv S t).toStarAlgHom.comp (finiteToeplitzAlgebra hS).subtype)
    (finiteToeplitzAlgebra hS)
    (fun a => by
      exact ambientTimeEvolution_mem_finiteToeplitzAlgebra hS t a.2)

@[simp] theorem finiteTimeEvolutionHom_coe
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (t : ℝ)
    (a : finiteToeplitzAlgebra hS) :
    ((finiteTimeEvolutionHom hS t a : finiteToeplitzAlgebra hS) : FiniteOperator S) =
      ambientTimeEvolution S t a := by
  rfl

/-- The finite Bost--Connes time evolution as a star-algebra automorphism of `T_S`. -/
def finiteTimeEvolution
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (t : ℝ) :
    finiteToeplitzAlgebra hS ≃⋆ₐ[ℂ] finiteToeplitzAlgebra hS :=
  StarAlgEquiv.ofBijective (finiteTimeEvolutionHom hS t) (by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply (ambientTimeStarAlgEquiv S t).injective
      exact congrArg Subtype.val hab
    · intro b
      refine ⟨finiteTimeEvolutionHom hS (-t) b, ?_⟩
      apply Subtype.ext
      change ambientTimeStarAlgEquiv S t
          (ambientTimeStarAlgEquiv S (-t) (b : FiniteOperator S)) = b
      rw [← ambientTimeStarAlgEquiv_symm]
      exact (ambientTimeStarAlgEquiv S t).apply_symm_apply (b : FiniteOperator S))

@[simp] theorem finiteTimeEvolution_coe
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (t : ℝ)
    (a : finiteToeplitzAlgebra hS) :
    ((finiteTimeEvolution hS t a : finiteToeplitzAlgebra hS) : FiniteOperator S) =
      ambientTimeEvolution S t a := by
  rfl

/-- The restricted time evolution is a one-parameter group of star-algebra automorphisms. -/
theorem finiteTimeEvolution_add
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (t u : ℝ) :
    finiteTimeEvolution hS (t + u) =
      (finiteTimeEvolution hS u).trans (finiteTimeEvolution hS t) := by
  apply StarAlgEquiv.ext
  intro a
  apply Subtype.ext
  have h := congrArg
    (fun e : FiniteOperator S ≃⋆ₐ[ℂ] FiniteOperator S => e (a : FiniteOperator S))
    (ambientTimeStarAlgEquiv_add S t u)
  simpa using h

/-- The restricted evolution has the expected action on every semigroup shift. -/
theorem finiteTimeEvolution_shift
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (t : ℝ)
    (m : finitePrimeSemigroup S) :
    finiteTimeEvolution hS t
        ⟨shiftOperator hS m, shiftOperator_mem_finiteToeplitzAlgebra hS m⟩ =
      timePhase t m •
        ⟨shiftOperator hS m, shiftOperator_mem_finiteToeplitzAlgebra hS m⟩ := by
  apply Subtype.ext
  simp [ambientTimeEvolution_shift]

end

end BostConnes
end BrickPileLean
