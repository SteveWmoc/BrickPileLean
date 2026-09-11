import BrickPileLean.BostConnes.FiniteToeplitzAlgebra
import Mathlib.Analysis.SpecialFunctions.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace BrickPileLean
namespace BostConnes

open scoped BigOperators InnerProduct

noncomputable section

/-- The unit-modulus phase `n^{it} = exp(i t log n)` attached to `n ∈ Λ_S`. -/
def timePhase {S : Finset ℕ} (t : ℝ) (n : finitePrimeSemigroup S) : ℂ :=
  Complex.exp (((t * Real.log ((n : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)

@[simp] theorem norm_timePhase {S : Finset ℕ} (t : ℝ) (n : finitePrimeSemigroup S) :
    ‖timePhase t n‖ = 1 := by
  simp [timePhase, Complex.norm_exp]

@[simp] theorem timePhase_zero {S : Finset ℕ} (n : finitePrimeSemigroup S) :
    timePhase 0 n = 1 := by
  simp [timePhase]

/-- The arithmetic phases are multiplicative on `Λ_S`. -/
theorem timePhase_mul
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (t : ℝ)
    (m n : finitePrimeSemigroup S) :
    timePhase t (m * n) = timePhase t m * timePhase t n := by
  have hm : (((m : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (finitePrimeSemigroup_coe_pos hS m).ne'
  have hn : (((n : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (finitePrimeSemigroup_coe_pos hS n).ne'
  unfold timePhase
  rw [show ((((m * n : finitePrimeSemigroup S) : ℕ) : ℝ)) =
      ((m : ℕ) : ℝ) * ((n : ℕ) : ℝ) by norm_num,
    Real.log_mul hm hn, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Opposite times give reciprocal phases. -/
@[simp] theorem timePhase_neg_mul_timePhase
    {S : Finset ℕ} (t : ℝ) (n : finitePrimeSemigroup S) :
    timePhase (-t) n * timePhase t n = 1 := by
  unfold timePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The phase-twisted canonical basis. -/
def timedBasis (S : Finset ℕ) (t : ℝ) (n : finitePrimeSemigroup S) : FiniteHilbertSpace S :=
  lp.single 2 n (timePhase t n)

/-- Multiplying each canonical basis vector by `n^{it}` preserves orthonormality. -/
theorem timedBasis_orthonormal (S : Finset ℕ) (t : ℝ) :
    Orthonormal ℂ (timedBasis S t) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  unfold timedBasis
  rw [lp.inner_single_left, lp.single_apply, Pi.single_apply]
  by_cases hij : i = j
  · subst j
    simp [norm_timePhase]
  · simp [hij]

/-- The diagonal isometry `U_t e_n = n^{it} e_n`. -/
def timeIsometry (S : Finset ℕ) (t : ℝ) :
    FiniteHilbertSpace S →ₗᵢ[ℂ] FiniteHilbertSpace S :=
  ((timedBasis_orthonormal S t).orthogonalFamily).linearIsometry

@[simp] theorem timeIsometry_single
    {S : Finset ℕ} (t : ℝ) (n : finitePrimeSemigroup S) (z : ℂ) :
    timeIsometry S t (lp.single 2 n z) = lp.single 2 n (timePhase t n * z) := by
  classical
  change
    ((timedBasis_orthonormal S t).orthogonalFamily).linearIsometry (lp.single 2 n z) =
      lp.single 2 n (timePhase t n * z)
  rw [OrthogonalFamily.linearIsometry_apply_single]
  ext k
  simp [Orthonormal.orthogonalFamily, timedBasis, lp.single_apply, Pi.single_apply, mul_comm]

/-- The bounded diagonal operator implementing time `t`. -/
def timeOperator (S : Finset ℕ) (t : ℝ) : FiniteOperator S :=
  (timeIsometry S t).toContinuousLinearMap

@[simp] theorem timeOperator_single
    {S : Finset ℕ} (t : ℝ) (n : finitePrimeSemigroup S) (z : ℂ) :
    timeOperator S t (lp.single 2 n z) = lp.single 2 n (timePhase t n * z) := by
  exact timeIsometry_single t n z

@[simp] theorem timeOperator_basisVector
    {S : Finset ℕ} (t : ℝ) (n : finitePrimeSemigroup S) :
    timeOperator S t (basisVector S n) = timePhase t n • basisVector S n := by
  unfold basisVector
  rw [timeOperator_single]
  ext k
  simp [lp.single_apply, Pi.single_apply]

/-- `U_{-t}` is a left inverse of `U_t`. -/
theorem timeOperator_neg_comp_timeOperator (S : Finset ℕ) (t : ℝ) :
    (timeOperator S (-t)).comp (timeOperator S t) =
      ContinuousLinearMap.id ℂ (FiniteHilbertSpace S) := by
  refine lp.ext_continuousLinearMap (ENNReal.ofNat_ne_top (n := nat_lit 2)) fun n => ?_
  ext z
  simp [mul_assoc]

/-- `U_t` is a one-parameter group on the canonical basis. -/
theorem timeOperator_add (S : Finset ℕ) (t u : ℝ) :
    (timeOperator S (t + u)) = (timeOperator S t).comp (timeOperator S u) := by
  refine lp.ext_continuousLinearMap (ENNReal.ofNat_ne_top (n := nat_lit 2)) fun n => ?_
  ext z
  simp [timePhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Conjugation by the diagonal time operators on the ambient bounded-operator algebra. -/
def ambientTimeEvolution (S : Finset ℕ) (t : ℝ) (a : FiniteOperator S) : FiniteOperator S :=
  timeOperator S t * a * timeOperator S (-t)

/-- The finite arithmetic dynamics scales each multiplicative shift by `m^{it}`. -/
theorem ambientTimeEvolution_shift
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (t : ℝ)
    (m : finitePrimeSemigroup S) :
    ambientTimeEvolution S t (shiftOperator hS m) =
      timePhase t m • shiftOperator hS m := by
  refine lp.ext_continuousLinearMap (ENNReal.ofNat_ne_top (n := nat_lit 2)) fun n => ?_
  ext z
  simp [ambientTimeEvolution, ContinuousLinearMap.mul_apply,
    timePhase_mul hS, mul_assoc]

end

end BostConnes
end BrickPileLean
