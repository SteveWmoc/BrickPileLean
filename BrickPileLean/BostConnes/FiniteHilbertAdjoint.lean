import BrickPileLean.BostConnes.FiniteHilbertShift
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace BrickPileLean
namespace BostConnes

open scoped InnerProduct

noncomputable section

/-- The multiplicative shift, now regarded as a bounded operator on `ℓ²(Λ_S)`. -/
def shiftOperator
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m : finitePrimeSemigroup S) :
    FiniteHilbertSpace S →L[ℂ] FiniteHilbertSpace S :=
  (shiftIsometry hS m).toContinuousLinearMap

@[simp] theorem shiftOperator_basisVector
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m n : finitePrimeSemigroup S) :
    shiftOperator hS m (basisVector S n) = basisVector S (m * n) := by
  simp [shiftOperator]

/-- The Hilbert-space adjoint `V_m*` of the multiplicative shift. -/
def shiftAdjoint
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m : finitePrimeSemigroup S) :
    FiniteHilbertSpace S →L[ℂ] FiniteHilbertSpace S :=
  (shiftOperator hS m)†

/-- The adjoint is a left inverse of the shift: `V_m* V_m = I`. -/
theorem shiftAdjoint_comp_shift
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m : finitePrimeSemigroup S) :
    (shiftAdjoint hS m).comp (shiftOperator hS m) =
      ContinuousLinearMap.id ℂ (FiniteHilbertSpace S) := by
  ext x
  apply ext_inner_left ℂ
  intro y
  change
    inner ℂ y (shiftAdjoint hS m (shiftOperator hS m x)) =
      inner ℂ y x
  rw [show shiftAdjoint hS m = (shiftOperator hS m)† by rfl,
    ContinuousLinearMap.adjoint_inner_right]
  exact (shiftIsometry hS m).inner_map_map y x

@[simp] theorem shiftAdjoint_shift_apply
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m : finitePrimeSemigroup S) (x : FiniteHilbertSpace S) :
    shiftAdjoint hS m (shiftOperator hS m x) = x := by
  have h := congrArg
    (fun T : FiniteHilbertSpace S →L[ℂ] FiniteHilbertSpace S => T x)
    (shiftAdjoint_comp_shift hS m)
  simpa using h

/-- On a basis vector in the range of `V_m`, the adjoint removes the factor `m`. -/
@[simp] theorem shiftAdjoint_basisVector_mul
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m n : finitePrimeSemigroup S) :
    shiftAdjoint hS m (basisVector S (m * n)) = basisVector S n := by
  rw [← shiftOperator_basisVector hS m n]
  exact shiftAdjoint_shift_apply hS m (basisVector S n)

/-- If `n` is not divisible by `m` inside `Λ_S`, then `V_m* e_n = 0`. -/
theorem shiftAdjoint_basisVector_eq_zero_of_not_dvd
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m n : finitePrimeSemigroup S) (hmn : ¬ m ∣ n) :
    shiftAdjoint hS m (basisVector S n) = 0 := by
  ext k
  have hk : m * k ≠ n := by
    intro h
    apply hmn
    exact ⟨k, h.symm⟩
  have hinner :
      inner ℂ (basisVector S k) (shiftAdjoint hS m (basisVector S n)) = 0 := by
    calc
      inner ℂ (basisVector S k) (shiftAdjoint hS m (basisVector S n)) =
          inner ℂ (shiftOperator hS m (basisVector S k)) (basisVector S n) := by
            simpa [shiftAdjoint] using
              (ContinuousLinearMap.adjoint_inner_right
                (shiftOperator hS m) (basisVector S k) (basisVector S n))
      _ = inner ℂ (basisVector S (m * k)) (basisVector S n) := by simp
      _ = 0 := by
        simp [basisVector, hk]
  simpa [basisVector] using hinner

end

end BostConnes
end BrickPileLean
