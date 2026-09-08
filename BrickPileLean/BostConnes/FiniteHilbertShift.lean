import BrickPileLean.BostConnes.LambdaPartition
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace BrickPileLean
namespace BostConnes

open scoped BigOperators

noncomputable section

/-- The Hilbert space `ℓ²(Λ_S)` for the finite prime semigroup. -/
abbrev FiniteHilbertSpace (S : Finset ℕ) :=
  lp (fun _ : finitePrimeSemigroup S => ℂ) 2

/-- The canonical basis vector `e_n` of `ℓ²(Λ_S)`. -/
def basisVector (S : Finset ℕ) (n : finitePrimeSemigroup S) : FiniteHilbertSpace S :=
  lp.single 2 n (1 : ℂ)

/-- Every element of the finite prime semigroup is positive when `S` consists of primes. -/
theorem finitePrimeSemigroup_coe_pos
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (n : finitePrimeSemigroup S) :
    0 < (n : ℕ) := by
  rcases n.2 with ⟨k, hk⟩
  rw [← hk]
  unfold semigroupElement
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (hS p.1 p.2).pos _

/-- Left multiplication by a nonzero semigroup element is injective. -/
theorem leftMul_injective
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m : finitePrimeSemigroup S) :
    Function.Injective (fun n : finitePrimeSemigroup S => m * n) := by
  intro a b hab
  apply Subtype.ext
  apply Nat.mul_left_cancel (finitePrimeSemigroup_coe_pos hS m)
  exact congrArg (fun x : finitePrimeSemigroup S => (x : ℕ)) hab

/-- Left multiplication preserves distinctness of basis labels. -/
@[simp] theorem leftMul_eq_iff
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m a b : finitePrimeSemigroup S) :
    m * a = m * b ↔ a = b :=
  (leftMul_injective hS m).eq_iff

/-- The shifted canonical basis remains orthonormal. -/
theorem shiftedBasis_orthonormal
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m : finitePrimeSemigroup S) :
    Orthonormal ℂ (fun n : finitePrimeSemigroup S => basisVector S (m * n)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  unfold basisVector
  rw [lp.inner_single_left, lp.single_apply, Pi.single_apply]
  simp [leftMul_eq_iff hS m i j]

/-- The multiplicative shift `V_m` on `ℓ²(Λ_S)`, defined by `V_m e_n = e_{mn}`. -/
def shiftIsometry
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m : finitePrimeSemigroup S) :
    FiniteHilbertSpace S →ₗᵢ[ℂ] FiniteHilbertSpace S :=
  ((shiftedBasis_orthonormal hS m).orthogonalFamily).linearIsometry

/-- The shift acts on arbitrary scalar basis vectors by moving the index. -/
@[simp] theorem shiftIsometry_single
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m n : finitePrimeSemigroup S) (z : ℂ) :
    shiftIsometry hS m (lp.single 2 n z) = lp.single 2 (m * n) z := by
  classical
  change
    ((shiftedBasis_orthonormal hS m).orthogonalFamily).linearIsometry
      (lp.single 2 n z) = lp.single 2 (m * n) z
  rw [OrthogonalFamily.linearIsometry_apply_single]
  ext k
  simp [Orthonormal.orthogonalFamily, basisVector, lp.single_apply, Pi.single_apply]

/-- In particular, `V_m e_n = e_{mn}`. -/
@[simp] theorem shiftIsometry_basisVector
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m n : finitePrimeSemigroup S) :
    shiftIsometry hS m (basisVector S n) = basisVector S (m * n) := by
  simp [basisVector]

/-- Multiplicative shifts compose according to multiplication in `Λ_S`. -/
theorem shiftIsometry_mul
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m n : finitePrimeSemigroup S) :
    (shiftIsometry hS m).toContinuousLinearMap.comp
        (shiftIsometry hS n).toContinuousLinearMap =
      (shiftIsometry hS (m * n)).toContinuousLinearMap := by
  refine lp.ext_continuousLinearMap (ENNReal.ofNat_ne_top (n := nat_lit 2)) fun k => ?_
  ext z
  simp [mul_assoc]

end

end BostConnes
end BrickPileLean
