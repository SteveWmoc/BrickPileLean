import BrickPileLean.BostConnes.FiniteHamiltonianDensity

namespace BrickPileLean
namespace BostConnes

open scoped BigOperators InnerProduct

noncomputable section

/-- The real diagonal energy multiplier can be moved across the inner product.
This is symmetry on the natural domain, with both products taken in the
ambient Hilbert space. -/
theorem finiteHamiltonian_symmetric (S : Finset ℕ)
    (x y : finiteHamiltonianDomain S) :
    inner ℂ (finiteHamiltonian S x) y.1 = inner ℂ x.1 (finiteHamiltonian S y) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  change inner ℂ ((finiteEnergy n : ℂ) • x.1 n) (y.1 n) =
    inner ℂ (x.1 n) ((finiteEnergy n : ℂ) • y.1 n)
  rw [inner_smul_left, inner_smul_right]
  simp

/-- The diagonal quadratic form at one coordinate is energy times squared norm. -/
theorem finiteHamiltonian_coordinate_quadratic (S : Finset ℕ)
    (x : finiteHamiltonianDomain S) (n : finitePrimeSemigroup S) :
    (inner ℂ (x.1 n) (finiteHamiltonian S x n)).re =
      finiteEnergy n * ‖x.1 n‖ ^ 2 := by
  change (inner ℂ (x.1 n) ((finiteEnergy n : ℂ) • x.1 n)).re = _
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- The energy quadratic-form series converges for every vector in the
Hamiltonian domain, by summability of the Hilbert-space inner product. -/
theorem hasSum_finiteHamiltonian_quadratic (S : Finset ℕ)
    (x : finiteHamiltonianDomain S) :
    HasSum (fun n : finitePrimeSemigroup S => finiteEnergy n * ‖x.1 n‖ ^ 2)
      (inner ℂ x.1 (finiteHamiltonian S x)).re := by
  have h := RCLike.hasSum_re ℂ
    (lp.hasSum_inner (𝕜 := ℂ) x.1 (finiteHamiltonian S x))
  simpa only [finiteHamiltonian_coordinate_quadratic] using h

/-- Summability form of the energy quadratic-form expansion. -/
theorem summable_finiteHamiltonian_quadratic (S : Finset ℕ)
    (x : finiteHamiltonianDomain S) :
    Summable (fun n : finitePrimeSemigroup S => finiteEnergy n * ‖x.1 n‖ ^ 2) :=
  (hasSum_finiteHamiltonian_quadratic S x).summable

/-- The real part of the Hamiltonian quadratic form equals the sum of the
nonnegative coordinate energy contributions. -/
theorem finiteHamiltonian_quadratic_eq_tsum (S : Finset ℕ)
    (x : finiteHamiltonianDomain S) :
    (inner ℂ x.1 (finiteHamiltonian S x)).re =
      ∑' n : finitePrimeSemigroup S, finiteEnergy n * ‖x.1 n‖ ^ 2 :=
  (hasSum_finiteHamiltonian_quadratic S x).tsum_eq.symm

/-- The logarithmic Hamiltonian is positive on its natural domain when
`S` consists of primes. No self-adjointness assertion is needed here. -/
theorem finiteHamiltonian_nonneg {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) (x : finiteHamiltonianDomain S) :
    0 ≤ (inner ℂ x.1 (finiteHamiltonian S x)).re := by
  rw [finiteHamiltonian_quadratic_eq_tsum]
  exact tsum_nonneg (fun n => mul_nonneg (finiteEnergy_nonneg hS n) (sq_nonneg _))

end

end BostConnes
end BrickPileLean
