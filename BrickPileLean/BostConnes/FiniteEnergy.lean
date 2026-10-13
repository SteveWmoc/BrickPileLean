import BrickPileLean.BostConnes.FiniteGibbsWeight

namespace BrickPileLean
namespace BostConnes

open scoped BigOperators

noncomputable section

/-- The energy eigenvalue associated with the basis label `n`.
This defines the spectrum data for the diagonal Hamiltonian, not its domain. -/
def finiteEnergy {S : Finset ℕ} (n : finitePrimeSemigroup S) : ℝ :=
  Real.log (n.1 : ℝ)

@[simp] theorem finiteEnergy_one (S : Finset ℕ) :
    finiteEnergy (1 : finitePrimeSemigroup S) = 0 := by
  simp [finiteEnergy]

/-- The arithmetic energy spectrum is nonnegative. -/
theorem finiteEnergy_nonneg {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) (n : finitePrimeSemigroup S) :
    0 ≤ finiteEnergy n := by
  apply Real.log_nonneg
  exact_mod_cast Nat.succ_le_of_lt (finitePrimeSemigroup_coe_pos hS n)

/-- Multiplication of basis labels adds their energies. -/
theorem finiteEnergy_mul {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) (m n : finitePrimeSemigroup S) :
    finiteEnergy (m * n) = finiteEnergy m + finiteEnergy n := by
  have hm : (m.1 : ℝ) ≠ 0 := by
    exact_mod_cast (finitePrimeSemigroup_coe_pos hS m).ne'
  have hn : (n.1 : ℝ) ≠ 0 := by
    exact_mod_cast (finitePrimeSemigroup_coe_pos hS n).ne'
  change Real.log ((m.1 * n.1 : ℕ) : ℝ) = _
  rw [Nat.cast_mul, Real.log_mul hm hn]
  rfl

/-- The existing Gibbs weight is exactly the Boltzmann exponential of energy. -/
theorem gibbsWeight_eq_exp_neg_energy {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) (β : ℝ) (n : finitePrimeSemigroup S) :
    gibbsWeight β n = Real.exp (-β * finiteEnergy n) := by
  unfold gibbsWeight finiteEnergy
  rw [Real.rpow_def_of_pos (by exact_mod_cast finitePrimeSemigroup_coe_pos hS n)]
  congr 1
  ring

/-- The Gibbs operator acts on each canonical basis vector by its Boltzmann
energy eigenvalue. The unbounded Hamiltonian is not constructed here. -/
theorem gibbsOperator_basisVector_energy {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (n : finitePrimeSemigroup S) :
    gibbsOperator S β (basisVector S n) =
      (Real.exp (-β * finiteEnergy n) : ℂ) • basisVector S n := by
  rw [gibbsOperator_basisVector hS hβ, gibbsWeight_eq_exp_neg_energy hS]

/-- The Boltzmann energy spectrum is summable at every positive temperature. -/
theorem summable_exp_neg_finiteEnergy {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) :
    Summable (fun n : finitePrimeSemigroup S => Real.exp (-β * finiteEnergy n)) := by
  have hfun : gibbsWeight (S := S) β =
      (fun n : finitePrimeSemigroup S => Real.exp (-β * finiteEnergy n)) := by
    funext n
    exact gibbsWeight_eq_exp_neg_energy hS β n
  rw [← hfun]
  exact gibbsWeight_summable hS hβ

/-- The sum of Boltzmann energy eigenvalues equals the finite Euler product.
This is a spectral sum identity; an operator trace requires trace-class theory. -/
theorem tsum_exp_neg_finiteEnergy {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) :
    (∑' n : finitePrimeSemigroup S, Real.exp (-β * finiteEnergy n)) =
      finiteEulerProduct S β := by
  simpa only [gibbsDiagonalSum, gibbsWeight_eq_exp_neg_energy hS] using
    gibbsDiagonalSum_eq_finiteEulerProduct hS hβ

end

end BostConnes
end BrickPileLean
