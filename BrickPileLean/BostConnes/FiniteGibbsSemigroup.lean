import BrickPileLean.BostConnes.FiniteHamiltonianTimeEvolution

namespace BrickPileLean
namespace BostConnes

open scoped ENNReal

noncomputable section

/-- Adding inverse temperatures multiplies the arithmetic Gibbs weights. -/
theorem gibbsWeight_add {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (β γ : ℝ) (n : finitePrimeSemigroup S) :
    gibbsWeight (β + γ) n = gibbsWeight β n * gibbsWeight γ n := by
  simp only [gibbsWeight_eq_exp_neg_energy hS]
  rw [← Real.exp_add]
  congr 1
  ring

/-- The Gibbs operator multiplies every coordinate by its Gibbs weight,
including on vectors with infinite support. -/
theorem gibbsOperator_apply_coordinate {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (x : FiniteHilbertSpace S) (n : finitePrimeSemigroup S) :
    gibbsOperator S β x n = (gibbsWeight β n : ℂ) * x n := by
  classical
  let ev := lp.evalCLM ℂ (fun _ : finitePrimeSemigroup S => ℂ) 2 n
  have hmaps : ev.comp (gibbsOperator S β) = (gibbsWeight β n : ℂ) • ev := by
    refine lp.ext_continuousLinearMap (ENNReal.ofNat_ne_top (n := 2)) ?_
    intro m
    apply ContinuousLinearMap.ext
    intro z
    change gibbsOperator S β
        (lp.single (E := fun _ : finitePrimeSemigroup S => ℂ) 2 m z) n =
      (gibbsWeight β n : ℂ) *
        lp.single (E := fun _ : finitePrimeSemigroup S => ℂ) 2 m z n
    have hs : lp.single (E := fun _ : finitePrimeSemigroup S => ℂ) 2 m z =
        z • basisVector S m := by
      simpa only [basisVector, smul_eq_mul, mul_one] using
        (lp.single_smul (E := fun _ : finitePrimeSemigroup S => ℂ) 2 m z (1 : ℂ))
    rw [hs, map_smul, gibbsOperator_basisVector hS hβ]
    by_cases h : n = m
    · subst m
      simp [basisVector, mul_comm]
    · simp [basisVector, lp.single_apply, h]
  exact congrArg (fun f : FiniteHilbertSpace S →L[ℂ] ℂ => f x) hmaps

/-- On arbitrary vectors the diagonal multiplier is the Boltzmann
exponential of the logarithmic energy. -/
theorem gibbsOperator_apply_coordinate_energy {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β)
    (x : FiniteHilbertSpace S) (n : finitePrimeSemigroup S) :
    gibbsOperator S β x n = (Real.exp (-β * finiteEnergy n) : ℂ) * x n := by
  rw [gibbsOperator_apply_coordinate hS hβ, gibbsWeight_eq_exp_neg_energy hS]

/-- The positive-temperature Gibbs operators satisfy the heat-semigroup
composition law. No value at zero temperature parameter is asserted here. -/
theorem gibbsOperator_add {S : Finset ℕ} {β γ : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) (hγ : 0 < γ) :
    gibbsOperator S (β + γ) = (gibbsOperator S β).comp (gibbsOperator S γ) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  change gibbsOperator S (β + γ) x n = gibbsOperator S β (gibbsOperator S γ x) n
  rw [gibbsOperator_apply_coordinate hS (add_pos hβ hγ),
    gibbsOperator_apply_coordinate hS hβ, gibbsOperator_apply_coordinate hS hγ,
    gibbsWeight_add hS, Complex.ofReal_mul, mul_assoc]

/-- Gibbs damping commutes with the real-time unitary evolution. -/
theorem gibbsOperator_comp_timeOperator {S : Finset ℕ} {β : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hβ : 0 < β) (t : ℝ) :
    (gibbsOperator S β).comp (timeOperator S t) =
      (timeOperator S t).comp (gibbsOperator S β) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  change gibbsOperator S β (timeOperator S t x) n =
    timeOperator S t (gibbsOperator S β x) n
  rw [gibbsOperator_apply_coordinate hS hβ, timeOperator_apply_coordinate,
    timeOperator_apply_coordinate, gibbsOperator_apply_coordinate hS hβ]
  ring

end

end BostConnes
end BrickPileLean
