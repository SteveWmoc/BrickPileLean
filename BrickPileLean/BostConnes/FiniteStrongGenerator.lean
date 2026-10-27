import BrickPileLean.BostConnes.FiniteStrongContinuity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace BrickPileLean
namespace BostConnes

open MeasureTheory
open scoped Interval

noncomputable section

/-- The arithmetic phase has real-time derivative `n^{it} (log n) i`. -/
theorem hasDerivAt_timePhase {S : Finset ℕ} (n : finitePrimeSemigroup S) (t : ℝ) :
    HasDerivAt (fun u : ℝ => timePhase u n)
      (timePhase t n * ((finiteEnergy n : ℂ) * Complex.I)) t := by
  have h := (((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const
    (finiteEnergy n : ℂ)).mul_const Complex.I).cexp
  simpa only [timePhase, finiteEnergy, Complex.ofReal_mul,
    Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul, mul_assoc] using h

/-- The candidate strong velocity for a Hamiltonian-domain vector. -/
def finiteHamiltonianVelocity (S : Finset ℕ) (x : finiteHamiltonianDomain S)
    (t : ℝ) : FiniteHilbertSpace S :=
  Complex.I • timeOperator S t (finiteHamiltonian S x)

/-- Strong continuity applied to `H x` gives continuity of the velocity. -/
theorem continuous_finiteHamiltonianVelocity (S : Finset ℕ)
    (x : finiteHamiltonianDomain S) : Continuous (finiteHamiltonianVelocity S x) := by
  exact continuous_const.smul (continuous_timeOperator_apply S (finiteHamiltonian S x))

/-- The derivative identity holds at each coordinate of a domain vector. -/
theorem hasDerivAt_timeOperator_coordinate (S : Finset ℕ)
    (x : finiteHamiltonianDomain S) (t : ℝ) (n : finitePrimeSemigroup S) :
    HasDerivAt (fun u : ℝ => timeOperator S u x.1 n)
      (finiteHamiltonianVelocity S x t n) t := by
  have h := (hasDerivAt_timePhase n t).mul_const (x.1 n)
  have hfun : (fun u : ℝ => timeOperator S u x.1 n) =
      (fun u : ℝ => timePhase u n * x.1 n) := by
    funext u
    exact timeOperator_apply_coordinate S u x.1 n
  rw [hfun]
  convert h using 1
  change Complex.I * timeOperator S t (finiteHamiltonian S x) n = _
  rw [timeOperator_apply_coordinate, finiteHamiltonian_apply]
  ring

/-- Integrating the continuous Hilbert-space velocity recovers the orbit
increment. Coordinate evaluation commutes with the Bochner integral. -/
theorem integral_finiteHamiltonianVelocity (S : Finset ℕ)
    (x : finiteHamiltonianDomain S) (a b : ℝ) :
    (∫ t in a..b, finiteHamiltonianVelocity S x t) =
      timeOperator S b x.1 - timeOperator S a x.1 := by
  apply lp.ext
  funext n
  let ev := lp.evalCLM ℂ (fun _ : finitePrimeSemigroup S => ℂ) 2 n
  have hv := continuous_finiteHamiltonianVelocity S x
  have hint := hv.intervalIntegrable a b
  have hcomm := ev.intervalIntegral_comp_comm hint
  change ev (∫ t in a..b, finiteHamiltonianVelocity S x t) = _
  rw [← hcomm]
  change (∫ t in a..b, finiteHamiltonianVelocity S x t n) =
    timeOperator S b x.1 n - timeOperator S a x.1 n
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_timeOperator_coordinate S x t n)
    ((ev.continuous.comp hv).intervalIntegrable a b)

/-- Every vector in the natural Hamiltonian domain has a strongly
differentiable orbit, with velocity `i U_t H x`. -/
theorem hasDerivAt_timeOperator_apply (S : Finset ℕ)
    (x : finiteHamiltonianDomain S) (t : ℝ) :
    HasDerivAt (fun u : ℝ => timeOperator S u x.1)
      (Complex.I • timeOperator S t (finiteHamiltonian S x)) t := by
  have hv := continuous_finiteHamiltonianVelocity S x
  have h := intervalIntegral.integral_hasDerivAt_right
    (hv.intervalIntegrable 0 t)
    hv.aestronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt
  have hfun : (fun u : ℝ => ∫ s in (0 : ℝ)..u, finiteHamiltonianVelocity S x s) =
      (fun u : ℝ => timeOperator S u x.1 - timeOperator S 0 x.1) := by
    funext u
    exact integral_finiteHamiltonianVelocity S x 0 u
  rw [hfun] at h
  simpa only [sub_add_cancel, finiteHamiltonianVelocity] using
    h.add_const (timeOperator S 0 x.1)

/-- Domain invariance and commutation put the velocity in Schrödinger form. -/
theorem hasDerivAt_timeOperator_hamiltonian (S : Finset ℕ)
    (x : finiteHamiltonianDomain S) (t : ℝ) :
    HasDerivAt (fun u : ℝ => timeOperator S u x.1)
      (Complex.I • finiteHamiltonian S (hamiltonianDomainTimeEvolution S t x)) t := by
  rw [finiteHamiltonian_timeEvolution]
  exact hasDerivAt_timeOperator_apply S x t

/-- The real-time infinitesimal generator acts as `i H` on the natural domain. -/
theorem hasDerivAt_timeOperator_zero (S : Finset ℕ)
    (x : finiteHamiltonianDomain S) :
    HasDerivAt (fun t : ℝ => timeOperator S t x.1)
      (Complex.I • finiteHamiltonian S x) 0 := by
  have hzero : timeOperator S 0 (finiteHamiltonian S x) = finiteHamiltonian S x := by
    apply lp.ext
    funext n
    rw [timeOperator_apply_coordinate, timePhase_zero, one_mul]
  simpa only [hzero] using hasDerivAt_timeOperator_apply S x 0

/-- Derivative API endpoint for the strong orbit derivative. -/
theorem deriv_timeOperator_apply (S : Finset ℕ)
    (x : finiteHamiltonianDomain S) (t : ℝ) :
    deriv (fun u : ℝ => timeOperator S u x.1) t =
      Complex.I • finiteHamiltonian S (hamiltonianDomainTimeEvolution S t x) :=
  (hasDerivAt_timeOperator_hamiltonian S x t).deriv

end

end BostConnes
end BrickPileLean
