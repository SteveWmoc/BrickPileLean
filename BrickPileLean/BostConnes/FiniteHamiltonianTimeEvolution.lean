import BrickPileLean.BostConnes.FiniteHamiltonianSelfAdjoint

namespace BrickPileLean
namespace BostConnes

open scoped ENNReal

noncomputable section

/-- Real-time evolution multiplies every coordinate by its arithmetic phase,
including for vectors with infinite support. -/
theorem timeOperator_apply_coordinate (S : Finset ℕ) (t : ℝ)
    (x : FiniteHilbertSpace S) (n : finitePrimeSemigroup S) :
    timeOperator S t x n = timePhase t n * x n := by
  classical
  let ev := lp.evalCLM ℂ (fun _ : finitePrimeSemigroup S => ℂ) 2 n
  have hmaps : ev.comp (timeOperator S t) = timePhase t n • ev := by
    refine lp.ext_continuousLinearMap (ENNReal.ofNat_ne_top (n := 2)) ?_
    intro m
    apply ContinuousLinearMap.ext
    intro z
    change timeOperator S t (lp.single 2 m z) n =
      timePhase t n * lp.single 2 m z n
    rw [timeOperator_single]
    by_cases h : n = m
    · subst m
      simp
    · simp [lp.single_apply, Pi.single_apply, h]
  exact congrArg (fun f : FiniteHilbertSpace S →L[ℂ] ℂ => f x) hmaps

/-- Real time preserves each coordinate norm. -/
theorem norm_timeOperator_apply_coordinate (S : Finset ℕ) (t : ℝ)
    (x : FiniteHilbertSpace S) (n : finitePrimeSemigroup S) :
    ‖timeOperator S t x n‖ = ‖x n‖ := by
  rw [timeOperator_apply_coordinate, norm_mul, norm_timePhase, one_mul]

/-- Membership in the natural Hamiltonian domain is invariant under real-time
evolution, since the energy-weighted square sum is unchanged. -/
theorem timeOperator_mem_finiteHamiltonianDomain_iff (S : Finset ℕ) (t : ℝ)
    (x : FiniteHilbertSpace S) :
    timeOperator S t x ∈ finiteHamiltonianDomain S ↔ x ∈ finiteHamiltonianDomain S := by
  rw [mem_finiteHamiltonianDomain_iff, mem_finiteHamiltonianDomain_iff]
  simp only [norm_timeOperator_apply_coordinate]

/-- Real-time evolution restricted to the Hamiltonian domain. No boundedness
of the Hamiltonian itself is needed for this linear map. -/
def hamiltonianDomainTimeEvolution (S : Finset ℕ) (t : ℝ) :
    finiteHamiltonianDomain S →ₗ[ℂ] finiteHamiltonianDomain S where
  toFun x := ⟨timeOperator S t x.1,
    (timeOperator_mem_finiteHamiltonianDomain_iff S t x.1).mpr x.2⟩
  map_add' x y := by
    apply Subtype.ext
    exact (timeOperator S t).map_add x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    exact (timeOperator S t).map_smul c x.1

@[simp] theorem hamiltonianDomainTimeEvolution_coe (S : Finset ℕ) (t : ℝ)
    (x : finiteHamiltonianDomain S) :
    (hamiltonianDomainTimeEvolution S t x : FiniteHilbertSpace S) =
      timeOperator S t x.1 := rfl

/-- The Hamiltonian commutes with real-time evolution on its entire natural
domain. Both sides are elements of the ambient Hilbert space. -/
theorem finiteHamiltonian_timeEvolution (S : Finset ℕ) (t : ℝ)
    (x : finiteHamiltonianDomain S) :
    finiteHamiltonian S (hamiltonianDomainTimeEvolution S t x) =
      timeOperator S t (finiteHamiltonian S x) := by
  apply lp.ext
  funext n
  change (finiteEnergy n : ℂ) * timeOperator S t x.1 n =
    timeOperator S t (finiteHamiltonian S x) n
  rw [timeOperator_apply_coordinate, timeOperator_apply_coordinate,
    finiteHamiltonian_apply]
  ring

/-- Real-time evolution also preserves the Hilbert norm of the Hamiltonian
output, as required for invariance of the graph norm. -/
theorem norm_finiteHamiltonian_timeEvolution (S : Finset ℕ) (t : ℝ)
    (x : finiteHamiltonianDomain S) :
    ‖finiteHamiltonian S (hamiltonianDomainTimeEvolution S t x)‖ =
      ‖finiteHamiltonian S x‖ := by
  rw [finiteHamiltonian_timeEvolution]
  change ‖timeIsometry S t (finiteHamiltonian S x)‖ = ‖finiteHamiltonian S x‖
  exact (timeIsometry S t).norm_map _

end

end BostConnes
end BrickPileLean
