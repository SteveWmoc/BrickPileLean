import BrickPileLean.BostConnes.FiniteHamiltonianTimeEvolution
import BrickPileLean.BostConnes.FinitePointNormContinuity

namespace BrickPileLean
namespace BostConnes

open Filter
open scoped BigOperators Topology

noncomputable section

/-- The real-time operators preserve Hilbert-space distances. -/
theorem dist_timeOperator (S : Finset ℕ) (t : ℝ) (x y : FiniteHilbertSpace S) :
    dist (timeOperator S t x) (timeOperator S t y) = dist x y :=
  (timeIsometry S t).isometry.dist_eq x y

/-- Every finite basis sum has a continuous real-time orbit. -/
theorem continuous_timeOperator_basis_sum (S : Finset ℕ)
    (F : Finset (finitePrimeSemigroup S)) (c : finitePrimeSemigroup S → ℂ) :
    Continuous (fun t : ℝ => timeOperator S t (∑ n ∈ F, c n • basisVector S n)) := by
  have hfun :
      (fun t : ℝ => timeOperator S t (∑ n ∈ F, c n • basisVector S n)) =
        (fun t : ℝ => ∑ n ∈ F, c n • (timePhase t n • basisVector S n)) := by
    funext t
    simp only [map_sum, map_smul, timeOperator_basisVector]
  rw [hfun]
  exact continuous_finset_sum F (fun n _ =>
    continuous_const.smul ((continuous_timePhase n).smul continuous_const))

/-- The diagonal unitary group is strongly continuous: every Hilbert-space
vector, including one with infinite support, has a norm-continuous orbit. -/
theorem continuous_timeOperator_apply (S : Finset ℕ) (x : FiniteHilbertSpace S) :
    Continuous (fun t : ℝ => timeOperator S t x) := by
  classical
  rw [continuous_iff_continuousAt]
  intro t₀
  apply Metric.continuousAt_iff'.2
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have happ : Tendsto
      (fun F : Finset (finitePrimeSemigroup S) => ∑ n ∈ F, x n • basisVector S n)
      atTop (𝓝 x) := hasSum_basisVector S x
  have hnear := (Metric.tendsto_nhds.1 happ) (ε / 3) hε3
  obtain ⟨F, hF⟩ := hnear.exists
  let b : FiniteHilbertSpace S := ∑ n ∈ F, x n • basisVector S n
  have hb : dist b x < ε / 3 := hF
  have hb_cont : Continuous (fun t : ℝ => timeOperator S t b) :=
    continuous_timeOperator_basis_sum S F (fun n => x n)
  have hmid : ∀ᶠ t in 𝓝 t₀,
      dist (timeOperator S t b) (timeOperator S t₀ b) < ε / 3 :=
    (Metric.continuousAt_iff'.1 hb_cont.continuousAt) (ε / 3) hε3
  filter_upwards [hmid] with t ht
  have htri := dist_triangle (timeOperator S t x) (timeOperator S t b)
    (timeOperator S t₀ x)
  have htri' := dist_triangle (timeOperator S t b) (timeOperator S t₀ b)
    (timeOperator S t₀ x)
  rw [dist_timeOperator] at htri
  rw [dist_timeOperator] at htri'
  have hxb : dist x b < ε / 3 := by simpa only [dist_comm] using hb
  linarith

/-- The restriction to the Hamiltonian domain is continuous in its inherited
Hilbert norm. -/
theorem continuous_hamiltonianDomainTimeEvolution (S : Finset ℕ)
    (x : finiteHamiltonianDomain S) :
    Continuous (fun t : ℝ => hamiltonianDomainTimeEvolution S t x) := by
  apply continuous_induced_rng.mpr
  exact continuous_timeOperator_apply S x.1

/-- For a domain vector, its Hamiltonian image also has a continuous orbit. -/
theorem continuous_finiteHamiltonian_timeEvolution (S : Finset ℕ)
    (x : finiteHamiltonianDomain S) :
    Continuous (fun t : ℝ =>
      finiteHamiltonian S (hamiltonianDomainTimeEvolution S t x)) := by
  simp only [finiteHamiltonian_timeEvolution]
  exact continuous_timeOperator_apply S (finiteHamiltonian S x)

/-- Real-time orbits are continuous as pairs of a vector and its Hamiltonian
image, i.e. in the topology inherited from the graph in `ℋ × ℋ`. -/
theorem continuous_timeEvolution_graph (S : Finset ℕ)
    (x : finiteHamiltonianDomain S) :
    Continuous (fun t : ℝ =>
      (timeOperator S t x.1,
        finiteHamiltonian S (hamiltonianDomainTimeEvolution S t x))) := by
  exact (continuous_timeOperator_apply S x.1).prodMk
    (continuous_finiteHamiltonian_timeEvolution S x)

end

end BostConnes
end BrickPileLean
