import BrickPileLean.BostConnes.FiniteHamiltonian

namespace BrickPileLean
namespace BostConnes

open scoped BigOperators ENNReal

noncomputable section

/-- Every vector is the norm-convergent sum of its canonical basis expansion. -/
theorem hasSum_basisVector (S : Finset ℕ) (x : FiniteHilbertSpace S) :
    HasSum (fun n : finitePrimeSemigroup S => x n • basisVector S n) x := by
  classical
  have hsingle (n : finitePrimeSemigroup S) :
      lp.single 2 n (x n) = x n • basisVector S n := by
    simpa only [basisVector, smul_eq_mul, mul_one] using
      (lp.single_smul 2 n (x n) (1 : ℂ))
  simpa only [hsingle] using (lp.hasSum_single ENNReal.ofNat_ne_top x)

/-- The finite linear span of the canonical basis is contained in the natural
Hamiltonian domain. No primality assumption is needed for this inclusion. -/
theorem basisVector_span_le_finiteHamiltonianDomain (S : Finset ℕ) :
    Submodule.span ℂ (Set.range (basisVector S)) ≤ finiteHamiltonianDomain S := by
  apply Submodule.span_le.mpr
  rintro _ ⟨n, rfl⟩
  exact basisVector_mem_finiteHamiltonianDomain S n

/-- Every finite basis truncation belongs to the Hamiltonian domain. -/
theorem basisVector_sum_mem_finiteHamiltonianDomain (S : Finset ℕ)
    (F : Finset (finitePrimeSemigroup S)) (c : finitePrimeSemigroup S → ℂ) :
    (∑ n ∈ F, c n • basisVector S n) ∈ finiteHamiltonianDomain S := by
  exact Submodule.sum_mem _ (fun n _ =>
    Submodule.smul_mem _ _ (basisVector_mem_finiteHamiltonianDomain S n))

/-- Canonical basis vectors have dense linear span in the arithmetic Hilbert space. -/
theorem basisVector_span_topologicalClosure (S : Finset ℕ) :
    (Submodule.span ℂ (Set.range (basisVector S))).topologicalClosure = ⊤ := by
  classical
  rw [eq_top_iff]
  intro x _
  refine mem_closure_of_tendsto (hasSum_basisVector S x) (Filter.Eventually.of_forall ?_)
  intro F
  change (∑ n ∈ F, x n • basisVector S n) ∈
    Submodule.span ℂ (Set.range (basisVector S))
  exact Submodule.sum_mem _ (fun n _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩))

/-- The natural logarithmic Hamiltonian domain is dense in the ambient
Hilbert space. This is density in the Hilbert norm, not graph-norm completeness. -/
theorem finiteHamiltonianDomain_topologicalClosure (S : Finset ℕ) :
    (finiteHamiltonianDomain S).topologicalClosure = ⊤ := by
  apply top_unique
  rw [← basisVector_span_topologicalClosure S]
  exact Submodule.topologicalClosure_mono (basisVector_span_le_finiteHamiltonianDomain S)

/-- Set-theoretic form of density of the Hamiltonian domain. -/
theorem finiteHamiltonianDomain_dense (S : Finset ℕ) :
    Dense (finiteHamiltonianDomain S : Set (FiniteHilbertSpace S)) := by
  rw [dense_iff_closure_eq]
  change ((finiteHamiltonianDomain S).topologicalClosure : Set (FiniteHilbertSpace S)) = Set.univ
  rw [finiteHamiltonianDomain_topologicalClosure]
  rfl

end

end BostConnes
end BrickPileLean
