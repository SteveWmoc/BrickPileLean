import BrickPileLean.BostConnes.FiniteAnalyticMonomial

namespace BrickPileLean
namespace BostConnes

open Filter

noncomputable section

/-- For fixed arithmetic state `n`, the real-time phase `t ↦ n^{it}` is continuous. -/
theorem continuous_timePhase
    {S : Finset ℕ} (n : finitePrimeSemigroup S) :
    Continuous fun t : ℝ => timePhase t n := by
  unfold timePhase
  fun_prop

/-- Time evolution is point-norm continuous on the dense algebraic Toeplitz core. -/
theorem continuous_ambientTimeEvolution_core
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (a : finiteToeplitzCore hS) :
    Continuous fun t : ℝ =>
      ambientTimeEvolution S t (a : FiniteOperator S) := by
  let a₀ : StarAlgebra.adjoin ℂ (primeShiftSet hS) := ⟨a.1, a.2⟩
  change Continuous fun t : ℝ =>
    ambientTimeStarAlgEquiv S t (a₀ : FiniteOperator S)
  induction a₀ using StarAlgebra.adjoin_induction_subtype with
  | mem x hx =>
      rcases hx with ⟨p, rfl⟩
      simp_rw [ambientTimeStarAlgEquiv_apply, ambientTimeEvolution_shift hS]
      exact (continuous_timePhase (primeSemigroupElement S p)).smul continuous_const
  | algebraMap c =>
      simpa using
        (continuous_const :
          Continuous fun _ : ℝ => algebraMap ℂ (FiniteOperator S) c)
  | add x y hx hy =>
      simpa using hx.add hy
  | mul x y hx hy =>
      simpa using hx.mul hy
  | star x hx =>
      simpa using hx.star

/-- Each ambient time automorphism preserves distances. -/
theorem dist_ambientTimeEvolution
    {S : Finset ℕ} (t : ℝ) (a b : FiniteOperator S) :
    dist (ambientTimeEvolution S t a) (ambientTimeEvolution S t b) =
      dist a b := by
  change dist (ambientTimeStarAlgEquiv S t a)
      (ambientTimeStarAlgEquiv S t b) = dist a b
  exact (StarAlgEquiv.isometry (ambientTimeStarAlgEquiv S t)).dist_eq a b

/-- Time evolution is point-norm continuous on the full finite Toeplitz algebra. -/
theorem continuous_ambientTimeEvolution_finiteToeplitz
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (a : finiteToeplitzAlgebra hS) :
    Continuous fun t : ℝ =>
      ambientTimeEvolution S t (a : FiniteOperator S) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  apply Metric.continuousAt_iff'.2
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have ha_closure :
      (a : FiniteOperator S) ∈
        closure (finiteToeplitzCore hS : Set (FiniteOperator S)) := by
    have ha := a.2
    change (a : FiniteOperator S) ∈
      (StarAlgebra.adjoin ℂ (primeShiftSet hS)).topologicalClosure at ha
    rw [StarSubalgebra.topologicalClosure_coe] at ha
    simpa [finiteToeplitzCore] using ha
  obtain ⟨b, hb, hab⟩ :=
    (Metric.mem_closure_iff.1 ha_closure) (ε / 3) hε3
  let b₀ : finiteToeplitzCore hS := ⟨b, hb⟩
  have hb_cont := continuous_ambientTimeEvolution_core hS b₀
  have hmid :
      ∀ᶠ t in 𝓝 t₀,
        dist (ambientTimeEvolution S t b)
          (ambientTimeEvolution S t₀ b) < ε / 3 :=
    (Metric.continuousAt_iff'.1 hb_cont.continuousAt) (ε / 3) hε3
  filter_upwards [hmid] with t ht
  have hleft :
      dist (ambientTimeEvolution S t (a : FiniteOperator S))
          (ambientTimeEvolution S t b) =
        dist (a : FiniteOperator S) b :=
    dist_ambientTimeEvolution t _ _
  have hright :
      dist (ambientTimeEvolution S t₀ b)
          (ambientTimeEvolution S t₀ (a : FiniteOperator S)) =
        dist b (a : FiniteOperator S) :=
    dist_ambientTimeEvolution t₀ _ _
  calc
    dist (ambientTimeEvolution S t (a : FiniteOperator S))
        (ambientTimeEvolution S t₀ (a : FiniteOperator S)) ≤
      dist (ambientTimeEvolution S t (a : FiniteOperator S))
          (ambientTimeEvolution S t b) +
        dist (ambientTimeEvolution S t b)
          (ambientTimeEvolution S t₀ (a : FiniteOperator S)) :=
      dist_triangle _ _ _
    _ ≤
      dist (ambientTimeEvolution S t (a : FiniteOperator S))
          (ambientTimeEvolution S t b) +
        (dist (ambientTimeEvolution S t b)
            (ambientTimeEvolution S t₀ b) +
          dist (ambientTimeEvolution S t₀ b)
            (ambientTimeEvolution S t₀ (a : FiniteOperator S))) := by
      gcongr
      exact dist_triangle _ _ _
    _ =
      dist (a : FiniteOperator S) b +
        (dist (ambientTimeEvolution S t b)
            (ambientTimeEvolution S t₀ b) +
          dist b (a : FiniteOperator S)) := by
      rw [hleft, hright]
    _ < ε := by
      rw [dist_comm b (a : FiniteOperator S)] at hab
      linarith

/-- The restricted finite Toeplitz dynamics is point-norm continuous. -/
theorem continuous_finiteTimeEvolution_apply
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (a : finiteToeplitzAlgebra hS) :
    Continuous fun t : ℝ => finiteTimeEvolution hS t a := by
  apply continuous_induced_rng.mpr
  simpa only [Function.comp_def, finiteTimeEvolution_coe] using
    continuous_ambientTimeEvolution_finiteToeplitz hS a

end

end BostConnes
end BrickPileLean
