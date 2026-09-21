import BrickPileLean.BostConnes.FiniteAnalyticMonomial

namespace BrickPileLean
namespace BostConnes

noncomputable section

/-- Adjoint shifts reverse multiplication in the finite prime semigroup. -/
theorem shiftAdjoint_mul
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m n : finitePrimeSemigroup S) :
    shiftAdjoint hS (m * n) =
      shiftAdjoint hS n * shiftAdjoint hS m := by
  unfold shiftAdjoint
  rw [shiftOperator_mul]
  exact ContinuousLinearMap.adjoint_comp _ _

/-- A common left factor in the middle of a Toeplitz product cancels:
`V_{da}* V_{db} = V_a* V_b`. -/
theorem shiftAdjoint_mul_shiftOperator_cancel_common
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (d a b : finitePrimeSemigroup S) :
    shiftAdjoint hS (d * a) * shiftOperator hS (d * b) =
      shiftAdjoint hS a * shiftOperator hS b := by
  have hd :
      shiftAdjoint hS d * shiftOperator hS d =
        (1 : FiniteOperator S) := by
    change (shiftAdjoint hS d).comp (shiftOperator hS d) =
      ContinuousLinearMap.id ℂ (FiniteHilbertSpace S)
    exact shiftAdjoint_comp_shift hS d
  rw [shiftAdjoint_mul, shiftOperator_mul]
  calc
    (shiftAdjoint hS a * shiftAdjoint hS d) *
        (shiftOperator hS d * shiftOperator hS b) =
      shiftAdjoint hS a *
        ((shiftAdjoint hS d * shiftOperator hS d) *
          shiftOperator hS b) := by
            simp only [mul_assoc]
    _ = shiftAdjoint hS a * shiftOperator hS b := by
      rw [hd]
      simp

/-- If the right middle index is a multiple of the left one, the middle
shift-adjoint pair reduces to the quotient shift. -/
theorem shiftAdjoint_mul_shiftOperator_right_multiple
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (n q : finitePrimeSemigroup S) :
    shiftAdjoint hS n * shiftOperator hS (n * q) =
      shiftOperator hS q := by
  have hn :
      shiftAdjoint hS n * shiftOperator hS n =
        (1 : FiniteOperator S) := by
    change (shiftAdjoint hS n).comp (shiftOperator hS n) =
      ContinuousLinearMap.id ℂ (FiniteHilbertSpace S)
    exact shiftAdjoint_comp_shift hS n
  rw [shiftOperator_mul]
  calc
    shiftAdjoint hS n *
        (shiftOperator hS n * shiftOperator hS q) =
      (shiftAdjoint hS n * shiftOperator hS n) *
        shiftOperator hS q := by
          simp only [mul_assoc]
    _ = shiftOperator hS q := by
      rw [hn]
      simp

/-- If the left middle index is a multiple of the right one, the middle
shift-adjoint pair reduces to the quotient adjoint shift. -/
theorem shiftAdjoint_mul_shiftOperator_left_multiple
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (r q : finitePrimeSemigroup S) :
    shiftAdjoint hS (r * q) * shiftOperator hS r =
      shiftAdjoint hS q := by
  have hr :
      shiftAdjoint hS r * shiftOperator hS r =
        (1 : FiniteOperator S) := by
    change (shiftAdjoint hS r).comp (shiftOperator hS r) =
      ContinuousLinearMap.id ℂ (FiniteHilbertSpace S)
    exact shiftAdjoint_comp_shift hS r
  rw [shiftAdjoint_mul]
  calc
    (shiftAdjoint hS q * shiftAdjoint hS r) *
        shiftOperator hS r =
      shiftAdjoint hS q *
        (shiftAdjoint hS r * shiftOperator hS r) := by
          simp only [mul_assoc]
    _ = shiftAdjoint hS q := by
      rw [hr]
      simp

/-- Product reduction when the right middle index is a multiple of the left:
`(V_m V_n*) (V_{nq} V_s*) = V_{mq} V_s*`. -/
theorem toeplitzMonomial_mul_of_right_multiple
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m n q s : finitePrimeSemigroup S) :
    toeplitzMonomial hS m n *
        toeplitzMonomial hS (n * q) s =
      toeplitzMonomial hS (m * q) s := by
  unfold toeplitzMonomial
  calc
    (shiftOperator hS m * shiftAdjoint hS n) *
        (shiftOperator hS (n * q) * shiftAdjoint hS s) =
      shiftOperator hS m *
        (shiftAdjoint hS n * shiftOperator hS (n * q)) *
        shiftAdjoint hS s := by
          simp only [mul_assoc]
    _ = shiftOperator hS m * shiftOperator hS q *
        shiftAdjoint hS s := by
          rw [shiftAdjoint_mul_shiftOperator_right_multiple]
    _ = shiftOperator hS (m * q) * shiftAdjoint hS s := by
          rw [shiftOperator_mul]

/-- Product reduction when the left middle index is a multiple of the right:
`(V_m V_{rq}*) (V_r V_s*) = V_m V_{sq}*`. -/
theorem toeplitzMonomial_mul_of_left_multiple
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m r q s : finitePrimeSemigroup S) :
    toeplitzMonomial hS m (r * q) *
        toeplitzMonomial hS r s =
      toeplitzMonomial hS m (s * q) := by
  unfold toeplitzMonomial
  calc
    (shiftOperator hS m * shiftAdjoint hS (r * q)) *
        (shiftOperator hS r * shiftAdjoint hS s) =
      shiftOperator hS m *
        (shiftAdjoint hS (r * q) * shiftOperator hS r) *
        shiftAdjoint hS s := by
          simp only [mul_assoc]
    _ = shiftOperator hS m * shiftAdjoint hS q *
        shiftAdjoint hS s := by
          rw [shiftAdjoint_mul_shiftOperator_left_multiple]
    _ = shiftOperator hS m * shiftAdjoint hS (s * q) := by
          rw [shiftAdjoint_mul hS s q]

/-- Matching middle indices cancel completely:
`(V_m V_n*) (V_n V_s*) = V_m V_s*`. -/
@[simp] theorem toeplitzMonomial_mul_matching
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (m n s : finitePrimeSemigroup S) :
    toeplitzMonomial hS m n * toeplitzMonomial hS n s =
      toeplitzMonomial hS m s := by
  simpa using
    (toeplitzMonomial_mul_of_right_multiple hS m n
      (1 : finitePrimeSemigroup S) s)

end

end BostConnes
end BrickPileLean
