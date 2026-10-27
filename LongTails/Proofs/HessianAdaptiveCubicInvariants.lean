import LongTails.Proofs.HessianAdaptiveCubicModel
import LongTails.Proofs.HessianAdaptiveCubicWeights

namespace LongTails.Proofs.HessianAdaptiveCubicInvariants

open LongTails.Setups.HessianAdaptiveStochasticConvex
open LongTails.Algorithms.HessianAdaptiveCubic
open LongTails.Proofs.HessianAdaptiveCubicModel
open LongTails.Proofs.HessianAdaptiveCubicWeights

structure Invariant (p : Public) (s : State p.d) : Prop where
  iteration : 1 ≤ s.iteration
  scale : 0 < s.scale
  weight : 0 ≤ s.weight
  weight_pos : 0 < s.weight ∨ s.iteration = 1
  point : s.point ∈ p.C
  dual : s.dual ∈ p.C
  trial : s.trial ∈ p.C

lemma initial_invariant (p : Public) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σg) (hx : p.x0 ∈ p.C) :
    Invariant p (initial p) := by
  constructor
  · simp [initial]
  · dsimp [initial]
    positivity
  · simp [initial]
  · simp [initial]
  · exact hx
  · exact hx
  · exact hx

lemma center_mem (p : Public) (s : State p.d) (hs : Invariant p s) : center s ∈ p.C := by
  apply p.C.convex hs.point hs.dual (sub_nonneg.mpr (mixing_le_one hs.iteration))
    (mixing_pos s.iteration).le
  ring

lemma queryPoint_eq {d : ℕ} (s : State d) :
    queryPoint s = (1 - mixing s.iteration) • s.point + mixing s.iteration • s.trial := by
  unfold queryPoint center displacement
  module

lemma queryPoint_mem (p : Public) (s : State p.d) (hs : Invariant p s) : queryPoint s ∈ p.C := by
  rw [queryPoint_eq]
  apply p.C.convex hs.point hs.trial (sub_nonneg.mpr (mixing_le_one hs.iteration))
    (mixing_pos s.iteration).le
  ring

lemma primal_mem (p : Public) (s : State p.d) (H : Point p.d →L[ℝ] Point p.d) :
    primal p s H ∈ p.C :=
  (model_minimize_spec p.C p.x0 _ _ _ _ _).1

lemma residualWeight_nonneg (p : Public) (s : State p.d) (hD : 0 < p.D)
    (hs : Invariant p s) : 0 ≤ residualWeight p s := by
  have ha := increment_pos p s hD hs.scale hs.iteration hs.weight_pos
  have hτ := damping_pos p s hD hs.scale hs.iteration
  have hα := mixing_pos s.iteration
  have hκ := hs.scale
  unfold residualWeight
  positivity

lemma advance_scale_ge (p : Public) (s : State p.d) (g : Point p.d) (hD : 0 < p.D)
    (hs : Invariant p s) : s.scale ≤ (advance p s g).scale := by
  have hW := residualWeight_nonneg p s hD hs
  apply le_trans _ (le_max_left _ _)
  apply (Real.le_sqrt hs.scale.le (by positivity)).2
  nlinarith [div_nonneg (mul_nonneg hW (sq_nonneg ‖g - s.modelGradient -
    s.modelHessian (displacement s)‖)) (sq_nonneg p.D)]

lemma advance_invariant (p : Public) (s : State p.d) (g : Point p.d)
    (hD : 0 < p.D) (hx : p.x0 ∈ p.C) (hs : Invariant p s) : Invariant p (advance p s g) := by
  have ha := increment_pos p s hD hs.scale hs.iteration hs.weight_pos
  have hA : 0 < s.weight + increment p s := by linarith [hs.weight]
  constructor
  · dsimp [advance]
    omega
  · exact hs.scale.trans_le (advance_scale_ge p s g hD hs)
  · exact hA.le
  · exact Or.inl hA
  · dsimp only [advance]
    have he : (s.weight + increment p s)⁻¹ •
        (s.weight • s.point + increment p s • s.trial) =
        (s.weight / (s.weight + increment p s)) • s.point +
        (increment p s / (s.weight + increment p s)) • s.trial := by
      simp only [smul_add, smul_smul, div_eq_mul_inv]
      congr 1 <;> congr 1 <;> ring
    rw [he]
    apply p.C.convex hs.point hs.trial (div_nonneg hs.weight hA.le) (div_nonneg ha.le hA.le)
    field_simp
  · exact (model_minimize_spec p.C p.x0 _ _ _ _ _).1
  · exact hx

lemma update_invariant (p : Public) (s : State p.d)
    (reply : Point p.d × (Point p.d →L[ℝ] Point p.d))
    (hD : 0 < p.D) (hx : p.x0 ∈ p.C) (hs : Invariant p s) :
    Invariant p (update p s reply) := by
  unfold update
  split_ifs
  · exact ⟨hs.iteration, hs.scale, hs.weight, hs.weight_pos, hs.point, hs.dual, hs.trial⟩
  · exact ⟨hs.iteration, hs.scale, hs.weight, hs.weight_pos, hs.point, hs.dual,
      primal_mem p s reply.2⟩
  · exact advance_invariant p s reply.1 hD hx hs

lemma modelState_invariant (p : Public) (s : State p.d) (g : Point p.d)
    (H : Point p.d →L[ℝ] Point p.d) (hs : Invariant p s) :
    Invariant p (modelState p s g H) := by
  exact ⟨hs.iteration, hs.scale, hs.weight, hs.weight_pos, hs.point, hs.dual,
    primal_mem p _ H⟩

lemma roundState_invariant {Ω : Type*} (p : Public) (g : Point p.d → Ω → Point p.d)
    (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → Ω)
    (hD : 0 < p.D) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σg) (hx : p.x0 ∈ p.C) (n : ℕ) :
    Invariant p (roundState p g H ξ n) := by
  induction n with
  | zero => exact initial_invariant p hρ hσ hx
  | succ n ih =>
    exact advance_invariant p _ _ hD hx (modelState_invariant p _ _ _ ih)

lemma roundState_iteration {Ω : Type*} (p : Public) (g : Point p.d → Ω → Point p.d)
    (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → Ω) (n : ℕ) :
    (roundState p g H ξ n).iteration = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (roundState p g H ξ n).iteration + 1 = n + 1 + 1
    omega

lemma roundState_phase {Ω : Type*} (p : Public) (g : Point p.d → Ω → Point p.d)
    (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → Ω) (n : ℕ) :
    (roundState p g H ξ n).phase = 0 := by
  cases n <;> rfl

lemma displacement_bound (p : Public) (s : State p.d) (hs : Invariant p s)
    (hdiam : ∀ x ∈ p.C, ∀ y ∈ p.C, ‖x - y‖ ≤ p.D) :
    ‖displacement s‖ ≤ mixing s.iteration * p.D := by
  rw [displacement, norm_smul, Real.norm_eq_abs, abs_of_pos (mixing_pos _)]
  exact mul_le_mul_of_nonneg_left (hdiam _ hs.trial _ hs.dual) (mixing_pos _).le

lemma roundState_gap_nonneg {Ω : Type*} (p : Public) (g : Point p.d → Ω → Point p.d)
    (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → Ω)
    (hD : 0 < p.D) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σg) (hx : p.x0 ∈ p.C)
    (f : Point p.d → ℝ) (xstar : Point p.d) (hmin : IsMinOn f p.C xstar) (n : ℕ) :
    0 ≤ f (output (roundState p g H ξ n)) - f xstar := by
  exact sub_nonneg.mpr (hmin (roundState_invariant p g H ξ hD hρ hσ hx n).point)

lemma modelAt_invariant {Ω : Type*} (p : Public) (g : Point p.d → Ω → Point p.d)
    (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → Ω)
    (hD : 0 < p.D) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σg) (hx : p.x0 ∈ p.C) (n : ℕ) :
    Invariant p (modelAt p g H ξ n) :=
  modelState_invariant p _ _ _ (roundState_invariant p g H ξ hD hρ hσ hx n)

lemma roundState_scale_floor {Ω : Type*} (p : Public) (g : Point p.d → Ω → Point p.d)
    (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → Ω)
    (hρ : 0 ≤ p.ρ) (n : ℕ) :
    p.σg * ((n + 1 : ℕ) : ℝ) ^ 3 / p.D ^ 2 ≤ (roundState p g H ξ n).scale := by
  cases n with
  | zero => simpa [roundState, initial] using (show p.σg / p.D ^ 2 ≤ 2 * p.ρ + p.σg / p.D ^ 2 by linarith)
  | succ n =>
    have h := advance_scale_floor p (modelAt p g H ξ n)
      (g (queryPoint (modelAt p g H ξ n)) (ξ (3 * n + 2)))
    have hi : (modelAt p g H ξ n).iteration = n + 1 := roundState_iteration p g H ξ n
    rw [hi] at h
    exact h

end LongTails.Proofs.HessianAdaptiveCubicInvariants
