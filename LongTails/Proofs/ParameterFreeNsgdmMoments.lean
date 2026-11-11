import LongTails.Proofs.HeavyTailedFreshProcess

open MeasureTheory

namespace LongTails.Proofs.ParameterFreeNsgdmMoments

variable {S E Ω : Type*}

def timedSum (step : S → Ω → S) (noise : ℕ → S → Ω → E) [Add E] :
    ℕ → ℕ → S → E → (ℕ → Ω) → E
  | 0, _, _, z, _ => z
  | n + 1, off, s, z, ξ => timedSum step noise n (off + 1) (step s (ξ 0)) (z + noise off s (ξ 0))
      (fun k => ξ (k + 1))

lemma timedSum_eq_sum [AddCommMonoid E] (step : S → Ω → S) (noise : ℕ → S → Ω → E)
    (n off : ℕ) (s : S) (z : E) (ξ : ℕ → Ω) :
    timedSum step noise n off s z ξ = z + ∑ k ∈ Finset.range n,
      noise (off + k) (HeavyTailedProductProcess.trajectory step k s ξ) (ξ k) := by
  induction n generalizing off s z ξ with
  | zero => simp [timedSum]
  | succ n ih =>
      rw [timedSum, ih, Finset.sum_range_succ']
      simp only [HeavyTailedProductProcess.trajectory, add_zero, Nat.add_assoc, Nat.add_comm 1]
      ac_rfl

variable [MeasurableSpace S] [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma timedSum_measurable {step : S → Ω → S} {noise : ℕ → S → Ω → E}
    (hs : Measurable (Function.uncurry step)) (he : ∀ k, Measurable (Function.uncurry (noise k)))
    (n off : ℕ) :
    Measurable (fun t : (S × E) × (ℕ → Ω) => timedSum step noise n off t.1.1 t.1.2 t.2) := by
  induction n generalizing off with
  | zero => exact measurable_snd.comp measurable_fst
  | succ n ih =>
      exact (ih (off + 1)).comp (((hs.comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_pi_apply 0).comp measurable_snd))).prodMk
        ((measurable_snd.comp measurable_fst).add
          ((he off).comp ((measurable_fst.comp measurable_fst).prodMk
            ((measurable_pi_apply 0).comp measurable_snd))))).prodMk (by fun_prop))

lemma timedSum_moment (P : Measure Ω) [IsProbabilityMeasure P]
    {step : S → Ω → S} {noise : ℕ → S → Ω → E}
    (hs : Measurable (Function.uncurry step)) (he : ∀ k, Measurable (Function.uncurry (noise k)))
    {p : ℝ} {κ : ℕ → ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hi : ∀ k s, Integrable (noise k s) P) (hm : ∀ k s, (∫ ω, noise k s ω ∂P) = 0)
    (hpi : ∀ k s, Integrable (fun ω => ‖noise k s ω‖ ^ p) P)
    (hpb : ∀ k s, (∫ ω, ‖noise k s ω‖ ^ p ∂P) ≤ κ k)
    (n off : ℕ) (s : S) (z : E) :
    Integrable (fun ξ => ‖timedSum step noise n off s z ξ‖ ^ p)
      (Measure.infinitePi fun _ : ℕ => P) ∧
    (∫ ξ, ‖timedSum step noise n off s z ξ‖ ^ p ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
      ‖z‖ ^ p + 6 * ∑ k ∈ Finset.range n, κ (off + k) := by
  induction n generalizing off s z with
  | zero => simp [timedSum]
  | succ n ih =>
      let F : Ω × (ℕ → Ω) → ℝ := fun t =>
        ‖timedSum step noise n (off + 1) (step s t.1) (z + noise off s t.1) t.2‖ ^ p
      have hF : Measurable F := by
        apply Measurable.pow_const
        apply Measurable.norm
        exact (timedSum_measurable hs he n (off + 1)).comp
          ((((hs.comp measurable_prodMk_left).comp measurable_fst).prodMk
            (measurable_const.add (((he off).comp measurable_prodMk_left).comp measurable_fst))).prodMk
            measurable_snd)
      have hZi := HeavyTailedMomentBounds.integrable_norm_add_rpow z
        (by linarith : 0 < p) (hi off s).aestronglyMeasurable (hpi off s)
      have hcontrol := LongTails.Proofs.WeakGradientConvolution.nonnegative_fiber_integral_bound
        hF.stronglyMeasurable (fun t => Real.rpow_nonneg (norm_nonneg _) _)
        (Filter.Eventually.of_forall (fun ω => (ih (off + 1) (step s ω) (z + noise off s ω)).1))
        (hZi.add (integrable_const (6 * ∑ k ∈ Finset.range n, κ (off + 1 + k))))
        (Filter.Eventually.of_forall (fun ω => (ih (off + 1) (step s ω) (z + noise off s ω)).2))
      have hsplit := HeavyTailedProductProcess.head_tail_preserving P
      have heq : (fun ξ => ‖timedSum step noise (n + 1) off s z ξ‖ ^ p) =
          F ∘ (fun ξ : ℕ → Ω => (ξ 0, fun k => ξ (k + 1))) := rfl
      rw [heq]
      refine ⟨hsplit.integrable_comp_of_integrable hcontrol.1, ?_⟩
      have heint := integral_map (μ := Measure.infinitePi fun _ : ℕ => P)
        hsplit.measurable.aemeasurable hF.aestronglyMeasurable
      rw [hsplit.map_eq] at heint
      change (∫ ξ, F (ξ 0, fun k => ξ (k + 1)) ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ _
      rw [← heint]
      have hone := HeavyTailedMomentBounds.integral_norm_add_rpow_le
        (w := z) hp hp2 (hi off s) (hpi off s) (hm off s)
      simp only [Pi.add_apply] at hcontrol
      rw [integral_add hZi (integrable_const _), integral_const] at hcontrol
      simp only [probReal_univ, smul_eq_mul, one_mul] at hcontrol
      have hsum : ∑ k ∈ Finset.range (n + 1), κ (off + k) =
          κ off + ∑ k ∈ Finset.range n, κ (off + 1 + k) := by
        rw [Finset.sum_range_succ']
        simp only [add_zero, Nat.add_right_comm off 1, Nat.add_assoc]
        ring
      rw [hsum]
      linarith [hpb off s]

end LongTails.Proofs.ParameterFreeNsgdmMoments
