import LongTails.Algorithms.LocalizedClippedExtragradient
import LongTails.Proofs.ClippedExtragradientBatch
import LongTails.Proofs.ClippedExtragradientConfidence

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.ClippedExtragradient

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [CompleteSpace E] in
lemma measurable_batchStep_of {A : Type*} [MeasurableSpace A]
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (n : ℕ) (b S d r : ℝ) {anchor center x : A → E}
    {samples : A → (Fin n → Ω) × (Fin n → Ω)}
    (ha : Measurable anchor) (hc : Measurable center) (hx : Measurable x)
    (hs : Measurable samples) :
    Measurable (fun w => batchStep n b S d r (anchor w) (center w) g (x w) (samples w)) := by
  have hfirst : Measurable (fun w => regularizedReply r (anchor w) (x w)
      ((1 / (n : ℝ)) • ∑ i, g (x w) ((samples w).1 i))) := by
    unfold regularizedReply
    apply Measurable.add
    · apply Measurable.const_smul
      apply Finset.measurable_sum
      intro i _
      exact hg.comp (hx.prodMk ((measurable_pi_apply i).comp (measurable_fst.comp hs)))
    · exact (hx.sub ha).const_smul r
  have hy := (measurable_halfStep b S).comp (hx.prodMk hfirst)
  have hsecond : Measurable (fun w => regularizedReply r (anchor w)
      (halfStep b S (x w) (regularizedReply r (anchor w) (x w)
        ((1 / (n : ℝ)) • ∑ i, g (x w) ((samples w).1 i))))
      ((1 / (n : ℝ)) • ∑ i, g
        (halfStep b S (x w) (regularizedReply r (anchor w) (x w)
          ((1 / (n : ℝ)) • ∑ j, g (x w) ((samples w).1 j)))) ((samples w).2 i))) := by
    unfold regularizedReply
    apply Measurable.add
    · apply Measurable.const_smul
      apply Finset.measurable_sum
      intro i _
      exact hg.comp (hy.prodMk ((measurable_pi_apply i).comp (measurable_snd.comp hs)))
    · exact (hy.sub ha).const_smul r
  exact (measurable_finishStep d).comp
    (((measurable_stepSize b S).comp hfirst).prodMk (hc.prodMk (hx.prodMk hsecond)))

omit [CompleteSpace E] in
lemma measurable_batchStep {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (n : ℕ) (b S d r : ℝ)
    (anchor center : E) :
    Measurable (fun w : E × ((Fin n → Ω) × (Fin n → Ω)) =>
      batchStep n b S d r anchor center g w.1 w.2) := by
  have hfirst : Measurable (fun w : E × ((Fin n → Ω) × (Fin n → Ω)) =>
      regularizedReply r anchor w.1 ((1 / (n : ℝ)) • ∑ i, g w.1 (w.2.1 i))) :=
    (measurable_batch_reply hg n r anchor).comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hγ := (measurable_stepSize b S).comp hfirst
  have hy := (measurable_halfStep b S).comp (measurable_fst.prodMk hfirst)
  have hsecond := (measurable_batch_reply hg n r anchor).comp
    (hy.prodMk (measurable_snd.comp measurable_snd))
  exact (measurable_finishStep d).comp
    (hγ.prodMk (measurable_const.prodMk (measurable_fst.prodMk hsecond)))

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
omit [MeasurableSpace E] in
lemma batchStep_ball (n : ℕ) (b S d r : ℝ) (hd : 0 ≤ d)
    (anchor center : E) (g : E → Ω → E) (x : E)
    (samples : (Fin n → Ω) × (Fin n → Ω)) :
    ‖batchStep n b S d r anchor center g x samples - center‖ ≤ 2 * d := by
  exact finishStep_ball hd _ _ _ _

set_option maxHeartbeats 1200000 in
lemma batchStep_integral {g : E → Ω → E} {F : E → E} {σ a b S r d : ℝ}
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) P)
    (hmean : ∀ x, (∫ ω, g x ω ∂P) = F x)
    (hvi : ∀ x, Integrable (fun ω => ‖g x ω - F x‖ ^ 2) P)
    (hv : ∀ x, (∫ ω, ‖g x ω - F x‖ ^ 2 ∂P) ≤ σ ^ 2)
    (n : ℕ) (hn : 0 < n) (hb : 0 < b) (hS : 0 < S)
    (haS : a ≤ S) (hr : 0 ≤ r) (hd : 0 ≤ d) (hrS : r ≤ S)
    (hscale : r * b ^ 2 * d ^ 2 ≤ S) (anchor center x p : E)
    (hp : ‖p - center‖ ≤ 2 * d) (hx : ‖x - p‖ ≤ 3 * d)
    (hmono : ∀ y, r * ‖y - p‖ ^ 2 ≤ ⟪HolderMonotone.reg F r anchor y, y - p⟫)
    (hl : ∀ first, ‖HolderMonotone.reg F r anchor (halfStep b S x first) -
        HolderMonotone.reg F r anchor x‖ ≤
      2 * (a + b * ‖HolderMonotone.reg F r anchor x‖) * ‖x - halfStep b S x first‖) :
    (∫ samples : (Fin n → Ω) × (Fin n → Ω),
      ‖batchStep n b S d r anchor center g x samples - p‖ ^ 2
      ∂(Measure.pi (fun _ : Fin n => P)).prod (Measure.pi (fun _ : Fin n => P))) ≤
      (1 - r / (4608 * S)) * ‖x - p‖ ^ 2 + (σ ^ 2 / n) / (64 * S ^ 2) := by
  let G : E → (Fin n → Ω) → E := fun y ξ =>
    regularizedReply r anchor y ((1 / (n : ℝ)) • ∑ i, g y (ξ i))
  have hG : Measurable (Function.uncurry G) := measurable_batch_reply hg n r anchor
  have hm (y : E) := batch_reply_moments hg hgi hmean hvi hv n hn anchor y (r := r)
  change (∫ w : (Fin n → Ω) × (Fin n → Ω),
    ‖finishStep d (stepSize b S (G x w.1)) center x
      (G (halfStep b S x (G x w.1)) w.2) - p‖ ^ 2
    ∂(Measure.pi (fun _ : Fin n => P)).prod (Measure.pi (fun _ : Fin n => P))) ≤ _
  exact one_step_integral (P := Measure.pi (fun _ : Fin n => P))
    (G1 := G x) (G2 := G) hb hS haS hr hd hrS hscale (by positivity)
    (HolderMonotone.reg F r anchor) center x p hp hx hmono hl
    (hG.comp measurable_prodMk_left) (hm x).2.2.1 (hm x).2.2.2 hG
    (fun y => (hm y).1) (fun y => (hm y).2.1)
    (fun y => (hm y).2.2.1) (fun y => (hm y).2.2.2)

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] in
omit [MeasurableSpace E] in
lemma tuned_local {F : E → E} (t : Tuning)
    (h0 : 0 ≤ t.L0) (h1 : 0 ≤ t.L1) (hR : 0 < t.R) (hε : 0 < t.ε)
    (hc : Continuous F)
    (hlip : ∀ x y M, (∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖F (x + θ • (y - x))‖ ≤ M) →
      ‖F x - F y‖ ≤ (t.L0 + t.L1 * M) * ‖x - y‖)
    (s : ℕ) {anchor p x : E}
    (hp : HolderMonotone.reg F (regularization t s) anchor p = 0)
    (hF : ‖F p‖ ≤ t.ε) (hx : ‖x - p‖ ≤ 3 * radius t s) (first : E) :
    ‖HolderMonotone.reg F (regularization t s) anchor
        (halfStep (clippingScale t s) (localScale t s) x first) -
        HolderMonotone.reg F (regularization t s) anchor x‖ ≤
      2 * (t.L0 + regularization t s + t.L1 * (t.ε + 4 * regularization t s * radius t s) +
        clippingScale t s * ‖HolderMonotone.reg F (regularization t s) anchor x‖) *
        ‖x - halfStep (clippingScale t s) (localScale t s) x first‖ := by
  have hr := regularization_pos t hR hε s
  have hd := radius_pos t hR s
  have hb := clippingScale_pos t h1 hR s
  have hS := hr.trans_le (localScale_lower t h0 h1 hR hε s)
  have hLb : t.L1 ≤ clippingScale t s := by
    unfold clippingScale
    linarith [one_div_pos.mpr hd]
  have he : ‖x - halfStep (clippingScale t s) (localScale t s) x first‖ =
      stepSize (clippingScale t s) (localScale t s) first * ‖first‖ := by
    unfold halfStep
    rw [sub_sub_cancel, norm_smul, Real.norm_eq_abs,
      abs_of_pos (stepSize_pos hS first)]
  have hshort : t.L1 * ‖x - halfStep (clippingScale t s) (localScale t s) x first‖ ≤ 1 / 2 := by
    rw [he]
    have hh := stepSize_mul_norm_le hb hS first
    have hh' := (le_div_iff₀ (show 0 < 16 * clippingScale t s by positivity)).mp hh
    have hm := mul_le_mul_of_nonneg_right hLb
      (show 0 ≤ stepSize (clippingScale t s) (localScale t s) first * ‖first‖ by
        exact mul_nonneg (stepSize_pos hS first).le (norm_nonneg first))
    nlinarith
  have hh := regularized_local h0 h1 hr.le hd.le hc hlip hp hF hx hshort
  apply hh.trans
  have hn := mul_le_mul_of_nonneg_right hLb
    (norm_nonneg (HolderMonotone.reg F (regularization t s) anchor x))
  exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

lemma tuned_step_integral {g : E → Ω → E} {F : E → E} (t : Tuning)
    (h0 : 0 ≤ t.L0) (h1 : 0 ≤ t.L1) (hR : 0 < t.R) (hε : 0 < t.ε)
    (hc : Continuous F) (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (hlip : ∀ x y M, (∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖F (x + θ • (y - x))‖ ≤ M) →
      ‖F x - F y‖ ≤ (t.L0 + t.L1 * M) * ‖x - y‖)
    (hg : Measurable (Function.uncurry g)) (hgi : ∀ x, Integrable (g x) P)
    (hmean : ∀ x, (∫ ω, g x ω ∂P) = F x)
    (hvi : ∀ x, Integrable (fun ω => ‖g x ω - F x‖ ^ 2) P)
    (hv : ∀ x, (∫ ω, ‖g x ω - F x‖ ^ 2 ∂P) ≤ t.σ ^ 2)
    (s : ℕ) {anchor center p x : E}
    (hp : HolderMonotone.reg F (regularization t s) anchor p = 0)
    (hF : ‖F p‖ ≤ t.ε) (hcroot : ‖p - center‖ ≤ radius t s)
    (hx : ‖x - center‖ ≤ 2 * radius t s) :
    (∫ samples : (Fin (batchSize t s) → Ω) × (Fin (batchSize t s) → Ω),
      ‖batchStep (batchSize t s) (clippingScale t s) (localScale t s)
          (radius t s) (regularization t s) anchor center g x samples - p‖ ^ 2
      ∂(Measure.pi (fun _ : Fin (batchSize t s) => P)).prod
        (Measure.pi (fun _ : Fin (batchSize t s) => P))) ≤
      (1 - regularization t s / (4608 * localScale t s)) * ‖x - p‖ ^ 2 +
        (t.σ ^ 2 / batchSize t s) / (64 * localScale t s ^ 2) := by
  have hr := regularization_pos t hR hε s
  have hd := radius_pos t hR s
  have hS := hr.trans_le (localScale_lower t h0 h1 hR hε s)
  have hcontrol := localScale_controls t h0 h1 hR hε s
  have hxroot : ‖x - p‖ ≤ 3 * radius t s := by
    have hh := norm_sub_le_norm_sub_add_norm_sub x center p
    rw [norm_sub_rev center p] at hh
    linarith
  apply batchStep_integral hg hgi hmean hvi hv (batchSize t s) (batchSize_pos t s)
    (a := t.L0 + regularization t s + t.L1 * (t.ε + 4 * regularization t s * radius t s))
    (clippingScale_pos t h1 hR s) hS hcontrol.1 hr.le hd.le
    (localScale_lower t h0 h1 hR hε s) hcontrol.2 anchor center x p
    (by linarith) hxroot
  · intro y
    have hh := HolderMonotone.reg_strong hmono (regularization t s) anchor y p
    simpa only [hp, sub_zero] using hh
  · exact tuned_local t h0 h1 hR hε hc hlip s hp hF hxroot

end OracleTemplate.ClippedExtragradient
