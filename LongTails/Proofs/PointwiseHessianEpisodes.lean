import LongTails.Proofs.PointwiseHessianLedger
import LongTails.Proofs.PointwiseHessianCounting

open scoped Classical

namespace LongTails.Proofs.PointwiseHessianEpisodes

lemma counted_growth_formula {L q : ℝ} (hL : 0 ≤ L) (hq : 1 ≤ q)
    (b : ℕ → ℝ) (c : ℕ → ℕ) (grow : ℕ → Prop) [DecidablePred grow]
    (hb : b 0 ≤ L) (hc0 : c 0 = 0) (N : ℕ)
    (hc : ∀ k < N, c (k + 1) = c k + if grow k then 1 else 0)
    (hs : ∀ k < N, b (k + 1) = if grow k then min L (b k * q) else b k) :
    b N = min L (b 0 * q ^ c N) := by
  induction N with
  | zero => simp [hc0, min_eq_right hb]
  | succ N ih =>
    have hh := ih (fun k hk => hc k (by omega)) (fun k hk => hs k (by omega))
    rw [hs N (by omega), hc N (by omega)]
    by_cases hg : grow N
    · simp only [ite_eq_left hg]
      rw [hh, min_mul_of_nonneg _ _ (by linarith : 0 ≤ q), ← min_assoc]
      have hm : L ≤ L * q := by nlinarith
      rw [min_eq_left hm, pow_succ]
      congr 1
      ring
    · simpa only [ite_eq_right hg, Nat.add_zero] using hh

lemma counted_growth_count {L q : ℝ} (hL : 0 < L) (hq : 1 < q)
    (b : ℕ → ℝ) (c : ℕ → ℕ) (grow : ℕ → Prop) [DecidablePred grow]
    (hb : 0 < b 0) (hbL : b 0 ≤ L) (hc0 : c 0 = 0) (N : ℕ)
    (hc : ∀ k < N, c (k + 1) = c k + if grow k then 1 else 0)
    (hs : ∀ k < N, b (k + 1) = if grow k then min L (b k * q) else b k)
    (hn : b N < L) : (c N : ℝ) < Real.log (L / b 0) / Real.log q := by
  have he := counted_growth_formula hL.le hq.le b c grow hbL hc0 N hc hs
  have hp : b 0 * q ^ c N < L := by
    rw [he] at hn
    exact (min_lt_iff.mp hn).resolve_left (lt_irrefl _)
  have hpow : q ^ c N < L / b 0 := (lt_div_iff₀ hb).mpr (by nlinarith)
  have hl := Real.log_lt_log (pow_pos (by linarith : 0 < q) (c N)) hpow
  rw [Real.log_pow] at hl
  exact (lt_div_iff₀ (Real.log_pos hq)).mpr hl

open LongTails.Setups.PointwiseHessianConvex
open LongTails.Algorithms.PointwiseHessianAccelerated

lemma continuation_update {p : Public} (s : State p) (g : p.E)
    (hp : s.phase = .newtonGradient) (hg : ¬ ‖g‖ ≤ gradientThreshold p)
    (hb : s.b < 1 / s.τ) :
    update s (.inl g) = { s with
      phase := .newtonHessian
      g := g
      b := min (1 / s.τ) (s.b * (1 + continuationRatio p s.τ s.r / 8)) } := by
  simp only [update, hp, readGradient, ite_eq_right hg, ite_eq_left hb]

lemma refinement_update {p : Public} (s : State p) (g : p.E)
    (hp : s.phase = .newtonGradient) (hg : ¬ ‖g‖ ≤ gradientThreshold p)
    (hb : ¬ s.b < 1 / s.τ)
    (hr : ¬ ‖s.b • g + s.x - s.center‖ ≤ ‖s.x - s.center‖ / 2) :
    update s (.inl g) = { s with phase := .newtonHessian, g := g } := by
  simp only [update, hp, readGradient, ite_eq_right hg, ite_eq_right hb, ite_eq_right hr]

lemma continuation_regularization_mono {p : Public} (s : State p) (g : p.E)
    (hp : s.phase = .newtonGradient) (hg : ¬ ‖g‖ ≤ gradientThreshold p)
    (hb : s.b < 1 / s.τ) (hb0 : 0 ≤ s.b) (ha : 0 ≤ continuationRatio p s.τ s.r) :
    s.b ≤ (update s (.inl g)).b ∧ (update s (.inl g)).b ≤ 1 / s.τ := by
  rw [continuation_update s g hp hg hb]
  constructor
  · apply le_min hb.le
    nlinarith
  · exact min_le_left _ _

lemma update_center_requires_accept {p : Public} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E))
    (hc : (update s reply).phase = .centerGradient) :
    PointwiseHessianLedger.Accepted s reply := by
  cases hp : s.phase with
  | finished => simp [update, hp] at hc
  | centerGradient =>
    simp only [update, hp] at hc
    split_ifs at hc <;> simp_all [finish, startTrial]
  | newtonHessian =>
    simp only [update, hp] at hc
    split_ifs at hc
    simp_all [failedTrial, startTrial]
    split_ifs at hc
  | newtonGradient =>
    by_cases hg : ‖readGradient reply‖ ≤ gradientThreshold p
    · simp only [update, hp, hg, ite_true, finish] at hc
      contradiction
    by_cases hb : s.b < 1 / s.τ
    · simp only [update, hp, hg, hb, ite_true, ite_false] at hc
      contradiction
    by_cases hr : ‖s.b • readGradient reply + s.x - s.center‖ ≤ ‖s.x - s.center‖ / 2
    · exact ⟨hp, hg, hb, hr⟩
    · simp only [update, hp, hg, hb, hr, ite_false] at hc
      contradiction

lemma path_center_count {p : Public} (s : ℕ → State p)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k)) :
    (∑ k ∈ Finset.range N, if (s k).phase = .centerGradient then (1 : ℝ) else 0) +
      (if (s N).phase = .centerGradient then (1 : ℝ) else 0) ≤
      (∑ k ∈ Finset.range N, if PointwiseHessianLedger.Accepted (s k) (reply k) then (1 : ℝ) else 0) +
      (if (s 0).phase = .centerGradient then (1 : ℝ) else 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hh := ih (fun k hk => hs k (by omega))
    have hu : (if (s (N + 1)).phase = .centerGradient then (1 : ℝ) else 0) ≤
        (if PointwiseHessianLedger.Accepted (s N) (reply N) then (1 : ℝ) else 0) := by
      by_cases hc : (s (N + 1)).phase = .centerGradient
      · have ha := update_center_requires_accept (s N) (reply N) (by rwa [← hs N (by omega)])
        simp only [ite_eq_left hc, ite_eq_left ha, le_refl]
      · simp only [ite_eq_right hc]
        split_ifs <;> norm_num
    simp only [Finset.sum_range_succ]
    linarith

lemma path_active_count {p : Public} (s : ℕ → State p)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k)) :
    (∑ k ∈ Finset.range N, if (s k).phase ≠ .finished then (1 : ℝ) else 0) ≤
      (∑ k ∈ Finset.range N, if PointwiseHessianLedger.Accepted (s k) (reply k) then (1 : ℝ) else 0) +
      2 * (∑ k ∈ Finset.range N, if (s k).phase = .newtonGradient then (1 : ℝ) else 0) +
      (∑ k ∈ Finset.range N, if (s k).phase = .newtonHessian ∧
        (s (k + 1)).phase ≠ .newtonGradient then (1 : ℝ) else 0) + 2 := by
  have hc := path_center_count s reply N hs
  have hh := PointwiseHessianLedger.path_hessian_count s reply N hs
  have hstart : (if (s 0).phase = .centerGradient then (1 : ℝ) else 0) ≤ 1 := by
    split_ifs <;> norm_num
  have hend : 0 ≤ (if (s N).phase = .centerGradient then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  have he : (∑ k ∈ Finset.range N, if (s k).phase ≠ .finished then (1 : ℝ) else 0) =
      (∑ k ∈ Finset.range N, if (s k).phase = .centerGradient then (1 : ℝ) else 0) +
      (∑ k ∈ Finset.range N, if (s k).phase = .newtonGradient then (1 : ℝ) else 0) +
      (∑ k ∈ Finset.range N, if (s k).phase = .newtonHessian then (1 : ℝ) else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    cases hp : (s k).phase <;> norm_num [hp]
  linarith

lemma interior_regularization {p : Public} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E))
    (hp : s.phase = .newtonHessian ∨ s.phase = .newtonGradient)
    (hn : (update s reply).phase = .newtonHessian ∨ (update s reply).phase = .newtonGradient)
    (hguard : s.phase = .newtonHessian →
      ‖newtonPoint p s.b s.center s.x s.g (readHessian reply) - s.center‖ ≤ 2 * s.r) :
    (update s reply).b = if s.phase = .newtonGradient ∧ s.b < 1 / s.τ then
      min (1 / s.τ) (s.b * (1 + continuationRatio p s.τ s.r / 8)) else s.b := by
  rcases hp with hp | hp
  · have hg := hguard hp
    simp only [update, hp, hg, ite_true, reduceCtorEq,
      false_and, ite_false]
  · by_cases hg : ‖readGradient reply‖ ≤ gradientThreshold p
    · simp only [update, hp, hg, ite_true, finish] at hn
      simp at hn
    by_cases hb : s.b < 1 / s.τ
    · simp only [update, hp, hg, hb, ite_true, ite_false, true_and]
    by_cases hr : ‖s.b • readGradient reply + s.x - s.center‖ ≤ ‖s.x - s.center‖ / 2
    · simp only [update, hp, hg, hb, hr, ite_true, ite_false, accept] at hn
      split_ifs at hn <;> simp_all [finish]
    · simp only [update, hp, hg, hb, hr, ite_false, and_false]

lemma counted_growth_total_count {L q : ℝ} (hL : 0 < L) (hq : 1 < q)
    (b : ℕ → ℝ) (c : ℕ → ℕ) (grow : ℕ → Prop) [DecidablePred grow]
    (hb : 0 < b 0) (hbL : b 0 ≤ L) (hc0 : c 0 = 0) (N : ℕ)
    (hc : ∀ k < N, c (k + 1) = c k + if grow k then 1 else 0)
    (hs : ∀ k < N, b (k + 1) = if grow k then min L (b k * q) else b k)
    (hbefore : ∀ k < N, grow k → b k < L) :
    (c N : ℝ) ≤ Real.log (L / b 0) / Real.log q + 1 := by
  induction N with
  | zero =>
    rw [hc0, Nat.cast_zero]
    have hl : 0 ≤ Real.log (L / b 0) :=
      Real.log_nonneg ((le_div_iff₀ hb).mpr (by simpa using hbL))
    have hqlog := Real.log_pos hq
    have hh := div_nonneg hl hqlog.le
    linarith
  | succ N ih =>
    rw [hc N (by omega)]
    by_cases hg : grow N
    · simp only [ite_eq_left hg, Nat.cast_add, Nat.cast_one]
      have hh := counted_growth_count hL hq b c grow hb hbL hc0 N
        (fun k hk => hc k (by omega)) (fun k hk => hs k (by omega)) (hbefore N (by omega) hg)
      linarith
    · simp only [ite_eq_right hg, Nat.add_zero]
      exact ih (fun k hk => hc k (by omega)) (fun k hk => hs k (by omega))
        (fun k hk => hbefore k (by omega))

lemma interior_not_accepted {p : Public} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E))
    (hn : (update s reply).phase = .newtonHessian ∨ (update s reply).phase = .newtonGradient) :
    ¬ PointwiseHessianLedger.Accepted s reply := by
  intro ha
  rw [PointwiseHessianLedger.accepted_update s reply ha] at hn
  let t := { s with g := readGradient reply }
  change (accept t).phase = .newtonHessian ∨ (accept t).phase = .newtonGradient at hn
  by_cases ht : targetWeight p ≤ t.A + (t.η / t.τ) * t.a
  · simp only [accept, ht, ite_true, finish, reduceCtorEq, or_self] at hn
  · simp only [accept, ht, ite_false, reduceCtorEq, or_self] at hn

lemma interior_scale_fields {p : Public} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E))
    (hp : s.phase = .newtonHessian ∨ s.phase = .newtonGradient)
    (hguard : s.phase = .newtonHessian →
      ‖newtonPoint p s.b s.center s.x s.g (readHessian reply) - s.center‖ ≤ 2 * s.r) :
    ((update s reply).τ, (update s reply).r) = (s.τ, s.r) := by
  have hacc (t : State p) : ((accept t).τ, (accept t).r) = (t.τ, t.r) := by
    by_cases ht : targetWeight p ≤ t.A + (t.η / t.τ) * t.a
    · simp only [accept, ht, ite_true, finish]
    · simp only [accept, ht, ite_false]
  rcases hp with hp | hp
  · have hg := hguard hp
    simp only [update, hp, hg, ite_true]
  · simp only [update, hp]
    split_ifs <;> first | rfl | exact hacc _

lemma interior_path_scales {p : Public} (s : ℕ → State p)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k))
    (hp : ∀ k < N, (s k).phase = .newtonHessian ∨ (s k).phase = .newtonGradient)
    (hguard : ∀ k < N, (s k).phase = .newtonHessian →
      ‖newtonPoint p (s k).b (s k).center (s k).x (s k).g (readHessian (reply k)) - (s k).center‖ ≤ 2 * (s k).r) :
    ((s N).τ, (s N).r) = ((s 0).τ, (s 0).r) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [hs N (by omega), interior_scale_fields (s N) (reply N) (hp N (by omega)) (hguard N (by omega))]
    exact ih (fun k hk => hs k (by omega)) (fun k hk => hp k (by omega))
      (fun k hk => hguard k (by omega))

lemma interior_continuation_count {p : Public} (s : ℕ → State p)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁) (hτ : 0 < (s 0).τ) (hr : 0 ≤ (s 0).r)
    (hb : 0 < (s 0).b) (hbL : (s 0).b ≤ 1 / (s 0).τ)
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k))
    (hp : ∀ k ≤ N, (s k).phase = .newtonHessian ∨ (s k).phase = .newtonGradient)
    (hguard : ∀ k < N, (s k).phase = .newtonHessian →
      ‖newtonPoint p (s k).b (s k).center (s k).x (s k).g (readHessian (reply k)) - (s k).center‖ ≤ 2 * (s k).r) :
    ((∑ k ∈ Finset.range N, if (s k).phase = .newtonGradient ∧ (s k).b < 1 / (s 0).τ then 1 else 0 : ℕ) : ℝ) ≤
      Real.log ((1 / (s 0).τ) / (s 0).b) /
        Real.log (1 + continuationRatio p (s 0).τ (s 0).r / 8) + 1 := by
  let grow := fun k => (s k).phase = .newtonGradient ∧ (s k).b < 1 / (s 0).τ
  let c := fun n => ∑ k ∈ Finset.range n, if grow k then (1 : ℕ) else 0
  have hfixed (k : ℕ) (hk : k ≤ N) := interior_path_scales s reply k
    (fun i hi => hs i (by omega)) (fun i hi => hp i (by omega))
    (fun i hi => hguard i (by omega))
  have ha := PointwiseHessianTuning.continuationRatio_pos p hM₀ hM₁ hτ hr
  apply counted_growth_total_count (one_div_pos.mpr hτ) (by linarith : 1 < 1 + continuationRatio p (s 0).τ (s 0).r / 8)
    (fun k => (s k).b) c grow hb hbL (by simp [c]) N
  · intro k hk
    simp only [c, Finset.sum_range_succ]
  · intro k hk
    have ht := congrArg Prod.fst (hfixed k hk.le)
    have hrad := congrArg Prod.snd (hfixed k hk.le)
    dsimp only at ht hrad
    have hh := interior_regularization (s k) (reply k) (hp k hk.le)
      (by rw [← hs k hk]; exact hp (k + 1) (by omega)) (hguard k hk)
    rw [← hs k hk] at hh
    simpa only [ht, hrad, grow] using hh
  · intro k hk hg
    exact hg.2

noncomputable def phaseResidual {p : Public} (f : p.E → ℝ) (s : State p) : ℝ :=
  (if s.phase = .newtonGradient then 4 else 1) * ‖s.b • gradient f s.x + s.x - s.center‖

lemma phaseResidual_nonneg {p : Public} (f : p.E → ℝ) (s : State p) :
    0 ≤ phaseResidual f s := by
  unfold phaseResidual
  split_ifs <;> positivity

lemma hessian_phaseResidual {p : Public} {f : p.E → ℝ} (s : State p)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    (hi : PointwiseHessianExecution.NewtonReady f s) (hp : s.phase = .newtonHessian)
    (hguard : ‖newtonPoint p s.b s.center s.x s.g (fderiv ℝ (gradient f) s.x) - s.center‖ ≤ 2 * s.r) :
    phaseResidual f (update s (.inr (fderiv ℝ (gradient f) s.x))) ≤ phaseResidual f s := by
  have he := hi.residual
  rw [hi.gradient_eq] at he
  have hh := (PointwiseHessianTrial.newton_contract p hf hc hM₀ hM₁ hT
    hi.τ_pos hi.r_pos hi.b_pos hi.b_le s.center s.x hi.radius he).2
  rw [PointwiseHessianExecution.hessian_update_guard s _ hp hguard]
  simp only [phaseResidual, hp, reduceCtorEq, ite_false, ite_true, one_mul]
  change 4 * ‖s.b • gradient f (newtonPoint p s.b s.center s.x s.g (fderiv ℝ (gradient f) s.x)) +
    newtonPoint p s.b s.center s.x s.g (fderiv ℝ (gradient f) s.x) - s.center‖ ≤
      ‖s.b • gradient f s.x + s.x - s.center‖
  rw [hi.gradient_eq]
  linarith

lemma refinement_phaseResidual {p : Public} (f : p.E → ℝ) (s : State p) (g : p.E)
    (hp : s.phase = .newtonGradient) (hg : ¬ ‖g‖ ≤ gradientThreshold p)
    (hb : ¬ s.b < 1 / s.τ)
    (hr : ¬ ‖s.b • g + s.x - s.center‖ ≤ ‖s.x - s.center‖ / 2) :
    phaseResidual f (update s (.inl g)) = phaseResidual f s / 4 := by
  rw [refinement_update s g hp hg hb hr]
  simp only [phaseResidual, hp, reduceCtorEq, ite_false, ite_true, one_mul]
  change ‖s.b • gradient f s.x + s.x - s.center‖ = 4 * ‖s.b • gradient f s.x + s.x - s.center‖ / 4
  ring

lemma refinement_phaseResidual_lower {p : Public} (f : p.E → ℝ) (s : State p)
    (hp : s.phase = .newtonGradient) (hb : 0 < s.b)
    (hg : ¬ ‖gradient f s.x‖ ≤ gradientThreshold p)
    (hr : ¬ ‖s.b • gradient f s.x + s.x - s.center‖ ≤ ‖s.x - s.center‖ / 2) :
    4 * s.b * gradientThreshold p / 3 < phaseResidual f s := by
  have hh : s.b * gradientThreshold p / 3 < ‖s.b • gradient f s.x + s.x - s.center‖ := by
    apply lt_of_not_ge
    intro he
    exact hg (PointwiseHessianTrial.residual_stop s.center s.x (gradient f s.x) hb he hr)
  simp only [phaseResidual, hp, ite_true]
  linarith

lemma phaseResidual_le {p : Public} {f : p.E → ℝ} {xs : p.E} (s : State p)
    (hi : PointwiseHessianExecution.PhaseInvariant f xs s)
    (hp : s.phase = .newtonHessian ∨ s.phase = .newtonGradient) :
    phaseResidual f s ≤ 2 * continuationRatio p s.τ s.r * s.r := by
  rcases hp with hp | hp
  · simp only [PointwiseHessianExecution.PhaseInvariant, hp] at hi
    have hh := hi.2.residual
    rw [hi.2.gradient_eq] at hh
    simpa only [phaseResidual, hp, reduceCtorEq, ite_false, one_mul] using hh
  · simp only [PointwiseHessianExecution.PhaseInvariant, hp] at hi
    have hh := hi.2.2
    simp only [phaseResidual, hp, ite_true]
    linarith

lemma interior_gradient_refines {p : Public} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (hp : s.phase = .newtonGradient)
    (hn : (update s reply).phase = .newtonHessian ∨ (update s reply).phase = .newtonGradient)
    (hb : ¬ s.b < 1 / s.τ) :
    ¬ ‖readGradient reply‖ ≤ gradientThreshold p ∧
      ¬ ‖s.b • readGradient reply + s.x - s.center‖ ≤ ‖s.x - s.center‖ / 2 := by
  have hg : ¬ ‖readGradient reply‖ ≤ gradientThreshold p := by
    intro hg
    simp only [update, hp, hg, ite_true, finish, reduceCtorEq, or_self] at hn
  refine ⟨hg, ?_⟩
  intro hr
  exact interior_not_accepted s reply hn ⟨hp, hg, hb, hr⟩

lemma interior_final_regularization {p : Public} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E))
    (hp : s.phase = .newtonHessian ∨ s.phase = .newtonGradient)
    (hn : (update s reply).phase = .newtonHessian ∨ (update s reply).phase = .newtonGradient)
    (hguard : s.phase = .newtonHessian →
      ‖newtonPoint p s.b s.center s.x s.g (readHessian reply) - s.center‖ ≤ 2 * s.r)
    (hb : s.b = 1 / s.τ) : (update s reply).b = 1 / (update s reply).τ := by
  have ht := congrArg Prod.fst (interior_scale_fields s reply hp hguard)
  dsimp only at ht
  rw [interior_regularization s reply hp hn hguard, ht, hb]
  simp only [lt_self_iff_false, and_false, ite_false]

lemma interior_final_phaseResidual {p : Public} {f : p.E → ℝ} {xs : p.E} (s : State p)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    (hi : PointwiseHessianExecution.PhaseInvariant f xs s)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E))
    (hp : s.phase = .newtonHessian ∨ s.phase = .newtonGradient)
    (hn : (update s reply).phase = .newtonHessian ∨ (update s reply).phase = .newtonGradient)
    (hguard : s.phase = .newtonHessian →
      ‖newtonPoint p s.b s.center s.x s.g (readHessian reply) - s.center‖ ≤ 2 * s.r)
    (hH : s.phase = .newtonHessian → reply = .inr (fderiv ℝ (gradient f) s.x))
    (hg : s.phase = .newtonGradient → reply = .inl (gradient f s.x))
    (hb : s.b = 1 / s.τ) :
    phaseResidual f (update s reply) ≤ if s.phase = .newtonGradient then phaseResidual f s / 4 else phaseResidual f s := by
  rcases hp with hp | hp
  · have hh := hguard hp
    rw [hH hp] at hh ⊢
    simp only [readHessian] at hh
    simp only [hp, reduceCtorEq, ite_false]
    simp only [PointwiseHessianExecution.PhaseInvariant, hp] at hi
    exact hessian_phaseResidual s hf hc hM₀ hM₁ hT hi.2 hp hh
  · have hnb : ¬ s.b < 1 / s.τ := by rw [hb]; exact lt_irrefl _
    have hh := interior_gradient_refines s reply hp hn hnb
    rw [hg hp] at hh ⊢
    simp only [readGradient] at hh
    simp only [hp, ite_true]
    exact (refinement_phaseResidual f s (gradient f s.x) hp hh.1 hnb hh.2).le

lemma counted_contraction_formula (e : ℕ → ℝ) (c : ℕ → ℕ)
    (shrink : ℕ → Prop) [DecidablePred shrink] {E : ℝ}
    (he : e 0 ≤ E) (hc0 : c 0 = 0) (N : ℕ)
    (hc : ∀ k < N, c (k + 1) = c k + if shrink k then 1 else 0)
    (hs : ∀ k < N, e (k + 1) ≤ if shrink k then e k / 4 else e k) :
    e N ≤ E / 4 ^ c N := by
  induction N with
  | zero => simpa [hc0] using he
  | succ N ih =>
    have hh := ih (fun k hk => hc k (by omega)) (fun k hk => hs k (by omega))
    have hu := hs N (by omega)
    rw [hc N (by omega)]
    by_cases hg : shrink N
    · simp only [ite_eq_left hg] at hu ⊢
      calc
        e (N + 1) ≤ e N / 4 := hu
        _ ≤ (E / 4 ^ c N) / 4 := div_le_div_of_nonneg_right hh (by norm_num)
        _ = E / 4 ^ (c N + 1) := by rw [pow_succ]; ring
    · simp only [ite_eq_right hg, Nat.add_zero] at hu ⊢
      exact hu.trans hh

lemma counted_contraction_count (e : ℕ → ℝ) (c : ℕ → ℕ)
    (shrink : ℕ → Prop) [DecidablePred shrink] {E t : ℝ}
    (he : e 0 ≤ E) (hc0 : c 0 = 0) (N : ℕ)
    (hc : ∀ k < N, c (k + 1) = c k + if shrink k then 1 else 0)
    (hs : ∀ k < N, e (k + 1) ≤ if shrink k then e k / 4 else e k)
    (ht : 0 < t) (hn : t < e N) :
    (c N : ℝ) < Real.log (E / t) / Real.log 4 := by
  have hh := hn.trans_le (counted_contraction_formula e c shrink he hc0 N hc hs)
  have hp : 0 < (4 : ℝ) ^ c N := by positivity
  have hm := (lt_div_iff₀ hp).mp hh
  have hpow : (4 : ℝ) ^ c N < E / t := (lt_div_iff₀ ht).mpr (by nlinarith)
  have hl := Real.log_lt_log hp hpow
  rw [Real.log_pow] at hl
  exact (lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 4))).mpr hl

lemma counted_contraction_total_count (e : ℕ → ℝ) (c : ℕ → ℕ)
    (shrink : ℕ → Prop) [DecidablePred shrink] {E t : ℝ}
    (he : e 0 ≤ E) (hc0 : c 0 = 0) (ht : 0 < t) (hEt : t ≤ E) (N : ℕ)
    (hc : ∀ k < N, c (k + 1) = c k + if shrink k then 1 else 0)
    (hs : ∀ k < N, e (k + 1) ≤ if shrink k then e k / 4 else e k)
    (hbefore : ∀ k < N, shrink k → t < e k) :
    (c N : ℝ) ≤ Real.log (E / t) / Real.log 4 + 1 := by
  induction N with
  | zero =>
    rw [hc0, Nat.cast_zero]
    have hl : 0 ≤ Real.log (E / t) :=
      Real.log_nonneg ((le_div_iff₀ ht).mpr (by simpa using hEt))
    have hh := div_nonneg hl (Real.log_pos (by norm_num : (1 : ℝ) < 4)).le
    linarith
  | succ N ih =>
    rw [hc N (by omega)]
    by_cases hg : shrink N
    · simp only [ite_eq_left hg, Nat.cast_add, Nat.cast_one]
      have hh := counted_contraction_count e c shrink he hc0 N
        (fun k hk => hc k (by omega)) (fun k hk => hs k (by omega)) ht (hbefore N (by omega) hg)
      linarith
    · simp only [ite_eq_right hg, Nat.add_zero]
      exact ih (fun k hk => hc k (by omega)) (fun k hk => hs k (by omega))
        (fun k hk => hbefore k (by omega))

lemma interior_path_final_regularization {p : Public} (s : ℕ → State p)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k))
    (hp : ∀ k ≤ N, (s k).phase = .newtonHessian ∨ (s k).phase = .newtonGradient)
    (hguard : ∀ k < N, (s k).phase = .newtonHessian →
      ‖newtonPoint p (s k).b (s k).center (s k).x (s k).g (readHessian (reply k)) - (s k).center‖ ≤ 2 * (s k).r)
    (hb : (s 0).b = 1 / (s 0).τ) : (s N).b = 1 / (s N).τ := by
  induction N with
  | zero => exact hb
  | succ N ih =>
    have hh := ih (fun k hk => hs k (by omega)) (fun k hk => hp k (by omega))
      (fun k hk => hguard k (by omega))
    rw [hs N (by omega)]
    exact interior_final_regularization (s N) (reply N) (hp N (by omega))
      (by rw [← hs N (by omega)]; exact hp (N + 1) le_rfl) (hguard N (by omega)) hh

lemma interior_refinement_count {p : Public} {f : p.E → ℝ} {xs : p.E} (s : ℕ → State p)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hi : ∀ k ≤ N, PointwiseHessianExecution.PhaseInvariant f xs (s k))
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k))
    (hp : ∀ k ≤ N, (s k).phase = .newtonHessian ∨ (s k).phase = .newtonGradient)
    (hguard : ∀ k < N, (s k).phase = .newtonHessian →
      ‖newtonPoint p (s k).b (s k).center (s k).x (s k).g (readHessian (reply k)) - (s k).center‖ ≤ 2 * (s k).r)
    (hH : ∀ k < N, (s k).phase = .newtonHessian → reply k = .inr (fderiv ℝ (gradient f) (s k).x))
    (hg : ∀ k < N, (s k).phase = .newtonGradient → reply k = .inl (gradient f (s k).x))
    (hb : (s 0).b = 1 / (s 0).τ) :
    let t := 4 * (1 / (s 0).τ) * gradientThreshold p / 3
    let E := 2 * continuationRatio p (s 0).τ (s 0).r * (s 0).r + t
    ((∑ k ∈ Finset.range N, if (s k).phase = .newtonGradient then 1 else 0 : ℕ) : ℝ) ≤
      Real.log (E / t) / Real.log 4 + 1 := by
  let t := 4 * (1 / (s 0).τ) * gradientThreshold p / 3
  let E := 2 * continuationRatio p (s 0).τ (s 0).r * (s 0).r + t
  let shrink := fun k => (s k).phase = .newtonGradient
  let c := fun n => ∑ k ∈ Finset.range n, if shrink k then (1 : ℕ) else 0
  have hpar : PointwiseHessianExecution.InnerParameters f (s 0) := by
    have hh := hi 0 (Nat.zero_le N)
    rcases hp 0 (Nat.zero_le N) with h | h
    · simp only [PointwiseHessianExecution.PhaseInvariant, h] at hh
      exact hh.1
    · simp only [PointwiseHessianExecution.PhaseInvariant, h] at hh
      exact hh.1
  have hτ0 := hpar.τ_pos
  have ht : 0 < t := by dsimp [t, gradientThreshold]; positivity
  have ha := PointwiseHessianTuning.continuationRatio_pos p hM₀ hM₁ hpar.τ_pos hpar.r_pos.le
  have hEt : t ≤ E := by dsimp [E]; nlinarith [mul_pos ha hpar.r_pos]
  have he : phaseResidual f (s 0) ≤ E := by
    have hh := phaseResidual_le (s 0) (hi 0 (Nat.zero_le N)) (hp 0 (Nat.zero_le N))
    dsimp [E]
    linarith
  have hcap (k : ℕ) (hk : k ≤ N) := interior_path_final_regularization s reply k
    (fun i hi' => hs i (by omega)) (fun i hi' => hp i (by omega))
    (fun i hi' => hguard i (by omega)) hb
  have hfixed (k : ℕ) (hk : k ≤ N) := interior_path_scales s reply k
    (fun i hi' => hs i (by omega)) (fun i hi' => hp i (by omega))
    (fun i hi' => hguard i (by omega))
  apply counted_contraction_total_count (fun k => phaseResidual f (s k)) c shrink he
    (by simp [c]) ht hEt N
  · intro k hk
    simp only [c, Finset.sum_range_succ]
  · intro k hk
    have hh := interior_final_phaseResidual (s k) hf hc hM₀ hM₁ hT (hi k hk.le)
      (reply k) (hp k hk.le) (by rw [← hs k hk]; exact hp (k + 1) (by omega))
      (hguard k hk) (hH k hk) (hg k hk) (hcap k hk.le)
    rwa [← hs k hk] at hh
  · intro k hk hphase
    have hτ := congrArg Prod.fst (hfixed k hk.le)
    dsimp only at hτ
    have hnb : ¬ (s k).b < 1 / (s k).τ := by rw [hcap k hk.le]; exact lt_irrefl _
    have hh := interior_gradient_refines (s k) (reply k) hphase
      (by rw [← hs k hk]; exact hp (k + 1) (by omega)) hnb
    rw [hg k hk hphase] at hh
    simp only [readGradient] at hh
    have hbp : 0 < (s k).b := by rw [hcap k hk.le, hτ]; exact one_div_pos.mpr hpar.τ_pos
    have hl := refinement_phaseResidual_lower f (s k) hphase hbp hh.1 hh.2
    simpa only [hcap k hk.le, hτ, t] using hl

lemma joint_refinement_step {p : Public} {f : p.E → ℝ} {xs : p.E} (s : State p)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E))
    (hi : PointwiseHessianExecution.PhaseInvariant f xs s)
    (hi' : PointwiseHessianExecution.PhaseInvariant f xs (update s reply))
    (hp : s.phase = .newtonHessian ∨ s.phase = .newtonGradient)
    (hn : (update s reply).phase = .newtonHessian ∨ (update s reply).phase = .newtonGradient)
    (hguard : s.phase = .newtonHessian →
      ‖newtonPoint p s.b s.center s.x s.g (readHessian reply) - s.center‖ ≤ 2 * s.r)
    (hH : s.phase = .newtonHessian → reply = .inr (fderiv ℝ (gradient f) s.x))
    (hg : s.phase = .newtonGradient → reply = .inl (gradient f s.x))
    (v : ℕ) (hv : 0 < v → s.b = 1 / s.τ)
    (hQ : phaseResidual f s ≤ 2 * continuationRatio p s.τ s.r * s.r / 4 ^ v) :
    let v' := v + if s.phase = .newtonGradient ∧ ¬ s.b < 1 / s.τ then (1 : ℕ) else 0
    (0 < v' → (update s reply).b = 1 / (update s reply).τ) ∧
      phaseResidual f (update s reply) ≤
        2 * continuationRatio p (update s reply).τ (update s reply).r * (update s reply).r / 4 ^ v' := by
  have hsc := interior_scale_fields s reply hp hguard
  have ht := congrArg Prod.fst hsc
  have hr := congrArg Prod.snd hsc
  dsimp only at ht hr
  rcases hp with hp | hp
  · simp only [hp, reduceCtorEq, false_and, ite_false, Nat.add_zero]
    constructor
    · intro hv'
      exact interior_final_regularization s reply (Or.inl hp) hn hguard (hv hv')
    · have hiH := hi
      simp only [PointwiseHessianExecution.PhaseInvariant, hp] at hiH
      have hh := hguard hp
      rw [hH hp] at hh
      simp only [readHessian] at hh
      have hstep := hessian_phaseResidual s hf hc hM₀ hM₁ hT hiH.2 hp hh
      rw [← hH hp] at hstep
      simpa only [ht, hr] using hstep.trans hQ
  · by_cases hb : s.b < 1 / s.τ
    · have hv0 : v = 0 := by
        by_contra hne
        have he := hv (Nat.pos_of_ne_zero hne)
        rw [he] at hb
        exact lt_irrefl _ hb
      simp only [hp, hb, not_true_eq_false, and_false, ite_false, Nat.add_zero, hv0,
        Nat.lt_irrefl, false_implies, true_and, pow_zero, div_one]
      exact phaseResidual_le (update s reply) hi' hn
    · have hip := hi
      simp only [PointwiseHessianExecution.PhaseInvariant, hp] at hip
      have hcap : s.b = 1 / s.τ := le_antisymm hip.1.b_le (le_of_not_gt hb)
      simp only [hp, hb, not_false_eq_true, and_self, ite_true]
      constructor
      · intro _
        exact interior_final_regularization s reply (Or.inr hp) hn hguard hcap
      · have hstep := interior_final_phaseResidual s hf hc hM₀ hM₁ hT hi reply
          (Or.inr hp) hn hguard hH hg hcap
        simp only [hp, ite_true] at hstep
        rw [ht, hr]
        calc
          phaseResidual f (update s reply) ≤ phaseResidual f s / 4 := hstep
          _ ≤ (2 * continuationRatio p s.τ s.r * s.r / 4 ^ v) / 4 :=
            div_le_div_of_nonneg_right hQ (by norm_num)
          _ = _ := by rw [pow_succ]; ring

lemma joint_refinement_path {p : Public} {f : p.E → ℝ} {xs : p.E} (s : ℕ → State p)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hi : ∀ k ≤ N, PointwiseHessianExecution.PhaseInvariant f xs (s k))
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k))
    (hp : ∀ k ≤ N, (s k).phase = .newtonHessian ∨ (s k).phase = .newtonGradient)
    (hguard : ∀ k < N, (s k).phase = .newtonHessian →
      ‖newtonPoint p (s k).b (s k).center (s k).x (s k).g (readHessian (reply k)) - (s k).center‖ ≤ 2 * (s k).r)
    (hH : ∀ k < N, (s k).phase = .newtonHessian → reply k = .inr (fderiv ℝ (gradient f) (s k).x))
    (hg : ∀ k < N, (s k).phase = .newtonGradient → reply k = .inl (gradient f (s k).x)) :
    let v := ∑ k ∈ Finset.range N, if (s k).phase = .newtonGradient ∧ ¬ (s k).b < 1 / (s k).τ then (1 : ℕ) else 0
    (0 < v → (s N).b = 1 / (s N).τ) ∧
      phaseResidual f (s N) ≤ 2 * continuationRatio p (s N).τ (s N).r * (s N).r / 4 ^ v := by
  let v := fun n => ∑ k ∈ Finset.range n,
    if (s k).phase = .newtonGradient ∧ ¬ (s k).b < 1 / (s k).τ then (1 : ℕ) else 0
  change (0 < v N → (s N).b = 1 / (s N).τ) ∧ _
  induction N with
  | zero =>
    simp only [v, Finset.range_zero, Finset.sum_empty, Nat.lt_irrefl, false_implies,
      true_and, pow_zero, div_one]
    exact phaseResidual_le (s 0) (hi 0 le_rfl) (hp 0 le_rfl)
  | succ N ih =>
    have hh := ih (fun k hk => hi k (by omega)) (fun k hk => hs k (by omega))
      (fun k hk => hp k (by omega)) (fun k hk => hguard k (by omega))
      (fun k hk => hH k (by omega)) (fun k hk => hg k (by omega))
    have hstep := joint_refinement_step (s N) hf hc hM₀ hM₁ hT (reply N)
      (hi N (by omega)) (by rw [← hs N (by omega)]; exact hi (N + 1) le_rfl)
      (hp N (by omega)) (by rw [← hs N (by omega)]; exact hp (N + 1) le_rfl)
      (hguard N (by omega)) (hH N (by omega)) (hg N (by omega)) (v N) hh.1 hh.2
    rw [← hs N (by omega)] at hstep
    simpa only [v, Finset.sum_range_succ] using hstep

lemma threshold_counter_bound (c : ℕ → ℕ) (event : ℕ → Prop) [DecidablePred event]
    {B : ℝ} (hB : 0 ≤ B) (hc0 : c 0 = 0) (N : ℕ)
    (hc : ∀ k < N, c (k + 1) = c k + if event k then 1 else 0)
    (hb : ∀ k < N, event k → (c k : ℝ) < B) : (c N : ℝ) ≤ B + 1 := by
  induction N with
  | zero => rw [hc0, Nat.cast_zero]; linarith
  | succ N ih =>
    rw [hc N (by omega)]
    by_cases he : event N
    · simp only [ite_eq_left he, Nat.cast_add, Nat.cast_one]
      linarith [hb N (by omega) he]
    · simp only [ite_eq_right he, Nat.add_zero]
      exact ih (fun k hk => hc k (by omega)) (fun k hk => hb k (by omega))

lemma whole_episode_refinement_count {p : Public} {f : p.E → ℝ} {xs : p.E} (s : ℕ → State p)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hi : ∀ k ≤ N, PointwiseHessianExecution.PhaseInvariant f xs (s k))
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k))
    (hp : ∀ k ≤ N, (s k).phase = .newtonHessian ∨ (s k).phase = .newtonGradient)
    (hguard : ∀ k < N, (s k).phase = .newtonHessian →
      ‖newtonPoint p (s k).b (s k).center (s k).x (s k).g (readHessian (reply k)) - (s k).center‖ ≤ 2 * (s k).r)
    (hH : ∀ k < N, (s k).phase = .newtonHessian → reply k = .inr (fderiv ℝ (gradient f) (s k).x))
    (hg : ∀ k < N, (s k).phase = .newtonGradient → reply k = .inl (gradient f (s k).x)) :
    let t := 4 * (1 / (s 0).τ) * gradientThreshold p / 3
    let E := 2 * continuationRatio p (s 0).τ (s 0).r * (s 0).r + t
    ((∑ k ∈ Finset.range N, if (s k).phase = .newtonGradient ∧ ¬ (s k).b < 1 / (s k).τ then 1 else 0 : ℕ) : ℝ) ≤
      Real.log (E / t) / Real.log 4 + 1 := by
  let t := 4 * (1 / (s 0).τ) * gradientThreshold p / 3
  let E := 2 * continuationRatio p (s 0).τ (s 0).r * (s 0).r + t
  let event := fun k => (s k).phase = .newtonGradient ∧ ¬ (s k).b < 1 / (s k).τ
  let v := fun n => ∑ k ∈ Finset.range n, if event k then (1 : ℕ) else 0
  have hpar : PointwiseHessianExecution.InnerParameters f (s 0) := by
    have hh := hi 0 (Nat.zero_le N)
    rcases hp 0 (Nat.zero_le N) with h | h
    · simp only [PointwiseHessianExecution.PhaseInvariant, h] at hh
      exact hh.1
    · simp only [PointwiseHessianExecution.PhaseInvariant, h] at hh
      exact hh.1
  have hτ0 := hpar.τ_pos
  have ht : 0 < t := by dsimp [t, gradientThreshold]; positivity
  have ha := PointwiseHessianTuning.continuationRatio_pos p hM₀ hM₁ hpar.τ_pos hpar.r_pos.le
  have hEt : t ≤ E := by dsimp [E]; nlinarith [mul_pos ha hpar.r_pos]
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  change (v N : ℝ) ≤ Real.log (E / t) / Real.log 4 + 1
  apply threshold_counter_bound v event (B := Real.log (E / t) / Real.log 4)
    (div_nonneg (Real.log_nonneg ((le_div_iff₀ ht).mpr (by simpa using hEt))) hlog4.le)
    (by simp [v]) N
  · intro k hk
    simp only [v, Finset.sum_range_succ]
  · intro k hk he
    have hsc := interior_path_scales s reply k
      (fun i hi' => hs i (by omega)) (fun i hi' => hp i (by omega))
      (fun i hi' => hguard i (by omega))
    have hτ := congrArg Prod.fst hsc
    have hr := congrArg Prod.snd hsc
    dsimp only at hτ hr
    have hQ := (joint_refinement_path s hf hc hM₀ hM₁ hT reply k
      (fun i hi' => hi i (by omega)) (fun i hi' => hs i (by omega))
      (fun i hi' => hp i (by omega)) (fun i hi' => hguard i (by omega))
      (fun i hi' => hH i (by omega)) (fun i hi' => hg i (by omega))).2
    have hip := hi k hk.le
    simp only [PointwiseHessianExecution.PhaseInvariant, he.1] at hip
    have hcap : (s k).b = 1 / (s k).τ := le_antisymm hip.1.b_le (le_of_not_gt he.2)
    have href := interior_gradient_refines (s k) (reply k) he.1
      (by rw [← hs k hk]; exact hp (k + 1) (by omega)) he.2
    rw [hg k hk he.1] at href
    simp only [readGradient] at href
    have hl := refinement_phaseResidual_lower f (s k) he.1 hip.1.b_pos href.1 href.2
    have hlt : t < phaseResidual f (s k) := by simpa only [hcap, hτ, t] using hl
    have hpowpos : 0 < (4 : ℝ) ^ v k := by positivity
    have hupper : phaseResidual f (s k) ≤ E / 4 ^ v k := by
      dsimp only [E]
      apply hQ.trans
      rw [hτ, hr]
      exact div_le_div_of_nonneg_right (by linarith) hpowpos.le
    have hm := (lt_div_iff₀ hpowpos).mp (hlt.trans_le hupper)
    have hpow : (4 : ℝ) ^ v k < E / t := (lt_div_iff₀ ht).mpr (by nlinarith)
    have hl' := Real.log_lt_log hpowpos hpow
    rw [Real.log_pow] at hl'
    exact (lt_div_iff₀ hlog4).mpr hl'

lemma refinement_log_bound {x Z : ℝ} (hx : 0 ≤ x) (hZ : 2 ≤ Z)
    (hxZ : x ≤ 384000 * Z) :
    Real.log (1 + x) / Real.log 4 + 1 ≤ 22 * Real.log Z / Real.log 4 := by
  have hp : (2 : ℝ) ^ 19 * Z ≤ Z ^ 20 := by
    have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hZ 19)
      (by linarith : 0 ≤ Z)
    simpa only [← pow_succ] using hh
  have harg : 1 + x ≤ Z ^ 20 := by
    norm_num at hp
    nlinarith
  have hl := Real.log_le_log (by positivity : 0 < 1 + x) harg
  rw [Real.log_pow] at hl
  have hz := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hZ
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have he4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  apply (le_div_iff₀ h4).mpr
  have he : (Real.log (1 + x) / Real.log 4 + 1) * Real.log 4 = Real.log (1 + x) + Real.log 4 := by
    field_simp
  rw [he]
  norm_num at hl
  linarith

lemma radius_restart_ledger {S T cap prev rnew : ℝ}
    (hprev : 0 ≤ prev) (hpc : prev ≤ cap / 2)
    (hT : T ≤ 4 * prev ^ 2) (hS : S ≤ 3 * cap ^ 2) :
    T + S ≤ 4 * cap ^ 2 ∧
      rnew ^ 2 ≤ if rnew < 2 * cap then (4 / 3 : ℝ) * rnew ^ 2 else 3 * rnew ^ 2 := by
  constructor
  · have hh := pow_le_pow_left₀ hprev hpc 2
    nlinarith
  · split_ifs <;> nlinarith [sq_nonneg rnew]

lemma radius_growth_ledger {S r cap : ℝ} (hr : 0 ≤ r) (hrc : r < cap)
    (hS : S ≤ (4 / 3 : ℝ) * r ^ 2) :
    S + (min (2 * r) cap) ^ 2 ≤
      if min (2 * r) cap < cap then (4 / 3 : ℝ) * (min (2 * r) cap) ^ 2
      else 3 * (min (2 * r) cap) ^ 2 := by
  by_cases hd : 2 * r < cap
  · rw [min_eq_left hd.le, ite_eq_left hd]
    exact PointwiseHessianCounting.doubled_radius_ledger hS
  · rw [min_eq_right (le_of_not_gt hd), ite_eq_right (lt_irrefl cap)]
    exact PointwiseHessianCounting.clipped_radius_ledger hr hrc.le hS


lemma continuation_log_lower {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    a / 16 ≤ Real.log (1 + a / 8) := by
  have hh := Real.le_log_one_add_of_nonneg (show 0 ≤ a / 8 by positivity)
  apply le_trans _ hh
  apply (le_div_iff₀ (show 0 < a / 8 + 2 by positivity)).mpr
  nlinarith [sq_nonneg a, mul_nonneg ha.le (sub_nonneg.mpr ha1)]

lemma continuation_count_log_bound {a L : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hL : 0 ≤ L) : L / Real.log (1 + a / 8) + 1 ≤ 16 * L / a + 1 := by
  have hl := continuation_log_lower ha ha1
  have hh : L / Real.log (1 + a / 8) ≤ L / (a / 16) :=
    div_le_div_of_nonneg_left hL (by positivity) hl
  have he : L / (a / 16) = 16 * L / a := by ring
  rw [he] at hh
  linarith

lemma continuation_inverse_bound {p : Public} (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁)
    {τ r : ℝ} (hτ : 0 < τ) (hr : r ≤ radiusCap p τ) :
    1 / continuationRatio p τ r ≤ 65 * (1 + p.M₁ * r ^ 2) := by
  have hh := PointwiseHessianTuning.radiusCap_scaled p hM₀ hτ hr
  simp only [continuationRatio, one_div_one_div]
  nlinarith [mul_nonneg hM₁ (sq_nonneg r)]


open LongTails.Proofs.PointwiseHessianLedger

def RadiusStart {p : Public} (s t : State p) : Prop :=
  (s.phase = .centerGradient ∨ s.phase = .newtonHessian) ∧ t.phase = .newtonHessian

noncomputable def radiusPairStep {p : Public} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (q : ℝ × ℝ) : ℝ × ℝ :=
  let t := update s reply
  if Accepted s reply then (0, 0)
  else if RadiusStart s t then
    if s.phase = .centerGradient then (t.r ^ 2, 0)
    else if t.τ = s.τ then (q.1 + t.r ^ 2, q.2)
    else (t.r ^ 2, q.2 + q.1)
  else q

noncomputable def radiusPair {p : Public} (s : ℕ → State p)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) : ℕ → ℝ × ℝ
  | 0 => (0, 0)
  | n + 1 => radiusPairStep (s n) (reply n) (radiusPair s reply n)

lemma accepted_not_radiusStart {p : Public} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (ha : Accepted s reply) :
    ¬ RadiusStart s (update s reply) := by
  intro hh
  rcases hh.1 with hc | hH
  · exact Phase.noConfusion (ha.1.symm.trans hc)
  · exact Phase.noConfusion (ha.1.symm.trans hH)

lemma radius_pair_balance {p : Public} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (q : ℝ × ℝ)
    (hc : s.phase = .centerGradient → q = (0, 0)) :
    q.1 + q.2 + (if RadiusStart s (update s reply) then (update s reply).r ^ 2 else 0) =
      (if Accepted s reply then q.1 + q.2 else 0) +
        (radiusPairStep s reply q).1 + (radiusPairStep s reply q).2 := by
  by_cases ha : Accepted s reply
  · have hn := accepted_not_radiusStart s reply ha
    simp [radiusPairStep, ha, hn]
  · by_cases hs : RadiusStart s (update s reply)
    · by_cases hp : s.phase = .centerGradient
      · rw [hc hp]
        simp [radiusPairStep, ha, hs, hp]
      · by_cases ht : (update s reply).τ = s.τ <;>
          simp [radiusPairStep, ha, hs, hp, ht] <;> ring
    · simp [radiusPairStep, ha, hs]

lemma radius_pair_center_zero {p : Public} (s : ℕ → State p)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k))
    (hc : (s N).phase = .centerGradient) : radiusPair s reply N = (0, 0) := by
  cases N with
  | zero => rfl
  | succ n =>
    have ha := update_center_requires_accept (s n) (reply n) (by rwa [← hs n (by omega)])
    simp only [radiusPair, radiusPairStep, ite_eq_left ha]

lemma radius_pair_path_balance {p : Public} (s : ℕ → State p)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k)) :
    (∑ k ∈ Finset.range N, if RadiusStart (s k) (s (k + 1)) then (s (k + 1)).r ^ 2 else 0) =
      (∑ k ∈ Finset.range N, if Accepted (s k) (reply k) then
        (radiusPair s reply k).1 + (radiusPair s reply k).2 else 0) +
        (radiusPair s reply N).1 + (radiusPair s reply N).2 := by
  induction N with
  | zero => simp [radiusPair]
  | succ N ih =>
    have ih' := ih (fun k hk => hs k (by omega))
    have hb := radius_pair_balance (s N) (reply N) (radiusPair s reply N)
      (fun hc => radius_pair_center_zero s reply N (fun k hk => hs k (by omega)) hc)
    rw [← hs N (by omega)] at hb
    simp only [Finset.sum_range_succ]
    change _ = _ + (radiusPairStep (s N) (reply N) (radiusPair s reply N)).1 +
      (radiusPairStep (s N) (reply N) (radiusPair s reply N)).2
    linarith

lemma radius_pair_nonneg {p : Public} (s : ℕ → State p)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ) :
    0 ≤ (radiusPair s reply N).1 ∧ 0 ≤ (radiusPair s reply N).2 := by
  induction N with
  | zero => norm_num [radiusPair]
  | succ N ih =>
    rcases ih with ⟨hS, hT⟩
    simp only [radiusPair, radiusPairStep]
    split_ifs <;> constructor <;> positivity


noncomputable def previousRadius {p : Public} (s : State p) : ℝ :=
  if s.τ = s.η then 0 else radiusCap p (s.τ / 2)

lemma previousRadius_nonneg {p : Public} (s : State p)
    (hM₀ : 0 ≤ p.M₀) (hR : 0 < p.R) (hτ : 0 < s.τ) : 0 ≤ previousRadius s := by
  unfold previousRadius
  split_ifs
  · exact le_rfl
  · exact (PointwiseHessianTuning.radiusCap_pos p hM₀ hR (by positivity)).le

lemma previousRadius_le_half {p : Public} {f : p.E → ℝ} (s : State p) (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hR : 0 < p.R) (hmin : IsMinOn f Set.univ xs)
    (hp : PointwiseHessianExecution.InnerParameters f s)
    (ho : PointwiseHessianOuter.Invariant f xs s) (hprev : PreviousFailure f s) :
    previousRadius s ≤ radiusCap p s.τ / 2 := by
  unfold previousRadius
  split_ifs with ht
  · have hh := PointwiseHessianTuning.radiusCap_pos p hM₀ hR hp.τ_pos
    positivity
  · exact (previous_cap_half s xs hf hc hR hmin hp ho hprev ht).le

lemma previousRadius_accept_bound {p : Public} {f : p.E → ℝ} (s : State p)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hτ : 0 < s.τ) (hprev : PreviousFailure f s)
    (hres : ‖(1 / s.τ) • gradient f s.x + s.x - s.center‖ ≤ ‖s.x - s.center‖ / 2) :
    previousRadius s ≤ 6 * ‖s.x - s.center‖ := by
  unfold previousRadius
  split_ifs with ht
  · positivity
  · exact (certified_previous_radius_accept_bound s hf hc hτ hprev ht hres).le

def RadiusPairBounds {p : Public} (s : State p) (q : ℝ × ℝ) : Prop :=
  q.1 ≤ (if s.r < radiusCap p s.τ then (4 / 3 : ℝ) * s.r ^ 2 else 3 * s.r ^ 2) ∧
    q.2 ≤ 4 * previousRadius s ^ 2

lemma radiusPairBounds_total {p : Public} (s : State p) (q : ℝ × ℝ)
    (hq : RadiusPairBounds s q) : q.1 + q.2 ≤ 3 * s.r ^ 2 + 4 * previousRadius s ^ 2 := by
  have hh := hq.1
  split_ifs at hh <;> linarith [hq.2, sq_nonneg s.r]

lemma radiusPairBounds_open {p : Public} (s : State p) (q : ℝ × ℝ)
    (hq : RadiusPairBounds s q) (hr : 0 ≤ s.r) (hrc : s.r ≤ radiusCap p s.τ)
    (hp : 0 ≤ previousRadius s) (hpc : previousRadius s ≤ radiusCap p s.τ) :
    q.1 + q.2 ≤ 1792 * p.R ^ 2 := by
  have hh := radiusPairBounds_total s q hq
  have hr2 := pow_le_pow_left₀ hr hrc 2
  have hp2 := pow_le_pow_left₀ hp hpc 2
  apply PointwiseHessianCounting.open_radius_ledger (hr.trans hrc)
    (PointwiseHessianTuning.radiusCap_le p s.τ)
  nlinarith

lemma radiusPairBounds_accept {p : Public} (s : State p) (q : ℝ × ℝ)
    (hq : RadiusPairBounds s q) (hr : 0 ≤ s.r) (hp : 0 ≤ previousRadius s)
    (hrd : s.r ≤ 6 * ‖s.x - s.center‖) (hpd : previousRadius s ≤ 6 * ‖s.x - s.center‖) :
    q.1 + q.2 ≤ 252 * ‖s.x - s.center‖ ^ 2 :=
  PointwiseHessianCounting.completed_radius_ledger hr hp hrd hpd (radiusPairBounds_total s q hq)


lemma initialTrial_radiusPairBounds {p : Public} (s : State p) :
    RadiusPairBounds (startTrial s s.η (initialRadius p s.η)) ((initialRadius p s.η) ^ 2, 0) := by
  constructor
  · change (initialRadius p s.η) ^ 2 ≤ if initialRadius p s.η < radiusCap p s.η then
      (4 / 3 : ℝ) * (initialRadius p s.η) ^ 2 else 3 * (initialRadius p s.η) ^ 2
    split <;> nlinarith [sq_nonneg (initialRadius p s.η)]
  · change (0 : ℝ) ≤ 4 * previousRadius (startTrial s s.η (initialRadius p s.η)) ^ 2
    positivity

lemma grownTrial_radiusPairBounds {p : Public} (s : State p) (q : ℝ × ℝ)
    (hq : RadiusPairBounds s q) (hr : 0 ≤ s.r) (hrc : s.r < radiusCap p s.τ) :
    RadiusPairBounds (startTrial s s.τ (min (2 * s.r) (radiusCap p s.τ)))
      (q.1 + (min (2 * s.r) (radiusCap p s.τ)) ^ 2, q.2) := by
  constructor
  · exact radius_growth_ledger hr hrc (by simpa only [ite_eq_left hrc] using hq.1)
  · exact hq.2

lemma doubledTrial_radiusPairBounds {p : Public} (s : State p) (q : ℝ × ℝ)
    (hq : RadiusPairBounds s q) (hτ : 0 < s.τ) (hη : s.η ≤ s.τ)
    (hrc : s.r = radiusCap p s.τ) (hp : 0 ≤ previousRadius s)
    (hpc : previousRadius s ≤ radiusCap p s.τ / 2) :
    RadiusPairBounds (startTrial s (2 * s.τ) (initialRadius p (2 * s.τ)))
      ((initialRadius p (2 * s.τ)) ^ 2, q.2 + q.1) := by
  constructor
  · change (initialRadius p (2 * s.τ)) ^ 2 ≤ if initialRadius p (2 * s.τ) < radiusCap p (2 * s.τ) then
      (4 / 3 : ℝ) * (initialRadius p (2 * s.τ)) ^ 2 else 3 * (initialRadius p (2 * s.τ)) ^ 2
    split <;> nlinarith [sq_nonneg (initialRadius p (2 * s.τ))]
  · have hh := hq.1
    rw [hrc] at hh
    simp only [lt_self_iff_false, ite_false] at hh
    have hb := (radius_restart_ledger hp hpc hq.2 hh (rnew := initialRadius p (2 * s.τ))).1
    have ht : 2 * s.τ ≠ s.η := by linarith
    have he : (2 * s.τ) / 2 = s.τ := by ring
    simpa only [previousRadius, startTrial, ite_eq_right ht, he] using hb

lemma radiusPairBounds_transfer {p : Public} {s t : State p} {q : ℝ × ℝ}
    (hq : RadiusPairBounds s q) (hr : t.r = s.r) (hτ : t.τ = s.τ) (hη : t.η = s.η) :
    RadiusPairBounds t q := by
  simpa only [RadiusPairBounds, previousRadius, hr, hτ, hη] using hq

def RadiusPairInvariant {p : Public} (s : State p) (q : ℝ × ℝ) : Prop :=
  match s.phase with
  | .centerGradient => q = (0, 0)
  | .newtonHessian | .newtonGradient => RadiusPairBounds s q
  | .finished => q.1 + q.2 ≤ 1792 * p.R ^ 2

lemma radiusPairInvariant_zero {p : Public} (s : State p) : RadiusPairInvariant s (0, 0) := by
  cases hp : s.phase <;> simp only [RadiusPairInvariant, hp]
  · constructor
    · split_ifs <;> positivity
    · positivity
  · constructor
    · split_ifs <;> positivity
    · positivity
  · simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 1792) (sq_nonneg p.R)

lemma radiusPairStep_gradient {p : Public} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (q : ℝ × ℝ)
    (hs : s.phase = .newtonGradient) (ha : ¬ Accepted s reply) :
    radiusPairStep s reply q = q := by
  simp [radiusPairStep, ha, RadiusStart, hs]

lemma radiusPairStep_finished {p : Public} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (q : ℝ × ℝ) (hs : s.phase = .finished) :
    radiusPairStep s reply q = q := by
  simp [radiusPairStep, Accepted, RadiusStart, hs]

lemma radiusPairStep_hessian_guard {p : Public} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (q : ℝ × ℝ) (hs : s.phase = .newtonHessian)
    (hg : ‖newtonPoint p s.b s.center s.x s.g (readHessian reply) - s.center‖ ≤ 2 * s.r) :
    radiusPairStep s reply q = q := by
  simp [radiusPairStep, Accepted, RadiusStart, update, hs, hg]

lemma radiusPairStep_hessian_failure {p : Public} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (q : ℝ × ℝ) (hs : s.phase = .newtonHessian)
    (hτ : 0 < s.τ)
    (hg : ¬ ‖newtonPoint p s.b s.center s.x s.g (readHessian reply) - s.center‖ ≤ 2 * s.r) :
    radiusPairStep s reply q =
      if s.r < radiusCap p s.τ then (q.1 + (min (2 * s.r) (radiusCap p s.τ)) ^ 2, q.2)
      else ((initialRadius p (2 * s.τ)) ^ 2, q.2 + q.1) := by
  have ht : 2 * s.τ ≠ s.τ := by linarith
  by_cases hr : s.r < radiusCap p s.τ <;>
    simp [radiusPairStep, Accepted, RadiusStart, update, hs, hg, failedTrial, hr, startTrial, ht]

lemma radiusPairInvariant_accepted {p : Public} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (q : ℝ × ℝ) (ha : Accepted s reply) :
    RadiusPairInvariant (update s reply) (radiusPairStep s reply q) := by
  simp only [radiusPairStep, ite_eq_left ha]
  exact radiusPairInvariant_zero _


lemma radiusPairInvariant_gradient {p : Public} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (q : ℝ × ℝ) (hs : s.phase = .newtonGradient)
    (hq : RadiusPairBounds s q) (hopen : q.1 + q.2 ≤ 1792 * p.R ^ 2) :
    RadiusPairInvariant (update s reply) (radiusPairStep s reply q) := by
  by_cases ha : Accepted s reply
  · exact radiusPairInvariant_accepted s reply q ha
  rw [radiusPairStep_gradient s reply q hs ha]
  simp only [update, hs]
  split_ifs with hstop hb hm
  · exact hopen
  · exact hq
  · exact False.elim (ha ⟨hs, hstop, hb, hm⟩)
  · exact hq

lemma radiusPairInvariant_center {p : Public} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (hs : s.phase = .centerGradient) :
    RadiusPairInvariant (update s reply) (radiusPairStep s reply (0, 0)) := by
  by_cases hg : ‖readGradient reply‖ ≤ gradientThreshold p
  · simp [radiusPairStep, Accepted, RadiusStart, update, hs, hg, finish, RadiusPairInvariant]
    positivity
  · have hh := initialTrial_radiusPairBounds ({ s with centerG := readGradient reply })
    simpa only [radiusPairStep, Accepted, hs, reduceCtorEq, false_and, ite_false,
      update, hg, RadiusStart, true_or, startTrial, and_self, ite_true, RadiusPairInvariant] using hh

lemma radiusPairInvariant_hessian {p : Public} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (q : ℝ × ℝ) (hs : s.phase = .newtonHessian)
    (hq : RadiusPairBounds s q) (hτ : 0 < s.τ) (hη : s.η ≤ s.τ)
    (hr : 0 ≤ s.r) (hrc : s.r ≤ radiusCap p s.τ)
    (hp : 0 ≤ previousRadius s) (hpc : previousRadius s ≤ radiusCap p s.τ / 2) :
    RadiusPairInvariant (update s reply) (radiusPairStep s reply q) := by
  by_cases hg : ‖newtonPoint p s.b s.center s.x s.g (readHessian reply) - s.center‖ ≤ 2 * s.r
  · rw [radiusPairStep_hessian_guard s reply q hs hg]
    simpa only [update, hs, hg, ite_true, RadiusPairInvariant, RadiusPairBounds, previousRadius] using hq
  · rw [radiusPairStep_hessian_failure s reply q hs hτ hg]
    simp only [update, hs, hg, ite_false]
    by_cases hsmall : s.r < radiusCap p s.τ
    · simp only [failedTrial, ite_eq_left hsmall]
      exact grownTrial_radiusPairBounds s q hq hr hsmall
    · simp only [failedTrial, ite_eq_right hsmall]
      exact doubledTrial_radiusPairBounds s q hq hτ hη
        (le_antisymm hrc (le_of_not_gt hsmall)) hp hpc


lemma radiusPairBounds_actual_open {p : Public} {f : p.E → ℝ} (s : State p) (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hR : 0 < p.R) (hmin : IsMinOn f Set.univ xs)
    (hp : PointwiseHessianExecution.InnerParameters f s)
    (ho : PointwiseHessianOuter.Invariant f xs s) (hprev : PreviousFailure f s)
    (q : ℝ × ℝ) (hq : RadiusPairBounds s q) : q.1 + q.2 ≤ 1792 * p.R ^ 2 := by
  have hcap := PointwiseHessianTuning.radiusCap_pos p hM₀ hR hp.τ_pos
  have hhalf := previousRadius_le_half s xs hf hc hM₀ hR hmin hp ho hprev
  exact radiusPairBounds_open s q hq hp.r_pos.le hp.r_le
    (previousRadius_nonneg s hM₀ hR hp.τ_pos) (by linarith)

lemma radiusPairInvariant_step {p : Public} {f : p.E → ℝ} (s : State p) (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hR : 0 < p.R) (hmin : IsMinOn f Set.univ xs)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (q : ℝ × ℝ)
    (hi : PointwiseHessianExecution.StateInvariant f xs s)
    (hprev : CertificateInvariant f s) (hq : RadiusPairInvariant s q) :
    RadiusPairInvariant (update s reply) (radiusPairStep s reply q) := by
  cases hs : s.phase with
  | centerGradient =>
    have he : q = (0, 0) := by simpa only [RadiusPairInvariant, hs] using hq
    rw [he]
    exact radiusPairInvariant_center s reply hs
  | newtonHessian =>
    have hh := hi.phase
    simp only [PointwiseHessianExecution.PhaseInvariant, hs] at hh
    have hb : RadiusPairBounds s q := by simpa only [RadiusPairInvariant, hs] using hq
    exact radiusPairInvariant_hessian s reply q hs hb hh.1.τ_pos hh.1.η_le hh.1.r_pos.le hh.1.r_le
      (previousRadius_nonneg s hM₀ hR hh.1.τ_pos)
      (previousRadius_le_half s xs hf hc hM₀ hR hmin hh.1 hi.outer (hprev (Or.inl hs)))
  | newtonGradient =>
    have hh := hi.phase
    simp only [PointwiseHessianExecution.PhaseInvariant, hs] at hh
    have hb : RadiusPairBounds s q := by simpa only [RadiusPairInvariant, hs] using hq
    exact radiusPairInvariant_gradient s reply q hs hb
      (radiusPairBounds_actual_open s xs hf hc hM₀ hR hmin hh.1 hi.outer (hprev (Or.inr hs)) q hb)
  | finished =>
    rw [radiusPairStep_finished s reply q hs]
    simpa only [update, hs] using hq

lemma radiusPairInvariant_path {p : Public} {f : p.E → ℝ} (s : ℕ → State p) (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hR : 0 < p.R) (hmin : IsMinOn f Set.univ xs)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hi : ∀ k < N, PointwiseHessianExecution.StateInvariant f xs (s k))
    (hprev : ∀ k < N, CertificateInvariant f (s k))
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k)) :
    RadiusPairInvariant (s N) (radiusPair s reply N) := by
  induction N with
  | zero => exact radiusPairInvariant_zero _
  | succ N ih =>
    have hh := ih (fun k hk => hi k (by omega)) (fun k hk => hprev k (by omega))
      (fun k hk => hs k (by omega))
    have hstep := radiusPairInvariant_step (s N) xs hf hc hM₀ hR hmin (reply N)
      (radiusPair s reply N) (hi N (by omega)) (hprev N (by omega)) hh
    rw [← hs N (by omega)] at hstep
    exact hstep


lemma radiusPairInvariant_open {p : Public} {f : p.E → ℝ} (s : State p) (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hR : 0 < p.R) (hmin : IsMinOn f Set.univ xs)
    (hi : PointwiseHessianExecution.StateInvariant f xs s)
    (hprev : CertificateInvariant f s) (q : ℝ × ℝ) (hq : RadiusPairInvariant s q) :
    q.1 + q.2 ≤ 1792 * p.R ^ 2 := by
  cases hs : s.phase with
  | centerGradient =>
    have he : q = (0, 0) := by simpa only [RadiusPairInvariant, hs] using hq
    rw [he]
    simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 1792) (sq_nonneg p.R)
  | newtonHessian =>
    have hh := hi.phase
    simp only [PointwiseHessianExecution.PhaseInvariant, hs] at hh
    exact radiusPairBounds_actual_open s xs hf hc hM₀ hR hmin hh.1 hi.outer (hprev (Or.inl hs)) q
      (by simpa only [RadiusPairInvariant, hs] using hq)
  | newtonGradient =>
    have hh := hi.phase
    simp only [PointwiseHessianExecution.PhaseInvariant, hs] at hh
    exact radiusPairBounds_actual_open s xs hf hc hM₀ hR hmin hh.1 hi.outer (hprev (Or.inr hs)) q
      (by simpa only [RadiusPairInvariant, hs] using hq)
  | finished => simpa only [RadiusPairInvariant, hs] using hq

lemma accepted_radiusPair_charge {p : Public} {f : p.E → ℝ} {xs : p.E} (s : State p)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f) (hM₀ : 0 ≤ p.M₀) (hR : 0 < p.R)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (q : ℝ × ℝ)
    (hi : PointwiseHessianExecution.PhaseInvariant f xs s)
    (hprev : CertificateInvariant f s) (hrad : RadiusInvariant f s)
    (hq : RadiusPairInvariant s q) (ha : Accepted s reply)
    (hg : readGradient reply = gradient f s.x) :
    q.1 + q.2 ≤ 252 * ‖s.x - s.center‖ ^ 2 := by
  have hp := hi
  simp only [PointwiseHessianExecution.PhaseInvariant, ha.1] at hp
  have hb : s.b = 1 / s.τ := le_antisymm hp.1.b_le (le_of_not_gt ha.2.2.1)
  have hstop : gradientThreshold p < ‖gradient f s.x‖ := by
    simpa only [hg] using lt_of_not_ge ha.2.1
  have hres : ‖(1 / s.τ) • gradient f s.x + s.x - s.center‖ ≤ ‖s.x - s.center‖ / 2 := by
    simpa only [hb, hg] using ha.2.2.2
  apply radiusPairBounds_accept s q (by simpa only [RadiusPairInvariant, ha.1] using hq)
    hp.1.r_pos.le (previousRadius_nonneg s hM₀ hR hp.1.τ_pos)
  · exact certified_radius_accept_bound s hf hc hp.1 (hrad (Or.inr ha.1)) hstop hres
  · exact previousRadius_accept_bound s hf hc hp.1.τ_pos (hprev (Or.inr ha.1)) hres

lemma path_radius_square_sum {p : Public} {f : p.E → ℝ} (s : ℕ → State p) (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hR : 0 < p.R) (hmin : IsMinOn f Set.univ xs)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hi : ∀ k ≤ N, PointwiseHessianExecution.StateInvariant f xs (s k))
    (hprev : ∀ k ≤ N, CertificateInvariant f (s k))
    (hrad : ∀ k < N, RadiusInvariant f (s k))
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k))
    (hg : ∀ k < N, (s k).phase = .newtonGradient → readGradient (reply k) = gradient f (s k).x)
    (hloss : (∑ k ∈ Finset.range N, loss (s k) (reply k)) ≤ p.R ^ 2) :
    (∑ k ∈ Finset.range N, if RadiusStart (s k) (s (k + 1)) then (s (k + 1)).r ^ 2 else 0) ≤
      2464 * p.R ^ 2 := by
  have hq (k : ℕ) (hk : k ≤ N) := radiusPairInvariant_path s xs hf hc hM₀ hR hmin reply k
    (fun i hi' => hi i (by omega)) (fun i hi' => hprev i (by omega))
    (fun i hi' => hs i (by omega))
  have hopen := radiusPairInvariant_open (s N) xs hf hc hM₀ hR hmin (hi N le_rfl)
    (hprev N le_rfl) (radiusPair s reply N) (hq N le_rfl)
  have hsum : (∑ k ∈ Finset.range N, if Accepted (s k) (reply k) then
      (radiusPair s reply k).1 + (radiusPair s reply k).2 else 0) ≤
      252 * (∑ k ∈ Finset.range N, if Accepted (s k) (reply k) then
        ‖(s k).x - (s k).center‖ ^ 2 else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hk' := Finset.mem_range.mp hk
    by_cases ha : Accepted (s k) (reply k)
    · simp only [ite_eq_left ha]
      exact accepted_radiusPair_charge (s k) hf hc hM₀ hR (reply k) (radiusPair s reply k)
        (hi k hk'.le).phase (hprev k hk'.le) (hrad k hk') (hq k hk'.le) ha (hg k hk' ha.1)
    · simp only [ite_eq_right ha, mul_zero, le_refl]
  have hsteps := path_displacement_sum s reply N (fun k hk => (hi k hk.le).outer) hloss
  rw [radius_pair_path_balance s reply N hs]
  linarith


lemma interior_gradient_count {p : Public} {f : p.E → ℝ} {xs : p.E} (s : ℕ → State p)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hi : ∀ k ≤ N, PointwiseHessianExecution.PhaseInvariant f xs (s k))
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k))
    (hp : ∀ k ≤ N, (s k).phase = .newtonHessian ∨ (s k).phase = .newtonGradient)
    (hguard : ∀ k < N, (s k).phase = .newtonHessian →
      ‖newtonPoint p (s k).b (s k).center (s k).x (s k).g (readHessian (reply k)) - (s k).center‖ ≤ 2 * (s k).r)
    (hH : ∀ k < N, (s k).phase = .newtonHessian → reply k = .inr (fderiv ℝ (gradient f) (s k).x))
    (hg : ∀ k < N, (s k).phase = .newtonGradient → reply k = .inl (gradient f (s k).x)) :
    let t := 4 * (1 / (s 0).τ) * gradientThreshold p / 3
    let E := 2 * continuationRatio p (s 0).τ (s 0).r * (s 0).r + t
    ((∑ k ∈ Finset.range N, if (s k).phase = .newtonGradient then 1 else 0 : ℕ) : ℝ) ≤
      Real.log ((1 / (s 0).τ) / (s 0).b) / Real.log (1 + continuationRatio p (s 0).τ (s 0).r / 8) +
        Real.log (E / t) / Real.log 4 + 2 := by
  dsimp only
  have hpar : PointwiseHessianExecution.InnerParameters f (s 0) := by
    have hh := hi 0 (Nat.zero_le N)
    rcases hp 0 (Nat.zero_le N) with h | h
    · simp only [PointwiseHessianExecution.PhaseInvariant, h] at hh
      exact hh.1
    · simp only [PointwiseHessianExecution.PhaseInvariant, h] at hh
      exact hh.1
  have hcont := interior_continuation_count s reply N hM₀ hM₁ hpar.τ_pos hpar.r_pos.le
    hpar.b_pos hpar.b_le hs hp hguard
  have href := whole_episode_refinement_count s hf hc hM₀ hM₁ hR hε hT reply N hi hs hp hguard hH hg
  dsimp only at href
  have he : (∑ k ∈ Finset.range N, if (s k).phase = .newtonGradient then 1 else 0 : ℕ) =
      (∑ k ∈ Finset.range N, if (s k).phase = .newtonGradient ∧ (s k).b < 1 / (s 0).τ then 1 else 0) +
      (∑ k ∈ Finset.range N, if (s k).phase = .newtonGradient ∧ ¬ (s k).b < 1 / (s k).τ then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hsc := interior_path_scales s reply k
      (fun i hi' => hs i (by omega)) (fun i hi' => hp i (by omega))
      (fun i hi' => hguard i (by omega))
    have hτ := congrArg Prod.fst hsc
    dsimp only at hτ
    rw [hτ]
    by_cases hp' : (s k).phase = .newtonGradient <;>
      by_cases hb' : (s k).b < 1 / (s 0).τ <;>
        simp only [hp', hb', true_and, false_and, not_true_eq_false, not_false_eq_true, ite_true, ite_false]
  rw [he, Nat.cast_add]
  linarith


end LongTails.Proofs.PointwiseHessianEpisodes
