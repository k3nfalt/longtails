import LongTails.Proofs.HeavyTailedPLStep
import LongTails.Proofs.HeavyTailedPLNoise
import LongTails.Proofs.TerminalClippingStopping
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

open MeasureTheory
open scoped RealInnerProductSpace
open OracleTemplate.ContinuizedSimilarQuasar OracleTemplate.TerminalClipping

namespace OracleTemplate.HeavyTailedPL

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

noncomputable def stepSize (μ : ℝ) (t0 t : ℕ) : ℝ := 4 / (μ * ((t : ℝ) + t0))

noncomputable def drift (μ : ℝ) (t0 t : ℕ) : ℝ := 4 * ((t : ℝ) + t0 - 1) / μ

noncomputable def weight (t0 t : ℕ) : ℝ := ((t : ℝ) + t0 - 1) * ((t : ℝ) + t0 - 2)

noncomputable def noise (f : E → ℝ) (g : E → Ω → E) (x : E) (ω : Ω) : E := g x ω - gradient f x

noncomputable def centered (f : E → ℝ) (g : E → Ω → E) (P0 : Measure Ω) (M : ℝ) (x : E)
    (ω : Ω) : E :=
  clip M (noise f g x ω) - ∫ u, clip M (noise f g x u) ∂P0

noncomputable def martingaleTerm (f : E → ℝ) (g : E → Ω → E) (P0 : Measure Ω)
    (μ M : ℝ) (t0 t : ℕ) (x : E) (ω : Ω) : ℝ :=
  -drift μ t0 t * ⟪centered f g P0 M x ω, gradient f x⟫ - drift μ t0 t / 8 * ‖gradient f x‖ ^ 2

noncomputable def exceed (M : ℝ) (e : E) : ℝ := if M < ‖e‖ then 1 else 0

abbrev State (E : Type*) := ℕ × E × ℝ × ℝ × ℝ

noncomputable def sgdStep (f : E → ℝ) (g : E → Ω → E) (P0 : Measure Ω) (μ lam M : ℝ) (t0 : ℕ)
    (s : State E) (ω : Ω) : State E :=
  (s.1 + 1, s.2.1 - stepSize μ t0 s.1 • g s.2.1 ω,
    s.2.2.1 + lam * martingaleTerm f g P0 μ M t0 s.1 s.2.1 ω,
    s.2.2.2.1 + ‖clip M (noise f g s.2.1 ω)‖ ^ 2 / M ^ 2,
    s.2.2.2.2 + exceed M (noise f g s.2.1 ω))

def Good (f : E → ℝ) (μ lam M : ℝ) (t0 T : ℕ) (s : State E) : Prop :=
  s.1 ≤ T ∧ 2 * (lam * drift μ t0 s.1) * M * ‖gradient f s.2.1‖ ≤ 1

noncomputable def transition (f : E → ℝ) (g : E → Ω → E) (P0 : Measure Ω) (μ lam M : ℝ)
    (t0 T : ℕ) : State E → Ω → State E :=
  stopUnless (Good f μ lam M t0 T) (sgdStep f g P0 μ lam M t0)

noncomputable def plainStep (g : E → Ω → E) (μ : ℝ) (t0 : ℕ) (s : ℕ × E) (ω : Ω) : ℕ × E :=
  (s.1 + 1, s.2 - stepSize μ t0 s.1 • g s.2 ω)

section Measurability

variable {f : E → ℝ} {g : E → Ω → E}

lemma noise_measurable (hg : Measurable (Function.uncurry g)) (hgm : Measurable (gradient f)) :
    Measurable (fun z : E × Ω => noise f g z.1 z.2) :=
  hg.sub (hgm.comp measurable_fst)

lemma clipNoise_measurable (hg : Measurable (Function.uncurry g)) (hgm : Measurable (gradient f))
    (M : ℝ) : Measurable (fun z : E × Ω => clip M (noise f g z.1 z.2)) :=
  (measurable_clip M).comp (noise_measurable hg hgm)

lemma clipMean_measurable (hg : Measurable (Function.uncurry g)) (hgm : Measurable (gradient f))
    (P0 : Measure Ω) [SFinite P0] (M : ℝ) :
    Measurable (fun x : E => ∫ u, clip M (noise f g x u) ∂P0) :=
  (clipNoise_measurable hg hgm M).stronglyMeasurable.integral_prod_right'.measurable

lemma centered_measurable (hg : Measurable (Function.uncurry g)) (hgm : Measurable (gradient f))
    (P0 : Measure Ω) [SFinite P0] (M : ℝ) :
    Measurable (fun z : E × Ω => centered f g P0 M z.1 z.2) :=
  (clipNoise_measurable hg hgm M).sub ((clipMean_measurable hg hgm P0 M).comp measurable_fst)

lemma sgdStep_measurable (hg : Measurable (Function.uncurry g)) (hgm : Measurable (gradient f))
    (P0 : Measure Ω) [SFinite P0] (μ lam M : ℝ) (t0 : ℕ) :
    Measurable (Function.uncurry (sgdStep f g P0 μ lam M t0)) := by
  have hx : Measurable (fun z : State E × Ω => z.1.2.1) := measurable_fst.snd.fst
  have ht : Measurable (fun z : State E × Ω => z.1.1) := measurable_fst.fst
  have hxω : Measurable (fun z : State E × Ω => (z.1.2.1, z.2)) := hx.prodMk measurable_snd
  have hgz : Measurable (fun z : State E × Ω => g z.1.2.1 z.2) := hg.comp hxω
  have hn : Measurable (fun z : State E × Ω => noise f g z.1.2.1 z.2) :=
    (noise_measurable hg hgm).comp hxω
  have hc : Measurable (fun z : State E × Ω => centered f g P0 M z.1.2.1 z.2) :=
    (centered_measurable hg hgm P0 M).comp hxω
  have hgr : Measurable (fun z : State E × Ω => gradient f z.1.2.1) := hgm.comp hx
  have hstep : Measurable (fun z : State E × Ω => stepSize μ t0 z.1.1) :=
    (measurable_of_countable (stepSize μ t0)).comp ht
  have hdrift : Measurable (fun z : State E × Ω => drift μ t0 z.1.1) :=
    (measurable_of_countable (drift μ t0)).comp ht
  have hexc : Measurable (fun z : State E × Ω => exceed M (noise f g z.1.2.1 z.2)) := by
    unfold exceed
    exact Measurable.ite (measurableSet_lt measurable_const measurable_norm) measurable_const
      measurable_const |>.comp hn
  refine (ht.add_const 1).prodMk ((hx.sub (hstep.smul hgz)).prodMk
    ((measurable_fst.snd.snd.fst.add (measurable_const.mul ?_)).prodMk
    ((measurable_fst.snd.snd.snd.fst.add ?_).prodMk (measurable_fst.snd.snd.snd.snd.add hexc))))
  · unfold martingaleTerm
    exact ((hdrift.neg).mul (hc.inner hgr)).sub ((hdrift.div_const 8).mul (hgr.norm.pow_const 2))
  · exact (((measurable_clip M).comp hn).norm.pow_const 2).div_const _

omit [SecondCountableTopology E] in
lemma good_measurableSet (hgm : Measurable (gradient f)) (μ lam M : ℝ) (t0 T : ℕ) :
    MeasurableSet {s : State E | Good f μ lam M t0 T s} := by
  have h1 : MeasurableSet {s : State E | s.1 ≤ T} :=
    measurable_fst (measurableSet_le measurable_id measurable_const)
  have h2 : MeasurableSet {s : State E | 2 * (lam * drift μ t0 s.1) * M * ‖gradient f s.2.1‖ ≤ 1} :=
    measurableSet_le ((((measurable_of_countable (fun t => 2 * (lam * drift μ t0 t) * M)).comp
      measurable_fst).mul (hgm.comp measurable_snd.fst).norm)) measurable_const
  exact h1.inter h2

lemma transition_measurable (hg : Measurable (Function.uncurry g)) (hgm : Measurable (gradient f))
    (P0 : Measure Ω) [SFinite P0] (μ lam M : ℝ) (t0 T : ℕ) :
    Measurable (Function.uncurry (transition f g P0 μ lam M t0 T)) :=
  stopUnless_measurable (good_measurableSet hgm μ lam M t0 T)
    (sgdStep_measurable hg hgm P0 μ lam M t0)

end Measurability

section StepBounds

variable {f : E → ℝ} {g : E → Ω → E} {P0 : Measure Ω} [IsProbabilityMeasure P0]

lemma martingale_step_mgf (hg : Measurable (Function.uncurry g)) (hgm : Measurable (gradient f))
    {μ lam M σ : ℝ} {t0 t : ℕ} {x : E} (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hdr : 0 ≤ drift μ t0 t)
    (h2i : Integrable (fun ω => ‖noise f g x ω‖ ^ 2) P0)
    (hvar : ∫ ω, ‖noise f g x ω‖ ^ 2 ∂P0 ≤ σ ^ 2)
    (hsmall : 2 * (lam * drift μ t0 t) * M * ‖gradient f x‖ ≤ 1)
    (hcomp : lam * drift μ t0 t * σ ^ 2 ≤ 1 / 8) :
    Integrable (fun ω => Real.exp (lam * martingaleTerm f g P0 μ M t0 t x ω)) P0 ∧
      ∫ ω, Real.exp (lam * martingaleTerm f g P0 μ M t0 t x ω) ∂P0 ≤ 1 := by
  set τ := lam * drift μ t0 t with hτ
  have hτ0 : 0 ≤ τ := mul_nonneg hlam hdr
  set z := gradient f x
  have hnm : Measurable (fun ω => noise f g x ω) :=
    (noise_measurable hg hgm).comp (measurable_const.prodMk measurable_id)
  let X := fun ω => clip M (noise f g x ω)
  have hXm : Measurable X := (measurable_clip M).comp hnm
  have hXi : Integrable X P0 := integrable_clip hnm hM
  have hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) P0 :=
    Integrable.of_bound (hXm.norm.pow_const 2).aestronglyMeasurable (M ^ 2)
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_clip_le hM _) 2))
  have hmoment : ∫ ω, ‖X ω‖ ^ 2 ∂P0 ≤ σ ^ 2 :=
    (integral_mono hX2 h2i (fun ω => pow_le_pow_left₀ (norm_nonneg _)
      (norm_clip_le_norm M _) 2)).trans hvar
  have hc := centered_inner_mgf hXm hXi hX2 hτ0 z (fun ω => norm_clip_le hM _) hmoment hsmall
  have hrw (ω : Ω) : lam * martingaleTerm f g P0 μ M t0 t x ω =
      -τ * ⟪X ω - ∫ u, X u ∂P0, z⟫ + (-(τ / 8) * ‖z‖ ^ 2) := by
    simp only [martingaleTerm, centered, X, z, hτ]; ring
  simp_rw [hrw, Real.exp_add]
  refine ⟨hc.1.mul_const _, ?_⟩
  rw [integral_mul_const]
  have hle : Real.exp (τ ^ 2 * ‖z‖ ^ 2 * σ ^ 2) * Real.exp (-(τ / 8) * ‖z‖ ^ 2) ≤ 1 := by
    rw [← Real.exp_add, Real.exp_le_one_iff]
    have : τ * σ ^ 2 ≤ 1 / 8 := by simpa [hτ] using hcomp
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hτ0 (sq_nonneg ‖z‖))]
  exact (mul_le_mul_of_nonneg_right hc.2 (Real.exp_nonneg _)).trans hle

lemma square_step_mgf (hg : Measurable (Function.uncurry g)) (hgm : Measurable (gradient f))
    {M σ : ℝ} {x : E} (hM : 0 < M)
    (h2i : Integrable (fun ω => ‖noise f g x ω‖ ^ 2) P0)
    (hvar : ∫ ω, ‖noise f g x ω‖ ^ 2 ∂P0 ≤ σ ^ 2) :
    Integrable (fun ω => Real.exp (‖clip M (noise f g x ω)‖ ^ 2 / M ^ 2)) P0 ∧
      ∫ ω, Real.exp (‖clip M (noise f g x ω)‖ ^ 2 / M ^ 2) ∂P0 ≤
        Real.exp (2 * σ ^ 2 / M ^ 2) := by
  have hnm : Measurable (fun ω => noise f g x ω) :=
    (noise_measurable hg hgm).comp (measurable_const.prodMk measurable_id)
  have hZm : Measurable (fun ω => ‖clip M (noise f g x ω)‖ ^ 2) :=
    ((measurable_clip M).comp hnm).norm.pow_const 2
  have hb (ω : Ω) : ‖clip M (noise f g x ω)‖ ^ 2 ≤ M ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_clip_le hM.le _) 2
  have hZi : Integrable (fun ω => ‖clip M (noise f g x ω)‖ ^ 2) P0 :=
    Integrable.of_bound hZm.aestronglyMeasurable (M ^ 2) (Filter.Eventually.of_forall
      (fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hb ω))
  have hmean : ∫ ω, ‖clip M (noise f g x ω)‖ ^ 2 ∂P0 ≤ σ ^ 2 :=
    (integral_mono hZi h2i (fun ω => pow_le_pow_left₀ (norm_nonneg _)
      (norm_clip_le_norm M _) 2)).trans hvar
  exact nonnegative_bounded_mgf hZm hZi (by positivity) (fun ω => sq_nonneg _) hb hmean

lemma exceed_step (hg : Measurable (Function.uncurry g)) (hgm : Measurable (gradient f))
    {M ν q : ℝ} {x : E} (hM : 0 < M) (hq : 0 < q)
    (hqi : Integrable (fun ω => ‖noise f g x ω‖ ^ q) P0)
    (hqm : ∫ ω, ‖noise f g x ω‖ ^ q ∂P0 ≤ ν ^ q) :
    Integrable (fun ω => exceed M (noise f g x ω)) P0 ∧
      ∫ ω, exceed M (noise f g x ω) ∂P0 ≤ ν ^ q / M ^ q := by
  have hnm : Measurable (fun ω => noise f g x ω) :=
    (noise_measurable hg hgm).comp (measurable_const.prodMk measurable_id)
  have hem : Measurable (fun ω => exceed M (noise f g x ω)) := by
    unfold exceed
    exact (Measurable.ite (measurableSet_lt measurable_const measurable_norm) measurable_const
      measurable_const).comp hnm
  have hei : Integrable (fun ω => exceed M (noise f g x ω)) P0 :=
    Integrable.of_bound hem.aestronglyMeasurable 1 (Filter.Eventually.of_forall
      (fun ω => by simp only [exceed]; split_ifs <;> simp))
  refine ⟨hei, ?_⟩
  have hb := integral_mono hei (hqi.div_const (M ^ q))
    (fun ω => exceed_le hM hq (norm_nonneg (noise f g x ω)))
  rw [integral_div] at hb
  exact hb.trans (div_le_div_of_nonneg_right hqm (Real.rpow_pos_of_pos hM q).le)

end StepBounds

def Invariant (f : E → ℝ) (m μ L lam M β start : ℝ) (t0 : ℕ) (s : State E) : Prop :=
  0 ≤ s.2.2.2.2 ∧ (s.2.2.2.2 = 0 ∨ 1 ≤ s.2.2.2.2) ∧
    (s.2.2.2.2 = 0 → weight t0 s.1 * (f s.2.1 - m) ≤
      start + s.2.2.1 / lam + 16 * L / μ ^ 2 * M ^ 2 * s.2.2.2.1 +
        8 * (s.1 : ℝ) * ((s.1 : ℝ) + t0) * β / μ)

omit [BorelSpace E] [SecondCountableTopology E] in
omit [MeasurableSpace E] in
lemma invariant_step {f : E → ℝ} {g : E → Ω → E} {P0 : Measure Ω}
    {m μ L lam M β start : ℝ} {t0 : ℕ}
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hpl : ∀ x, 2 * μ * (f x - m) ≤ ‖gradient f x‖ ^ 2)
    (hμ : 0 < μ) (hL : 0 ≤ L) (hlam : 0 < lam) (hM : 0 < M) (ht0 : 3 ≤ t0)
    (hLη : ∀ t, L * stepSize μ t0 t ≤ 1 / 2)
    (hbias : ∀ x, ‖∫ u, clip M (noise f g x u) ∂P0‖ ^ 2 ≤ β)
    (s : State E) (hs : Invariant f m μ L lam M β start t0 s) (ω : Ω) :
    Invariant f m μ L lam M β start t0 (sgdStep f g P0 μ lam M t0 s ω) := by
  obtain ⟨t, x, A, B, C⟩ := s
  obtain ⟨hC0, hC01, hbound⟩ := hs
  simp only at hC0 hC01 hbound
  have hex0 : 0 ≤ exceed M (noise f g x ω) := by unfold exceed; split_ifs <;> norm_num
  have hex01 : exceed M (noise f g x ω) = 0 ∨ exceed M (noise f g x ω) = 1 := by
    unfold exceed; split_ifs <;> simp
  refine ⟨?_, ?_, ?_⟩
  · simp only [sgdStep]; linarith
  · simp only [sgdStep]
    rcases hC01 with h | h <;> rcases hex01 with h' | h'
    · left; rw [h, h']; ring
    · right; rw [h, h']; norm_num
    · right; rw [h']; linarith
    · right; rw [h']; linarith
  · intro hC'
    simp only [sgdStep] at hC' ⊢
    have hC : C = 0 := by linarith
    have hex : exceed M (noise f g x ω) = 0 := by linarith
    have hsmall : ‖noise f g x ω‖ ≤ M := by
      by_contra hn
      push Not at hn
      simp [exceed, hn] at hex
    have hclip : clip M (noise f g x ω) = noise f g x ω := clip_of_le hsmall
    have hprev := hbound hC
    set n : ℝ := (t : ℝ) + t0 with hn
    have hn3 : 3 ≤ n := by
      have : (3 : ℝ) ≤ t0 := by exact_mod_cast ht0
      have : (0 : ℝ) ≤ t := t.cast_nonneg
      linarith
    set η := stepSize μ t0 t with hη
    have hηe : η = 4 / (μ * n) := rfl
    have hηpos : 0 ≤ η := by rw [hηe]; positivity
    have hdesc := noisy_step hg hlip hL hηpos (hLη t) x (g x ω)
    set u := gradient f x
    set c := ∫ v, clip M (noise f g x v) ∂P0 with hcdef
    set z := centered f g P0 M x ω with hz
    have hnz : g x ω - u = z + c := by
      show g x ω - gradient f x = (clip M (noise f g x ω) - c) + c
      rw [sub_add_cancel, hclip]; rfl
    rw [hnz, inner_add_right] at hdesc
    have hY : ‖z + c‖ ^ 2 = ‖clip M (noise f g x ω)‖ ^ 2 := by
      rw [hclip, ← hnz]; rfl
    rw [hY] at hdesc
    have hipc : -⟪u, c⟫ ≤ ‖u‖ ^ 2 / 8 + 2 * ‖c‖ ^ 2 := by
      have h1 := neg_le_abs ⟪u, c⟫
      have h2 := abs_real_inner_le_norm u c
      nlinarith [sq_nonneg (‖u‖ / 2 - 2 * ‖c‖), norm_nonneg u, norm_nonneg c]
    have hw := weighted_step (r := f x - m) (r' := f (x - η • g x ω) - m) (G2 := ‖u‖ ^ 2)
      (ip := ⟪u, z⟫) (ipc := ⟪u, c⟫) (cc := ‖c‖ ^ 2)
      (Y := ‖clip M (noise f g x ω)‖ ^ 2) hμ hL hn3 (by rw [← hηe]; linarith)
      (hpl x) hipc (sq_nonneg _)
    have hwt : weight t0 (t + 1) = n * (n - 1) := by
      simp only [weight, hn]; push_cast; ring
    have hwt0 : weight t0 t = (n - 1) * (n - 2) := by
      simp only [weight, hn]
    have hmt : lam * martingaleTerm f g P0 μ M t0 t x ω / lam =
        -(4 * (n - 1) / μ) * ⟪u, z⟫ - 4 * (n - 1) / μ / 8 * ‖u‖ ^ 2 := by
      rw [mul_div_cancel_left₀ _ hlam.ne']
      simp only [martingaleTerm, drift, hz, u, hn, real_inner_comm]
    have hcb : 8 * (n - 1) * ‖c‖ ^ 2 / μ ≤ 8 * (n - 1) * β / μ := by
      apply div_le_div_of_nonneg_right _ hμ.le
      exact mul_le_mul_of_nonneg_left (hbias x) (by linarith)
    have hbias_sum : 8 * (t : ℝ) * ((t : ℝ) + t0) * β / μ + 8 * (n - 1) * β / μ ≤
        8 * ((t + 1 : ℕ) : ℝ) * (((t + 1 : ℕ) : ℝ) + t0) * β / μ := by
      have hβ : 0 ≤ β := (sq_nonneg _).trans (hbias x)
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ hμ.le
      push_cast
      have : 0 ≤ (t : ℝ) := t.cast_nonneg
      nlinarith [mul_nonneg hβ this]
    have hsplit : (A + lam * martingaleTerm f g P0 μ M t0 t x ω) / lam =
        A / lam + lam * martingaleTerm f g P0 μ M t0 t x ω / lam := add_div _ _ _
    have hB : 16 * L / μ ^ 2 * M ^ 2 * (B + ‖clip M (noise f g x ω)‖ ^ 2 / M ^ 2) =
        16 * L / μ ^ 2 * M ^ 2 * B + 16 * L / μ ^ 2 * ‖clip M (noise f g x ω)‖ ^ 2 := by
      field_simp
    rw [hwt, hsplit, hmt, hB]
    rw [hwt0] at hprev
    linarith

end OracleTemplate.HeavyTailedPL
