import LongTails.Proofs.GatedEscapeMoments
import LongTails.Proofs.GatedEscapePancake
import LongTails.Proofs.StrongGrowthAgdDrift
import Mathlib.Algebra.Order.Field.GeomSum

namespace LongTails.Proofs.GatedEscapeDeviation

open MeasureTheory ProbabilityTheory LongTails.Algorithms.GatedPerturbedEscape
  LongTails.Proofs.GatedEscapeProcess LongTails.Proofs.GatedEscapeMoments
  LongTails.Proofs.StrongGrowthAgdBlocks LongTails.Proofs.ComparisonTrustTaylor
  LongTails.Proofs.GatedEscapePancake
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]
variable {σ : ℝ}

abbrev DState (E : Type) := E × E × ℕ × Bool

variable (cfg : Config) (g : E → Ω → E) (f : E → ℝ)

def bad (R δn : ℝ) (u w : E) : Prop := cfg.r < ‖u‖ ∨ R < ‖w‖ ∨ δn < ‖u - w‖

open Classical in
noncomputable def dstep (x g0 : E) (R δn : ℝ) (s : DState E) (ω : Fin cfg.b → Ω) : DState E :=
  if s.2.2.2 = true then s else
    (s.1 - cfg.η • (bmean cfg g (x + s.1) ω - g0), s.2.1 - cfg.η • (gradient f (x + s.2.1) - g0),
      s.2.2.1 + 1, decide (bad cfg R δn (s.1 - cfg.η • (bmean cfg g (x + s.1) ω - g0))
        (s.2.1 - cfg.η • (gradient f (x + s.2.1) - g0))))

noncomputable def dY (q : ℝ) (s : DState E) : ℝ := ‖s.1 - s.2.1‖ ^ 2 / q ^ (2 * s.2.2.1)

noncomputable def tY (q A : ℝ) (s : DState E) : ℝ := min (‖s.1 - s.2.1‖ ^ 2) A / q ^ (2 * s.2.2.1)

variable {cfg g f}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma dY_nonneg {q : ℝ} (hq : 0 < q) (s : DState E) : 0 ≤ dY q s := by
  unfold dY; positivity

theorem dY_step (hb : 0 < cfg.b) (h : Noise g (gradient f) p σ)
    (x g0 : E) {R δn q : ℝ} (hq : 1 ≤ q)
    (hlin : ∀ u w : E, ‖u‖ ≤ R → ‖w‖ ≤ R →
      ‖(u - w) - cfg.η • (gradient f (x + u) - gradient f (x + w))‖ ≤ q * ‖u - w‖)
    (hrR : cfg.r ≤ R) (s : DState E) (hs : s.2.2.2 = false) (hgood : ¬ bad cfg R δn s.1 s.2.1) :
    ∫ ω, dY q (dstep cfg g f x g0 R δn s ω) ∂(Measure.pi fun _ : Fin cfg.b => p) ≤
      dY q s + cfg.η ^ 2 * σ ^ 2 / cfg.b / q ^ (2 * (s.2.2.1 + 1)) := by
  unfold bad at hgood
  push Not at hgood
  obtain ⟨hu, hw, _⟩ := hgood
  have hq0 : 0 < q := by linarith
  set e : (Fin cfg.b → Ω) → E := fun ω => bmean cfg g (x + s.1) ω - gradient f (x + s.1) with he
  set D := (s.1 - s.2.1) - cfg.η • (gradient f (x + s.1) - gradient f (x + s.2.1)) with hD
  have hdiff : ∀ ω, (dstep cfg g f x g0 R δn s ω).1 - (dstep cfg g f x g0 R δn s ω).2.1 = D - cfg.η • e ω := by
    intro ω; simp only [dstep, hs, Bool.false_eq_true, ↓reduceIte, hD, he]; module
  have ht : ∀ ω, (dstep cfg g f x g0 R δn s ω).2.2.1 = s.2.2.1 + 1 := by
    intro ω; simp only [dstep, hs, Bool.false_eq_true, ↓reduceIte]
  have hval : ∀ ω, dY q (dstep cfg g f x g0 R δn s ω) = ‖D - cfg.η • e ω‖ ^ 2 / q ^ (2 * (s.2.2.1 + 1)) := by
    intro ω; unfold dY; rw [hdiff, ht]
  simp_rw [hval]
  have hexp : ∀ ω, ‖D - cfg.η • e ω‖ ^ 2 = ‖D‖ ^ 2 - 2 * cfg.η * ⟪D, e ω⟫ + cfg.η ^ 2 * ‖e ω‖ ^ 2 := by
    intro ω
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]; ring
  simp_rw [hexp]
  have hi1 : Integrable (fun ω => ⟪D, e ω⟫) (Measure.pi fun _ : Fin cfg.b => p) :=
    (err_integrable cfg hb h (x + s.1)).const_inner D
  have hi2 := err_sq_integrable cfg hb h (x + s.1)
  have H1 : Integrable (fun ω => ‖D‖ ^ 2 - 2 * cfg.η * ⟪D, e ω⟫) (Measure.pi fun _ : Fin cfg.b => p) :=
    (integrable_const _).sub (hi1.const_mul _)
  have H2 : Integrable (fun ω => cfg.η ^ 2 * ‖e ω‖ ^ 2) (Measure.pi fun _ : Fin cfg.b => p) := hi2.const_mul _
  have H3 : Integrable (fun ω => 2 * cfg.η * ⟪D, e ω⟫) (Measure.pi fun _ : Fin cfg.b => p) := hi1.const_mul _
  have hz : ∫ ω, ⟪D, e ω⟫ ∂(Measure.pi fun _ : Fin cfg.b => p) = 0 := integral_inner_err cfg hb h (x + s.1) D
  have hint : ∫ ω, (‖D‖ ^ 2 - 2 * cfg.η * ⟪D, e ω⟫ + cfg.η ^ 2 * ‖e ω‖ ^ 2) / q ^ (2 * (s.2.2.1 + 1))
      ∂(Measure.pi fun _ : Fin cfg.b => p) =
      (‖D‖ ^ 2 + cfg.η ^ 2 * ∫ ω, ‖e ω‖ ^ 2 ∂(Measure.pi fun _ : Fin cfg.b => p)) / q ^ (2 * (s.2.2.1 + 1)) := by
    rw [integral_div, integral_add H1 H2, integral_sub (integrable_const _) H3, integral_const_mul,
      integral_const_mul, hz]
    simp
  rw [hint]
  have hD' : ‖D‖ ≤ q * ‖s.1 - s.2.1‖ := hlin s.1 s.2.1 (hu.trans hrR) hw
  have hE : ∫ ω, ‖e ω‖ ^ 2 ∂(Measure.pi fun _ : Fin cfg.b => p) ≤ σ ^ 2 / cfg.b :=
    integral_err_sq cfg hb h (x + s.1)
  have hqp : 0 < q ^ (2 * (s.2.2.1 + 1)) := pow_pos hq0 _
  have hsplit : q ^ (2 * (s.2.2.1 + 1)) = q ^ (2 * s.2.2.1) * q ^ 2 := by rw [← pow_add]; ring_nf
  have hD2 : ‖D‖ ^ 2 ≤ q ^ 2 * ‖s.1 - s.2.1‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hD' 2
  rw [add_div]
  have h1 : ‖D‖ ^ 2 / q ^ (2 * (s.2.2.1 + 1)) ≤ dY q s := by
    unfold dY
    rw [div_le_div_iff₀ hqp (pow_pos hq0 _), hsplit]
    nlinarith [pow_pos hq0 (2 * s.2.2.1)]
  have h2 : cfg.η ^ 2 * (∫ ω, ‖e ω‖ ^ 2 ∂(Measure.pi fun _ : Fin cfg.b => p)) / q ^ (2 * (s.2.2.1 + 1)) ≤
      cfg.η ^ 2 * σ ^ 2 / cfg.b / q ^ (2 * (s.2.2.1 + 1)) := by
    apply div_le_div_of_nonneg_right _ hqp.le
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hE (sq_nonneg _)
  linarith

lemma dY_step_integrable (hb : 0 < cfg.b) (h : Noise g (gradient f) p σ) (x g0 : E) {R δn q : ℝ}
    (s : DState E) (hs : s.2.2.2 = false) :
    Integrable (fun ω => dY q (dstep cfg g f x g0 R δn s ω)) (Measure.pi fun _ : Fin cfg.b => p) := by
  set e : (Fin cfg.b → Ω) → E := fun ω => bmean cfg g (x + s.1) ω - gradient f (x + s.1) with he
  set D := (s.1 - s.2.1) - cfg.η • (gradient f (x + s.1) - gradient f (x + s.2.1)) with hD
  have hval : ∀ ω, dY q (dstep cfg g f x g0 R δn s ω) =
      (‖D‖ ^ 2 - 2 * cfg.η * ⟪D, e ω⟫ + cfg.η ^ 2 * ‖e ω‖ ^ 2) / q ^ (2 * (s.2.2.1 + 1)) := by
    intro ω
    have hdiff : (dstep cfg g f x g0 R δn s ω).1 - (dstep cfg g f x g0 R δn s ω).2.1 =
        D - cfg.η • e ω := by
      simp only [dstep, hs, Bool.false_eq_true, ↓reduceIte, hD, he]; module
    have ht : (dstep cfg g f x g0 R δn s ω).2.2.1 = s.2.2.1 + 1 := by
      simp only [dstep, hs, Bool.false_eq_true, ↓reduceIte]
    unfold dY; rw [hdiff, ht, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs]
    ring
  simp_rw [hval]
  have hi1 : Integrable (fun ω => ⟪D, e ω⟫) (Measure.pi fun _ : Fin cfg.b => p) :=
    (err_integrable cfg hb h (x + s.1)).const_inner D
  have hi2 : Integrable (fun ω => ‖e ω‖ ^ 2) (Measure.pi fun _ : Fin cfg.b => p) :=
    err_sq_integrable cfg hb h (x + s.1)
  have H1 : Integrable (fun ω => ‖D‖ ^ 2 - 2 * cfg.η * ⟪D, e ω⟫ + cfg.η ^ 2 * ‖e ω‖ ^ 2)
      (Measure.pi fun _ : Fin cfg.b => p) := ((integrable_const _).sub (hi1.const_mul _)).add (hi2.const_mul _)
  exact H1.div_const (q ^ (2 * (s.2.2.1 + 1)))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma tY_le_dY {q A : ℝ} (hq : 0 < q) (s : DState E) : tY q A s ≤ dY q s := by
  unfold tY dY
  exact div_le_div_of_nonneg_right (min_le_left _ _) (pow_pos hq _).le

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma tY_nonneg {q A : ℝ} (hq : 0 < q) (hA : 0 ≤ A) (s : DState E) : 0 ≤ tY q A s := by
  unfold tY
  exact div_nonneg (le_min (sq_nonneg _) hA) (pow_pos hq _).le

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma tY_le {q A : ℝ} (hq : 1 ≤ q) (hA : 0 ≤ A) (s : DState E) : tY q A s ≤ A := by
  unfold tY
  rw [div_le_iff₀ (pow_pos (by linarith) _)]
  have : 1 ≤ q ^ (2 * s.2.2.1) := one_le_pow₀ hq
  nlinarith [min_le_right (‖s.1 - s.2.1‖ ^ 2) A]

lemma tY_measurable (q A : ℝ) : Measurable (tY (E := E) q A) := by
  unfold tY
  refine Measurable.div ?_ ?_
  · exact ((measurable_fst.sub (measurable_fst.comp measurable_snd)).norm.pow_const 2).min
      measurable_const
  · exact (measurable_from_top (f := fun k : ℕ => q ^ (2 * k))).comp
      (measurable_fst.comp (measurable_snd.comp measurable_snd))

lemma dstep_measurable (hg : Measurable (Function.uncurry g)) (hgf : Continuous (gradient f))
    (x g0 : E) (R δn : ℝ) : Measurable (Function.uncurry (dstep cfg g f x g0 R δn)) := by
  have hb : Measurable (fun z : DState E × (Fin cfg.b → Ω) => bmean cfg g (x + z.1.1) z.2) :=
    bmean_measurable_joint cfg hg (q := fun s : DState E => x + s.1)
      (measurable_const.add measurable_fst)
  have hu : Measurable (fun z : DState E × (Fin cfg.b → Ω) =>
      z.1.1 - cfg.η • (bmean cfg g (x + z.1.1) z.2 - g0)) :=
    (measurable_fst.comp measurable_fst).sub ((hb.sub measurable_const).const_smul _)
  have hw : Measurable (fun z : DState E × (Fin cfg.b → Ω) =>
      z.1.2.1 - cfg.η • (gradient f (x + z.1.2.1) - g0)) := by
    have h1 : Measurable (fun z : DState E × (Fin cfg.b → Ω) => z.1.2.1) :=
      measurable_fst.comp (measurable_snd.comp measurable_fst)
    exact h1.sub (((hgf.measurable.comp (measurable_const.add h1)).sub measurable_const).const_smul _)
  have hset : MeasurableSet {z : DState E × (Fin cfg.b → Ω) |
      bad cfg R δn (z.1.1 - cfg.η • (bmean cfg g (x + z.1.1) z.2 - g0))
        (z.1.2.1 - cfg.η • (gradient f (x + z.1.2.1) - g0))} := by
    unfold bad
    exact (measurableSet_lt measurable_const hu.norm).union ((measurableSet_lt measurable_const hw.norm).union
      (measurableSet_lt measurable_const (hu.sub hw).norm))
  have hdec : Measurable (fun z : DState E × (Fin cfg.b → Ω) =>
      (Classical.propDecidable (bad cfg R δn (z.1.1 - cfg.η • (bmean cfg g (x + z.1.1) z.2 - g0))
        (z.1.2.1 - cfg.η • (gradient f (x + z.1.2.1) - g0)))).decide) := by
    refine measurable_to_countable' fun c => ?_
    cases c
    · convert hset.compl using 1; ext z; simp
    · convert hset using 1; ext z; simp
  have hfr : MeasurableSet {z : DState E × (Fin cfg.b → Ω) | z.1.2.2.2 = true} :=
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_fst)))
      (measurableSet_singleton true)
  unfold dstep
  exact Measurable.ite hfr measurable_fst (hu.prodMk (hw.prodMk
    (((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))).add_const 1).prodMk
      hdec)))

theorem tY_step (hb : 0 < cfg.b) (h : Noise g (gradient f) p σ)
    (x g0 : E) {R δn q : ℝ} (hq : 1 ≤ q)
    (hlin : ∀ u w : E, ‖u‖ ≤ R → ‖w‖ ≤ R →
      ‖(u - w) - cfg.η • (gradient f (x + u) - gradient f (x + w))‖ ≤ q * ‖u - w‖)
    (hrR : cfg.r ≤ R) (s : DState E) (hs : s.2.2.2 = false) (hgood : ¬ bad cfg R δn s.1 s.2.1) :
    ∫ ω, tY q (δn ^ 2) (dstep cfg g f x g0 R δn s ω) ∂(Measure.pi fun _ : Fin cfg.b => p) ≤
      tY q (δn ^ 2) s + cfg.η ^ 2 * σ ^ 2 / cfg.b / q ^ (2 * (s.2.2.1 + 1)) := by
  have hq0 : 0 < q := by linarith
  have hfull := dY_step hb h x g0 hq hlin hrR s hs hgood
  have hint := dY_step_integrable (R := R) (δn := δn) (q := q) hb h x g0 s hs
  have hmono : ∫ ω, tY q (δn ^ 2) (dstep cfg g f x g0 R δn s ω) ∂(Measure.pi fun _ : Fin cfg.b => p) ≤
      ∫ ω, dY q (dstep cfg g f x g0 R δn s ω) ∂(Measure.pi fun _ : Fin cfg.b => p) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => tY_nonneg hq0 (sq_nonneg _) _) hint
      (Filter.Eventually.of_forall fun ω => tY_le_dY hq0 _)
  have hcur : tY q (δn ^ 2) s = dY q s := by
    unfold bad at hgood
    push Not at hgood
    unfold tY dY
    rw [min_eq_left (pow_le_pow_left₀ (norm_nonneg _) hgood.2.2 2)]
  rw [hcur]
  linarith

noncomputable def dcost (q κ : ℝ) (s : DState E) : ℝ := if s.2.2.2 = true then 0 else κ / q ^ (2 * (s.2.2.1 + 1))

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma dcost_measurable (q κ : ℝ) : Measurable (dcost (E := E) q κ) := by
  unfold dcost
  refine Measurable.ite ((measurable_snd.comp (measurable_snd.comp measurable_snd))
    (measurableSet_singleton true)) measurable_const ?_
  exact measurable_const.div ((measurable_from_top (f := fun k : ℕ => q ^ (2 * (k + 1)))).comp
    (measurable_fst.comp (measurable_snd.comp measurable_snd)))

theorem dev_terminal (hb : 0 < cfg.b) (h : Noise g (gradient f) p σ) (hgf : Continuous (gradient f))
    (x g0 : E) {R δn q : ℝ} (hq : 1 < q)
    (hlin : ∀ u w : E, ‖u‖ ≤ R → ‖w‖ ≤ R →
      ‖(u - w) - cfg.η • (gradient f (x + u) - gradient f (x + w))‖ ≤ q * ‖u - w‖)
    (hrR : cfg.r ≤ R) (s0 : DState E) (hs0 : s0.2.2.2 = false → ¬ bad cfg R δn s0.1 s0.2.1)
    (hs0t : s0.2.2.1 = 0) (n : ℕ) :
    ∫ β, tY q (δn ^ 2) (run (dstep cfg g f x g0 R δn) s0 β n)
        ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) ≤
      tY q (δn ^ 2) s0 + cfg.η ^ 2 * σ ^ 2 / cfg.b / (q ^ 2 - 1) := by
  have hq1 : 1 ≤ q := hq.le
  have hq0 : 0 < q := by linarith
  set κ := cfg.η ^ 2 * σ ^ 2 / cfg.b with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set ν := Measure.pi fun _ : Fin cfg.b => p
  set step := dstep cfg g f x g0 R δn
  have hstep : Measurable (Function.uncurry step) := dstep_measurable h.meas hgf x g0 R δn
  set Inv : ℕ → Set (DState E) := fun t =>
    {s | s.2.2.1 ≤ t ∧ (s.2.2.2 = false → s.2.2.1 = t ∧ ¬ bad cfg R δn s.1 s.2.1)} with hInv
  have hInvStep : ∀ t, ∀ s ∈ Inv t, ∀ y, step s y ∈ Inv (t + 1) := by
    intro t s hs y
    by_cases hfz : s.2.2.2 = true
    · have : step s y = s := by simp only [step, dstep, hfz, ↓reduceIte]
      rw [this]
      exact ⟨hs.1.trans (Nat.le_succ t), fun hf => absurd hfz (by simp [hf])⟩
    · have hf : s.2.2.2 = false := by simpa using hfz
      obtain ⟨ht, _⟩ := hs.2 hf
      refine ⟨?_, ?_⟩
      · simp only [step, dstep, hf, Bool.false_eq_true, ↓reduceIte]; omega
      · intro hb2
        simp only [step, dstep, hf, Bool.false_eq_true, ↓reduceIte, decide_eq_false_iff_not] at hb2 ⊢
        exact ⟨by omega, hb2⟩
  have hs0' : s0 ∈ Inv 0 := ⟨by rw [hs0t], fun hf => ⟨hs0t, hs0 hf⟩⟩
  have hmem : ∀ β t, run step s0 β t ∈ Inv t := fun β t => run_mem_inv step s0 Inv hInvStep hs0' β t
  have hYint : ∀ t, Integrable (fun β => tY q (δn ^ 2) (run step s0 β t))
      (Measure.infinitePi fun _ : ℕ => ν) := by
    intro t
    refine Integrable.of_bound (C := δn ^ 2)
      ((tY_measurable q (δn ^ 2)).comp (run_measurable step _ hstep t)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun β => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (tY_nonneg hq0 (sq_nonneg _) _)]
    exact tY_le hq1 (sq_nonneg _) _
  have hcbd : ∀ s : DState E, 0 ≤ dcost q κ s ∧ dcost q κ s ≤ κ := by
    intro s; unfold dcost
    split_ifs
    · exact ⟨le_rfl, hκ0⟩
    · exact ⟨by positivity, div_le_self hκ0 (one_le_pow₀ hq1)⟩
  have hcint : ∀ t, Integrable (fun β => dcost q κ (run step s0 β t)) (Measure.infinitePi fun _ : ℕ => ν) := by
    intro t
    refine Integrable.of_bound (C := κ)
      ((dcost_measurable q κ).comp (run_measurable step _ hstep t)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun β => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hcbd _).1]; exact (hcbd _).2
  have hdr := drift step s0 ν hstep 1 Inv hInvStep hs0' (tY q (δn ^ 2)) (dcost q κ) (fun _ _ => 0)
    (tY_measurable q (δn ^ 2)) (dcost_measurable q κ) measurable_const hYint hcint
    (fun _ => integrable_const _) n (by
      intro e _ s hs
      simp only [add_zero]
      have hrun1 : ∀ tail, run step s tail 1 = step s (tail 0) := fun _ => rfl
      simp_rw [hrun1]
      rw [integral_eval ν (fun y => tY q (δn ^ 2) (step s y))
        ((tY_measurable q (δn ^ 2)).comp (hstep.comp (measurable_const.prodMk measurable_id)))]
      by_cases hfz : s.2.2.2 = true
      · have : ∀ y, step s y = s := fun y => by simp only [step, dstep, hfz, ↓reduceIte]
        simp_rw [this]
        rw [integral_const]; simp only [probReal_univ, one_smul]
        linarith [(hcbd s).1]
      · have hf : s.2.2.2 = false := by simpa using hfz
        have hc : dcost q κ s = κ / q ^ (2 * (s.2.2.1 + 1)) := by simp only [dcost, hf]; rfl
        rw [hc]
        exact tY_step hb h x g0 hq1 hlin hrR s hf ((hs.2 hf).2))
  simp only [mul_one, integral_zero, Finset.sum_const_zero, add_zero] at hdr
  have hsum : ∑ e ∈ Finset.range n, ∫ β, dcost q κ (run step s0 β e) ∂(Measure.infinitePi fun _ : ℕ => ν) ≤
      ∑ e ∈ Finset.range n, κ / q ^ (2 * (e + 1)) := by
    apply Finset.sum_le_sum
    intro e _
    have : ∫ β, dcost q κ (run step s0 β e) ∂(Measure.infinitePi fun _ : ℕ => ν) ≤
        ∫ _β, κ / q ^ (2 * (e + 1)) ∂(Measure.infinitePi fun _ : ℕ => ν) := by
      refine integral_mono (hcint e) (integrable_const _) (fun β => ?_)
      have hm := hmem β e
      unfold dcost
      split_ifs with hfz
      · positivity
      · have hf : (run step s0 β e).2.2.2 = false := by simpa using hfz
        rw [(hm.2 hf).1]
    simpa using this
  have hgeom : ∑ e ∈ Finset.range n, κ / q ^ (2 * (e + 1)) ≤ κ / (q ^ 2 - 1) := by
    have hq2 : 1 < q ^ 2 := by nlinarith
    have hr0 : 0 < (q ^ 2)⁻¹ := by positivity
    have hr1 : (q ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq2
    have hterm : ∀ e : ℕ, κ / q ^ (2 * (e + 1)) = κ * (q ^ 2)⁻¹ * ((q ^ 2)⁻¹) ^ e := by
      intro e; rw [pow_mul, div_eq_mul_inv, ← inv_pow, pow_succ]; ring
    simp_rw [hterm]
    rw [← Finset.mul_sum]
    have hgs : ∑ i ∈ Finset.range n, ((q ^ 2)⁻¹) ^ i ≤ 1 / (1 - (q ^ 2)⁻¹) := by
      have := geom_sum_Ico_le_of_lt_one (le_of_lt hr0) hr1 (m := 0) (n := n)
      rwa [pow_zero, ← Finset.range_eq_Ico] at this
    have hfin : κ * (q ^ 2)⁻¹ * (1 / (1 - (q ^ 2)⁻¹)) = κ / (q ^ 2 - 1) := by
      have : q ^ 2 - 1 ≠ 0 := by linarith
      field_simp
    have hk : 0 ≤ κ * (q ^ 2)⁻¹ := by positivity
    calc κ * (q ^ 2)⁻¹ * ∑ i ∈ Finset.range n, ((q ^ 2)⁻¹) ^ i
        ≤ κ * (q ^ 2)⁻¹ * (1 / (1 - (q ^ 2)⁻¹)) := mul_le_mul_of_nonneg_left hgs hk
      _ = κ / (q ^ 2 - 1) := hfin
  linarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem tY_of_dev {q δn : ℝ} (hq : 1 ≤ q) (s : DState E) (n : ℕ) (hn : s.2.2.1 ≤ n)
    (hdev : δn < ‖s.1 - s.2.1‖) (hδ : 0 ≤ δn) : δn ^ 2 / q ^ (2 * n) ≤ tY q (δn ^ 2) s := by
  unfold tY
  have hq0 : 0 < q := by linarith
  rw [min_eq_right (pow_le_pow_left₀ hδ hdev.le 2)]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hq0 _)
    (pow_le_pow_right₀ hq (by omega))

end LongTails.Proofs.GatedEscapeDeviation
