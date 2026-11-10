import LongTails.Proofs.StrongGrowthAgdCounting

namespace LongTails.Proofs.StrongGrowthAgdValidation

open MeasureTheory LongTails.Algorithms.StrongGrowthRestartedAgd LongTails.Proofs.StrongGrowthAgdProcess
  LongTails.Proofs.StrongGrowthAgdMoments LongTails.Proofs.StrongGrowthAgdMeasurable
  LongTails.Proofs.StrongGrowthAgdWeights LongTails.Proofs.StrongGrowthAgdModel
  LongTails.Proofs.StrongGrowthAgdEpochEnd LongTails.Proofs.StrongGrowthAgdInvariant
  LongTails.Proofs.StrongGrowthAgdEpoch LongTails.Proofs.StrongGrowthAgdBlocks
  LongTails.Proofs.StrongGrowthAgdEpochRun LongTails.Proofs.StrongGrowthAgdCounting
open scoped RealInnerProductSpace
open Classical

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]
variable {cfg : Config} {x0 : E} {g : E → Ω → E} {f : E → ℝ} {L ρ κ Δ εi : ℝ}

lemma chebyshev (H : Hyps cfg x0 g f p L ρ κ Δ εi) (q : E) (c : ℝ) (hc : 0 < c) :
    ∫ ω, (if c ≤ ‖bmean cfg g q ω - gradient f q‖ then (1 : ℝ) else 0)
        ∂(Measure.pi fun _ : Fin cfg.b => p) ≤
      (κ - 1) / cfg.b * ‖gradient f q‖ ^ 2 / c ^ 2 := by
  have hint := bmean_err_integrable cfg H.hb H.ho q
  have hmeas : Measurable (fun ω => if c ≤ ‖bmean cfg g q ω - gradient f q‖ then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_le measurable_const
      ((bmean_measurable cfg H.ho.meas q).sub measurable_const).norm) measurable_const measurable_const
  have hpt : ∀ ω, (if c ≤ ‖bmean cfg g q ω - gradient f q‖ then (1 : ℝ) else 0) ≤
      ‖bmean cfg g q ω - gradient f q‖ ^ 2 / c ^ 2 := by
    intro ω
    split_ifs with h
    · rw [le_div_iff₀ (by positivity)]
      nlinarith [norm_nonneg (bmean cfg g q ω - gradient f q)]
    · positivity
  have h1 : Integrable (fun ω => if c ≤ ‖bmean cfg g q ω - gradient f q‖ then (1 : ℝ) else 0)
      (Measure.pi fun _ : Fin cfg.b => p) := by
    refine (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    split_ifs <;> simp
  have h2 := integral_mono h1 (hint.div_const _) hpt
  rw [integral_div] at h2
  refine h2.trans ?_
  rw [div_le_div_iff_of_pos_right (by positivity)]
  exact integral_bmean_err cfg H.hb H.ho q

omit [IsProbabilityMeasure p] [BorelSpace E] in
variable (cfg x0 g f) in
lemma run_val_fields (H : Hyps cfg x0 g f p L ρ κ Δ εi) {sN : State E × E} (hinv : Inv cfg x0 f ρ sN)
    (hpos : cfg.pos sN.1.t = 0) (hd : sN.1.done = false) (tail : ℕ → (Fin cfg.b → Ω)) :
    ∀ t, cfg.K ≤ t → t ≤ cfg.Eb - 1 →
      (run (astep cfg x0 g f) sN tail t).1.trig = (run (astep cfg x0 g f) sN tail cfg.K).1.trig ∧
      (run (astep cfg x0 g f) sN tail t).1.ybar = (run (astep cfg x0 g f) sN tail cfg.K).1.ybar ∧
      (run (astep cfg x0 g f) sN tail t).1.xStart = sN.1.xStart ∧
      (run (astep cfg x0 g f) sN tail t).1.done = false ∧
      (run (astep cfg x0 g f) sN tail t).1.t = sN.1.t + t ∧
      (cfg.K < t → (run (astep cfg x0 g f) sN tail t).1.trig = false →
        (run (astep cfg x0 g f) sN tail t).1.vCount + cfg.K + 1 ≤ t) := by
  have hEb : 1 < cfg.Eb := Eb_gt cfg (by have := H.hc.hK; omega)
  have hKE : cfg.K < cfg.Eb := K_lt_Eb cfg
  have hpre : ∀ t ≤ cfg.K, (run (astep cfg x0 g f) sN tail t).1.done = false ∧
      (run (astep cfg x0 g f) sN tail t).1.t = sN.1.t + t ∧
      (run (astep cfg x0 g f) sN tail t).1.xStart = sN.1.xStart := by
    intro t
    induction t with
    | zero => intro _; exact ⟨hd, by simp [run_zero], rfl⟩
    | succ t ih =>
      intro ht
      obtain ⟨h1, h2, h3⟩ := ih (by omega)
      have hp : cfg.pos (run (astep cfg x0 g f) sN tail t).1.t = t := by
        rw [h2]; exact pos_add_of_zero cfg hpos (by omega)
      obtain ⟨a, b, c⟩ := blockStep_not_last (cfg := cfg) (x0 := x0) (g := g) h1 (by omega) (tail t)
      rw [run_succ, astep_fst]
      exact ⟨a, by rw [c, h2]; ring, by rw [b, h3]⟩
  intro t hKt htE
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hKt
  induction k with
  | zero =>
    obtain ⟨h1, h2, h3⟩ := hpre cfg.K le_rfl
    exact ⟨rfl, rfl, h3, h1, by simpa using h2, fun h => absurd h (by omega)⟩
  | succ k ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih (by omega) (by omega)
    set s' := run (astep cfg x0 g f) sN tail (cfg.K + k) with hs'
    have hp : cfg.pos s'.1.t = cfg.K + k := by rw [h5]; exact pos_add_of_zero cfg hpos (by omega)
    have hinv' : Inv cfg x0 f ρ s' := run_inv H.hc H.h hinv tail (cfg.K + k)
    rw [← add_assoc, run_succ, astep_fst]
    by_cases hk0 : k = 0
    ·
      subst hk0
      rw [blockStep_gd cfg x0 g h4 (by omega)]
      refine ⟨h1, h2, h3, h4, by simp only; rw [h5]; ring, fun _ _ => ?_⟩
      show s'.1.vCount + cfg.K + 1 ≤ cfg.K + 0 + 1
      have := hinv'.hvc0 h4 (by omega)
      omega
    · have hKk : cfg.K < cfg.pos s'.1.t := by rw [hp]; omega
      rw [blockStep_val cfg x0 g h4 hKk (by rw [hp]; omega)]
      refine ⟨h1, h2, h3, h4, by simp only; rw [h5]; ring, fun _ htr => ?_⟩
      show (if s'.1.trig = true then s'.1.vCount
        else s'.1.vCount + (if ‖bmean cfg g s'.1.ybar (tail (cfg.K + k))‖ ≤ cfg.thr then 1 else 0)) +
          cfg.K + 1 ≤ cfg.K + (k + 1)
      have hvc := hinv'.hvc2 h4 hKk
      rw [hp] at hvc
      split_ifs <;> omega

variable (cfg x0 g f) in
def acceptLast (sN : State E × E) (ω : Fin cfg.b → Ω) : Prop :=
  sN.1.trig = false ∧
    cfg.m < 2 * (sN.1.vCount + (if ‖bmean cfg g sN.1.ybar ω‖ ≤ cfg.thr then 1 else 0))

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] [FiniteDimensional ℝ E] in
variable (cfg x0 g f) in
lemma last_block_cases {s : State E} (hd : s.done = false) (hk : cfg.K < cfg.pos s.t)
    (heq : cfg.pos s.t + 1 = cfg.Eb) (ω : Fin cfg.b → Ω) :
    (acceptLast cfg g (s, (0 : E)) ω →
      blockStep cfg x0 g s ω = { s with t := s.t + 1, done := true, out := s.ybar }) ∧
    (¬ acceptLast cfg g (s, (0 : E)) ω → blockStep cfg x0 g s ω = restart cfg x0 s) := by
  rw [blockStep_last cfg x0 g hd hk heq]
  unfold acceptLast
  simp only
  constructor
  · intro ⟨h1, h2⟩
    rw [ite_eq_left]
    refine ⟨by simp [h1], ?_⟩
    simp only [h1, Bool.false_eq_true, ↓reduceIte]
    exact h2
  · intro hn
    rw [ite_eq_right]
    intro ⟨h1, h2⟩
    apply hn
    have h1' : s.trig = false := by simpa using h1
    refine ⟨h1', ?_⟩
    simp only [h1', Bool.false_eq_true, ↓reduceIte] at h2
    exact h2

omit [IsProbabilityMeasure p] [BorelSpace E] in
variable (cfg x0 g f) in
lemma done_run_Eb (H : Hyps cfg x0 g f p L ρ κ Δ εi) {sN : State E × E} (hinv : Inv cfg x0 f ρ sN)
    (hpos : cfg.pos sN.1.t = 0) (hd : sN.1.done = false) (tail : ℕ → (Fin cfg.b → Ω)) :
    ((run (astep cfg x0 g f) sN tail cfg.Eb).1.done = true ↔
      acceptLast cfg g (run (astep cfg x0 g f) sN tail (cfg.Eb - 1)) (tail (cfg.Eb - 1))) ∧
    (acceptLast cfg g (run (astep cfg x0 g f) sN tail (cfg.Eb - 1)) (tail (cfg.Eb - 1)) →
      (run (astep cfg x0 g f) sN tail cfg.Eb).1.out = (run (astep cfg x0 g f) sN tail cfg.K).1.ybar) := by
  have hEb : 1 < cfg.Eb := Eb_gt cfg (by have := H.hc.hK; omega)
  have hKE : cfg.K < cfg.Eb := K_lt_Eb cfg
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := run_val_fields cfg x0 g f H hinv hpos hd tail (cfg.Eb - 1) (by omega) le_rfl
  set sL := run (astep cfg x0 g f) sN tail (cfg.Eb - 1) with hsL
  have hp : cfg.pos sL.1.t = cfg.Eb - 1 := by rw [h5]; exact pos_add_of_zero cfg hpos (by omega)
  have hrun : run (astep cfg x0 g f) sN tail cfg.Eb = astep cfg x0 g f sL (tail (cfg.Eb - 1)) := by
    have hEb' : cfg.Eb = cfg.Eb - 1 + 1 := by omega
    rw [hsL]
    conv_lhs => rw [hEb']
    exact run_succ _ _ _ _
  obtain ⟨hA, hR⟩ := last_block_cases cfg x0 g h4 (by rw [hp]; have := H.hm; unfold Config.Eb; omega)
    (by rw [hp]; omega) (tail (cfg.Eb - 1))
  have hacc_iff : acceptLast cfg g (sL.1, (0 : E)) (tail (cfg.Eb - 1)) ↔ acceptLast cfg g sL (tail (cfg.Eb - 1)) :=
    Iff.rfl
  rw [hrun]
  constructor
  · constructor
    · intro hdone
      by_contra hn
      rw [astep_fst, hR (fun h' => hn (hacc_iff.mp h'))] at hdone
      unfold restart at hdone
      simp only at hdone
      rw [h4] at hdone
      exact Bool.noConfusion hdone
    · intro hacc
      rw [astep_fst, hA (hacc_iff.mpr hacc)]
  · intro hacc
    rw [astep_fst, hA (hacc_iff.mpr hacc)]
    exact h2

variable (cfg x0 g f) in
noncomputable def rejE (εi : ℝ) (sN : State E × E) (tail : ℕ → (Fin cfg.b → Ω)) : ℝ :=
  if sN.1.done = false ∧ (run (astep cfg x0 g f) sN tail cfg.K).1.trig = false ∧
      ‖gradient f (run (astep cfg x0 g f) sN tail cfg.K).1.ybar‖ ≤ εi ∧
      (run (astep cfg x0 g f) sN tail cfg.Eb).1.done = false then 1 else 0

variable (cfg x0 g f) in
noncomputable def trigE (sN : State E × E) (tail : ℕ → (Fin cfg.b → Ω)) : ℝ :=
  if sN.1.done = false ∧ (run (astep cfg x0 g f) sN tail cfg.K).1.trig = true then 1 else 0

variable (cfg x0 g f) in
noncomputable def wbadE (εi : ℝ) (sN : State E × E) (tail : ℕ → (Fin cfg.b → Ω)) : ℝ :=
  if sN.1.done = false ∧ (run (astep cfg x0 g f) sN tail cfg.Eb).1.done = true ∧
      3 * εi < ‖gradient f (run (astep cfg x0 g f) sN tail cfg.K).1.ybar‖ then
    ‖gradient f (run (astep cfg x0 g f) sN tail cfg.K).1.ybar‖ else 0

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma epoch_trichotomy (sN : State E × E) (tail : ℕ → (Fin cfg.b → Ω)) (hd : sN.1.done = false)
    (hnd : (run (astep cfg x0 g f) sN tail cfg.Eb).1.done = false) :
    1 ≤ trigE cfg x0 g f sN tail + badE cfg x0 g f εi sN tail + rejE cfg x0 g f εi sN tail := by
  have hb0 : 0 ≤ badE cfg x0 g f εi sN tail := by unfold badE; positivity
  have hr0 : 0 ≤ rejE cfg x0 g f εi sN tail := by unfold rejE; positivity
  have ht0 : 0 ≤ trigE cfg x0 g f sN tail := by unfold trigE; positivity
  by_cases htr : (run (astep cfg x0 g f) sN tail cfg.K).1.trig = true
  · have h1 : trigE cfg x0 g f sN tail = 1 := by unfold trigE; rw [ite_eq_left ⟨hd, htr⟩]
    linarith
  · have htr' : (run (astep cfg x0 g f) sN tail cfg.K).1.trig = false := by simpa using htr
    by_cases hb : εi < ‖gradient f (run (astep cfg x0 g f) sN tail cfg.K).1.ybar‖
    · have h1 : badE cfg x0 g f εi sN tail = 1 := by unfold badE; rw [ite_eq_left ⟨hd, htr', hb⟩]
      linarith
    · have h1 : rejE cfg x0 g f εi sN tail = 1 := by
        unfold rejE; rw [ite_eq_left ⟨hd, htr', not_lt.mp hb, hnd⟩]
      linarith

section chernoff

variable (H : Hyps cfg x0 g f p L ρ κ Δ εi)
include H

lemma block_fail_le (q : E) (hq : ‖gradient f q‖ ≤ εi) :
    ∫ ω, (if ¬ ‖bmean cfg g q ω‖ ≤ cfg.thr then (1 : ℝ) else 0) ∂(Measure.pi fun _ : Fin cfg.b => p) ≤
      4 * ((κ - 1) / cfg.b) := by
  have hε := H.hεi
  have h1 := chebyshev H q (εi / 2) (by positivity)
  have hpt : ∀ ω, (if ¬ ‖bmean cfg g q ω‖ ≤ cfg.thr then (1 : ℝ) else 0) ≤
      (if εi / 2 ≤ ‖bmean cfg g q ω - gradient f q‖ then (1 : ℝ) else 0) := by
    intro ω
    by_cases ha : ‖bmean cfg g q ω‖ ≤ cfg.thr
    · rw [ite_eq_right (not_not.mpr ha)]
      split_ifs <;> norm_num
    · rw [ite_eq_left ha]
      have hb : εi / 2 ≤ ‖bmean cfg g q ω - gradient f q‖ := by
        rw [H.hthr] at ha
        have := norm_sub_norm_le (bmean cfg g q ω) (gradient f q)
        rw [not_le] at ha
        linarith
      simp only [ite_eq_left hb, le_refl]
  have hm1 : Measurable (fun ω => if ¬ ‖bmean cfg g q ω‖ ≤ cfg.thr then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_le (bmean_measurable cfg H.ho.meas q).norm measurable_const).compl
      measurable_const measurable_const
  have hm2 : Measurable (fun ω => if εi / 2 ≤ ‖bmean cfg g q ω - gradient f q‖ then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_le measurable_const
      ((bmean_measurable cfg H.ho.meas q).sub measurable_const).norm) measurable_const measurable_const
  have hi1 : Integrable (fun ω => if ¬ ‖bmean cfg g q ω‖ ≤ cfg.thr then (1 : ℝ) else 0)
      (Measure.pi fun _ : Fin cfg.b => p) :=
    (integrable_const (1 : ℝ)).mono' hm1.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by split_ifs <;> simp)
  have hi2 : Integrable (fun ω => if εi / 2 ≤ ‖bmean cfg g q ω - gradient f q‖ then (1 : ℝ) else 0)
      (Measure.pi fun _ : Fin cfg.b => p) :=
    (integrable_const (1 : ℝ)).mono' hm2.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by split_ifs <;> simp)
  refine (integral_mono hi1 hi2 hpt).trans (h1.trans ?_)
  have hδ0 : 0 ≤ (κ - 1) / cfg.b := div_nonneg (by linarith [H.hκ]) (Nat.cast_nonneg _)
  rw [div_le_iff₀ (by positivity)]
  have hg2 : ‖gradient f q‖ ^ 2 ≤ εi ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hq 2
  nlinarith [mul_le_mul_of_nonneg_left hg2 hδ0]

lemma block_pass_le (q : E) (hq : 3 * εi < ‖gradient f q‖) :
    ∫ ω, (if ‖bmean cfg g q ω‖ ≤ cfg.thr then (1 : ℝ) else 0) ∂(Measure.pi fun _ : Fin cfg.b => p) ≤
      4 * ((κ - 1) / cfg.b) := by
  have hε := H.hεi
  have hgpos : 0 < ‖gradient f q‖ := by linarith
  have h1 := chebyshev H q (‖gradient f q‖ / 2) (by positivity)
  have hpt : ∀ ω, (if ‖bmean cfg g q ω‖ ≤ cfg.thr then (1 : ℝ) else 0) ≤
      (if ‖gradient f q‖ / 2 ≤ ‖bmean cfg g q ω - gradient f q‖ then (1 : ℝ) else 0) := by
    intro ω
    by_cases ha : ‖bmean cfg g q ω‖ ≤ cfg.thr
    · rw [ite_eq_left ha]
      have hb : ‖gradient f q‖ / 2 ≤ ‖bmean cfg g q ω - gradient f q‖ := by
        rw [H.hthr] at ha
        have := norm_sub_norm_le (gradient f q) (bmean cfg g q ω)
        rw [norm_sub_rev] at this
        linarith
      simp only [ite_eq_left hb, le_refl]
    · rw [ite_eq_right ha]
      split_ifs <;> norm_num
  have hm1 : Measurable (fun ω => if ‖bmean cfg g q ω‖ ≤ cfg.thr then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_le (bmean_measurable cfg H.ho.meas q).norm measurable_const)
      measurable_const measurable_const
  have hm2 : Measurable (fun ω => if ‖gradient f q‖ / 2 ≤ ‖bmean cfg g q ω - gradient f q‖ then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_le measurable_const
      ((bmean_measurable cfg H.ho.meas q).sub measurable_const).norm) measurable_const measurable_const
  have hi1 : Integrable (fun ω => if ‖bmean cfg g q ω‖ ≤ cfg.thr then (1 : ℝ) else 0)
      (Measure.pi fun _ : Fin cfg.b => p) :=
    (integrable_const (1 : ℝ)).mono' hm1.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by split_ifs <;> simp)
  have hi2 : Integrable (fun ω => if ‖gradient f q‖ / 2 ≤ ‖bmean cfg g q ω - gradient f q‖ then (1 : ℝ) else 0)
      (Measure.pi fun _ : Fin cfg.b => p) :=
    (integrable_const (1 : ℝ)).mono' hm2.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by split_ifs <;> simp)
  refine (integral_mono hi1 hi2 hpt).trans (h1.trans ?_)
  rw [div_le_iff₀ (by positivity)]
  have hδ0 : 0 ≤ (κ - 1) / cfg.b := div_nonneg (by linarith [H.hκ]) (Nat.cast_nonneg _)
  nlinarith [mul_nonneg hδ0 (sq_nonneg ‖gradient f q‖)]

omit [BorelSpace E] [IsProbabilityMeasure p] in
lemma prod_factors (c : ℝ) :
    ∏ e ∈ Finset.range (cfg.Eb - 1), (if e ≤ cfg.K then (1 : ℝ) else c) = c ^ (cfg.m - 1) := by
  have hEb : cfg.Eb - 1 = (cfg.K + 1) + (cfg.m - 1) := by
    unfold Config.Eb; have := H.hm; omega
  rw [hEb, Finset.prod_range_add]
  have h1 : ∏ e ∈ Finset.range (cfg.K + 1), (if e ≤ cfg.K then (1 : ℝ) else c) = 1 := by
    refine Finset.prod_eq_one (fun e he => ?_)
    rw [ite_eq_left]; exact Nat.lt_succ_iff.mp (Finset.mem_range.mp he)
  have h2 : ∏ e ∈ Finset.range (cfg.m - 1), (if cfg.K + 1 + e ≤ cfg.K then (1 : ℝ) else c) = c ^ (cfg.m - 1) := by
    rw [Finset.prod_congr rfl (fun e _ => ite_eq_right (by omega)), Finset.prod_const, Finset.card_range]
  rw [h1, h2, one_mul]

omit [BorelSpace E] [IsProbabilityMeasure p] in
lemma pos_lt_Eb' (t : ℕ) : cfg.pos t < cfg.Eb :=
  Nat.mod_lt _ (by have := H.hc.hK; unfold Config.Eb; omega)

theorem val_drift (Y : State E × E → ℝ) (hY : Measurable Y)
    (hYbd : ∀ sN', |Y sN'| ≤ (4 : ℝ) ^ cfg.Eb * W x0 sN')
    (hYpre : ∀ sN' : State E × E, cfg.pos sN'.1.t ≤ cfg.K → sN'.1.done = false → Y sN' = 1)
    (hYfirst : ∀ sN' : State E × E, cfg.pos sN'.1.t = cfg.K + 1 → sN'.1.done = false →
      Inv cfg x0 f ρ sN' → Y sN' ≤ 1)
    (hYstep : ∀ sN' : State E × E, sN'.1.done = false → cfg.K < cfg.pos sN'.1.t →
      cfg.pos sN'.1.t + 1 < cfg.Eb → Inv cfg x0 f ρ sN' →
      ∫ ω, Y (astep cfg x0 g f sN' ω) ∂(Measure.pi fun _ : Fin cfg.b => p) ≤
        (1 + 3 * (4 * ((κ - 1) / cfg.b))) * Y sN')
    {sN : State E × E} (hinv : Inv cfg x0 f ρ sN) (hpos : cfg.pos sN.1.t = 0) (hd : sN.1.done = false) :
    ∫ tail, Y (run (astep cfg x0 g f) sN tail (cfg.Eb - 1))
        ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) ≤
      (1 + 3 * (4 * ((κ - 1) / cfg.b))) ^ (cfg.m - 1) := by
  have hEb : 1 < cfg.Eb := Eb_gt cfg (by have := H.hc.hK; omega)
  have hKE : cfg.K < cfg.Eb := K_lt_Eb cfg
  set ν := (Measure.pi fun _ : Fin cfg.b => p) with hν
  set q := 4 * ((κ - 1) / cfg.b) with hq
  have hq0 : 0 ≤ q := by
    have : 0 ≤ (κ - 1) / cfg.b := div_nonneg (by linarith [H.hκ]) (Nat.cast_nonneg _)
    positivity
  let Inv₁ : ℕ → Set (State E × E) := fun t => {sN' | Inv cfg x0 f ρ sN' ∧
    (t < cfg.Eb → sN'.1.t = sN.1.t + t ∧ sN'.1.done = false)}
  let a : ℕ → ℝ := fun e => if e ≤ cfg.K then 1 else 1 + 3 * q
  have ha : ∀ e, 0 ≤ a e := fun e => by simp only [a]; split_ifs <;> linarith
  have hInv₁ : ∀ t, ∀ sN' ∈ Inv₁ t, ∀ ω, astep cfg x0 g f sN' ω ∈ Inv₁ (t + 1) := by
    intro t sN' hsN' ω
    refine ⟨inv_preserved cfg x0 g f ρ H.hc H.h hsN'.1 ω, fun ht => ?_⟩
    obtain ⟨ht', hd''⟩ := hsN'.2 (by omega)
    have hp : cfg.pos sN'.1.t = t := by rw [ht']; exact pos_add_of_zero cfg hpos (by omega)
    obtain ⟨h1, _, h3⟩ := blockStep_not_last (cfg := cfg) (x0 := x0) (g := g) hd'' (by omega) ω
    exact ⟨by rw [astep_fst, h3, ht']; ring, h1⟩
  have hs0 : sN ∈ Inv₁ 0 := ⟨hinv, fun _ => ⟨rfl, hd⟩⟩
  have hstep := measurable_astep' H
  have hYint : ∀ t, Integrable (fun tail => Y (run (astep cfg x0 g f) sN tail t))
      (Measure.infinitePi fun _ : ℕ => ν) := fun t => integrable_of_le_W H Y hY _ hYbd sN t
  have hdrift : ∀ e < cfg.Eb - 1, ∀ sN' ∈ Inv₁ (e * 1),
      ∫ tail, Y (run (astep cfg x0 g f) sN' tail 1) ∂(Measure.infinitePi fun _ : ℕ => ν) ≤ a e * Y sN' := by
    intro e he sN' hsN'
    rw [mul_one] at hsN'
    obtain ⟨hinv', ht', hd''⟩ := And.imp_right (fun h' => h' (by omega)) hsN'
    have hp : cfg.pos sN'.1.t = e := by rw [ht']; exact pos_add_of_zero cfg hpos (by omega)
    have hrw : ∀ tail : ℕ → (Fin cfg.b → Ω), Y (run (astep cfg x0 g f) sN' tail 1) =
        (fun ω => Y (astep cfg x0 g f sN' ω)) (tail 0) := fun tail => rfl
    simp_rw [hrw]
    rw [integral_eval ν (fun ω => Y (astep cfg x0 g f sN' ω))
      (hY.comp (measurable_astep_fun cfg x0 g f H.h H.ho.meas sN'))]
    have hnl : ∀ ω, (astep cfg x0 g f sN' ω).1.done = false ∧
        cfg.pos (astep cfg x0 g f sN' ω).1.t = e + 1 := by
      intro ω
      obtain ⟨h1, _, h3⟩ := blockStep_not_last (cfg := cfg) (x0 := x0) (g := g) hd'' (by omega) ω
      refine ⟨h1, ?_⟩
      rw [astep_fst, h3, pos_succ_of_lt cfg hEb (by omega), hp]
    by_cases he : e ≤ cfg.K
    · simp only [a, ite_eq_left he]
      rw [hYpre sN' (by rw [hp]; exact he) hd'', one_mul]
      have hle : ∀ ω, Y (astep cfg x0 g f sN' ω) ≤ 1 := by
        intro ω
        obtain ⟨h1, h2⟩ := hnl ω
        by_cases hpk : e + 1 ≤ cfg.K
        · rw [hYpre _ (by rw [h2]; exact hpk) h1]
        · have heK : e = cfg.K := by omega
          exact hYfirst _ (by rw [h2, heK]) h1 (inv_preserved cfg x0 g f ρ H.hc H.h hinv' ω)
      have hint : Integrable (fun ω => Y (astep cfg x0 g f sN' ω)) ν := by
        refine ((W_astep_integrable cfg x0 g f H.hb H.h H.ho H.hc sN').const_mul ((4 : ℝ) ^ cfg.Eb)).mono'
          (hY.comp (measurable_astep_fun cfg x0 g f H.h H.ho.meas sN')).aestronglyMeasurable
          (Filter.Eventually.of_forall fun ω => ?_)
        rw [Real.norm_eq_abs]
        exact hYbd _
      calc ∫ ω, Y (astep cfg x0 g f sN' ω) ∂ν ≤ ∫ ω, (1 : ℝ) ∂ν := integral_mono hint (integrable_const _) hle
        _ = 1 := by simp
    · simp only [a, ite_eq_right he]
      exact hYstep sN' hd'' (by rw [hp]; omega) (by rw [hp]; omega) hinv'
  have hdr := drift_mul (astep cfg x0 g f) sN ν hstep 1 Inv₁ hInv₁ hs0 Y hY a ha hYint (cfg.Eb - 1) hdrift
  rw [mul_one, hYpre sN (by rw [hpos]; exact Nat.zero_le _) hd, mul_one] at hdr
  have hprod : ∏ e ∈ Finset.range (cfg.Eb - 1), a e = (1 + 3 * q) ^ (cfg.m - 1) := prod_factors H _
  rw [hprod] at hdr
  exact hdr

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] H in
lemma pow_block (Y0 : ℝ) (hY0 : 0 ≤ Y0) (P : (Fin cfg.b → Ω) → Prop) [DecidablePred P]
    (hP : Measurable (fun ω => if P ω then (1 : ℝ) else 0))
    (hprob : ∫ ω, (if P ω then (1 : ℝ) else 0) ∂(Measure.pi fun _ : Fin cfg.b => p) ≤
      4 * ((κ - 1) / cfg.b)) :
    ∫ ω, Y0 * (if P ω then (4 : ℝ) else 1) ∂(Measure.pi fun _ : Fin cfg.b => p) ≤
      (1 + 3 * (4 * ((κ - 1) / cfg.b))) * Y0 := by
  have he : ∀ ω, Y0 * (if P ω then (4 : ℝ) else 1) = Y0 + 3 * Y0 * (if P ω then (1 : ℝ) else 0) := by
    intro ω; split_ifs <;> ring
  simp_rw [he]
  have hint : Integrable (fun ω => if P ω then (1 : ℝ) else 0) (Measure.pi fun _ : Fin cfg.b => p) :=
    (integrable_const (1 : ℝ)).mono' hP.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by split_ifs <;> simp)
  rw [integral_add (integrable_const _) (hint.const_mul _), integral_const, integral_const_mul]
  simp only [probReal_univ, one_smul]
  nlinarith [mul_le_mul_of_nonneg_left hprob (by positivity : (0:ℝ) ≤ 3 * Y0)]

theorem rej_bound {sN : State E × E} (hinv : Inv cfg x0 f ρ sN) (hpos : cfg.pos sN.1.t = 0)
    (hd : sN.1.done = false) :
    ∫ tail, rejE cfg x0 g f εi sN tail
        ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) ≤
      ((1 + 3 * (4 * ((κ - 1) / cfg.b))) / 2) ^ cfg.m := by
  have hEb : 1 < cfg.Eb := Eb_gt cfg (by have := H.hc.hK; omega)
  have hKE : cfg.K < cfg.Eb := K_lt_Eb cfg
  have hm := H.hm
  set ν := (Measure.pi fun _ : Fin cfg.b => p) with hν
  set q := 4 * ((κ - 1) / cfg.b) with hq
  have hq0 : 0 ≤ q := by
    have : 0 ≤ (κ - 1) / cfg.b := div_nonneg (by linarith [H.hκ]) (Nat.cast_nonneg _)
    positivity
  let Y : State E × E → ℝ := fun sN' =>
    if cfg.pos sN'.1.t ≤ cfg.K then (if sN'.1.done = false then 1 else 0)
    else if sN'.1.done = false ∧ sN'.1.trig = false ∧ ‖gradient f sN'.1.ybar‖ ≤ εi then
      (4 : ℝ) ^ (cfg.pos sN'.1.t - cfg.K - 1 - sN'.1.vCount) else 0
  have hY : Measurable Y := by
    have hT : Measurable (fun sN' : State E × E => sN'.1.t) := measurable_t.comp measurable_fst
    have hD : Measurable (fun sN' : State E × E => sN'.1.done) := measurable_done.comp measurable_fst
    have hTr : Measurable (fun sN' : State E × E => sN'.1.trig) := measurable_trig.comp measurable_fst
    have hVC : Measurable (fun sN' : State E × E => sN'.1.vCount) := measurable_vCount.comp measurable_fst
    have hG : Measurable (fun sN' : State E × E => ‖gradient f sN'.1.ybar‖) :=
      ((gradient_measurable f H.h).comp (measurable_ybar.comp measurable_fst)).norm
    refine Measurable.ite (hT (MeasurableSet.of_discrete (s := {n | cfg.pos n ≤ cfg.K}))) ?_ ?_
    · exact Measurable.ite (hD (MeasurableSet.of_discrete (s := {false}))) measurable_const measurable_const
    · refine Measurable.ite ?_ ?_ measurable_const
      · exact MeasurableSet.inter (hD (MeasurableSet.of_discrete (s := {false})))
          (MeasurableSet.inter (hTr (MeasurableSet.of_discrete (s := {false})))
            (measurableSet_le hG measurable_const))
      · exact (measurable_of_countable (fun n : ℕ × ℕ => (4 : ℝ) ^ (cfg.pos n.1 - cfg.K - 1 - n.2))).comp
          (hT.prodMk hVC)
  have hYbd : ∀ sN', |Y sN'| ≤ (4 : ℝ) ^ cfg.Eb * W x0 sN' := by
    intro sN'
    have hW := W_pos x0 sN'
    have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ cfg.Eb := one_le_pow₀ (by norm_num)
    have hp := pos_lt_Eb' H sN'.1.t
    simp only [Y]
    split_ifs
    · rw [abs_one]; nlinarith
    · rw [abs_zero]; positivity
    · rw [abs_of_nonneg (by positivity)]
      have : (4 : ℝ) ^ (cfg.pos sN'.1.t - cfg.K - 1 - sN'.1.vCount) ≤ (4 : ℝ) ^ cfg.Eb :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith
    · rw [abs_zero]; positivity
  have hYpre : ∀ sN' : State E × E, cfg.pos sN'.1.t ≤ cfg.K → sN'.1.done = false → Y sN' = 1 := by
    intro sN' h1 h2; simp only [Y, ite_eq_left h1, ite_eq_left h2]
  have hYfirst : ∀ sN' : State E × E, cfg.pos sN'.1.t = cfg.K + 1 → sN'.1.done = false →
      Inv cfg x0 f ρ sN' → Y sN' ≤ 1 := by
    intro sN' h1 h2 hinv'
    simp only [Y, ite_eq_right (by omega : ¬ cfg.pos sN'.1.t ≤ cfg.K)]
    split_ifs with h3
    · have hvc := hinv'.hvc2 h2 (by omega)
      rw [h1] at hvc ⊢
      have : cfg.K + 1 - cfg.K - 1 - sN'.1.vCount = 0 := by omega
      rw [this, pow_zero]
    · norm_num
  have hYstep : ∀ sN' : State E × E, sN'.1.done = false → cfg.K < cfg.pos sN'.1.t →
      cfg.pos sN'.1.t + 1 < cfg.Eb → Inv cfg x0 f ρ sN' →
      ∫ ω, Y (astep cfg x0 g f sN' ω) ∂ν ≤ (1 + 3 * q) * Y sN' := by
    intro sN' hd' hk hlt hinv'
    obtain ⟨s', N'⟩ := sN'
    simp only at hd' hk hlt
    have hval : ∀ ω, astep cfg x0 g f (s', N') ω =
        ({ s' with t := s'.t + 1, vCount := if s'.trig = true then s'.vCount
          else s'.vCount + (if ‖bmean cfg g s'.ybar ω‖ ≤ cfg.thr then 1 else 0) }, N') := by
      intro ω
      unfold astep
      rw [blockStep_val cfg x0 g hd' hk hlt, nextN_of_not cfg g f ω (by omega)]
    simp_rw [hval]
    have hp1 : cfg.pos (s'.t + 1) = cfg.pos s'.t + 1 := pos_succ_of_lt cfg hEb hlt
    simp only [Y, hp1, ite_eq_right (by omega : ¬ cfg.pos s'.t + 1 ≤ cfg.K), ite_eq_right (by omega : ¬ cfg.pos s'.t ≤ cfg.K)]
    by_cases hcond : s'.done = false ∧ s'.trig = false ∧ ‖gradient f s'.ybar‖ ≤ εi
    · obtain ⟨_, htr, hgood⟩ := hcond
      simp only [htr, Bool.false_eq_true, ↓reduceIte, hd', hgood, and_self]
      have hvc : s'.vCount + cfg.K + 1 ≤ cfg.pos s'.t := hinv'.hvc2 hd' hk
      set F := cfg.pos s'.t - cfg.K - 1 - s'.vCount with hF
      have hexp : ∀ ω, (4 : ℝ) ^ (cfg.pos s'.t + 1 - cfg.K - 1 -
          (s'.vCount + (if ‖bmean cfg g s'.ybar ω‖ ≤ cfg.thr then 1 else 0))) =
          (4 : ℝ) ^ F * (if ¬ ‖bmean cfg g s'.ybar ω‖ ≤ cfg.thr then (4 : ℝ) else 1) := by
        intro ω
        by_cases h1 : ‖bmean cfg g s'.ybar ω‖ ≤ cfg.thr
        · rw [ite_eq_left h1, ite_eq_right (not_not.mpr h1), mul_one]
          congr 1; rw [hF]; omega
        · rw [ite_eq_right h1, ite_eq_left h1, add_zero,
            show cfg.pos s'.t + 1 - cfg.K - 1 - s'.vCount = F + 1 by rw [hF]; omega, pow_succ]
      simp_rw [hexp]
      exact pow_block ((4 : ℝ) ^ F) (by positivity) _
        (Measurable.ite (measurableSet_le (bmean_measurable cfg H.ho.meas s'.ybar).norm measurable_const).compl
          measurable_const measurable_const) (block_fail_le H s'.ybar hgood)
    · have hc0 : ¬ (s'.done = false ∧ s'.trig = false ∧ ‖gradient f s'.ybar‖ ≤ εi) := hcond
      simp only [ite_eq_right hc0]
      simp only [integral_const, probReal_univ, one_smul, mul_zero, le_refl]
  have hvd := val_drift H Y hY hYbd hYpre hYfirst hYstep hinv hpos hd
  have hrej : ∀ tail, rejE cfg x0 g f εi sN tail =
      (fun (sL : State E × E) (ω : Fin cfg.b → Ω) =>
        if sL.1.trig = false ∧ ‖gradient f sL.1.ybar‖ ≤ εi ∧ ¬ acceptLast cfg g sL ω then (1 : ℝ) else 0)
        (run (astep cfg x0 g f) sN tail (cfg.Eb - 1)) (tail (cfg.Eb - 1)) := by
    intro tail
    obtain ⟨a1, a2, _, _, _, _⟩ := run_val_fields cfg x0 g f H hinv hpos hd tail (cfg.Eb - 1) (by omega) le_rfl
    obtain ⟨hiff, _⟩ := done_run_Eb cfg x0 g f H hinv hpos hd tail
    unfold rejE
    simp only [a1, a2, hd, true_and]
    congr 1
    apply propext
    constructor
    · rintro ⟨x1, x2, x3⟩
      refine ⟨x1, x2, fun hacc => ?_⟩
      rw [hiff.mpr hacc] at x3; exact Bool.noConfusion x3
    · rintro ⟨x1, x2, x3⟩
      refine ⟨x1, x2, ?_⟩
      by_contra hne
      exact x3 (hiff.mp (by simpa using hne))
  simp_rw [hrej]
  set Fn : State E × E → (Fin cfg.b → Ω) → ℝ := fun sL ω =>
    if sL.1.trig = false ∧ ‖gradient f sL.1.ybar‖ ≤ εi ∧ ¬ acceptLast cfg g sL ω then (1 : ℝ) else 0 with hFn
  have hFm : Measurable (Function.uncurry Fn) := by
    unfold Function.uncurry
    simp only [hFn]
    have hTr : Measurable (fun z : (State E × E) × (Fin cfg.b → Ω) => z.1.1.trig) :=
      measurable_trig.comp (measurable_fst.comp measurable_fst)
    have hG : Measurable (fun z : (State E × E) × (Fin cfg.b → Ω) => ‖gradient f z.1.1.ybar‖) :=
      ((gradient_measurable f H.h).comp (measurable_ybar.comp (measurable_fst.comp measurable_fst))).norm
    have hVC : Measurable (fun z : (State E × E) × (Fin cfg.b → Ω) => z.1.1.vCount) :=
      measurable_vCount.comp (measurable_fst.comp measurable_fst)
    have hB : Measurable (fun z : (State E × E) × (Fin cfg.b → Ω) => ‖bmean cfg g z.1.1.ybar z.2‖) :=
      (bmean_measurable_joint cfg H.ho.meas (α := State E × E) (q := fun sN' => sN'.1.ybar)
        (measurable_ybar.comp measurable_fst)).norm
    have hcount : Measurable (fun z : (State E × E) × (Fin cfg.b → Ω) =>
        2 * (z.1.1.vCount + (if ‖bmean cfg g z.1.1.ybar z.2‖ ≤ cfg.thr then 1 else 0))) :=
      (hVC.add (Measurable.ite (measurableSet_le hB measurable_const) measurable_const measurable_const)).const_mul 2
    have hacc : MeasurableSet {z : (State E × E) × (Fin cfg.b → Ω) | acceptLast cfg g z.1 z.2} := by
      unfold acceptLast
      exact MeasurableSet.inter (hTr (MeasurableSet.of_discrete (s := {false})))
        (hcount (MeasurableSet.of_discrete (s := {n | cfg.m < n})))
    have hset : MeasurableSet {z : (State E × E) × (Fin cfg.b → Ω) | z.1.1.trig = false ∧
        ‖gradient f z.1.1.ybar‖ ≤ εi ∧ ¬ acceptLast cfg g z.1 z.2} :=
      MeasurableSet.inter (hTr (MeasurableSet.of_discrete (s := {false})))
        (MeasurableSet.inter (measurableSet_le hG measurable_const) hacc.compl)
    exact Measurable.ite hset
      (measurable_const : Measurable fun _ : (State E × E) × (Fin cfg.b → Ω) => (1 : ℝ))
      (measurable_const : Measurable fun _ : (State E × E) × (Fin cfg.b → Ω) => (0 : ℝ))
  have hFint : Integrable (fun tail => Fn (run (astep cfg x0 g f) sN tail (cfg.Eb - 1)) (tail (cfg.Eb - 1)))
      (Measure.infinitePi fun _ : ℕ => ν) := by
    refine (integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun tail => ?_)
    · exact (hFm.comp ((run_measurable _ sN (measurable_astep' H) (cfg.Eb - 1)).prodMk
        (measurable_pi_apply _))).aestronglyMeasurable
    · simp only [hFn]; split_ifs <;> simp
  rw [step_integral (astep cfg x0 g f) sN ν (measurable_astep' H) (cfg.Eb - 1) Fn hFm hFint]
  have hlast : ∀ tail, ∫ ω, Fn (run (astep cfg x0 g f) sN tail (cfg.Eb - 1)) ω ∂ν ≤
      (1 + 3 * q) / 2 ^ cfg.m * Y (run (astep cfg x0 g f) sN tail (cfg.Eb - 1)) := by
    intro tail
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := run_val_fields cfg x0 g f H hinv hpos hd tail (cfg.Eb - 1) (by omega) le_rfl
    set sL := run (astep cfg x0 g f) sN tail (cfg.Eb - 1) with hsL
    have hp : cfg.pos sL.1.t = cfg.Eb - 1 := by rw [a5]; exact pos_add_of_zero cfg hpos (by omega)
    have hinvL : Inv cfg x0 f ρ sL := run_inv H.hc H.h hinv tail (cfg.Eb - 1)
    by_cases hc : sL.1.trig = false ∧ ‖gradient f sL.1.ybar‖ ≤ εi
    · obtain ⟨htr, hgood⟩ := hc
      have hvc := a6 (by have := H.hm; unfold Config.Eb; omega) htr
      have hY : Y sL = (4 : ℝ) ^ (cfg.pos sL.1.t - cfg.K - 1 - sL.1.vCount) := by
        simp only [Y]
        rw [ite_eq_right (by rw [hp]; have := H.hm; unfold Config.Eb; omega : ¬ cfg.pos sL.1.t ≤ cfg.K),
          ite_eq_left (show sL.1.done = false ∧ sL.1.trig = false ∧ ‖gradient f sL.1.ybar‖ ≤ εi from
            ⟨a4, htr, hgood⟩)]
      rw [hY]
      set F := cfg.pos sL.1.t - cfg.K - 1 - sL.1.vCount with hF
      have hFm' : F = cfg.m - 1 - sL.1.vCount := by rw [hF, hp]; unfold Config.Eb; omega
      have hpt : ∀ ω, Fn sL ω ≤ (1 / 2 ^ cfg.m) *
          ((4 : ℝ) ^ F * (if ¬ ‖bmean cfg g sL.1.ybar ω‖ ≤ cfg.thr then (4 : ℝ) else 1)) := by
        intro ω
        have h2m : (0 : ℝ) < 2 ^ cfg.m := by positivity
        simp only [hFn]
        split_ifs with h1 hpass hpass
        · obtain ⟨_, _, hnacc⟩ := h1
          unfold acceptLast at hnacc
          have hle : 2 * (sL.1.vCount + 1) ≤ cfg.m := by
            by_contra hcon; push Not at hcon
            exact hnacc ⟨htr, by rw [ite_eq_left hpass]; exact hcon⟩
          have h2 : cfg.m ≤ 2 * F := by omega
          have key : (2 : ℝ) ^ cfg.m ≤ (4 : ℝ) ^ F * 1 := by
            calc (2 : ℝ) ^ cfg.m ≤ (2 : ℝ) ^ (2 * F) := pow_le_pow_right₀ (by norm_num) h2
              _ = (4 : ℝ) ^ F * 1 := by rw [pow_mul]; norm_num
          rw [one_div, inv_mul_eq_div, le_div_iff₀ h2m, one_mul]; exact key
        · obtain ⟨_, _, hnacc⟩ := h1
          unfold acceptLast at hnacc
          have hle : 2 * (sL.1.vCount + 0) ≤ cfg.m := by
            by_contra hcon; push Not at hcon
            exact hnacc ⟨htr, by rw [ite_eq_right hpass]; exact hcon⟩
          have h2 : cfg.m ≤ 2 * (F + 1) := by omega
          have key : (2 : ℝ) ^ cfg.m ≤ (4 : ℝ) ^ F * 4 := by
            calc (2 : ℝ) ^ cfg.m ≤ (2 : ℝ) ^ (2 * (F + 1)) := pow_le_pow_right₀ (by norm_num) h2
              _ = (4 : ℝ) ^ F * 4 := by rw [pow_mul, pow_succ]; norm_num
          rw [one_div, inv_mul_eq_div, le_div_iff₀ h2m, one_mul]; exact key
        · positivity
        · positivity
      have hint1 : Integrable (fun ω => Fn sL ω) ν :=
        (integrable_const (1 : ℝ)).mono' (hFm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
          (Filter.Eventually.of_forall fun ω => by simp only [hFn]; split_ifs <;> simp)
      have hmP : Measurable (fun ω => if ¬ ‖bmean cfg g sL.1.ybar ω‖ ≤ cfg.thr then (1 : ℝ) else 0) :=
        Measurable.ite (measurableSet_le (bmean_measurable cfg H.ho.meas sL.1.ybar).norm measurable_const).compl
          measurable_const measurable_const
      have hint2 : Integrable (fun ω => (1 / 2 ^ cfg.m) *
          ((4 : ℝ) ^ F * (if ¬ ‖bmean cfg g sL.1.ybar ω‖ ≤ cfg.thr then (4 : ℝ) else 1))) ν := by
        refine (integrable_const ((1 / 2 ^ cfg.m) * ((4 : ℝ) ^ F * 4))).mono' ?_
          (Filter.Eventually.of_forall fun ω => ?_)
        · refine (Measurable.const_mul (Measurable.const_mul ?_ _) _).aestronglyMeasurable
          exact Measurable.ite (measurableSet_le (bmean_measurable cfg H.ho.meas sL.1.ybar).norm
            measurable_const).compl measurable_const measurable_const
        · rw [Real.norm_eq_abs, abs_of_nonneg (by split_ifs <;> positivity)]
          split_ifs <;> nlinarith [show (0:ℝ) ≤ (1 / 2 ^ cfg.m) * (4 : ℝ) ^ F by positivity]
      have hpb := pow_block ((4 : ℝ) ^ F) (by positivity) _ hmP (block_fail_le H sL.1.ybar hgood)
      calc ∫ ω, Fn sL ω ∂ν ≤ ∫ ω, (1 / 2 ^ cfg.m) *
            ((4 : ℝ) ^ F * (if ¬ ‖bmean cfg g sL.1.ybar ω‖ ≤ cfg.thr then (4 : ℝ) else 1)) ∂ν :=
            integral_mono hint1 hint2 hpt
        _ = (1 / 2 ^ cfg.m) * ∫ ω, (4 : ℝ) ^ F * (if ¬ ‖bmean cfg g sL.1.ybar ω‖ ≤ cfg.thr then (4 : ℝ) else 1) ∂ν :=
            integral_const_mul _ _
        _ ≤ (1 / 2 ^ cfg.m) * ((1 + 3 * q) * (4 : ℝ) ^ F) := mul_le_mul_of_nonneg_left hpb (by positivity)
        _ = (1 + 3 * q) / 2 ^ cfg.m * (4 : ℝ) ^ F := by ring
    · have hY0 : Y sL = 0 := by
        simp only [Y]
        rw [ite_eq_right (by rw [hp]; have := H.hm; unfold Config.Eb; omega : ¬ cfg.pos sL.1.t ≤ cfg.K)]
        rw [ite_eq_right (fun h' => hc ⟨h'.2.1, h'.2.2⟩)]
      have hF0 : ∀ ω, Fn sL ω = 0 := by
        intro ω; simp only [hFn]; rw [ite_eq_right (fun h' => hc ⟨h'.1, h'.2.1⟩)]
      simp_rw [hF0]
      rw [hY0]; simp
  have hYint := integrable_of_le_W H Y hY _ hYbd sN (cfg.Eb - 1)
  have hnn : ∀ tail, 0 ≤ ∫ ω, Fn (run (astep cfg x0 g f) sN tail (cfg.Eb - 1)) ω ∂ν := by
    intro tail
    refine integral_nonneg (fun ω => ?_)
    simp only [hFn]; split_ifs <;> norm_num
  calc ∫ tail, (∫ ω, Fn (run (astep cfg x0 g f) sN tail (cfg.Eb - 1)) ω ∂ν) ∂(Measure.infinitePi fun _ : ℕ => ν)
      ≤ ∫ tail, (1 + 3 * q) / 2 ^ cfg.m * Y (run (astep cfg x0 g f) sN tail (cfg.Eb - 1))
          ∂(Measure.infinitePi fun _ : ℕ => ν) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) (hYint.const_mul _)
          (Filter.Eventually.of_forall hlast)
    _ = (1 + 3 * q) / 2 ^ cfg.m * ∫ tail, Y (run (astep cfg x0 g f) sN tail (cfg.Eb - 1))
          ∂(Measure.infinitePi fun _ : ℕ => ν) := integral_const_mul _ _
    _ ≤ (1 + 3 * q) / 2 ^ cfg.m * (1 + 3 * q) ^ (cfg.m - 1) :=
        mul_le_mul_of_nonneg_left hvd (by positivity)
    _ = ((1 + 3 * q) / 2) ^ cfg.m := by
        rw [div_pow]
        have : (1 + 3 * q) / 2 ^ cfg.m * (1 + 3 * q) ^ (cfg.m - 1) = (1 + 3 * q) ^ (cfg.m - 1 + 1) / 2 ^ cfg.m := by
          rw [pow_succ]; ring
        rw [this, Nat.sub_add_cancel hm]

theorem wbad_bound {sN : State E × E} (hinv : Inv cfg x0 f ρ sN) (hpos : cfg.pos sN.1.t = 0)
    (hd : sN.1.done = false) :
    ∫ tail, wbadE cfg x0 g f εi sN tail
        ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) ≤
      ((1 + 3 * (4 * ((κ - 1) / cfg.b))) / 2) ^ cfg.m * (‖gradient f sN.1.x‖ + 2 * L * cfg.B) := by
  have hEb : 1 < cfg.Eb := Eb_gt cfg (by have := H.hc.hK; omega)
  have hKE : cfg.K < cfg.Eb := K_lt_Eb cfg
  have hm := H.hm
  set ν := (Measure.pi fun _ : Fin cfg.b => p) with hν
  set q := 4 * ((κ - 1) / cfg.b) with hq
  have hq0 : 0 ≤ q := by
    have : 0 ≤ (κ - 1) / cfg.b := div_nonneg (by linarith [H.hκ]) (Nat.cast_nonneg _)
    positivity
  set G := ‖gradient f sN.1.x‖ + 2 * L * cfg.B with hG
  have hG0 : 0 ≤ G := by have := H.h.hL; have := H.hc.hB; positivity
  let Y : State E × E → ℝ := fun sN' =>
    if cfg.pos sN'.1.t ≤ cfg.K then (if sN'.1.done = false then 1 else 0)
    else if sN'.1.done = false ∧ sN'.1.trig = false ∧ 3 * εi < ‖gradient f sN'.1.ybar‖ then
      (4 : ℝ) ^ (min sN'.1.vCount cfg.m) else 0
  have hY : Measurable Y := by
    have hT : Measurable (fun sN' : State E × E => sN'.1.t) := measurable_t.comp measurable_fst
    have hD : Measurable (fun sN' : State E × E => sN'.1.done) := measurable_done.comp measurable_fst
    have hTr : Measurable (fun sN' : State E × E => sN'.1.trig) := measurable_trig.comp measurable_fst
    have hVC : Measurable (fun sN' : State E × E => sN'.1.vCount) := measurable_vCount.comp measurable_fst
    have hGm : Measurable (fun sN' : State E × E => ‖gradient f sN'.1.ybar‖) :=
      ((gradient_measurable f H.h).comp (measurable_ybar.comp measurable_fst)).norm
    refine Measurable.ite (hT (MeasurableSet.of_discrete (s := {n | cfg.pos n ≤ cfg.K}))) ?_ ?_
    · exact Measurable.ite (hD (MeasurableSet.of_discrete (s := {false}))) measurable_const measurable_const
    · refine Measurable.ite ?_ ?_ measurable_const
      · exact MeasurableSet.inter (hD (MeasurableSet.of_discrete (s := {false})))
          (MeasurableSet.inter (hTr (MeasurableSet.of_discrete (s := {false})))
            (measurableSet_lt measurable_const hGm))
      · exact (measurable_from_nat (f := fun n : ℕ => (4 : ℝ) ^ (min n cfg.m))).comp hVC
  have hYbd : ∀ sN', |Y sN'| ≤ (4 : ℝ) ^ cfg.Eb * W x0 sN' := by
    intro sN'
    have hW := W_pos x0 sN'
    have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ cfg.Eb := one_le_pow₀ (by norm_num)
    simp only [Y]
    split_ifs
    · rw [abs_one]; nlinarith
    · rw [abs_zero]; positivity
    · rw [abs_of_nonneg (by positivity)]
      have : (4 : ℝ) ^ (min sN'.1.vCount cfg.m) ≤ (4 : ℝ) ^ cfg.Eb :=
        pow_le_pow_right₀ (by norm_num) (by unfold Config.Eb; omega)
      nlinarith
    · rw [abs_zero]; positivity
  have hYpre : ∀ sN' : State E × E, cfg.pos sN'.1.t ≤ cfg.K → sN'.1.done = false → Y sN' = 1 := by
    intro sN' h1 h2; simp only [Y, ite_eq_left h1, ite_eq_left h2]
  have hYfirst : ∀ sN' : State E × E, cfg.pos sN'.1.t = cfg.K + 1 → sN'.1.done = false →
      Inv cfg x0 f ρ sN' → Y sN' ≤ 1 := by
    intro sN' h1 h2 hinv'
    simp only [Y, ite_eq_right (by omega : ¬ cfg.pos sN'.1.t ≤ cfg.K)]
    split_ifs with h3
    · have hvc := hinv'.hvc2 h2 (by omega)
      have hv0 : sN'.1.vCount = 0 := by omega
      rw [hv0, Nat.zero_min, pow_zero]
    · norm_num
  have hYstep : ∀ sN' : State E × E, sN'.1.done = false → cfg.K < cfg.pos sN'.1.t →
      cfg.pos sN'.1.t + 1 < cfg.Eb → Inv cfg x0 f ρ sN' →
      ∫ ω, Y (astep cfg x0 g f sN' ω) ∂ν ≤ (1 + 3 * q) * Y sN' := by
    intro sN' hd' hk hlt hinv'
    obtain ⟨s', N'⟩ := sN'
    simp only at hd' hk hlt
    have hval : ∀ ω, astep cfg x0 g f (s', N') ω =
        ({ s' with t := s'.t + 1, vCount := if s'.trig = true then s'.vCount
          else s'.vCount + (if ‖bmean cfg g s'.ybar ω‖ ≤ cfg.thr then 1 else 0) }, N') := by
      intro ω
      unfold astep
      rw [blockStep_val cfg x0 g hd' hk hlt, nextN_of_not cfg g f ω (by omega)]
    simp_rw [hval]
    have hp1 : cfg.pos (s'.t + 1) = cfg.pos s'.t + 1 := pos_succ_of_lt cfg hEb hlt
    simp only [Y, hp1, ite_eq_right (by omega : ¬ cfg.pos s'.t + 1 ≤ cfg.K), ite_eq_right (by omega : ¬ cfg.pos s'.t ≤ cfg.K)]
    by_cases hcond : s'.done = false ∧ s'.trig = false ∧ 3 * εi < ‖gradient f s'.ybar‖
    · obtain ⟨_, htr, hbad⟩ := hcond
      simp only [htr, Bool.false_eq_true, ↓reduceIte, hd', hbad, and_self]
      have hvc : s'.vCount + cfg.K + 1 ≤ cfg.pos s'.t := hinv'.hvc2 hd' hk
      have hvcm : s'.vCount + 1 ≤ cfg.m := by
        have := pos_lt_Eb' H s'.t; unfold Config.Eb at *; omega
      have hexp : ∀ ω, (4 : ℝ) ^ (min (s'.vCount + (if ‖bmean cfg g s'.ybar ω‖ ≤ cfg.thr then 1 else 0)) cfg.m) =
          (4 : ℝ) ^ (min s'.vCount cfg.m) * (if ‖bmean cfg g s'.ybar ω‖ ≤ cfg.thr then (4 : ℝ) else 1) := by
        intro ω
        by_cases h1 : ‖bmean cfg g s'.ybar ω‖ ≤ cfg.thr
        · rw [ite_eq_left h1, ite_eq_left h1, min_eq_left (by omega), min_eq_left (by omega), pow_succ]
        · rw [ite_eq_right h1, ite_eq_right h1, add_zero, mul_one]
      simp_rw [hexp]
      exact pow_block ((4 : ℝ) ^ (min s'.vCount cfg.m)) (by positivity) _
        (Measurable.ite (measurableSet_le (bmean_measurable cfg H.ho.meas s'.ybar).norm measurable_const)
          measurable_const measurable_const) (block_pass_le H s'.ybar hbad)
    · have hc0 : ¬ (s'.done = false ∧ s'.trig = false ∧ 3 * εi < ‖gradient f s'.ybar‖) := hcond
      simp only [ite_eq_right hc0]
      simp only [integral_const, probReal_univ, one_smul, mul_zero, le_refl]
  have hvd := val_drift H Y hY hYbd hYpre hYfirst hYstep hinv hpos hd
  have hw : ∀ tail, wbadE cfg x0 g f εi sN tail =
      (fun (sL : State E × E) (ω : Fin cfg.b → Ω) =>
        if acceptLast cfg g sL ω ∧ 3 * εi < ‖gradient f sL.1.ybar‖ then ‖gradient f sL.1.ybar‖ else 0)
        (run (astep cfg x0 g f) sN tail (cfg.Eb - 1)) (tail (cfg.Eb - 1)) := by
    intro tail
    obtain ⟨a1, a2, _, _, _, _⟩ := run_val_fields cfg x0 g f H hinv hpos hd tail (cfg.Eb - 1) (by omega) le_rfl
    obtain ⟨hiff, _⟩ := done_run_Eb cfg x0 g f H hinv hpos hd tail
    unfold wbadE
    simp only [a2, hd, true_and]
    congr 1
    apply propext
    exact and_congr_left (fun _ => hiff)
  simp_rw [hw]
  set Fn : State E × E → (Fin cfg.b → Ω) → ℝ := fun sL ω =>
    if acceptLast cfg g sL ω ∧ 3 * εi < ‖gradient f sL.1.ybar‖ then ‖gradient f sL.1.ybar‖ else 0 with hFn
  have hFm : Measurable (Function.uncurry Fn) := by
    unfold Function.uncurry
    simp only [hFn]
    have hTr : Measurable (fun z : (State E × E) × (Fin cfg.b → Ω) => z.1.1.trig) :=
      measurable_trig.comp (measurable_fst.comp measurable_fst)
    have hGm : Measurable (fun z : (State E × E) × (Fin cfg.b → Ω) => ‖gradient f z.1.1.ybar‖) :=
      ((gradient_measurable f H.h).comp (measurable_ybar.comp (measurable_fst.comp measurable_fst))).norm
    have hVC : Measurable (fun z : (State E × E) × (Fin cfg.b → Ω) => z.1.1.vCount) :=
      measurable_vCount.comp (measurable_fst.comp measurable_fst)
    have hB : Measurable (fun z : (State E × E) × (Fin cfg.b → Ω) => ‖bmean cfg g z.1.1.ybar z.2‖) :=
      (bmean_measurable_joint cfg H.ho.meas (α := State E × E) (q := fun sN' => sN'.1.ybar)
        (measurable_ybar.comp measurable_fst)).norm
    have hcount : Measurable (fun z : (State E × E) × (Fin cfg.b → Ω) =>
        2 * (z.1.1.vCount + (if ‖bmean cfg g z.1.1.ybar z.2‖ ≤ cfg.thr then 1 else 0))) :=
      (hVC.add (Measurable.ite (measurableSet_le hB measurable_const) measurable_const measurable_const)).const_mul 2
    have hacc : MeasurableSet {z : (State E × E) × (Fin cfg.b → Ω) | acceptLast cfg g z.1 z.2} := by
      unfold acceptLast
      exact MeasurableSet.inter (hTr (MeasurableSet.of_discrete (s := {false})))
        (hcount (MeasurableSet.of_discrete (s := {n | cfg.m < n})))
    have hset : MeasurableSet {z : (State E × E) × (Fin cfg.b → Ω) | acceptLast cfg g z.1 z.2 ∧
        3 * εi < ‖gradient f z.1.1.ybar‖} :=
      MeasurableSet.inter hacc (measurableSet_lt measurable_const hGm)
    exact Measurable.ite hset hGm
      (measurable_const : Measurable fun _ : (State E × E) × (Fin cfg.b → Ω) => (0 : ℝ))
  have hGb : ∀ tail, 3 * εi < ‖gradient f (run (astep cfg x0 g f) sN tail (cfg.Eb - 1)).1.ybar‖ →
      (run (astep cfg x0 g f) sN tail (cfg.Eb - 1)).1.trig = false →
      ‖gradient f (run (astep cfg x0 g f) sN tail (cfg.Eb - 1)).1.ybar‖ ≤ G := by
    intro tail _ htr
    obtain ⟨_, _, a3, a4, a5, _⟩ := run_val_fields cfg x0 g f H hinv hpos hd tail (cfg.Eb - 1) (by omega) le_rfl
    set sL := run (astep cfg x0 g f) sN tail (cfg.Eb - 1) with hsL
    have hp : cfg.pos sL.1.t = cfg.Eb - 1 := by rw [a5]; exact pos_add_of_zero cfg hpos (by omega)
    have hinvL : Inv cfg x0 f ρ sL := run_inv H.hc H.h hinv tail (cfg.Eb - 1)
    have hval := hinvL.hval a4 (by rw [hp]; have := H.hm; unfold Config.Eb; omega) htr
    rw [a3] at hval
    have hxS : sN.1.xStart = sN.1.x :=
      ((hinv.hagd hd (by rw [hpos]; exact Nat.zero_le _) (hinv.hfresh hd hpos)).hstart hpos).2.1.symm
    rw [hxS] at hval
    have h1 := H.h.lip sL.1.ybar sN.1.x
    have h2 := norm_sub_norm_le (gradient f sL.1.ybar) (gradient f sN.1.x)
    have hL := H.h.hL
    nlinarith
  have hFint : Integrable (fun tail => Fn (run (astep cfg x0 g f) sN tail (cfg.Eb - 1)) (tail (cfg.Eb - 1)))
      (Measure.infinitePi fun _ : ℕ => ν) := by
    refine (integrable_const G).mono' ?_ (Filter.Eventually.of_forall fun tail => ?_)
    · exact (hFm.comp ((run_measurable _ sN (measurable_astep' H) (cfg.Eb - 1)).prodMk
        (measurable_pi_apply _))).aestronglyMeasurable
    · simp only [hFn]
      split_ifs with h1
      · rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact hGb tail h1.2 h1.1.1
      · simp [hG0]
  rw [step_integral (astep cfg x0 g f) sN ν (measurable_astep' H) (cfg.Eb - 1) Fn hFm hFint]
  have hlast : ∀ tail, ∫ ω, Fn (run (astep cfg x0 g f) sN tail (cfg.Eb - 1)) ω ∂ν ≤
      (1 + 3 * q) / 2 ^ cfg.m * G * Y (run (astep cfg x0 g f) sN tail (cfg.Eb - 1)) := by
    intro tail
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := run_val_fields cfg x0 g f H hinv hpos hd tail (cfg.Eb - 1) (by omega) le_rfl
    set sL := run (astep cfg x0 g f) sN tail (cfg.Eb - 1) with hsL
    have hp : cfg.pos sL.1.t = cfg.Eb - 1 := by rw [a5]; exact pos_add_of_zero cfg hpos (by omega)
    by_cases hc : sL.1.trig = false ∧ 3 * εi < ‖gradient f sL.1.ybar‖
    · obtain ⟨htr, hbad⟩ := hc
      have hvc := a6 (by have := H.hm; unfold Config.Eb; omega) htr
      have hvcm : sL.1.vCount + 1 ≤ cfg.m := by unfold Config.Eb at *; omega
      have hGl := hGb tail hbad htr
      have hY : Y sL = (4 : ℝ) ^ (min sL.1.vCount cfg.m) := by
        simp only [Y]
        rw [ite_eq_right (by rw [hp]; have := H.hm; unfold Config.Eb; omega : ¬ cfg.pos sL.1.t ≤ cfg.K),
          ite_eq_left (show sL.1.done = false ∧ sL.1.trig = false ∧ 3 * εi < ‖gradient f sL.1.ybar‖ from
            ⟨a4, htr, hbad⟩)]
      rw [hY, min_eq_left (by omega)]
      have hpt : ∀ ω, Fn sL ω ≤ (G / 2 ^ cfg.m) *
          ((4 : ℝ) ^ sL.1.vCount * (if ‖bmean cfg g sL.1.ybar ω‖ ≤ cfg.thr then (4 : ℝ) else 1)) := by
        intro ω
        have h2m : (0 : ℝ) < 2 ^ cfg.m := by positivity
        simp only [hFn]
        split_ifs with h1 hpass hpass
        · obtain ⟨⟨_, hacc⟩, _⟩ := h1
          rw [ite_eq_left hpass] at hacc
          have h2 : cfg.m ≤ 2 * (sL.1.vCount + 1) := by omega
          have key : (2 : ℝ) ^ cfg.m ≤ (4 : ℝ) ^ sL.1.vCount * 4 := by
            calc (2 : ℝ) ^ cfg.m ≤ (2 : ℝ) ^ (2 * (sL.1.vCount + 1)) := pow_le_pow_right₀ (by norm_num) h2
              _ = (4 : ℝ) ^ sL.1.vCount * 4 := by rw [pow_mul, pow_succ]; norm_num
          calc ‖gradient f sL.1.ybar‖ ≤ G := hGl
            _ = G / 2 ^ cfg.m * 2 ^ cfg.m := by field_simp
            _ ≤ G / 2 ^ cfg.m * ((4 : ℝ) ^ sL.1.vCount * 4) :=
                mul_le_mul_of_nonneg_left key (by positivity)
        · obtain ⟨⟨_, hacc⟩, _⟩ := h1
          rw [ite_eq_right hpass] at hacc
          have h2 : cfg.m ≤ 2 * sL.1.vCount := by omega
          have key : (2 : ℝ) ^ cfg.m ≤ (4 : ℝ) ^ sL.1.vCount * 1 := by
            calc (2 : ℝ) ^ cfg.m ≤ (2 : ℝ) ^ (2 * sL.1.vCount) := pow_le_pow_right₀ (by norm_num) h2
              _ = (4 : ℝ) ^ sL.1.vCount * 1 := by rw [pow_mul]; norm_num
          calc ‖gradient f sL.1.ybar‖ ≤ G := hGl
            _ = G / 2 ^ cfg.m * 2 ^ cfg.m := by field_simp
            _ ≤ G / 2 ^ cfg.m * ((4 : ℝ) ^ sL.1.vCount * 1) :=
                mul_le_mul_of_nonneg_left key (by positivity)
        · positivity
        · positivity
      have hint1 : Integrable (fun ω => Fn sL ω) ν :=
        (integrable_const G).mono' (hFm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
          (Filter.Eventually.of_forall fun ω => by
            simp only [hFn]; split_ifs
            · rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact hGl
            · simp [hG0])
      have hmP : Measurable (fun ω => if ‖bmean cfg g sL.1.ybar ω‖ ≤ cfg.thr then (1 : ℝ) else 0) :=
        Measurable.ite (measurableSet_le (bmean_measurable cfg H.ho.meas sL.1.ybar).norm measurable_const)
          measurable_const measurable_const
      have hint2 : Integrable (fun ω => (G / 2 ^ cfg.m) *
          ((4 : ℝ) ^ sL.1.vCount * (if ‖bmean cfg g sL.1.ybar ω‖ ≤ cfg.thr then (4 : ℝ) else 1))) ν := by
        refine (integrable_const ((G / 2 ^ cfg.m) * ((4 : ℝ) ^ sL.1.vCount * 4))).mono' ?_
          (Filter.Eventually.of_forall fun ω => ?_)
        · refine (Measurable.const_mul (Measurable.const_mul ?_ _) _).aestronglyMeasurable
          exact Measurable.ite (measurableSet_le (bmean_measurable cfg H.ho.meas sL.1.ybar).norm
            measurable_const) measurable_const measurable_const
        · rw [Real.norm_eq_abs, abs_of_nonneg (by split_ifs <;> positivity)]
          split_ifs <;> nlinarith [show (0:ℝ) ≤ (G / 2 ^ cfg.m) * (4 : ℝ) ^ sL.1.vCount by positivity]
      have hpb := pow_block ((4 : ℝ) ^ sL.1.vCount) (by positivity) _ hmP (block_pass_le H sL.1.ybar hbad)
      calc ∫ ω, Fn sL ω ∂ν ≤ ∫ ω, (G / 2 ^ cfg.m) *
            ((4 : ℝ) ^ sL.1.vCount * (if ‖bmean cfg g sL.1.ybar ω‖ ≤ cfg.thr then (4 : ℝ) else 1)) ∂ν :=
            integral_mono hint1 hint2 hpt
        _ = (G / 2 ^ cfg.m) * ∫ ω, (4 : ℝ) ^ sL.1.vCount * (if ‖bmean cfg g sL.1.ybar ω‖ ≤ cfg.thr then (4 : ℝ) else 1) ∂ν :=
            integral_const_mul _ _
        _ ≤ (G / 2 ^ cfg.m) * ((1 + 3 * q) * (4 : ℝ) ^ sL.1.vCount) := mul_le_mul_of_nonneg_left hpb (by positivity)
        _ = (1 + 3 * q) / 2 ^ cfg.m * G * (4 : ℝ) ^ sL.1.vCount := by ring
    · have hY0 : Y sL = 0 := by
        simp only [Y]
        rw [ite_eq_right (by rw [hp]; have := H.hm; unfold Config.Eb; omega : ¬ cfg.pos sL.1.t ≤ cfg.K)]
        rw [ite_eq_right (fun h' => hc ⟨h'.2.1, h'.2.2⟩)]
      have hF0 : ∀ ω, Fn sL ω = 0 := by
        intro ω; simp only [hFn]; rw [ite_eq_right (fun h' => hc ⟨h'.1.1, h'.2⟩)]
      simp_rw [hF0]
      rw [hY0]; simp
  have hYint := integrable_of_le_W H Y hY _ hYbd sN (cfg.Eb - 1)
  have hnn : ∀ tail, 0 ≤ ∫ ω, Fn (run (astep cfg x0 g f) sN tail (cfg.Eb - 1)) ω ∂ν := by
    intro tail
    refine integral_nonneg (fun ω => ?_)
    simp only [hFn]; split_ifs <;> positivity
  calc ∫ tail, (∫ ω, Fn (run (astep cfg x0 g f) sN tail (cfg.Eb - 1)) ω ∂ν) ∂(Measure.infinitePi fun _ : ℕ => ν)
      ≤ ∫ tail, (1 + 3 * q) / 2 ^ cfg.m * G * Y (run (astep cfg x0 g f) sN tail (cfg.Eb - 1))
          ∂(Measure.infinitePi fun _ : ℕ => ν) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) (hYint.const_mul _)
          (Filter.Eventually.of_forall hlast)
    _ = (1 + 3 * q) / 2 ^ cfg.m * G * ∫ tail, Y (run (astep cfg x0 g f) sN tail (cfg.Eb - 1))
          ∂(Measure.infinitePi fun _ : ℕ => ν) := integral_const_mul _ _
    _ ≤ (1 + 3 * q) / 2 ^ cfg.m * G * (1 + 3 * q) ^ (cfg.m - 1) :=
        mul_le_mul_of_nonneg_left hvd (by positivity)
    _ = ((1 + 3 * q) / 2) ^ cfg.m * G := by
        rw [div_pow]
        have : (1 + 3 * q) / 2 ^ cfg.m * G * (1 + 3 * q) ^ (cfg.m - 1) =
            (1 + 3 * q) ^ (cfg.m - 1 + 1) / 2 ^ cfg.m * G := by
          rw [pow_succ]; ring
        rw [this, Nat.sub_add_cancel hm]

end chernoff

end LongTails.Proofs.StrongGrowthAgdValidation
