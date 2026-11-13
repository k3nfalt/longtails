import LongTails.Proofs.GatedEscapeEscape

namespace LongTails.Proofs.GatedEscapeAttemptProb

open MeasureTheory ProbabilityTheory LongTails.Algorithms.GatedPerturbedEscape
  LongTails.Proofs.GatedEscapeProcess LongTails.Proofs.GatedEscapeMoments
  LongTails.Proofs.GatedEscapePhases LongTails.Proofs.GatedEscapeAttempt
  LongTails.Proofs.GatedEscapeMajority LongTails.Proofs.GatedEscapeMeasurable
  LongTails.Proofs.GatedEscapeDescent LongTails.Proofs.GatedEscapeEscape
  LongTails.Proofs.GatedEscapeAccept LongTails.Proofs.StrongGrowthAgdBlocks
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p] {σ : ℝ}
variable (cfg : Config) (d : ℕ) (g : E → Ω → E) (f : E → ℝ)

lemma majority_of_not (M : ℕ) (τ : ℝ) {α : Type} [NormedAddCommGroup α] (sq : ℕ → α) (μ : α)
    (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ c < M, ¬ P c → ‖sq c - μ‖ ≤ τ) (hsel : ¬ ‖select M τ sq - μ‖ ≤ 3 * τ) :
    M ≤ 2 * ((Finset.range M).filter P).card := by
  by_contra hlt
  push Not at hlt
  apply hsel
  apply select_close M τ sq μ
  have hsub : (Finset.range M).filter (fun c => ¬ P c) ⊆ (Finset.range M).filter (fun c => ‖sq c - μ‖ ≤ τ) := by
    intro c hc
    rw [Finset.mem_filter] at hc ⊢
    exact ⟨hc.1, hP c (Finset.mem_range.mp hc.1) hc.2⟩
  have hcard := Finset.card_filter_add_card_filter_not (s := Finset.range M) P
  rw [Finset.card_range] at hcard
  have := Finset.card_le_card hsub
  omega

lemma ite_ind_le {A B : Prop} [Decidable A] [Decidable B] (h : ¬ A → B) :
    (if A then (0 : ℝ) else 1) ≤ (if B then 1 else 0) := by
  by_cases hA : A
  · rw [ite_eq_left hA]; split_ifs <;> norm_num
  · rw [ite_eq_right hA, ite_eq_left (h hA)]

lemma ite_ind_le' {A B : Prop} [Decidable A] [Decidable B] (h : A → B) :
    (if A then (1 : ℝ) else 0) ≤ (if B then 1 else 0) := by
  by_cases hA : A
  · rw [ite_eq_left hA, ite_eq_left (h hA)]
  · rw [ite_eq_right hA]; split_ifs <;> norm_num

omit [IsProbabilityMeasure p] in
lemma maj_integrable (h : Noise g (gradient f) p σ) (q : E) (τ : ℝ) {ν : Measure ((Fin cfg.b → Ω) × E)}
    [IsProbabilityMeasure ν] :
    Integrable (fun β : ℕ → (Fin cfg.b → Ω) × E => if cfg.M ≤ 2 * ((Finset.range cfg.M).filter
      (fun c => τ < ‖bmean cfg g q (β c).1 - gradient f q‖)).card then (1 : ℝ) else 0)
      (Measure.infinitePi fun _ : ℕ => ν) := by
  refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun β => by split_ifs <;> simp)
  refine (Measurable.ite ?_ measurable_const measurable_const).aestronglyMeasurable
  have hc : Measurable (fun β : ℕ → (Fin cfg.b → Ω) × E => ((Finset.range cfg.M).filter
      (fun c => τ < ‖bmean cfg g q (β c).1 - gradient f q‖)).card) := by
    simp_rw [Finset.card_filter]
    refine Finset.measurable_sum _ (fun c _ => ?_)
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_lt measurable_const (((bmean_measurable cfg h.meas q).comp
      (measurable_fst.comp (measurable_pi_apply c))).sub measurable_const).norm
  exact measurableSet_le measurable_const (hc.const_mul 2)

variable (hb : 0 < cfg.b) (h : Noise g (gradient f) p σ)

include hb h in
theorem prob_A0 (hM : 0 < cfg.M) (hT : 0 < cfg.T) (hτ0 : 0 < cfg.τ0)
    (hvar : σ ^ 2 / cfg.b / cfg.τ0 ^ 2 ≤ 1 / 16) (s : State E) (hd : s.done = false)
    (hph : s.ph = .grad0) (hj : s.j = 0) :
    ∫ β, (if A0S cfg f s.x (run (astep cfg d g) s β (alen cfg)) then (0 : ℝ) else 1)
        ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p).prod (stdGaussian E)) ≤
      (19 / 32) ^ cfg.M := by
  have hmaj := mom_phase cfg hb h (stdGaussian E) s.x hτ0 hvar
  have hrw : (fun β : ℕ → (Fin cfg.b → Ω) × E =>
      if A0S cfg f s.x (run (astep cfg d g) s β (alen cfg)) then (0 : ℝ) else 1) =
      fun β => if ‖select cfg.M cfg.τ0 (fill cfg g s.store s.x β cfg.M) - gradient f s.x‖ ≤ 3 * cfg.τ0
        then (0 : ℝ) else 1 := by
    funext β
    simp only [A0S, (post_core cfg d g s hd hph hj hM hT β).2.1]
  rw [hrw]
  refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun β => by
    simp only [Pi.zero_apply]; split_ifs <;> norm_num) ?_ (Filter.Eventually.of_forall fun β => ?_)) hmaj
  · exact maj_integrable cfg g f h s.x cfg.τ0
  · exact ite_ind_le (fun h1 => majority_of_not cfg.M cfg.τ0 _ _
      (fun c => cfg.τ0 < ‖bmean cfg g s.x (β c).1 - gradient f s.x‖)
      (fun c hc hnot => by
        unfold fill; rw [ite_eq_left hc]; push Not at hnot; exact hnot) h1)

include hb h in
theorem prob_Aq_ray (hM : 0 < cfg.M) (hr : 0 < cfg.r) (hτq : 0 < cfg.τq)
    (hvar : σ ^ 2 / cfg.b / (cfg.r * cfg.τq) ^ 2 ≤ 1 / 16) (x : E) (s : State E) (hd : s.done = false)
    (hph : s.ph = .ray) (hj : s.j = 0) (hx : s.x = x) (hw1 : ‖s.w‖ ≤ 1) :
    ∫ tail, (if AqS cfg f x (run (astep cfg d g) s tail cfg.M) then (0 : ℝ) else 1)
        ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p).prod (stdGaussian E)) ≤
      (19 / 32) ^ cfg.M := by
  have hmaj := mom_phase cfg hb h (stdGaussian E) (x + cfg.r • s.w) (by positivity) hvar
  have hre := run_ray_end cfg d g s hd hph hj hM
  have hcore : ∀ tail, (run (astep cfg d g) s tail cfg.M).w = s.w ∧
      (run (astep cfg d g) s tail cfg.M).g0 = s.g0 ∧
      (run (astep cfg d g) s tail cfg.M).store = fill cfg g s.store (s.x + cfg.r • s.w) tail cfg.M := by
    intro tail
    rw [hre tail]
    refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> simp only [endAttempt] <;> split_ifs <;> rfl
  refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun β => by
    simp only [Pi.zero_apply]; split_ifs <;> norm_num) (maj_integrable cfg g f h _ _)
    (Filter.Eventually.of_forall fun tail => ?_)) hmaj
  obtain ⟨hw, hg0, hst⟩ := hcore tail
  refine ite_ind_le (fun h1 => ?_)
  · unfold AqS qhS at h1
    rw [hw, hg0, hst] at h1
    refine majority_of_not cfg.M cfg.τq
      (fun c => ⟪s.w, fill cfg g s.store (s.x + cfg.r • s.w) tail cfg.M c - s.g0⟫ / cfg.r)
      (⟪s.w, gradient f (x + cfg.r • s.w) - s.g0⟫ / cfg.r)
      (fun c => cfg.r * cfg.τq < ‖bmean cfg g (x + cfg.r • s.w) (tail c).1 - gradient f (x + cfg.r • s.w)‖)
      (fun c hc hnot => ?_) (by rwa [Real.norm_eq_abs])
    push Not at hnot
    unfold fill
    rw [ite_eq_left hc, hx, Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos hr, div_le_iff₀ hr]
    have e : ⟪s.w, bmean cfg g (x + cfg.r • s.w) (tail c).1 - s.g0⟫ -
        ⟪s.w, gradient f (x + cfg.r • s.w) - s.g0⟫ =
        ⟪s.w, bmean cfg g (x + cfg.r • s.w) (tail c).1 - gradient f (x + cfg.r • s.w)⟫ := by
      rw [← inner_sub_right]; congr 1; abel
    rw [e]
    refine (abs_real_inner_le_norm _ _).trans ?_
    have hn := norm_nonneg (bmean cfg g (x + cfg.r • s.w) (tail c).1 - gradient f (x + cfg.r • s.w))
    calc ‖s.w‖ * ‖bmean cfg g (x + cfg.r • s.w) (tail c).1 - gradient f (x + cfg.r • s.w)‖
        ≤ 1 * (cfg.r * cfg.τq) := mul_le_mul hw1 hnot hn zero_le_one
      _ = cfg.τq * cfg.r := by ring

lemma qhS_measurable : Measurable (qhS (E := E) cfg) := by
  unfold qhS
  exact (measurable_select (β := ℝ) cfg.M cfg.τq).comp (measurable_pi_iff.mpr fun c =>
    ((measurable_w.inner ((measurable_pi_apply c).comp measurable_store |>.sub measurable_g0)).div_const _))

lemma AqS_measurable (hgf : Continuous (gradient f)) (x : E) :
    MeasurableSet {s : State E | AqS cfg f x s} := by
  unfold AqS
  refine measurableSet_le ?_ measurable_const
  refine continuous_abs.measurable.comp ((qhS_measurable cfg).sub ?_)
  exact (measurable_w.inner ((hgf.measurable.comp (measurable_const.add (measurable_w.const_smul _))).sub
    measurable_g0)).div_const _

include hb h in
theorem prob_Aq (hM : 0 < cfg.M) (hT : 0 < cfg.T) (hr : 0 < cfg.r) (hτq : 0 < cfg.τq)
    (hvar : σ ^ 2 / cfg.b / (cfg.r * cfg.τq) ^ 2 ≤ 1 / 16) (hgf : Continuous (gradient f))
    (s : State E) (hd : s.done = false) (hph : s.ph = .grad0) (hj : s.j = 0) :
    ∫ β, (if AqS cfg f s.x (run (astep cfg d g) s β (alen cfg)) then (0 : ℝ) else 1)
        ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p).prod (stdGaussian E)) ≤
      (19 / 32) ^ cfg.M := by
  set ν := (Measure.pi fun _ : Fin cfg.b => p).prod (stdGaussian E)
  have hstep := measurable_astep cfg d g h.meas
  set F : State E → (ℕ → (Fin cfg.b → Ω) × E) → ℝ := fun s' tail =>
    if AqS cfg f s.x (run (astep cfg d g) s' tail cfg.M) then 0 else 1 with hF
  have hFm : Measurable (Function.uncurry F) :=
    Measurable.ite ((run_measurable₂ (astep cfg d g) hstep cfg.M) (AqS_measurable cfg f hgf s.x))
      measurable_const measurable_const
  have hrw : (fun β => if AqS cfg f s.x (run (astep cfg d g) s β (alen cfg)) then (0 : ℝ) else 1) =
      fun β => F (run (astep cfg d g) s β (cfg.M + 1 + cfg.T)) (shift (cfg.M + 1 + cfg.T) β) := by
    funext β; simp only [hF, (post_core cfg d g s hd hph hj hM hT β).1]
  have hint : Integrable (fun β => F (run (astep cfg d g) s β (cfg.M + 1 + cfg.T)) (shift (cfg.M + 1 + cfg.T) β)) (Measure.infinitePi fun _ : ℕ => ν) := by
    refine Integrable.of_bound (C := 1)
      (hFm.comp ((run_measurable _ s hstep (cfg.M + 1 + cfg.T)).prodMk (shift_measurable (cfg.M + 1 + cfg.T)))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun β => by simp only [hF]; split_ifs <;> simp)
  rw [hrw, tail_integral (astep cfg d g) s ν hstep (cfg.M + 1 + cfg.T) F hFm hint]
  have hinner : ∀ β, ∫ tail, F (run (astep cfg d g) s β (cfg.M + 1 + cfg.T)) tail ∂(Measure.infinitePi fun _ : ℕ => ν) ≤
      (19 / 32) ^ cfg.M := by
    intro β
    obtain ⟨_, _, _, hw, _, h3ph, h3j, h3d, h3x, h3w, _⟩ := post_core cfg d g s hd hph hj hM hT β
    refine prob_Aq_ray cfg d g f hb h hM hr hτq hvar s.x _ h3d h3ph h3j h3x ?_
    rw [h3w, hw]; exact unit_le _
  calc ∫ β, ∫ tail, F (run (astep cfg d g) s β (cfg.M + 1 + cfg.T)) tail ∂(Measure.infinitePi fun _ : ℕ => ν)
        ∂(Measure.infinitePi fun _ : ℕ => ν) ≤ ∫ _β, (19 / 32 : ℝ) ^ cfg.M ∂(Measure.infinitePi fun _ : ℕ => ν) :=
        integral_mono (tail_inner_integrable (astep cfg d g) s ν hstep (cfg.M + 1 + cfg.T) F hFm hint)
          (integrable_const _) hinner
    _ = (19 / 32) ^ cfg.M := by simp

include hb h in
theorem prob_harm {L ρ : ℝ} (hsm : LongTails.Proofs.ComparisonTrustTaylor.Smooth f L ρ) (hρ : 0 ≤ ρ)
    (hM : 0 < cfg.M) (hT : 0 < cfg.T) (hr : 0 < cfg.r) (hθ : 0 ≤ cfg.θ) (hρr : ρ * cfg.r ≤ cfg.θ)
    (hτ0 : 0 < cfg.τ0) (h3τ0 : 3 * cfg.τ0 ≤ cfg.r * cfg.θ / 8) (hτq : 0 < cfg.τq)
    (h3τq : 3 * cfg.τq ≤ 3 * cfg.θ / 8)
    (hvar0 : σ ^ 2 / cfg.b / cfg.τ0 ^ 2 ≤ 1 / 16) (hvarq : σ ^ 2 / cfg.b / (cfg.r * cfg.τq) ^ 2 ≤ 1 / 16)
    (hgf : Continuous (gradient f))
    (s : State E) (hd : s.done = false) (hph : s.ph = .grad0) (hj : s.j = 0) :
    ∫ β, (if accS cfg (run (astep cfg d g) s β (alen cfg)) ∧
        f s.x - cfg.r ^ 2 * cfg.θ / 5 < f (s.x + dxS cfg (run (astep cfg d g) s β (alen cfg)))
      then (1 : ℝ) else 0)
        ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p).prod (stdGaussian E)) ≤
      2 * (19 / 32) ^ cfg.M := by
  set ν := (Measure.pi fun _ : Fin cfg.b => p).prod (stdGaussian E)
  have hstep := measurable_astep cfg d g h.meas
  have hrun := run_measurable (astep cfg d g) s hstep (alen cfg)
  have hA0m : MeasurableSet {s' : State E | A0S cfg f s.x s'} :=
    measurableSet_le (measurable_g0.sub measurable_const).norm measurable_const
  have hi1 : Integrable (fun β => (if A0S cfg f s.x (run (astep cfg d g) s β (alen cfg)) then (0 : ℝ) else 1))
      (Measure.infinitePi fun _ : ℕ => ν) :=
    Integrable.of_bound (C := 1) ((Measurable.ite (hrun hA0m) measurable_const measurable_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun β => by split_ifs <;> simp)
  have hi2 : Integrable (fun β => (if AqS cfg f s.x (run (astep cfg d g) s β (alen cfg)) then (0 : ℝ) else 1))
      (Measure.infinitePi fun _ : ℕ => ν) :=
    Integrable.of_bound (C := 1) ((Measurable.ite (hrun (AqS_measurable cfg f hgf s.x)) measurable_const
      measurable_const)).aestronglyMeasurable (Filter.Eventually.of_forall fun β => by split_ifs <;> simp)
  have hpt : ∀ β, (if accS cfg (run (astep cfg d g) s β (alen cfg)) ∧
        f s.x - cfg.r ^ 2 * cfg.θ / 5 < f (s.x + dxS cfg (run (astep cfg d g) s β (alen cfg)))
      then (1 : ℝ) else 0) ≤
      (if A0S cfg f s.x (run (astep cfg d g) s β (alen cfg)) then (0 : ℝ) else 1) +
      (if AqS cfg f s.x (run (astep cfg d g) s β (alen cfg)) then (0 : ℝ) else 1) := by
    intro β
    set post := run (astep cfg d g) s β (alen cfg)
    obtain ⟨_, _, _, hw, _⟩ := post_core cfg d g s hd hph hj hM hT β
    by_cases hc : accS cfg post ∧ f s.x - cfg.r ^ 2 * cfg.θ / 5 < f (s.x + dxS cfg post)
    · rw [ite_eq_left hc]
      by_cases h0 : A0S cfg f s.x post
      · by_cases hq : AqS cfg f s.x post
        · exfalso
          obtain ⟨⟨hv, hqh⟩, hlt⟩ := hc
          have hsafe := accept_safe hsm hρ s.x post.g0 post.v hr hθ hρr h3τ0 h3τq h0
            (by unfold AqS at hq; rw [hw] at hq; exact hq) hv hqh
          unfold dxS at hlt
          rw [hw] at hlt
          linarith
        · rw [ite_eq_left h0, ite_eq_right hq]; norm_num
      · rw [ite_eq_right h0]; split_ifs <;> norm_num
    · rw [ite_eq_right hc]; split_ifs <;> norm_num
  have hm := integral_mono_of_nonneg (Filter.Eventually.of_forall fun β => by split_ifs <;> norm_num)
    (hi1.add hi2) (Filter.Eventually.of_forall hpt)
  rw [integral_add' hi1 hi2] at hm
  have p1 := prob_A0 cfg d g f hb h hM hT hτ0 hvar0 s hd hph hj
  have p2 := prob_Aq cfg d g f hb h hM hT hr hτq hvarq hgf s hd hph hj
  linarith

end LongTails.Proofs.GatedEscapeAttemptProb
