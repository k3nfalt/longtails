import LongTails.Proofs.GatedEscapeTrajectory
import LongTails.Proofs.GatedEscapeCoupling

namespace LongTails.Proofs.GatedEscapeTrajProb

open MeasureTheory ProbabilityTheory LongTails.Algorithms.GatedPerturbedEscape
  LongTails.Proofs.GatedEscapeProcess LongTails.Proofs.GatedEscapeMoments
  LongTails.Proofs.GatedEscapeEnergy LongTails.Proofs.GatedEscapeDeviation
  LongTails.Proofs.GatedEscapeCoupling LongTails.Proofs.GatedEscapePhases
  LongTails.Proofs.GatedEscapeSlice LongTails.Proofs.GatedEscapeTrajectory
  LongTails.Proofs.GatedEscapeDirection LongTails.Proofs.StrongGrowthAgdBlocks
  LongTails.Proofs.ComparisonTrustTaylor
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]
variable {ι : Type} [Fintype ι]
variable (cfg : Config) (g : E → Ω → E) (f : E → ℝ)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma tstep_run (x g0 v0 : E) (B : ℕ → (Fin cfg.b → Ω)) : ∀ t,
    (run (tstep cfg g (gradient f) x g0) (v0, 0, 0) B t).1 = vrun cfg g x g0 v0 B t ∧
    (run (tstep cfg g (gradient f) x g0) (v0, 0, 0) B t).2.1 = t ∧
    (run (tstep cfg g (gradient f) x g0) (v0, 0, 0) B t).2.2 =
      ∑ s ∈ Finset.range t, cfg.η * ‖bmean cfg g (x + vrun cfg g x g0 v0 B s) (B s) -
        gradient f (x + vrun cfg g x g0 v0 B s)‖ := by
  intro t
  induction t with
  | zero => exact ⟨rfl, rfl, by simp [run_zero]⟩
  | succ t ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [run_succ]
    refine ⟨?_, ?_, ?_⟩
    · show clip cfg.r _ = vstep cfg g x g0 _ _
      rw [h1]; rfl
    · show _ + 1 = t + 1
      rw [h2]
    · show _ + _ = _
      rw [h3, h1, Finset.sum_range_succ]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma vrun_norm_le (x g0 v0 : E) (B : ℕ → (Fin cfg.b → Ω)) (hr : 0 ≤ cfg.r) (hv0 : ‖v0‖ ≤ cfg.r) :
    ∀ t, ‖vrun cfg g x g0 v0 B t‖ ≤ cfg.r := by
  intro t
  cases t with
  | zero => exact hv0
  | succ t => exact clip_norm_le _ _ hr

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma dstep_time (x g0 : E) (R δn : ℝ) (s0 : DState E) (hs0 : s0.2.2.1 = 0)
    (B : ℕ → (Fin cfg.b → Ω)) : ∀ t, (run (dstep cfg g f x g0 R δn) s0 B t).2.2.1 ≤ t := by
  intro t
  induction t with
  | zero => simp [run_zero, hs0]
  | succ t ih =>
    rw [run_succ]
    by_cases hfz : (run (dstep cfg g f x g0 R δn) s0 B t).2.2.2 = true
    · simp only [dstep, hfz, ↓reduceIte]; omega
    · have hf : (run (dstep cfg g f x g0 R δn) s0 B t).2.2.2 = false := by simpa using hfz
      simp only [dstep, hf, Bool.false_eq_true, ↓reduceIte]; omega

def TG (H : E →L[ℝ] E) (θ : ℝ) (v : E) : Prop := cfg.r / 2 ≤ ‖v‖ ∧ ⟪v, H v⟫ ≤ -3 * θ * ‖v‖ ^ 2

noncomputable instance instTGDecidable (H : E →L[ℝ] E) (θ : ℝ) (v : E) : Decidable (TG cfg H θ v) :=
  Classical.dec _

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
theorem traj_det (x g0 v0 : E) (b : OrthonormalBasis ι ℝ E)
    (eig : ι → ℝ) (hc : ∀ i v, ⟪b i, fderiv ℝ (gradient f) x v⟫ = eig i * ⟪b i, v⟫)
    {θ μ R δn U : ℝ} {T T' : ℕ}
    (hη : 0 < cfg.η) (hr : 0 < cfg.r) (hθ : 0 < θ) (heig : ∀ i, cfg.η * eig i ≤ 1)
    (hμθ : 8 * θ ≤ μ) (haT : (1 + cfg.η * μ) ^ T ≤ 5 / 4) (hT'T : T' ≤ T)
    (hU : ∀ v : E, ‖v‖ ≤ cfg.r → ‖gradient f (x + v) - fderiv ℝ (gradient f) x v - g0‖ ≤ U)
    (hTU : T * (cfg.η * U) ≤ cfg.r / 64) (hδ : 0 ≤ δn) (hrR : cfg.r + δn ≤ R)
    (hexit : ∃ t ≤ T', R < ‖orbit (nmap cfg f x g0) t v0‖) (hv0 : ‖v0‖ ≤ cfg.r / 32)
    (B : ℕ → (Fin cfg.b → Ω))
    (hdev : ¬ ((run (dstep cfg g f x g0 R δn) (v0, v0, 0, false) B T').2.2.2 = true ∧
        δn < ‖(run (dstep cfg g f x g0 R δn) (v0, v0, 0, false) B T').1 -
          (run (dstep cfg g f x g0 R δn) (v0, v0, 0, false) B T').2.1‖))
    (hacc : (run (tstep cfg g (gradient f) x g0) (v0, 0, 0) B T).2.2 < cfg.r / 40)
    (hpsi : Psi b eig cfg.η T (run (tstep cfg g (gradient f) x g0) (v0, 0, 0) B T) ≤
      4 * θ * cfg.r ^ 2) :
    TG cfg (fderiv ℝ (gradient f) x) θ (vrun cfg g x g0 v0 B T) := by
  set H := fderiv ℝ (gradient f) x
  have hv0r : ‖v0‖ ≤ cfg.r := hv0.trans (by linarith)
  have h0 : ¬ bad cfg R δn v0 v0 := by
    unfold bad; push Not
    exact ⟨hv0r, hv0r.trans (by linarith), by simp [hδ]⟩
  obtain ⟨τ, hτ, hcl⟩ := (exit_or_dev cfg g f x g0 v0 R δn B h0 hrR T' hexit).resolve_left hdev
  set v := vrun cfg g x g0 v0 B
  set fo : ℕ → E := fun t => gradient f (x + v t) - H (v t) - g0
  set e : ℕ → E := fun t => bmean cfg g (x + v t) (B t) - gradient f (x + v t)
  have hv : ∀ t, v (t + 1) = clip cfg.r (v t - cfg.η • H (v t) - cfg.η • fo t - cfg.η • e t) :=
    fun t => vrun_succ_split cfg g f x g0 v0 B H t
  have hvr := vrun_norm_le cfg g x g0 v0 B hr.le hv0r
  have hfoS : ∑ t ∈ Finset.range T, cfg.η * ‖fo t‖ ≤ cfg.r / 64 := by
    have : ∑ t ∈ Finset.range T, cfg.η * ‖fo t‖ ≤ ∑ _t ∈ Finset.range T, cfg.η * U :=
      Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hU _ (hvr t)) hη.le
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    linarith
  obtain ⟨hr1, hr2, hr3⟩ := tstep_run cfg g f x g0 v0 B T
  have heS : ∑ t ∈ Finset.range T, cfg.η * ‖e t‖ ≤ cfg.r / 40 := by
    rw [hr3] at hacc; exact hacc.le
  have hclip : cfg.r < ‖v τ - cfg.η • H (v τ) - cfg.η • fo τ - cfg.η • e τ‖ := by
    rw [← preclip_split cfg g f x g0 (v τ) (B τ) H]; exact hcl
  have hΨ : ∑ j ∈ posSet eig, eig j * ⟪b j, v T⟫ ^ 2 ≤ 4 * θ * cfg.r ^ 2 := by
    have : Psi b eig cfg.η T (run (tstep cfg g (gradient f) x g0) (v0, 0, 0) B T) =
        ∑ j ∈ posSet eig, eig j * ⟪b j, v T⟫ ^ 2 := by
      unfold Psi; rw [hr1, hr2]; simp; rfl
    rw [← this]; exact hpsi
  exact traj_good H b eig hc hη hr hθ heig hμθ haT v fo e hv hfoS heS (by exact hv0) τ
    (lt_of_lt_of_le hτ hT'T) hclip hΨ

lemma TG_measurable (H : E →L[ℝ] E) (θ : ℝ) : MeasurableSet {v : E | TG cfg H θ v} := by
  unfold TG
  rw [Set.ofPred_and]
  exact (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le (measurable_id.inner H.continuous.measurable)
      ((measurable_norm.pow_const 2).const_mul _))

theorem traj_prob (hb : 0 < cfg.b) (h : Noise g (gradient f) p σ) (hσ : 0 ≤ σ) {L ρ : ℝ}
    (hsm : Smooth f L ρ) (x g0 v0 : E) (b : OrthonormalBasis ι ℝ E)
    (eig : ι → ℝ) (hc : ∀ i v, ⟪b i, fderiv ℝ (gradient f) x v⟫ = eig i * ⟪b i, v⟫)
    {θ μ R δn qd U : ℝ} {T T' : ℕ}
    (hη : 0 < cfg.η) (hr : 0 < cfg.r) (hθ : 0 < θ) (heig : ∀ i, cfg.η * eig i ≤ 1)
    (hμθ : 8 * θ ≤ μ) (haT : (1 + cfg.η * μ) ^ T ≤ 5 / 4) (hT'T : T' ≤ T)
    (hU : ∀ v : E, ‖v‖ ≤ cfg.r → ‖gradient f (x + v) - fderiv ℝ (gradient f) x v - g0‖ ≤ U)
    (hTU : T * (cfg.η * U) ≤ cfg.r / 64) (hδ : 0 < δn) (hrR : cfg.r + δn ≤ R) (hq : 1 < qd)
    (hlin : ∀ u w : E, ‖u‖ ≤ R → ‖w‖ ≤ R →
      ‖(u - w) - cfg.η • (gradient f (x + u) - gradient f (x + w))‖ ≤ qd * ‖u - w‖)
    (hexit : ∃ t ≤ T', R < ‖orbit (nmap cfg f x g0) t v0‖) (hv0 : ‖v0‖ ≤ cfg.r / 32) :
    ∫ B, (if TG cfg (fderiv ℝ (gradient f) x) θ (vrun cfg g x g0 v0 B T) then (0 : ℝ) else 1)
        ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) ≤
      cfg.η ^ 2 * σ ^ 2 / cfg.b / (qd ^ 2 - 1) * (qd ^ (2 * T') / δn ^ 2) +
        T * (cfg.η * (σ / Real.sqrt cfg.b)) / (cfg.r / 40) +
        (Psi b eig cfg.η T (v0, 0, 0) + T * (3 * cfg.η * U ^ 2) +
          cfg.η * (σ ^ 2 / cfg.b) * (1 + Real.log T)) / (4 * θ * cfg.r ^ 2) := by
  set P := Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)
  have hgf : Continuous (gradient f) :=
    LipschitzWith.continuous (K := ⟨|L|, abs_nonneg L⟩) (LipschitzWith.of_dist_le_mul fun y z => by
      rw [dist_eq_norm, dist_eq_norm]
      exact (hsm.lip y z).trans (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _)))
  have hv0r : ‖v0‖ ≤ cfg.r := hv0.trans (by linarith)
  set dstp := dstep cfg g f x g0 R δn
  set tstp := tstep cfg g (gradient f) x g0
  have hdm : Measurable (Function.uncurry dstp) := dstep_measurable h.meas hgf x g0 R δn
  have htm : Measurable (Function.uncurry tstp) := tstep_measurable cfg g (gradient f) h.meas hgf x g0
  set Idev : (ℕ → (Fin cfg.b → Ω)) → ℝ := fun B =>
    tY qd (δn ^ 2) (run dstp (v0, v0, 0, false) B T') * (qd ^ (2 * T') / δn ^ 2) with hIdev
  set IL1 : (ℕ → (Fin cfg.b → Ω)) → ℝ := fun B =>
    min (run tstp (v0, 0, 0) B T).2.2 (cfg.r / 40) / (cfg.r / 40) with hIL1
  set Ien : (ℕ → (Fin cfg.b → Ω)) → ℝ := fun B =>
    Psi b eig cfg.η T (run tstp (v0, 0, 0) B T) / (4 * θ * cfg.r ^ 2) with hIen
  have hq0 : 0 < qd := by linarith
  have hfac : 0 < qd ^ (2 * T') / δn ^ 2 := by positivity
  have hIdev_nn : ∀ B, 0 ≤ Idev B := fun B => mul_nonneg (tY_nonneg hq0 (sq_nonneg _) _) hfac.le
  have hacc_nn : ∀ B, 0 ≤ (run tstp (v0, 0, 0) B T).2.2 := by
    intro B; rw [(tstep_run cfg g f x g0 v0 B T).2.2]
    exact Finset.sum_nonneg fun s _ => mul_nonneg hη.le (norm_nonneg _)
  have hIL1_nn : ∀ B, 0 ≤ IL1 B := fun B =>
    div_nonneg (le_min (hacc_nn B) (by positivity)) (by positivity)
  have hIen_nn : ∀ B, 0 ≤ Ien B := fun B =>
    div_nonneg (Psi_nonneg b eig heig T _) (by positivity)
  have hpt : ∀ B, (if TG cfg (fderiv ℝ (gradient f) x) θ (vrun cfg g x g0 v0 B T) then (0 : ℝ) else 1) ≤
      Idev B + IL1 B + Ien B := by
    intro B
    split_ifs with hTG
    · have := hIdev_nn B; have := hIL1_nn B; have := hIen_nn B; linarith
    · by_cases hdv : (run dstp (v0, v0, 0, false) B T').2.2.2 = true ∧
          δn < ‖(run dstp (v0, v0, 0, false) B T').1 - (run dstp (v0, v0, 0, false) B T').2.1‖
      · have ht := dstep_time cfg g f x g0 R δn (v0, v0, 0, false) rfl B T'
        have hge := tY_of_dev hq.le (run dstp (v0, v0, 0, false) B T') T' ht hdv.2 hδ.le
        have h1 : 1 ≤ Idev B := by
          simp only [hIdev]
          rw [div_le_iff₀ (pow_pos hq0 _)] at hge
          rw [mul_div_assoc', le_div_iff₀ (by positivity)]
          linarith
        have := hIL1_nn B; have := hIen_nn B; linarith
      · by_cases hac : cfg.r / 40 ≤ (run tstp (v0, 0, 0) B T).2.2
        · have h1 : IL1 B = 1 := by
            simp only [hIL1]; rw [min_eq_right hac, div_self (by positivity)]
          have := hIdev_nn B; have := hIen_nn B; linarith
        · push Not at hac
          by_cases hps : Psi b eig cfg.η T (run tstp (v0, 0, 0) B T) ≤ 4 * θ * cfg.r ^ 2
          · exact absurd (traj_det cfg g f x g0 v0 b eig hc hη hr hθ heig hμθ haT hT'T hU hTU
              hδ.le hrR hexit hv0 B hdv hac hps) hTG
          · push Not at hps
            have h1 : 1 ≤ Ien B := by
              simp only [hIen]; rw [le_div_iff₀ (by positivity)]; linarith
            have := hIdev_nn B; have := hIL1_nn B; linarith
  have hIdev_m : Measurable Idev :=
    ((tY_measurable qd (δn ^ 2)).comp (run_measurable dstp _ hdm T')).mul_const _
  have hIL1_m : Measurable IL1 :=
    (((measurable_snd.comp measurable_snd).comp (run_measurable tstp _ htm T)).min
      measurable_const).div_const _
  have hIen_m : Measurable Ien :=
    ((Psi_measurable b eig cfg.η T).comp (run_measurable tstp _ htm T)).div_const _
  have hIdev_i : Integrable Idev P := by
    refine Integrable.of_bound (C := δn ^ 2 * (qd ^ (2 * T') / δn ^ 2)) hIdev_m.aestronglyMeasurable
      (Filter.Eventually.of_forall fun B => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hIdev_nn B)]
    exact mul_le_mul_of_nonneg_right (tY_le hq.le (sq_nonneg _) _) hfac.le
  have hIL1_i : Integrable IL1 P := by
    refine Integrable.of_bound (C := 1) hIL1_m.aestronglyMeasurable
      (Filter.Eventually.of_forall fun B => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hIL1_nn B), div_le_one (by positivity)]
    exact min_le_right _ _
  have hIen_i : Integrable Ien P := by
    refine Integrable.of_bound (C := (∑ j ∈ posSet eig, eig j) * cfg.r ^ 2 / (4 * θ * cfg.r ^ 2))
      hIen_m.aestronglyMeasurable (Filter.Eventually.of_forall fun B => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hIen_nn B)]
    refine div_le_div_of_nonneg_right ((Psi_le b eig hη.le heig T _).trans ?_) (by positivity)
    have hsum : 0 ≤ ∑ j ∈ posSet eig, eig j :=
      Finset.sum_nonneg fun j hj => (Finset.mem_filter.mp hj).2.le
    rw [(tstep_run cfg g f x g0 v0 B T).1]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
      (vrun_norm_le cfg g x g0 v0 B hr.le hv0r T) 2) hsum
  have hind_m : Measurable (fun B : ℕ → (Fin cfg.b → Ω) =>
      if TG cfg (fderiv ℝ (gradient f) x) θ (vrun cfg g x g0 v0 B T) then (0 : ℝ) else 1) := by
    refine Measurable.ite ?_ measurable_const measurable_const
    have hv : Measurable (fun B : ℕ → (Fin cfg.b → Ω) => vrun cfg g x g0 v0 B T) := by
      have h2 : (fun B : ℕ → (Fin cfg.b → Ω) => vrun cfg g x g0 v0 B T) =
          fun B => (run tstp (v0, 0, 0) B T).1 := by
        funext B; exact ((tstep_run cfg g f x g0 v0 B T).1).symm
      rw [h2]; exact measurable_fst.comp (run_measurable tstp _ htm T)
    exact hv (TG_measurable cfg _ θ)
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun B => by split_ifs <;> norm_num)
    ((hIdev_i.add hIL1_i).add hIen_i) (Filter.Eventually.of_forall hpt)
  refine hmono.trans ?_
  rw [integral_add' (hIdev_i.add hIL1_i) hIen_i, integral_add' hIdev_i hIL1_i]
  have hd1 : ∫ B, Idev B ∂P ≤ cfg.η ^ 2 * σ ^ 2 / cfg.b / (qd ^ 2 - 1) * (qd ^ (2 * T') / δn ^ 2) := by
    simp only [hIdev]
    rw [integral_mul_const]
    have hdt := dev_terminal (R := R) (δn := δn) hb h hgf x g0 hq hlin (by linarith) (v0, v0, 0, false)
      (fun _ => by unfold bad; push Not; exact ⟨hv0r, hv0r.trans (by linarith), by simp [hδ.le]⟩)
      rfl T'
    have hz : tY qd (δn ^ 2) ((v0, v0, 0, false) : DState E) = 0 := by
      have hδ2 : 0 ≤ δn ^ 2 := sq_nonneg δn
      simp [tY, hδ2]
    rw [hz, zero_add] at hdt
    exact mul_le_mul_of_nonneg_right hdt hfac.le
  have hd2 : ∫ B, IL1 B ∂P ≤ T * (cfg.η * (σ / Real.sqrt cfg.b)) / (cfg.r / 40) := by
    simp only [hIL1]
    rw [integral_div]
    exact div_le_div_of_nonneg_right (acc_total hb h hgf x g0 hσ hη.le (cfg.r / 40) (by positivity) v0 T)
      (by positivity)
  have hd3 : ∫ B, Ien B ∂P ≤ (Psi b eig cfg.η T (v0, 0, 0) + T * (3 * cfg.η * U ^ 2) +
      cfg.η * (σ ^ 2 / cfg.b) * (1 + Real.log T)) / (4 * θ * cfg.r ^ 2) := by
    simp only [hIen]
    rw [integral_div]
    exact div_le_div_of_nonneg_right
      (energy_total hb h hgf x g0 (fderiv ℝ (gradient f) x) b eig hc hη hr.le heig T U hU v0 hv0r)
      (by positivity)
  linarith

end LongTails.Proofs.GatedEscapeTrajProb
