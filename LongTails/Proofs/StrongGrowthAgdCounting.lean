import LongTails.Proofs.StrongGrowthAgdEpochRun

namespace LongTails.Proofs.StrongGrowthAgdCounting

open MeasureTheory LongTails.Algorithms.StrongGrowthRestartedAgd LongTails.Proofs.StrongGrowthAgdProcess
  LongTails.Proofs.StrongGrowthAgdMoments LongTails.Proofs.StrongGrowthAgdMeasurable
  LongTails.Proofs.StrongGrowthAgdWeights LongTails.Proofs.StrongGrowthAgdModel
  LongTails.Proofs.StrongGrowthAgdEpochEnd LongTails.Proofs.StrongGrowthAgdInvariant
  LongTails.Proofs.StrongGrowthAgdEpoch LongTails.Proofs.StrongGrowthAgdBlocks
  LongTails.Proofs.StrongGrowthAgdEpochRun
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]
variable {cfg : Config} {x0 : E} {g : E → Ω → E} {f : E → ℝ} {L ρ κ Δ εi : ℝ}
variable (H : Hyps cfg x0 g f p L ρ κ Δ εi)
include H

omit [IsProbabilityMeasure p] [BorelSpace E] in
lemma movement_invariant {sN : State E × E} (hinv : Inv cfg x0 f ρ sN) (hpos : cfg.pos sN.1.t = 0)
    (hd : sN.1.done = false) (tail : ℕ → (Fin cfg.b → Ω)) :
    ∀ t ≤ cfg.K,
      0 ≤ (run (astep cfg x0 g f) sN tail t).1.S ∧
      cfg.θ / cfg.η / 16 * (run (astep cfg x0 g f) sN tail t).1.S ≤
        ∑ i ∈ Finset.range t, Dblk cfg x0 g f (run (astep cfg x0 g f) sN tail i) (tail i) ∧
      ((run (astep cfg x0 g f) sN tail t).1.trig = true →
        cfg.B ^ 2 < cfg.K * (run (astep cfg x0 g f) sN tail t).1.S) ∧
      (run (astep cfg x0 g f) sN tail t).1.done = false ∧
      (run (astep cfg x0 g f) sN tail t).1.t = sN.1.t + t := by
  have hEb : 1 < cfg.Eb := Eb_gt cfg (by have := H.hc.hK; omega)
  have hKE : cfg.K < cfg.Eb := K_lt_Eb cfg
  have hθη : 0 ≤ cfg.θ / cfg.η / 16 := by have := H.hc.hη; have := H.hc.hθ0; positivity
  intro t
  induction t with
  | zero =>
    intro _
    have hA := hinv.hagd hd (by rw [hpos]; exact Nat.zero_le _) (hinv.hfresh hd hpos)
    have hS0 := (hA.hstart hpos).2.2.2.1
    refine ⟨hA.hS0, ?_, ?_, hd, by simp [run_zero]⟩
    · simp [run_zero, hS0]
    · intro h'
      have h'' : sN.1.trig = true := h'
      rw [hinv.hfresh hd hpos] at h''
      exact Bool.noConfusion h''
  | succ t ih =>
    intro ht
    obtain ⟨hS0, hSD, htrig, hdt, htt⟩ := ih (by omega)
    set sN' := run (astep cfg x0 g f) sN tail t with hsN'
    have hp : cfg.pos sN'.1.t = t := by rw [htt]; exact pos_add_of_zero cfg hpos (by omega)
    have hinv' : Inv cfg x0 f ρ sN' := run_inv H.hc H.h hinv tail t
    have hnl := blockStep_not_last (cfg := cfg) (x0 := x0) (g := g) hdt (by omega) (tail t)
    rw [run_succ, Finset.sum_range_succ]
    by_cases htr : sN'.1.trig = true
    · have hfz : astep cfg x0 g f sN' (tail t) = ({ sN'.1 with t := sN'.1.t + 1 }, sN'.2) := by
        unfold astep
        rw [blockStep_frozen cfg x0 g hdt (by omega) htr, nextN_of_not cfg g f _
          (by show ¬ (sN'.1.done = false ∧ cfg.pos sN'.1.t < cfg.K ∧ sN'.1.trig = false); simp [htr])]
      have hDb : Dblk cfg x0 g f sN' (tail t) = 0 := by
        unfold Dblk; rw [ite_eq_right]; simp [htr]
      rw [hfz, hDb]
      refine ⟨hS0, by simpa using hSD, fun _ => htrig htr, hdt, ?_⟩
      show sN'.1.t + 1 = sN.1.t + (t + 1)
      rw [htt]; ring
    · have htr' : sN'.1.trig = false := by simpa using htr
      have hA := hinv'.hagd hdt (by omega) htr'
      have hag := blockStep_agd cfg x0 g hdt (by omega) htr' (tail t)
      have hDb : Dblk cfg x0 g f sN' (tail t) =
          cfg.θ / cfg.η / 16 * ‖(blockStep cfg x0 g sN'.1 (tail t)).x - sN'.1.x‖ ^ 2 +
            cfg.η / 32 * ‖gMs cfg f sN'.1‖ ^ 2 := by
        unfold Dblk; rw [ite_eq_left ⟨hdt, by omega, htr'⟩]
      rw [hDb]
      have hx' : (blockStep cfg x0 g sN'.1 (tail t)).x =
          ypoint cfg sN'.1 - cfg.η • bmean cfg g (ypoint cfg sN'.1) (tail t) := by rw [hag]
      have hS' : (astep cfg x0 g f sN' (tail t)).1.S =
          sN'.1.S + ‖ypoint cfg sN'.1 - cfg.η • bmean cfg g (ypoint cfg sN'.1) (tail t) - sN'.1.x‖ ^ 2 := by
        rw [astep_fst, hag]
      have htrig' : (astep cfg x0 g f sN' (tail t)).1.trig =
          decide (cfg.B ^ 2 < ((cfg.pos sN'.1.t + 1 : ℕ) : ℝ) *
            (sN'.1.S + ‖ypoint cfg sN'.1 - cfg.η • bmean cfg g (ypoint cfg sN'.1) (tail t) - sN'.1.x‖ ^ 2)) := by
        rw [astep_fst, hag]
      have hgm := sq_nonneg ‖gMs cfg f sN'.1‖
      have hηpos := H.hc.hη
      refine ⟨?_, ?_, ?_, hnl.1, ?_⟩
      · rw [hS']; positivity
      · rw [hS', hx']
        nlinarith [mul_nonneg hηpos.le hgm]
      · intro hfire
        rw [htrig'] at hfire
        have hlt := of_decide_eq_true hfire
        rw [hS', hp] at *
        have hK' : ((t + 1 : ℕ) : ℝ) ≤ cfg.K := by exact_mod_cast ht
        have hSS : 0 ≤ sN'.1.S + ‖ypoint cfg sN'.1 - cfg.η • bmean cfg g (ypoint cfg sN'.1) (tail t) - sN'.1.x‖ ^ 2 := by
          positivity
        calc cfg.B ^ 2 < ((t + 1 : ℕ) : ℝ) * _ := hlt
          _ ≤ cfg.K * _ := mul_le_mul_of_nonneg_right hK' hSS
      · rw [astep_fst, hnl.2.2, htt]; ring

omit [IsProbabilityMeasure p] [BorelSpace E] in
theorem trig_decrease {sN : State E × E} (hinv : Inv cfg x0 f ρ sN) (hpos : cfg.pos sN.1.t = 0)
    (hd : sN.1.done = false) (tail : ℕ → (Fin cfg.b → Ω))
    (htrig : (run (astep cfg x0 g f) sN tail cfg.K).1.trig = true) :
    cfg.θ ^ 2 * cfg.B ^ 2 / (32 * cfg.η) ≤ Dep cfg x0 g f sN tail := by
  obtain ⟨hS0, hSD, hT, _, _⟩ := movement_invariant H hinv hpos hd tail cfg.K le_rfl
  have hKS := hT htrig
  have hKE : cfg.K < cfg.Eb := K_lt_Eb cfg
  have hsub : ∑ i ∈ Finset.range cfg.K, Dblk cfg x0 g f (run (astep cfg x0 g f) sN tail i) (tail i) ≤
      Dep cfg x0 g f sN tail := by
    unfold Dep
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => Dblk_nonneg H.hc _ _)
    intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
  have hθ := H.hc.hθ0
  have hη := H.hc.hη
  have hKθ := H.hK2
  have hKpos : (0 : ℝ) < cfg.K := by exact_mod_cast (show 0 < cfg.K by have := H.hc.hK; omega)
  have hS1 : cfg.θ * cfg.B ^ 2 / 2 ≤ (run (astep cfg x0 g f) sN tail cfg.K).1.S := by
    have h1 : cfg.θ * cfg.B ^ 2 ≤ 2 * (run (astep cfg x0 g f) sN tail cfg.K).1.S := by
      nlinarith [mul_le_mul_of_nonneg_left hKS.le hθ.le, sq_nonneg cfg.B]
    linarith
  have h2 : cfg.θ / cfg.η / 16 * (cfg.θ * cfg.B ^ 2 / 2) ≤
      cfg.θ / cfg.η / 16 * (run (astep cfg x0 g f) sN tail cfg.K).1.S :=
    mul_le_mul_of_nonneg_left hS1 (by positivity)
  have h3 : cfg.θ / cfg.η / 16 * (cfg.θ * cfg.B ^ 2 / 2) = cfg.θ ^ 2 * cfg.B ^ 2 / (32 * cfg.η) := by
    field_simp; ring
  linarith

noncomputable def cert (cfg : Config) (ρ : ℝ) : ℝ := cw cfg * cfg.B / cfg.η + 2 * Dm cfg ρ

omit H [MeasurableSpace E] [BorelSpace E] in
lemma certificate_pathwise (hc : CfgHyp cfg) (h : Hyp f L ρ) {sN : State E × E} (hinv : Inv cfg x0 f ρ sN)
    (hd : sN.1.done = false) (hpos : cfg.pos sN.1.t = cfg.K) (htr : sN.1.trig = false) :
    ‖gradient f sN.1.ybar‖ ≤ cert cfg ρ + ‖sN.2‖ := by
  have hA := hinv.hagd hd (by rw [hpos]) htr
  have hK2 : 2 ≤ cfg.K := by have := hc.hK; omega
  have hws : wsum cfg cfg.K = 1 := sum_pw hK2
  have hZ := hA.hZ (by rw [hpos]; omega)
  have hyb := hA.hyb
  rw [hpos, hws, one_smul, mul_one] at hyb
  rw [hpos] at hZ
  unfold Zvec Avec at hZ
  rw [hpos, hws, one_smul, one_smul, pw_self, mul_zero, zero_smul, add_zero] at hZ
  set xS := sN.1.xStart
  set gM := gradModel (fderiv ℝ (gradient f) xS) xS (gradient f xS) sN.1.ybar with hgM
  have hgMeq : gradient f xS + fderiv ℝ (gradient f) xS (sN.1.ybar - xS) = gM := rfl
  rw [hgMeq, norm_smul, Real.norm_eq_abs, abs_of_pos hc.hη] at hZ
  have hS := hA.hS
  rw [hpos] at hS
  have hsq : Real.sqrt (cfg.K * sN.1.S) ≤ cfg.B := by
    rw [Real.sqrt_le_left hc.hB.le]; exact hS
  have hcw := cw_nonneg hc
  have h1 : ‖gM + sN.2‖ ≤ cw cfg * cfg.B / cfg.η + Dm cfg ρ := by
    have h2 : cfg.η * ‖gM + sN.2‖ ≤ cw cfg * cfg.B + cfg.η * Dm cfg ρ := by
      have := mul_le_mul_of_nonneg_left hsq hcw
      linarith
    have hη := hc.hη
    rw [div_add' _ _ _ hη.ne', le_div_iff₀ hη]
    linarith
  have hδ : ‖gradient f sN.1.ybar - gM‖ ≤ Dm cfg ρ := by
    refine (h.gradModel_err xS sN.1.ybar).trans ?_
    unfold Dm
    have hsq2 : ‖sN.1.ybar - xS‖ ^ 2 ≤ (2 * cfg.B) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hyb 2
    have := mul_le_mul_of_nonneg_left hsq2 h.hρ
    nlinarith [this]
  have h3 : ‖gradient f sN.1.ybar‖ ≤ ‖gM + sN.2‖ + ‖sN.2‖ + ‖gradient f sN.1.ybar - gM‖ := by
    have e : gradient f sN.1.ybar = (gM + sN.2) - sN.2 + (gradient f sN.1.ybar - gM) := by abel
    calc ‖gradient f sN.1.ybar‖ = ‖(gM + sN.2) - sN.2 + (gradient f sN.1.ybar - gM)‖ := by rw [← e]
      _ ≤ ‖(gM + sN.2) - sN.2‖ + ‖gradient f sN.1.ybar - gM‖ := norm_add_le _ _
      _ ≤ ‖gM + sN.2‖ + ‖sN.2‖ + ‖gradient f sN.1.ybar - gM‖ := by
          linarith [norm_sub_le (gM + sN.2) sN.2]
  unfold cert
  linarith

noncomputable def badE (cfg : Config) (x0 : E) (g : E → Ω → E) (f : E → ℝ) (εi : ℝ) (sN : State E × E)
    (tail : ℕ → (Fin cfg.b → Ω)) : ℝ :=
  if sN.1.done = false ∧ (run (astep cfg x0 g f) sN tail cfg.K).1.trig = false ∧
      εi < ‖gradient f (run (astep cfg x0 g f) sN tail cfg.K).1.ybar‖ then 1 else 0

theorem noise_second_moment {sN : State E × E} (hinv : Inv cfg x0 f ρ sN) (hpos : cfg.pos sN.1.t = 0)
    (hd : sN.1.done = false) :
    ∫ tail, ‖(run (astep cfg x0 g f) sN tail cfg.K).2‖ ^ 2
        ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) ≤
      (2 / cfg.K) ^ 2 * ((κ - 1) / cfg.b) *
        ((64 / cfg.η) * ∫ tail, Dep cfg x0 g f sN tail
            ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) +
          2 * cfg.K * Dm cfg ρ ^ 2) := by
  obtain ⟨s, N⟩ := sN
  have hEb : 1 < cfg.Eb := Eb_gt cfg (by have := H.hc.hK; omega)
  have hKE : cfg.K < cfg.Eb := K_lt_Eb cfg
  have hK2 : 2 ≤ cfg.K := by have := H.hc.hK; omega
  have hKpos : (0 : ℝ) < cfg.K := by exact_mod_cast (show 0 < cfg.K by omega)
  set ν := (Measure.pi fun _ : Fin cfg.b => p) with hν
  set δ2 := (κ - 1) / cfg.b with hδ2
  have hδ0 : 0 ≤ δ2 := div_nonneg (by linarith [H.hκ]) (Nat.cast_nonneg _)
  let Inv₁ : ℕ → Set (State E × E) := fun t => {sN' | Inv cfg x0 f ρ sN' ∧
    (t < cfg.Eb → sN'.1.t = s.t + t ∧ sN'.1.done = false)}
  let Y₂ : State E × E → ℝ := fun sN' =>
    if 1 ≤ cfg.pos sN'.1.t ∧ cfg.pos sN'.1.t ≤ cfg.K then ‖sN'.2‖ ^ 2 else 0
  let c₂ : State E × E → ℝ := fun sN' =>
    if sN'.1.done = false ∧ cfg.pos sN'.1.t < cfg.K ∧ sN'.1.trig = false then
      pw cfg.K (cfg.pos sN'.1.t) ^ 2 * δ2 * ‖gradient f (ypoint cfg sN'.1)‖ ^ 2 else 0
  let D₂ : State E × E → (ℕ → (Fin cfg.b → Ω)) → ℝ := fun _ _ => 0
  have hInv₁ : ∀ t, ∀ sN' ∈ Inv₁ t, ∀ ω, astep cfg x0 g f sN' ω ∈ Inv₁ (t + 1) := by
    intro t sN' hsN' ω
    refine ⟨inv_preserved cfg x0 g f ρ H.hc H.h hsN'.1 ω, fun ht => ?_⟩
    obtain ⟨ht', hd''⟩ := hsN'.2 (by omega)
    have hp : cfg.pos sN'.1.t = t := by rw [ht']; exact pos_add_of_zero cfg hpos (by omega)
    obtain ⟨h1, _, h3⟩ := blockStep_not_last (cfg := cfg) (x0 := x0) (g := g) hd'' (by omega) ω
    exact ⟨by rw [astep_fst, h3, ht']; ring, h1⟩
  have hs0 : (s, N) ∈ Inv₁ 0 := ⟨hinv, fun _ => ⟨rfl, hd⟩⟩
  have hstep := measurable_astep' H
  have hY₂ : Measurable Y₂ := by
    refine Measurable.ite ((measurable_t.comp measurable_fst)
      (MeasurableSet.of_discrete (s := {n | 1 ≤ cfg.pos n ∧ cfg.pos n ≤ cfg.K}))) ?_ measurable_const
    exact measurable_snd.norm.pow_const 2
  have hc₂ : Measurable c₂ := by
    have hT : Measurable (fun sN' : State E × E => sN'.1.t) := measurable_t.comp measurable_fst
    have hD : Measurable (fun sN' : State E × E => sN'.1.done) := measurable_done.comp measurable_fst
    have hTr : Measurable (fun sN' : State E × E => sN'.1.trig) := measurable_trig.comp measurable_fst
    refine Measurable.ite ?_ ?_ measurable_const
    · exact MeasurableSet.inter (hD (MeasurableSet.of_discrete (s := {false})))
        (MeasurableSet.inter (hT (MeasurableSet.of_discrete (s := {n | cfg.pos n < cfg.K})))
          (hTr (MeasurableSet.of_discrete (s := {false}))))
    · refine Measurable.mul (Measurable.mul ?_ measurable_const) ?_
      · exact (measurable_from_nat (f := fun n => pw cfg.K (cfg.pos n) ^ 2)).comp hT
      · exact ((gradient_measurable f H.h).comp ((measurable_ypoint cfg).comp measurable_fst)).norm.pow_const 2
  have hD₂ : Measurable (Function.uncurry D₂) := measurable_const
  have hY₂W : ∀ sN', |Y₂ sN'| ≤ 1 * W x0 sN' := by
    intro sN'
    simp only [Y₂]
    split_ifs
    · rw [abs_of_nonneg (sq_nonneg _), one_mul]
      unfold W; nlinarith [sq_nonneg ‖sN'.1.x - x0‖, sq_nonneg ‖sN'.1.xPrev - x0‖, sq_nonneg ‖sN'.1.xStart - x0‖,
        sq_nonneg ‖sN'.1.glast‖, sq_nonneg ‖sN'.1.ybar‖]
    · rw [abs_zero, one_mul]; exact W_nonneg x0 _
  have hc₂W : ∀ sN', |c₂ sN'| ≤ (δ2 * (2 * ‖gradient f x0‖ ^ 2 + 12 * L ^ 2)) * W x0 sN' := by
    intro sN'
    have hW := W_pos x0 sN'
    have hg := gradf_sq_le x0 f H.h (ypoint cfg sN'.1)
    have hy := ypoint_sub_sq_le cfg x0 H.hc sN'.1
    have hL2 := sq_nonneg L
    simp only [c₂]
    split_ifs with hcond
    · rw [abs_of_nonneg (by positivity)]
      have hw : pw cfg.K (cfg.pos sN'.1.t) ^ 2 ≤ 1 := by
        have h1 := pw_nonneg hK2 hcond.2.1.le
        have h2 := (pw_le (k := cfg.pos sN'.1.t) hK2).trans (by rw [div_le_one hKpos]; exact_mod_cast hK2)
        nlinarith
      have hw0 := sq_nonneg (pw cfg.K (cfg.pos sN'.1.t))
      have hg2 := sq_nonneg ‖gradient f (ypoint cfg sN'.1)‖
      have hWx : 6 * ‖sN'.1.x - x0‖ ^ 2 + 4 * ‖sN'.1.xPrev - x0‖ ^ 2 ≤ 6 * W x0 sN' := by
        unfold W; nlinarith [sq_nonneg ‖sN'.1.x - x0‖, sq_nonneg ‖sN'.1.xPrev - x0‖, sq_nonneg ‖sN'.1.xStart - x0‖,
          sq_nonneg ‖sN'.1.glast‖, sq_nonneg ‖sN'.1.ybar‖, sq_nonneg ‖sN'.2‖]
      have h5 : ‖gradient f (ypoint cfg sN'.1)‖ ^ 2 ≤ (2 * ‖gradient f x0‖ ^ 2 + 12 * L ^ 2) * W x0 sN' := by
        nlinarith [mul_le_mul_of_nonneg_left hWx (by positivity : (0:ℝ) ≤ 2 * L ^ 2), sq_nonneg ‖gradient f x0‖]
      calc pw cfg.K (cfg.pos sN'.1.t) ^ 2 * δ2 * ‖gradient f (ypoint cfg sN'.1)‖ ^ 2
          ≤ 1 * δ2 * ‖gradient f (ypoint cfg sN'.1)‖ ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ hg2
            exact mul_le_mul_of_nonneg_right hw hδ0
        _ ≤ δ2 * ((2 * ‖gradient f x0‖ ^ 2 + 12 * L ^ 2) * W x0 sN') := by
            rw [one_mul]; exact mul_le_mul_of_nonneg_left h5 hδ0
        _ = _ := by ring
    · rw [abs_zero]; positivity
  have hYint : ∀ t, Integrable (fun tail => Y₂ (run (astep cfg x0 g f) (s, N) tail t))
      (Measure.infinitePi fun _ : ℕ => ν) := fun t => integrable_of_le_W H Y₂ hY₂ _ hY₂W (s, N) t
  have hcint : ∀ t, Integrable (fun tail => c₂ (run (astep cfg x0 g f) (s, N) tail t))
      (Measure.infinitePi fun _ : ℕ => ν) := fun t => integrable_of_le_W H c₂ hc₂ _ hc₂W (s, N) t
  have hDint : ∀ e, Integrable (fun tail => D₂ (run (astep cfg x0 g f) (s, N) tail (e * 1)) (shift (e * 1) tail))
      (Measure.infinitePi fun _ : ℕ => ν) := fun e => integrable_const 0
  have hdrift : ∀ e < cfg.K, ∀ sN' ∈ Inv₁ (e * 1),
      ∫ tail, (Y₂ (run (astep cfg x0 g f) sN' tail 1) + D₂ sN' tail) ∂(Measure.infinitePi fun _ : ℕ => ν)
        ≤ Y₂ sN' + c₂ sN' := by
    intro e he sN' hsN'
    rw [mul_one] at hsN'
    obtain ⟨hinv', ht', hd''⟩ := And.imp_right (fun h' => h' (by omega)) hsN'
    have hp : cfg.pos sN'.1.t = e := by rw [ht']; exact pos_add_of_zero cfg hpos (by omega)
    have hp1 : cfg.pos (sN'.1.t + 1) = e + 1 := by rw [pos_succ_of_lt cfg hEb (by omega), hp]
    have hrw : ∀ tail : ℕ → (Fin cfg.b → Ω), Y₂ (run (astep cfg x0 g f) sN' tail 1) + D₂ sN' tail =
        (fun ω => Y₂ (astep cfg x0 g f sN' ω)) (tail 0) := fun tail => by simp [D₂, run_succ, run_zero]
    simp_rw [hrw]
    have hmeas : Measurable (fun ω => Y₂ (astep cfg x0 g f sN' ω)) :=
      hY₂.comp (measurable_astep_fun cfg x0 g f H.h H.ho.meas sN')
    rw [integral_eval ν _ hmeas]
    obtain ⟨s', N'⟩ := sN'
    simp only at hp hp1 hd''
    have ht1 : ∀ ω, (blockStep cfg x0 g s' ω).t = s'.t + 1 := fun ω =>
      (blockStep_not_last hd'' (by omega) ω).2.2
    have hc0 : 0 ≤ c₂ (s', N') := by
      simp only [c₂]; split_ifs
      · positivity
      · exact le_rfl
    by_cases htr : s'.trig = true
    · have hval : ∀ ω, Y₂ (astep cfg x0 g f (s', N') ω) = ‖N'‖ ^ 2 := by
        intro ω
        simp only [Y₂, astep]
        rw [nextN_of_not cfg g f ω (by simp [htr]), ht1, hp1,
          ite_eq_left (show 1 ≤ e + 1 ∧ e + 1 ≤ cfg.K from ⟨by omega, by omega⟩)]
      simp_rw [hval]
      simp only [integral_const, probReal_univ, one_smul]
      have he0 : e ≠ 0 := by
        intro h0; have := hinv'.hfresh hd'' (by rw [hp, h0]); rw [this] at htr; exact Bool.noConfusion htr
      simp only [Y₂, hp]
      rw [ite_eq_left (show 1 ≤ e ∧ e ≤ cfg.K from ⟨by omega, by omega⟩)]
      linarith
    · have htr' : s'.trig = false := by simpa using htr
      have hval : ∀ ω, Y₂ (astep cfg x0 g f (s', N') ω) =
          ‖(if e = 0 then 0 else N') + pw cfg.K e • (bmean cfg g (ypoint cfg s') ω - gradient f (ypoint cfg s'))‖ ^ 2 := by
        intro ω
        simp only [Y₂, astep]
        rw [nextN_agd cfg g f ω hd'' (by omega) htr', ht1, hp1, hp,
          ite_eq_left (show 1 ≤ e + 1 ∧ e + 1 ≤ cfg.K from ⟨by omega, by omega⟩)]
      simp_rw [hval]
      set y := ypoint cfg s' with hy
      set N0 : E := if e = 0 then 0 else N' with hN0
      have hint_e : Integrable (fun ω => bmean cfg g y ω - gradient f y) ν :=
        (bmean_integrable cfg H.hb H.ho y).sub (integrable_const _)
      have hint_e2 := bmean_err_integrable cfg H.hb H.ho y
      have hexp : ∀ ω, ‖N0 + pw cfg.K e • (bmean cfg g y ω - gradient f y)‖ ^ 2 =
          ‖N0‖ ^ 2 + (2 * pw cfg.K e) * ⟪N0, bmean cfg g y ω - gradient f y⟫ +
            pw cfg.K e ^ 2 * ‖bmean cfg g y ω - gradient f y‖ ^ 2 := by
        intro ω
        rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        ring
      simp_rw [hexp]
      have hI3 : Integrable (fun ω => (2 * pw cfg.K e) * ⟪N0, bmean cfg g y ω - gradient f y⟫) ν :=
        (hint_e.const_inner N0).const_mul _
      have hI1 : Integrable (fun ω => ‖N0‖ ^ 2 + (2 * pw cfg.K e) * ⟪N0, bmean cfg g y ω - gradient f y⟫) ν :=
        (integrable_const _).add hI3
      have hI2 : Integrable (fun ω => pw cfg.K e ^ 2 * ‖bmean cfg g y ω - gradient f y‖ ^ 2) ν :=
        hint_e2.const_mul _
      rw [integral_add hI1 hI2, integral_add (integrable_const _) hI3,
        integral_const, integral_const_mul, integral_const_mul, integral_inner_bmean_err cfg H.hb H.ho y N0]
      simp only [probReal_univ, one_smul, mul_zero, add_zero]
      have h2 := integral_bmean_err cfg H.hb H.ho y
      have hw2 := sq_nonneg (pw cfg.K e)
      have hc2 : c₂ (s', N') = pw cfg.K e ^ 2 * δ2 * ‖gradient f y‖ ^ 2 := by
        simp only [c₂, hp, hy]
        rw [ite_eq_left (show s'.done = false ∧ e < cfg.K ∧ s'.trig = false from ⟨hd'', he, htr'⟩)]
      rw [hc2]
      by_cases he0 : e = 0
      · simp only [Y₂, hp, he0, ite_eq_right (by omega : ¬ (1 ≤ 0 ∧ 0 ≤ cfg.K))]
        simp only [hN0, he0, ↓reduceIte, norm_zero]
        nlinarith [mul_le_mul_of_nonneg_left h2 hw2]
      · simp only [Y₂, hp]
        rw [ite_eq_left (show 1 ≤ e ∧ e ≤ cfg.K from ⟨by omega, by omega⟩)]
        simp only [hN0, he0, ↓reduceIte]
        nlinarith [mul_le_mul_of_nonneg_left h2 hw2]
  have hdr := drift (astep cfg x0 g f) (s, N) ν hstep 1 Inv₁ hInv₁ hs0 Y₂ c₂ D₂ hY₂ hc₂ hD₂ hYint hcint hDint
    cfg.K hdrift
  simp only [mul_one, D₂, integral_zero, Finset.sum_const_zero, add_zero] at hdr
  have hY0 : Y₂ (s, N) = 0 := by simp only [Y₂, hpos]; rw [ite_eq_right (by omega)]
  rw [hY0, zero_add] at hdr
  have hYK : ∀ tail, Y₂ (run (astep cfg x0 g f) (s, N) tail cfg.K) = ‖(run (astep cfg x0 g f) (s, N) tail cfg.K).2‖ ^ 2 := by
    intro tail
    have hmem := run_mem_inv (astep cfg x0 g f) (s, N) Inv₁ hInv₁ hs0 tail cfg.K
    obtain ⟨_, htt, _⟩ := And.imp_right (fun h' => h' (by omega)) hmem
    have hp : cfg.pos (run (astep cfg x0 g f) (s, N) tail cfg.K).1.t = cfg.K := by
      rw [htt]; exact pos_add_of_zero cfg hpos (by omega)
    simp only [Y₂, hp]
    rw [ite_eq_left (show 1 ≤ cfg.K ∧ cfg.K ≤ cfg.K from ⟨by omega, le_rfl⟩)]
  simp_rw [hYK] at hdr
  have hcbound : ∀ tail, ∑ t ∈ Finset.range cfg.K, c₂ (run (astep cfg x0 g f) (s, N) tail t) ≤
      (2 / cfg.K) ^ 2 * δ2 * ((64 / cfg.η) * Dep cfg x0 g f (s, N) tail + 2 * cfg.K * Dm cfg ρ ^ 2) := by
    intro tail
    have hterm : ∀ t ∈ Finset.range cfg.K, c₂ (run (astep cfg x0 g f) (s, N) tail t) ≤
        (2 / cfg.K) ^ 2 * δ2 * ((64 / cfg.η) * Dblk cfg x0 g f (run (astep cfg x0 g f) (s, N) tail t) (tail t) +
          2 * Dm cfg ρ ^ 2) := by
      intro t ht
      have ht' : t < cfg.K := Finset.mem_range.mp ht
      have hmem := run_mem_inv (astep cfg x0 g f) (s, N) Inv₁ hInv₁ hs0 tail t
      obtain ⟨hinv', htt, hdd⟩ := And.imp_right (fun h' => h' (by omega)) hmem
      set sN' := run (astep cfg x0 g f) (s, N) tail t with hsN'
      have hp : cfg.pos sN'.1.t = t := by rw [htt]; exact pos_add_of_zero cfg hpos (by omega)
      have hDb : 0 ≤ Dblk cfg x0 g f sN' (tail t) := Dblk_nonneg H.hc sN' (tail t)
      have hDm := sq_nonneg (Dm cfg ρ)
      have hw2 : pw cfg.K t ^ 2 ≤ (2 / cfg.K) ^ 2 := by
        have h1 := pw_nonneg hK2 ht'.le
        have h2 := pw_le (k := t) hK2
        nlinarith
      simp only [c₂, hp]
      split_ifs with hcond
      · obtain ⟨_, _, htr'⟩ := hcond
        have hA := hinv'.hagd hdd (by omega) htr'
        have hyS := hA.y_le H.hc
        have hDm0 : 0 ≤ Dm cfg ρ := by unfold Dm; have := H.h.hρ; positivity
        have hδv : ‖gradient f (ypoint cfg sN'.1) - gMs cfg f sN'.1‖ ≤ Dm cfg ρ := by
          unfold gMs
          refine (H.h.gradModel_err sN'.1.xStart (ypoint cfg sN'.1)).trans ?_
          unfold Dm
          have hsq2 : ‖ypoint cfg sN'.1 - sN'.1.xStart‖ ^ 2 ≤ (2 * cfg.B) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hyS 2
          have := mul_le_mul_of_nonneg_left hsq2 H.h.hρ
          nlinarith [this]
        have hgf : ‖gradient f (ypoint cfg sN'.1)‖ ≤ ‖gMs cfg f sN'.1‖ + Dm cfg ρ := by
          have := norm_sub_norm_le (gradient f (ypoint cfg sN'.1)) (gMs cfg f sN'.1); linarith
        have hgf2 : ‖gradient f (ypoint cfg sN'.1)‖ ^ 2 ≤ 2 * ‖gMs cfg f sN'.1‖ ^ 2 + 2 * Dm cfg ρ ^ 2 := by
          nlinarith [norm_nonneg (gradient f (ypoint cfg sN'.1)), norm_nonneg (gMs cfg f sN'.1),
            sq_nonneg (‖gMs cfg f sN'.1‖ - Dm cfg ρ)]
        have hDbk : cfg.η / 32 * ‖gMs cfg f sN'.1‖ ^ 2 ≤ Dblk cfg x0 g f sN' (tail t) := by
          unfold Dblk
          rw [ite_eq_left ⟨hdd, by omega, htr'⟩]
          have : 0 ≤ cfg.θ / cfg.η / 16 * ‖(blockStep cfg x0 g sN'.1 (tail t)).x - sN'.1.x‖ ^ 2 := by
            have := H.hc.hη; have := H.hc.hθ0; positivity
          linarith
        have hη := H.hc.hη
        have h64 : 2 * ‖gMs cfg f sN'.1‖ ^ 2 ≤ (64 / cfg.η) * Dblk cfg x0 g f sN' (tail t) := by
          have := mul_le_mul_of_nonneg_left hDbk (by positivity : (0:ℝ) ≤ 64 / cfg.η)
          have e : 64 / cfg.η * (cfg.η / 32 * ‖gMs cfg f sN'.1‖ ^ 2) = 2 * ‖gMs cfg f sN'.1‖ ^ 2 := by
            field_simp; ring
          linarith
        calc pw cfg.K t ^ 2 * δ2 * ‖gradient f (ypoint cfg sN'.1)‖ ^ 2
            ≤ (2 / cfg.K) ^ 2 * δ2 * ‖gradient f (ypoint cfg sN'.1)‖ ^ 2 := by
              apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
              exact mul_le_mul_of_nonneg_right hw2 hδ0
          _ ≤ (2 / cfg.K) ^ 2 * δ2 * ((64 / cfg.η) * Dblk cfg x0 g f sN' (tail t) + 2 * Dm cfg ρ ^ 2) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              linarith
      · have hη := H.hc.hη
        exact mul_nonneg (mul_nonneg (sq_nonneg _) hδ0)
          (add_nonneg (mul_nonneg (by positivity) hDb) (by positivity))
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    have hsub : ∑ i ∈ Finset.range cfg.K, Dblk cfg x0 g f (run (astep cfg x0 g f) (s, N) tail i) (tail i) ≤
        Dep cfg x0 g f (s, N) tail := by
      unfold Dep
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => Dblk_nonneg H.hc _ _)
      intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
    have hc0 : 0 ≤ (2 / cfg.K) ^ 2 * δ2 := by positivity
    have hη := H.hc.hη
    nlinarith [mul_le_mul_of_nonneg_left hsub (by positivity : (0:ℝ) ≤ (2 / cfg.K) ^ 2 * δ2 * (64 / cfg.η))]
  have hcint' : Integrable (fun tail => ∑ t ∈ Finset.range cfg.K, c₂ (run (astep cfg x0 g f) (s, N) tail t))
      (Measure.infinitePi fun _ : ℕ => ν) := integrable_finsetSum _ (fun t _ => hcint t)
  have hDepint : Integrable (fun tail => Dep cfg x0 g f (s, N) tail) (Measure.infinitePi fun _ : ℕ => ν) := by
    unfold Dep
    exact integrable_finsetSum _ (fun t _ => Dblk_run_integrable H (s, N) t)
  have hsum : ∑ t ∈ Finset.range cfg.K, ∫ tail, c₂ (run (astep cfg x0 g f) (s, N) tail t) ∂(Measure.infinitePi fun _ : ℕ => ν) ≤
      (2 / cfg.K) ^ 2 * δ2 * ((64 / cfg.η) * ∫ tail, Dep cfg x0 g f (s, N) tail ∂(Measure.infinitePi fun _ : ℕ => ν) +
        2 * cfg.K * Dm cfg ρ ^ 2) := by
    rw [← integral_finsetSum _ (fun t _ => hcint t)]
    have hJ1 : Integrable (fun tail => (64 / cfg.η) * Dep cfg x0 g f (s, N) tail)
        (Measure.infinitePi fun _ : ℕ => ν) := hDepint.const_mul _
    have hJ : Integrable (fun tail => (64 / cfg.η) * Dep cfg x0 g f (s, N) tail + 2 * cfg.K * Dm cfg ρ ^ 2)
        (Measure.infinitePi fun _ : ℕ => ν) := hJ1.add (integrable_const _)
    have := integral_mono hcint' (hJ.const_mul _) hcbound
    rw [integral_const_mul, integral_add hJ1 (integrable_const _), integral_const_mul, integral_const] at this
    simpa using this
  linarith

end LongTails.Proofs.StrongGrowthAgdCounting
