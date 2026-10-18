import LongTails.Proofs.DyadicHolderMoments

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.CenteredDyadic

open OracleTemplate.NormalizedStorm OracleTemplate.DyadicHolder

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ω : Type} [MeasurableSpace Ω]

structure Hyp (p : Measure Ω) (F : E → ℝ) (g : E → Ω → E) (L M ν σ : ℝ) : Prop where
  grad : ∀ x, HasGradientAt F (gradient F x) x
  lip : ∀ x y, ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖
  meas : Measurable (Function.uncurry g)
  int : ∀ x, Integrable (g x) p
  mean : ∀ x, ∫ ω, g x ω ∂p = gradient F x
  var_int : ∀ x, Integrable (fun ω => ‖g x ω - gradient F x‖ ^ 2) p
  var : ∀ x, ∫ ω, ‖g x ω - gradient F x‖ ^ 2 ∂p ≤ σ ^ 2
  diff_int : ∀ x y, Integrable (fun ω => ‖(g x ω - g y ω) - (gradient F x - gradient F y)‖ ^ 2) p
  msh : ∀ x y, ∫ ω, ‖(g x ω - g y ω) - (gradient F x - gradient F y)‖ ^ 2 ∂p ≤ M * ‖x - y‖ ^ (2 * ν)
  L_pos : 0 < L
  M_nn : 0 ≤ M
  ν_pos : 0 < ν

section Error

variable {p : Measure Ω} [IsProbabilityMeasure p] {F : E → ℝ} {g : E → Ω → E} {L M ν σ : ℝ}

local notation "P" => Measure.infinitePi fun _ : ℕ => p

omit [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure p] in
lemma Hyp.grad_continuous (H : Hyp p F g L M ν σ) : Continuous (gradient F) := by
  have hl : LipschitzWith ⟨L, H.L_pos.le⟩ (gradient F) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simp only [dist_eq_norm]
      exact H.lip x y
  exact hl.continuous

omit [IsProbabilityMeasure p] in
lemma Hyp.measurable_err (H : Hyp p F g L M ν σ) (cfg : DyadicConfig) (x0 : E) (k : ℕ) :
    Measurable fun ξ : ℕ → Ω => err cfg g F x0 ξ k :=
  (measurable_D H.meas x0 0 k).sub (H.grad_continuous.measurable.comp (measurable_X H.meas x0 0 k))

lemma Hyp.err_moment (H : Hyp p F g L M ν σ) (cfg : DyadicConfig) (x0 : E)
    (hη : 0 ≤ cfg.η) (hbA : 1 ≤ cfg.bA) (hb : ∀ j, 1 ≤ cfg.b j) {β : ℝ}
    (hβ : ∀ j, j < cfg.J → M * (2 ^ j * cfg.η) ^ (2 * ν) / cfg.b j ≤ β) :
    ∀ k, Integrable (fun ξ => ‖err cfg g F x0 ξ k‖ ^ 2) P ∧
      ∫ ξ, ‖err cfg g F x0 ξ k‖ ^ 2 ∂P ≤
        σ ^ 2 / cfg.bA + (if cfg.pos k = 0 then 0 else β * ((cfg.J : ℝ) - cfg.level k)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  have hgm : Measurable (gradient F) := H.grad_continuous.measurable
  have hXk := measurable_X (cfg := cfg) H.meas x0 0 k
  by_cases hk : cfg.pos k = 0
  · simp only [hk, ite_true, add_zero]
    set W : E → Ω → E := fun y ω => (1 / (cfg.bA : ℝ)) • (g y ω - gradient F y)
    have hW : Measurable (Function.uncurry W) :=
      (H.meas.sub (hgm.comp measurable_fst)).const_smul _
    have hWi : ∀ y, Integrable (W y) p := fun y => ((H.int y).sub (integrable_const _)).smul _
    have hW0 : ∀ y, ∫ ω, W y ω ∂p = 0 := by
      intro y
      simp only [W]
      rw [integral_smul, integral_sub (H.int y) (integrable_const _), H.mean y, integral_const]
      simp
    have hW2 : ∀ y, Integrable (fun ω => ‖W y ω‖ ^ 2) p := by
      intro y
      simp only [W, norm_smul, mul_pow]
      exact (H.var_int y).const_mul _
    have hb0 : (0 : ℝ) < cfg.bA := by exact_mod_cast hbA
    have hw : ∀ y, ∫ ω, ‖W y ω‖ ^ 2 ∂p ≤ σ ^ 2 / (cfg.bA : ℝ) ^ 2 := by
      intro y
      simp only [W, norm_smul, mul_pow]
      rw [integral_const_mul]
      have := H.var y
      rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_pow, one_pow, one_div,
        ← div_eq_inv_mul]
      gcongr
    have hres := batch_sum_sq p (off cfg k) (fun ξ => X cfg g x0 0 ξ k) hXk
      (fun ξ ξ' h => X_congr k h) (fun _ => (0 : E)) measurable_const (fun _ _ _ => rfl)
      (by simp) W hW hWi hW0 hW2 _ hw cfg.bA
    have e : ∀ ξ : ℕ → Ω, err cfg g F x0 ξ k =
        0 + ∑ i ∈ Finset.range cfg.bA, W (X cfg g x0 0 ξ k) (ξ (off cfg k + i)) := by
      intro ξ
      simp only [err, D_anchor hk, W, zero_add, ← Finset.smul_sum, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_range, smul_sub]
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, one_div, inv_mul_cancel₀ hb0.ne', one_smul]
    simp_rw [e]
    refine ⟨hres.1, hres.2.trans (le_of_eq ?_)⟩
    simp only [zero_add, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      integral_zero]
    field_simp
  · simp only [hk, ite_false]
    set j := cfg.level k
    set b := cfg.b j
    set r : ℝ := 2 ^ j * cfg.η
    have hjJ : j < cfg.J := cfg.level_lt hk
    have hpk := cfg.pred_lt hk
    obtain ⟨ihI, ihle⟩ := ih (cfg.pred k) hpk
    have hb0 : (0 : ℝ) < b := by exact_mod_cast hb j
    have hr0 : 0 ≤ r := by positivity
    set W : E × E → Ω → E := fun y ω => if ‖y.1 - y.2‖ ≤ r then
      (1 / (b : ℝ)) • ((g y.1 ω - g y.2 ω) - (gradient F y.1 - gradient F y.2)) else 0
    have hset : MeasurableSet {y : E × E | ‖y.1 - y.2‖ ≤ r} :=
      measurableSet_le (measurable_fst.sub measurable_snd).norm measurable_const
    have hW : Measurable (Function.uncurry W) := by
      have h1 : Measurable fun z : (E × E) × Ω =>
          (1 / (b : ℝ)) • ((g z.1.1 z.2 - g z.1.2 z.2) - (gradient F z.1.1 - gradient F z.1.2)) :=
        (((H.meas.comp (measurable_fst.fst.prodMk measurable_snd)).sub
          (H.meas.comp (measurable_fst.snd.prodMk measurable_snd))).sub
          ((hgm.comp measurable_fst.fst).sub (hgm.comp measurable_fst.snd))).const_smul _
      exact Measurable.ite (measurable_fst hset) h1 measurable_const
    have hZi : ∀ y : E × E, Integrable (fun ω =>
        (1 / (b : ℝ)) • ((g y.1 ω - g y.2 ω) - (gradient F y.1 - gradient F y.2))) p :=
      fun y => (((H.int y.1).sub (H.int y.2)).sub (integrable_const _)).smul _
    have hWi : ∀ y, Integrable (W y) p := by
      intro y; simp only [W]; split_ifs
      · exact hZi y
      · exact integrable_const _
    have hW0 : ∀ y, ∫ ω, W y ω ∂p = 0 := by
      intro y
      simp only [W]
      split_ifs
      · rw [integral_smul, integral_sub (f := fun ω => g y.1 ω - g y.2 ω)
          ((H.int y.1).sub (H.int y.2)) (integrable_const _),
          integral_sub (H.int y.1) (H.int y.2), H.mean, H.mean, integral_const]
        simp
      · simp
    have hW2 : ∀ y, Integrable (fun ω => ‖W y ω‖ ^ 2) p := by
      intro y; simp only [W]; split_ifs
      · simp only [norm_smul, mul_pow]
        exact (H.diff_int y.1 y.2).const_mul _
      · simp
    have hw : ∀ y, ∫ ω, ‖W y ω‖ ^ 2 ∂p ≤ M * r ^ (2 * ν) / (b : ℝ) ^ 2 := by
      intro y
      have hMr : 0 ≤ M * r ^ (2 * ν) / (b : ℝ) ^ 2 := by
        have := H.M_nn; positivity
      simp only [W]
      split_ifs with hy
      · simp only [norm_smul, mul_pow]
        rw [integral_const_mul, Real.norm_eq_abs, abs_of_pos (by positivity), div_pow, one_pow,
          one_div, ← div_eq_inv_mul]
        gcongr
        refine (H.msh y.1 y.2).trans ?_
        gcongr
        · exact H.M_nn
        · have := H.ν_pos; positivity
      · simpa using hMr
    have hS0 : Measurable fun ξ : ℕ → Ω => (X cfg g x0 0 ξ k, X cfg g x0 0 ξ (cfg.pred k)) :=
      hXk.prodMk (measurable_X H.meas x0 0 _)
    have hoff : off cfg (cfg.pred k + 1) ≤ off cfg k := off_mono (by omega)
    have hres := batch_sum_sq p (off cfg k)
      (fun ξ => (X cfg g x0 0 ξ k, X cfg g x0 0 ξ (cfg.pred k))) hS0
      (fun ξ ξ' h => by
        rw [X_congr k h, X_congr (cfg.pred k)
          (fun i hi => h i (lt_of_lt_of_le hi (off_mono hpk.le)))])
      (fun ξ => err cfg g F x0 ξ (cfg.pred k)) (H.measurable_err cfg x0 _)
      (fun ξ ξ' h => by
        simp only [err]
        rw [D_congr (cfg.pred k) (fun i hi => h i (lt_of_lt_of_le hi hoff)),
          X_congr (cfg.pred k) (fun i hi => h i (lt_of_lt_of_le hi (off_mono hpk.le)))])
      ihI W hW hWi hW0 hW2 _ hw b
    have e : ∀ ξ : ℕ → Ω, err cfg g F x0 ξ k = err cfg g F x0 ξ (cfg.pred k) +
        ∑ i ∈ Finset.range b, W (X cfg g x0 0 ξ k, X cfg g x0 0 ξ (cfg.pred k))
          (ξ (off cfg k + i)) := by
      intro ξ
      have hd : ‖X cfg g x0 0 ξ k - X cfg g x0 0 ξ (cfg.pred k)‖ ≤ r := X_pred_dist hη hk
      simp only [W, hd, ite_true, err, D_level hk]
      exact batch_identity (hb j) _ _ _ _ _
    simp_rw [e]
    refine ⟨hres.1, hres.2.trans ?_⟩
    have hβj : M * r ^ (2 * ν) / b ≤ β := hβ j hjJ
    have hcast : (b : ℝ) * (M * r ^ (2 * ν) / (b : ℝ) ^ 2) = M * r ^ (2 * ν) / b := by
      field_simp
    have hβ0 : 0 ≤ β := le_trans (by have := H.M_nn; positivity) hβj
    have hprev : (if cfg.pos (cfg.pred k) = 0 then 0
        else β * ((cfg.J : ℝ) - cfg.level (cfg.pred k)))
        ≤ β * ((cfg.J : ℝ) - j - 1) := by
      split_ifs with hp
      · have : (j : ℝ) + 1 ≤ cfg.J := by exact_mod_cast hjJ
        nlinarith
      · have hl := cfg.level_pred_gt hk hp
        have : (j : ℝ) + 1 ≤ cfg.level (cfg.pred k) := by exact_mod_cast hl
        nlinarith
    rw [hcast]
    nlinarith

end Error

end OracleTemplate.CenteredDyadic
