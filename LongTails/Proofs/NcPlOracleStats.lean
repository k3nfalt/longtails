import LongTails.Proofs.NcPlOracle
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.NcPlOracleStats

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open Classical
open LongTails.Proofs.AbcChainProfiles LongTails.Proofs.NcPlCalc LongTails.Proofs.NcPlSchedule
open LongTails.Proofs.NcPlBlock LongTails.Proofs.NcPlBlockSmooth LongTails.Proofs.NcPlChain
open LongTails.Proofs.NcPlChainPL LongTails.Proofs.NcPlFlat LongTails.Proofs.NcPlCut
open LongTails.Proofs.NcPlInstance LongTails.Proofs.NcPlLipschitz LongTails.Proofs.NcPlPL
open LongTails.Proofs.NcPlMoreau LongTails.Proofs.NcPlTrunc LongTails.Proofs.NcPlOracle
open LongTails.Proofs.AbcChain (Chain)
open LongTails.Proofs.AbcHardFunction (Space sel sel_apply sel_norm adjoint_norm adjoint_congr)
open LongTails.Proofs.MintyChainGeometry (ball ball_norm_le ball_lipschitz ball_of_le)
open LongTails.Proofs.AbcHardOracle (coin unif coin_integral coin_sq_integral coin_integrable
  coin_measurable setOf_le_measurable)

variable (G : Geo) {d : ℕ} (π : Fin (G.k + 1) ↪ Fin d)

lemma gxOf_sub (x : Space d) (A A' : Chain G.k) :
    gxOf G π x A' - gxOf G π x A =
      cutv G.Bx x • (sel π).adjoint (A' - A) + ⟪A' - A, sel π x⟫ • cutGrad G.Bx x := by
  unfold gxOf
  rw [map_sub, inner_sub_left, smul_sub, sub_smul]
  abel

lemma gxOf_sub_norm (x : Space d) (A A' : Chain G.k) :
    ‖gxOf G π x A' - gxOf G π x A‖ ≤ 17 * ‖A' - A‖ := by
  have hB := G.hBx
  rw [gxOf_sub, smul_cutGrad_ball G.hBx (fun z => ⟪A' - A, sel π z⟫) x]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 := cutv_abs G.Bx x
  have h2 := adjoint_norm π (A' - A)
  have h3 : |⟪A' - A, sel π (ball (2 * G.Bx) x)⟫| ≤ ‖A' - A‖ * (2 * G.Bx) :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      ((sel_norm π _).trans (ball_norm_le _ (by positivity) _)) (norm_nonneg _))
  have h4 := cutGrad_norm_le G.hBx x
  have t1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
  have t2 := mul_le_mul h3 h4 (norm_nonneg _) (by positivity)
  have e : ‖A' - A‖ * (2 * G.Bx) * (8 / G.Bx) = 16 * ‖A' - A‖ := by
    field_simp
    ring
  linarith

lemma gyOf_sub (y : Space d) (B B' : Chain G.k) (R R' : ℝ) :
    gyOf G π y B' R' - gyOf G π y B R =
      cutv G.By y • (sel π).adjoint (B' - B) + (R' - R) • cutGrad G.By y := by
  unfold gyOf
  rw [map_sub, smul_sub, sub_smul]
  abel

lemma gyOf_sub_norm (y : Space d) (B B' : Chain G.k) (R R' : ℝ) :
    ‖gyOf G π y B' R' - gyOf G π y B R‖ ≤ ‖B' - B‖ + |R' - R| * (8 / G.By) := by
  have hB := G.hBy
  rw [gyOf_sub]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 := cutv_abs G.By y
  have h2 := adjoint_norm π (B' - B)
  have h4 := cutGrad_norm_le G.hBy y
  have t1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
  have t2 := mul_le_mul_of_nonneg_left h4 (abs_nonneg (R' - R))
  linarith

section Masked

variable {θ : ℝ}

theorem masked_bound (hθ0 : 0 ≤ θ) (hθρ : θ ≤ G.ρ) (hθ2 : θ ≤ 1 / 2) (s : ℕ)
    (hsk : s < G.k + 1) (hm : masked G s) (x y : Space d)
    (hs : ∀ p : Fin (G.k + 1), s ≤ p.val → ¬ big G θ x y (π p)) :
    ‖hardGx G π x y - knownGx G π s x y‖ ^ 2 + ‖hardGy G π x y - knownGy G π s x y‖ ^ 2 ≤
      (2 ^ 23 * θ + 1 / (3 * ((G.n : ℝ) + 1) * G.ρ)) ^ 2 := by
  obtain ⟨hx, hy⟩ := known_exact G π hθ0 hθρ hθ2 s x y hs
  rw [← hx, ← hy]
  have hρ := G.scales.hρ
  have hBy := G.hBy
  obtain ⟨w, hw⟩ : ∃ w, w = 1 / (3 * ((G.n : ℝ) + 1) * G.ρ) := ⟨_, rfl⟩
  have hw0 : 0 ≤ w := by
    rw [hw]
    positivity
  rw [← hw]
  have hbs : |seq (yhat G π y) s| ≤ θ := seq_yhat_small G π hθ0 s x y hs s le_rfl
  have hbs2 : ‖trC (s + 1) (yhat G π y) - trC s (yhat G π y)‖ ^ 2 ≤ θ ^ 2 := by
    refine (trC_succ_sub_sq s (yhat G π y)).trans ?_
    have := pow_le_pow_left₀ (abs_nonneg _) hbs 2
    rwa [sq_abs] at this
  have hbs1 : ‖trC (s + 1) (yhat G π y) - trC s (yhat G π y)‖ ≤ θ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) hθ0 two_ne_zero).mp hbs2
  have hu : uOf G.n (seq (trC (s + 1) (chA G π x))) = uOf G.n (seq (trC s (chA G π x))) := by
    rw [seq_trC, seq_trC]
    exact uOf_tr_succ _ hm.1
  have hVA : vecA G (trC (s + 1) (chA G π x)) (trC (s + 1) (yhat G π y)) (cutv G.By y) =
      vecA G (trC s (chA G π x)) (trC (s + 1) (yhat G π y)) (cutv G.By y) := by
    unfold vecA
    congr 1
    funext p
    unfold gA gAu
    rw [hu]
  have hVB : vecB G (trC (s + 1) (chA G π x)) (trC (s + 1) (yhat G π y)) =
      vecB G (trC s (chA G π x)) (trC (s + 1) (yhat G π y)) := by
    unfold vecB
    congr 1
    funext p
    unfold gB
    rw [hu]
  have hRu : RK G π (s + 1) x y = rF G.m G.n G.r (seq (trC s (chA G π x)))
      (seq (trC (s + 1) (yhat G π y))) := by
    unfold RK rF
    rw [hu]
  have hΔA : ‖AK G π (s + 1) x y - AK G π s x y‖ ^ 2 ≤ 2 ^ 33 * θ ^ 2 := by
    unfold AK
    rw [hVA, norm_sub_sq_eq]
    have hcoord : ∀ p ∈ (Finset.univ : Finset (Fin (G.k + 1))),
        (trC (s + 1) (vecA G (trC s (chA G π x)) (trC (s + 1) (yhat G π y)) (cutv G.By y)) p -
          trC s (vecA G (trC s (chA G π x)) (trC s (yhat G π y)) (cutv G.By y)) p) ^ 2 ≤
        (vecA G (trC s (chA G π x)) (trC (s + 1) (yhat G π y)) (cutv G.By y) p -
          vecA G (trC s (chA G π x)) (trC s (yhat G π y)) (cutv G.By y) p) ^ 2 := by
      intro p _
      rw [trC_apply, trC_apply]
      by_cases h1 : p.val < s
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
      · rw [ite_eq_right h1]
        by_cases h2 : p.val = s
        · have hz : vecA G (trC s (chA G π x)) (trC (s + 1) (yhat G π y)) (cutv G.By y) p = 0 := by
            change gA G.m G.n G.r _ _ (cutv G.By y) p = 0
            unfold gA
            rw [ite_eq_right]
            rw [h2]
            exact hm.1
          rw [hz]
          split_ifs
          · rw [sub_zero]
            nlinarith [sq_nonneg (vecA G (trC s (chA G π x)) (trC s (yhat G π y))
              (cutv G.By y) p)]
          · rw [sub_zero]
            nlinarith [sq_nonneg (vecA G (trC s (chA G π x)) (trC s (yhat G π y))
              (cutv G.By y) p)]
        · rw [ite_eq_right (by omega), sub_zero]
          nlinarith [sq_nonneg (vecA G (trC s (chA G π x)) (trC (s + 1) (yhat G π y))
            (cutv G.By y) p - vecA G (trC s (chA G π x)) (trC s (yhat G π y)) (cutv G.By y) p)]
    refine (Finset.sum_le_sum hcoord).trans ?_
    rw [← norm_sub_sq_eq]
    have hl := vecA_lip_sq G (trC s (chA G π x)) (trC s (chA G π x)) (trC s (yhat G π y))
      (trC (s + 1) (yhat G π y)) (c := cutv G.By y) (c' := cutv G.By y) (cutv_abs G.By y)
    rw [sub_self, norm_zero, sub_self] at hl
    nlinarith
  have hΔB : ‖BK G π (s + 1) x y - BK G π s x y‖ ^ 2 ≤ 2 ^ 25 * θ ^ 2 + w ^ 2 := by
    unfold BK
    rw [hVB, norm_sub_sq_eq]
    have hcoord : ∀ p ∈ (Finset.univ : Finset (Fin (G.k + 1))),
        (trC (s + 1) (vecB G (trC s (chA G π x)) (trC (s + 1) (yhat G π y))) p -
          trC s (vecB G (trC s (chA G π x)) (trC s (yhat G π y))) p) ^ 2 ≤
        (vecB G (trC s (chA G π x)) (trC (s + 1) (yhat G π y)) p -
          vecB G (trC s (chA G π x)) (trC s (yhat G π y)) p) ^ 2 +
        (if p = ⟨s, hsk⟩ then
          vecB G (trC s (chA G π x)) (trC (s + 1) (yhat G π y)) p ^ 2 else 0) := by
      intro p _
      rw [trC_apply, trC_apply]
      by_cases h1 : p.val < s
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
        have hne : p ≠ ⟨s, hsk⟩ := fun h => by
          rw [h] at h1
          exact lt_irrefl _ h1
        rw [ite_eq_right hne, add_zero]
      · rw [ite_eq_right h1, sub_zero]
        by_cases h2 : p.val = s
        · have hpe : p = ⟨s, hsk⟩ := Fin.ext h2
          rw [ite_eq_left (by omega), ite_eq_left hpe]
          nlinarith [sq_nonneg (vecB G (trC s (chA G π x)) (trC (s + 1) (yhat G π y)) p -
            vecB G (trC s (chA G π x)) (trC s (yhat G π y)) p)]
        · rw [ite_eq_right (by omega)]
          have hne : p ≠ ⟨s, hsk⟩ := fun h => h2 (by rw [h])
          rw [ite_eq_right hne, add_zero]
          nlinarith [sq_nonneg (vecB G (trC s (chA G π x)) (trC (s + 1) (yhat G π y)) p -
            vecB G (trC s (chA G π x)) (trC s (yhat G π y)) p)]
    refine (Finset.sum_le_sum hcoord).trans ?_
    rw [Finset.sum_add_distrib, ← norm_sub_sq_eq, Finset.sum_ite_eq',
      ite_eq_left (Finset.mem_univ _)]
    have hl := vecB_lip_sq G (trC s (chA G π x)) (trC s (chA G π x)) (trC s (yhat G π y))
      (trC (s + 1) (yhat G π y))
    rw [sub_self, norm_zero] at hl
    have hj : s % (G.n + 2) ≤ G.n := by
      have := Nat.mod_lt s (show 0 < G.n + 2 by omega)
      have := hm.1
      omega
    have hrj := G.scales.pos hj
    have hrge := G.scales.ge _ hj
    have hval : |vecB G (trC s (chA G π x)) (trC (s + 1) (yhat G π y)) ⟨s, hsk⟩| ≤ w := by
      change |gB G.n G.r (seq (trC s (chA G π x))) (seq (trC (s + 1) (yhat G π y))) s| ≤ w
      unfold gB
      rw [ite_eq_right hm.1]
      unfold gW
      have hyk : wOf G.n (seq (trC (s + 1) (yhat G π y))) (s / (G.n + 2)) (s % (G.n + 2)) ≤
          G.r (s % (G.n + 2)) := by
        unfold wOf
        rw [Nat.div_add_mod' s (G.n + 2), seq_trC, tr_lt _ (Nat.lt_succ_self s)]
        exact ((le_abs_self _).trans hbs).trans (hθρ.trans hrge)
      refine (rwGrad_small hrj hyk _ _).trans ?_
      rw [wt_bulk hm.2, hw, div_div, one_div_le_one_div (by positivity) (by positivity)]
      have hn1 : (0 : ℝ) < (G.n : ℝ) + 1 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hrge hn1.le]
    have hval2 : vecB G (trC s (chA G π x)) (trC (s + 1) (yhat G π y)) ⟨s, hsk⟩ ^ 2 ≤ w ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) hval 2
      rwa [sq_abs] at this
    nlinarith
  have hΔR : |RK G π (s + 1) x y - RK G π s x y| ≤ 2 * G.By * θ := by
    rw [hRu]
    unfold RK
    exact (rF_lip_b G (seq (trC s (chA G π x))) (trC s (yhat G π y))
      (trC (s + 1) (yhat G π y))).trans (mul_le_mul_of_nonneg_left hbs1 (by positivity))
  have hA1 : ‖AK G π (s + 1) x y - AK G π s x y‖ ≤ 2 ^ 17 * θ := by
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp
    nlinarith
  have hB1 : ‖BK G π (s + 1) x y - BK G π s x y‖ ≤ 2 ^ 13 * θ + w := by
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp
    nlinarith [mul_nonneg hθ0 hw0]
  have hDx : ‖knownGx G π (s + 1) x y - knownGx G π s x y‖ ≤ 2 ^ 22 * θ := by
    unfold knownGx
    refine (gxOf_sub_norm G π x _ _).trans ?_
    linarith
  have hDy : ‖knownGy G π (s + 1) x y - knownGy G π s x y‖ ≤ 2 ^ 14 * θ + w := by
    unfold knownGy
    refine (gyOf_sub_norm G π y _ _ _ _).trans ?_
    have h1 := mul_le_mul_of_nonneg_right hΔR (by positivity : (0 : ℝ) ≤ 8 / G.By)
    have e : 2 * G.By * θ * (8 / G.By) = 16 * θ := by
      field_simp
      ring
    linarith
  have hn1 := norm_nonneg (knownGx G π (s + 1) x y - knownGx G π s x y)
  have hn2 := norm_nonneg (knownGy G π (s + 1) x y - knownGy G π s x y)
  have hsum : ‖knownGx G π (s + 1) x y - knownGx G π s x y‖ +
      ‖knownGy G π (s + 1) x y - knownGy G π s x y‖ ≤ 2 ^ 23 * θ + w := by linarith
  have hsq := pow_le_pow_left₀ (add_nonneg hn1 hn2) hsum 2
  nlinarith [mul_nonneg hn1 hn2]

end Masked

section Integrals

variable (θ q : ℝ)

lemma replyX_integrable (x y : Space d) : Integrable (replyX G π θ q x y) unif := by
  unfold replyX
  exact (integrable_const _).add ((coin_integrable _).smul_const _)

lemma replyY_integrable (x y : Space d) : Integrable (replyY G π θ q x y) unif := by
  unfold replyY
  exact (integrable_const _).add ((coin_integrable _).smul_const _)

variable {q}

lemma replyX_integral (hq0 : 0 < q) (hq1 : q ≤ 1) (x y : Space d) :
    ∫ ω, replyX G π θ q x y ω ∂unif = hardGx G π x y := by
  unfold replyX
  rw [integral_add (integrable_const _) ((coin_integrable _).smul_const _), integral_const,
    probReal_univ, one_smul, integral_smul_const,
    coin_integral _ (qOf_pos G hq0 _) (qOf_le G hq1 _), one_smul]
  abel

lemma replyY_integral (hq0 : 0 < q) (hq1 : q ≤ 1) (x y : Space d) :
    ∫ ω, replyY G π θ q x y ω ∂unif = hardGy G π x y := by
  unfold replyY
  rw [integral_add (integrable_const _) ((coin_integrable _).smul_const _), integral_const,
    probReal_univ, one_smul, integral_smul_const,
    coin_integral _ (qOf_pos G hq0 _) (qOf_le G hq1 _), one_smul]
  abel

lemma reply_sq_eq (x y : Space d) (ω : ℝ) :
    ‖replyX G π θ q x y ω - hardGx G π x y‖ ^ 2 + ‖replyY G π θ q x y ω - hardGy G π x y‖ ^ 2 =
      (coin (qOf G q (stage G π θ x y)) ω - 1) ^ 2 *
        (‖hardGx G π x y - knownGx G π (stage G π θ x y) x y‖ ^ 2 +
          ‖hardGy G π x y - knownGy G π (stage G π θ x y) x y‖ ^ 2) := by
  have h1 : replyX G π θ q x y ω - hardGx G π x y = (coin (qOf G q (stage G π θ x y)) ω - 1) •
      (hardGx G π x y - knownGx G π (stage G π θ x y) x y) := by
    unfold replyX
    rw [sub_smul, one_smul]
    abel
  have h2 : replyY G π θ q x y ω - hardGy G π x y = (coin (qOf G q (stage G π θ x y)) ω - 1) •
      (hardGy G π x y - knownGy G π (stage G π θ x y) x y) := by
    unfold replyY
    rw [sub_smul, one_smul]
    abel
  rw [h1, h2, norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

lemma reply_var_integrable (x y : Space d) :
    Integrable (fun ω => ‖replyX G π θ q x y ω - hardGx G π x y‖ ^ 2 +
      ‖replyY G π θ q x y ω - hardGy G π x y‖ ^ 2) unif := by
  have he : (fun ω => ‖replyX G π θ q x y ω - hardGx G π x y‖ ^ 2 +
      ‖replyY G π θ q x y ω - hardGy G π x y‖ ^ 2) = fun ω =>
      Set.indicator {ω | ω ≤ qOf G q (stage G π θ x y)}
        (fun _ => ((1 / qOf G q (stage G π θ x y) - 1) ^ 2 - 1) *
          (‖hardGx G π x y - knownGx G π (stage G π θ x y) x y‖ ^ 2 +
            ‖hardGy G π x y - knownGy G π (stage G π θ x y) x y‖ ^ 2)) ω +
        (‖hardGx G π x y - knownGx G π (stage G π θ x y) x y‖ ^ 2 +
          ‖hardGy G π x y - knownGy G π (stage G π θ x y) x y‖ ^ 2) := by
    funext ω
    rw [reply_sq_eq]
    simp only [coin, Set.indicator, Set.mem_ofPred_eq]
    split_ifs <;> ring
  rw [he]
  exact ((integrable_const _).indicator (setOf_le_measurable _)).add (integrable_const _)

theorem reply_var_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθρ : θ ≤ G.ρ) (hθ2 : θ ≤ 1 / 2) (hq0 : 0 < q)
    (hq1 : q ≤ 1) (x y : Space d) :
    ∫ ω, (‖replyX G π θ q x y ω - hardGx G π x y‖ ^ 2 +
      ‖replyY G π θ q x y ω - hardGy G π x y‖ ^ 2) ∂unif ≤
      (1 / q - 1) * (2 ^ 23 * θ + 1 / (3 * ((G.n : ℝ) + 1) * G.ρ)) ^ 2 := by
  have he : (fun ω => ‖replyX G π θ q x y ω - hardGx G π x y‖ ^ 2 +
      ‖replyY G π θ q x y ω - hardGy G π x y‖ ^ 2) = fun ω =>
      (coin (qOf G q (stage G π θ x y)) ω - 1) ^ 2 *
        (‖hardGx G π x y - knownGx G π (stage G π θ x y) x y‖ ^ 2 +
          ‖hardGy G π x y - knownGy G π (stage G π θ x y) x y‖ ^ 2) :=
    funext fun ω => reply_sq_eq G π θ x y ω
  rw [he, integral_mul_const, coin_sq_integral _ (qOf_pos G hq0 _) (qOf_le G hq1 _)]
  have hq' : 0 ≤ 1 / q - 1 := by
    rw [sub_nonneg, le_div_iff₀ hq0]
    linarith
  have hW : 0 ≤ (2 ^ 23 * θ + 1 / (3 * ((G.n : ℝ) + 1) * G.ρ)) ^ 2 := sq_nonneg _
  by_cases hsk : stage G π θ x y < G.k + 1
  · by_cases hm : masked G (stage G π θ x y)
    · have hb := masked_bound G π hθ0 hθρ hθ2 (stage G π θ x y) hsk hm x y
        (fun p hp => not_big_of_stage G π θ x y p hp)
      unfold qOf
      rw [ite_eq_left hm]
      exact mul_le_mul_of_nonneg_left hb hq'
    · unfold qOf
      rw [ite_eq_right hm, div_one, sub_self, zero_mul]
      exact mul_nonneg hq' hW
  · have hsK : stage G π θ x y = G.k + 1 := by
      have := stage_le G π θ x y
      omega
    rw [hsK, known_full_x, known_full_y, sub_self, sub_self, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, mul_zero]
    exact mul_nonneg hq' hW

end Integrals

section Measurable

lemma continuous_of_sq_le {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E] (f : X → E)
    (K : ℝ) (h : ∀ z z', ‖f z' - f z‖ ^ 2 ≤ K * dist z' z ^ 2) : Continuous f := by
  rw [Metric.continuous_iff]
  intro z ε hε
  have hK : 0 < |K| + 1 := by positivity
  refine ⟨ε / (|K| + 1), div_pos hε hK, fun z' hz' => ?_⟩
  rw [dist_eq_norm]
  have hd0 : 0 ≤ dist z' z := dist_nonneg
  have h1 := h z z'
  have h2 : K * dist z' z ^ 2 ≤ |K| * dist z' z ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self K) (sq_nonneg _)
  have h3 : dist z' z ^ 2 ≤ (ε / (|K| + 1)) ^ 2 := pow_le_pow_left₀ hd0 hz'.le 2
  have h4 : |K| * (ε / (|K| + 1)) ^ 2 < ε ^ 2 := by
    rw [div_pow, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
    have hk0 := abs_nonneg K
    have he2 : 0 < ε ^ 2 := by positivity
    nlinarith [mul_nonneg he2.le hk0, mul_nonneg he2.le (sq_nonneg |K|)]
  have h5 : ‖f z' - f z‖ ^ 2 < ε ^ 2 := by
    have := mul_le_mul_of_nonneg_left h3 (abs_nonneg K)
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 hε.le h5

lemma fst_le (z z' : Space d × Space d) : ‖z'.1 - z.1‖ ≤ dist z' z := by
  rw [← dist_eq_norm, Prod.dist_eq]
  exact le_max_left _ _

lemma snd_le (z z' : Space d × Space d) : ‖z'.2 - z.2‖ ≤ dist z' z := by
  rw [← dist_eq_norm, Prod.dist_eq]
  exact le_max_right _ _

lemma continuous_of_lip {E : Type*} [NormedAddCommGroup E] (f : Space d × Space d → E) (C : ℝ)
    (hC : 0 ≤ C) (h : ∀ z z', ‖f z' - f z‖ ≤ C * (‖z'.1 - z.1‖ + ‖z'.2 - z.2‖)) :
    Continuous f := by
  refine continuous_of_sq_le f ((2 * C) ^ 2) (fun z z' => ?_)
  have h1 := h z z'
  have h2 := fst_le z z'
  have h3 := snd_le z z'
  have h4 : ‖f z' - f z‖ ≤ 2 * C * dist z' z := by nlinarith
  have := pow_le_pow_left₀ (norm_nonneg _) h4 2
  rw [mul_pow] at this
  exact this

lemma ball_continuous {B : ℝ} (hB : 0 < B) : Continuous (ball (E := Space d) B) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  exact ball_lipschitz B hB u v

lemma cutv_continuous (B : ℝ) : Continuous (cutv B : Space d → ℝ) :=
  continuous_iff_continuousAt.mpr fun x => (cutv_hasGradientAt (B := B) x).continuousAt

lemma cutGrad_continuous {B : ℝ} (hB : 0 < B) : Continuous (cutGrad B : Space d → Space d) := by
  refine continuous_of_sq_le _ ((260 / B ^ 2) ^ 2) (fun z z' => ?_)
  have h := cutGrad_lip hB z' z
  rw [← dist_eq_norm z' z] at h
  have := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow] at this
  exact this

lemma trC_continuous {k : ℕ} (s : ℕ) : Continuous (trC (k := k) s) := by
  refine continuous_of_sq_le _ 1 (fun z z' => ?_)
  have h := trC_sub_norm s z z'
  rw [← dist_eq_norm z' z] at h
  have := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [one_mul]
  exact this

lemma chA_continuous : Continuous (fun z : Space d × Space d => chA G π z.1) := by
  refine continuous_of_lip _ 17 (by norm_num) (fun z z' => ?_)
  have h := chA_lip G π z.1 z'.1
  have := norm_nonneg (z'.2 - z.2)
  linarith

lemma yhat_continuous : Continuous (fun z : Space d × Space d => yhat G π z.2) := by
  have hB := G.hBy
  exact ((sel π).continuous.comp (ball_continuous (by positivity))).comp continuous_snd

lemma vecA_continuous (s : ℕ) : Continuous (fun z : Space d × Space d =>
    vecA G (trC s (chA G π z.1)) (trC s (yhat G π z.2)) (cutv G.By z.2)) := by
  have hBy := G.hBy
  refine continuous_of_sq_le _ (2 ^ 33 * 290 + 2 ^ 15 * ((G.m : ℝ) + 1) * (8 / G.By) ^ 2)
    (fun z z' => ?_)
  have h := vecA_lip_sq G (trC s (chA G π z.1)) (trC s (chA G π z'.1)) (trC s (yhat G π z.2))
    (trC s (yhat G π z'.2)) (c := cutv G.By z.2) (c' := cutv G.By z'.2) (cutv_abs G.By z'.2)
  have h1 := (trC_sub_norm s (chA G π z.1) (chA G π z'.1)).trans (chA_lip G π z.1 z'.1)
  have h2 := (trC_sub_norm s (yhat G π z.2) (yhat G π z'.2)).trans
    ((sel_sub_norm π _ _).trans (ball_lipschitz (2 * G.By) (by positivity) z'.2 z.2))
  have h3 := cutv_lip hBy z'.2 z.2
  have hf := fst_le z z'
  have hs := snd_le z z'
  have hd0 : 0 ≤ dist z' z := dist_nonneg
  have a1 : ‖trC s (chA G π z'.1) - trC s (chA G π z.1)‖ ^ 2 ≤ 289 * dist z' z ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) (h1.trans (mul_le_mul_of_nonneg_left hf
      (by norm_num))) 2
    rw [mul_pow] at this
    linarith
  have a2 : ‖trC s (yhat G π z'.2) - trC s (yhat G π z.2)‖ ^ 2 ≤ dist z' z ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (h2.trans hs) 2
  have a3 : (cutv G.By z'.2 - cutv G.By z.2) ^ 2 ≤ (8 / G.By) ^ 2 * dist z' z ^ 2 := by
    have h8 : |cutv G.By z'.2 - cutv G.By z.2| ≤ 8 / G.By * dist z' z :=
      h3.trans (mul_le_mul_of_nonneg_left hs (by positivity))
    have := pow_le_pow_left₀ (abs_nonneg _) h8 2
    rw [sq_abs, mul_pow] at this
    exact this
  have hm0 : (0 : ℝ) ≤ 2 ^ 15 * ((G.m : ℝ) + 1) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left a3 hm0]

lemma vecB_continuous (s : ℕ) : Continuous (fun z : Space d × Space d =>
    vecB G (trC s (chA G π z.1)) (trC s (yhat G π z.2))) := by
  have hBy := G.hBy
  refine continuous_of_sq_le _ (2 ^ 25 * 290) (fun z z' => ?_)
  have h := vecB_lip_sq G (trC s (chA G π z.1)) (trC s (chA G π z'.1)) (trC s (yhat G π z.2))
    (trC s (yhat G π z'.2))
  have h1 := (trC_sub_norm s (chA G π z.1) (chA G π z'.1)).trans (chA_lip G π z.1 z'.1)
  have h2 := (trC_sub_norm s (yhat G π z.2) (yhat G π z'.2)).trans
    ((sel_sub_norm π _ _).trans (ball_lipschitz (2 * G.By) (by positivity) z'.2 z.2))
  have hf := fst_le z z'
  have hs := snd_le z z'
  have a1 : ‖trC s (chA G π z'.1) - trC s (chA G π z.1)‖ ^ 2 ≤ 289 * dist z' z ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) (h1.trans (mul_le_mul_of_nonneg_left hf
      (by norm_num))) 2
    rw [mul_pow] at this
    linarith
  have a2 : ‖trC s (yhat G π z'.2) - trC s (yhat G π z.2)‖ ^ 2 ≤ dist z' z ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (h2.trans hs) 2
  linarith

lemma AK_continuous (s : ℕ) : Continuous (fun z : Space d × Space d => AK G π s z.1 z.2) :=
  (trC_continuous s).comp (vecA_continuous G π s)

lemma BK_continuous (s : ℕ) : Continuous (fun z : Space d × Space d => BK G π s z.1 z.2) :=
  (trC_continuous s).comp (vecB_continuous G π s)

lemma RK_continuous (s : ℕ) : Continuous (fun z : Space d × Space d => RK G π s z.1 z.2) := by
  have hBy := G.hBy
  refine continuous_of_sq_le _ ((19 * G.By) ^ 2) (fun z z' => ?_)
  have h1 := rF_lip_b G (seq (trC s (chA G π z'.1))) (trC s (yhat G π z.2))
    (trC s (yhat G π z'.2))
  have h2 := rF_lip_a G (seq (trC s (yhat G π z.2))) (trC s (chA G π z.1))
    (trC s (chA G π z'.1))
  have hA := (trC_sub_norm s (chA G π z.1) (chA G π z'.1)).trans (chA_lip G π z.1 z'.1)
  have hY := (trC_sub_norm s (yhat G π z.2) (yhat G π z'.2)).trans
    ((sel_sub_norm π _ _).trans (ball_lipschitz (2 * G.By) (by positivity) z'.2 z.2))
  have hf := fst_le z z'
  have hs := snd_le z z'
  have e : RK G π s z'.1 z'.2 - RK G π s z.1 z.2 =
      (rF G.m G.n G.r (seq (trC s (chA G π z'.1))) (seq (trC s (yhat G π z'.2))) -
        rF G.m G.n G.r (seq (trC s (chA G π z'.1))) (seq (trC s (yhat G π z.2)))) +
      (rF G.m G.n G.r (seq (trC s (chA G π z'.1))) (seq (trC s (yhat G π z.2))) -
        rF G.m G.n G.r (seq (trC s (chA G π z.1))) (seq (trC s (yhat G π z.2)))) := by
    unfold RK
    ring
  have hb : |RK G π s z'.1 z'.2 - RK G π s z.1 z.2| ≤ 19 * G.By * dist z' z := by
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have t1 := mul_le_mul_of_nonneg_left hY (by positivity : (0 : ℝ) ≤ 2 * G.By)
    have t2 := mul_le_mul_of_nonneg_left hA hBy.le
    have hd0 : 0 ≤ dist z' z := dist_nonneg
    nlinarith
  have := pow_le_pow_left₀ (abs_nonneg _) hb 2
  rw [mul_pow] at this
  rw [Real.norm_eq_abs]
  exact this

lemma hardGx_continuous : Continuous (fun z : Space d × Space d => hardGx G π z.1 z.2) :=
  continuous_of_lip _ (2 ^ 26) (by norm_num) (fun z z' => hardGx_lip G π z.1 z.2 z'.1 z'.2)

lemma hardGy_continuous : Continuous (fun z : Space d × Space d => hardGy G π z.1 z.2) :=
  continuous_of_lip _ (2 ^ 26) (by norm_num) (fun z z' => hardGy_lip G π z.1 z.2 z'.1 z'.2)

lemma knownGx_continuous (s : ℕ) :
    Continuous (fun z : Space d × Space d => knownGx G π s z.1 z.2) := by
  have hA := AK_continuous G π s
  have hcx : Continuous (fun z : Space d × Space d => cutv G.Bx z.1) :=
    (cutv_continuous G.Bx).comp continuous_fst
  have hcg : Continuous (fun z : Space d × Space d => cutGrad G.Bx z.1) :=
    (cutGrad_continuous G.hBx).comp continuous_fst
  have hx : Continuous (fun z : Space d × Space d => z.1) := continuous_fst
  have h1 : Continuous (fun z : Space d × Space d => (1 / 16 : ℝ) • z.1) :=
    (continuous_const (y := (1 / 16 : ℝ))).smul hx
  have h2 : Continuous (fun z : Space d × Space d =>
      cutv G.Bx z.1 • (sel π).adjoint (AK G π s z.1 z.2)) :=
    hcx.smul ((sel π).adjoint.continuous.comp hA)
  have hS : Continuous (fun z : Space d × Space d => sel π z.1) := (sel π).continuous.comp hx
  have h3 : Continuous (fun z : Space d × Space d => ⟪AK G π s z.1 z.2, sel π z.1⟫) :=
    hA.inner hS
  have h4 : Continuous (fun z : Space d × Space d =>
      ⟪AK G π s z.1 z.2, sel π z.1⟫ • cutGrad G.Bx z.1) := h3.smul hcg
  exact (h1.add h2).add h4

lemma baseGrad_continuous (lam ρ : ℝ) (hlam : 0 ≤ lam) :
    Continuous (baseGrad lam ρ : Space d → Space d) := by
  refine continuous_of_sq_le _ ((lam + 1) ^ 2) (fun z z' => ?_)
  have h := baseGrad_lip hlam ρ z' z
  rw [← dist_eq_norm z' z] at h
  have := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow] at this
  exact this

lemma knownGy_continuous (s : ℕ) :
    Continuous (fun z : Space d × Space d => knownGy G π s z.1 z.2) := by
  have hB := BK_continuous G π s
  have hR := RK_continuous G π s
  have hcy : Continuous (fun z : Space d × Space d => cutv G.By z.2) :=
    (cutv_continuous G.By).comp continuous_snd
  have hcg : Continuous (fun z : Space d × Space d => cutGrad G.By z.2) :=
    (cutGrad_continuous G.hBy).comp continuous_snd
  have hb : Continuous (fun z : Space d × Space d => baseGrad (lamOf G.n) G.ρ z.2) :=
    (baseGrad_continuous (lamOf G.n) G.ρ (lamOf_pos G.n).le).comp continuous_snd
  have h2 : Continuous (fun z : Space d × Space d =>
      cutv G.By z.2 • (sel π).adjoint (BK G π s z.1 z.2)) :=
    hcy.smul ((sel π).adjoint.continuous.comp hB)
  have h3 : Continuous (fun z : Space d × Space d => RK G π s z.1 z.2 • cutGrad G.By z.2) :=
    hR.smul hcg
  exact (hb.add h2).add h3

lemma stage_measurable (θ : ℝ) :
    Measurable (fun z : Space d × Space d => stage G π θ z.1 z.2) := by
  have hBx := G.hBx
  have hBy := G.hBy
  have hne : (Finset.univ : Finset (Fin (G.k + 1))).Nonempty := Finset.univ_nonempty
  have he : (fun z : Space d × Space d => stage G π θ z.1 z.2) = Finset.univ.sup' hne
      (fun (p : Fin (G.k + 1)) (z : Space d × Space d) =>
        if big G θ z.1 z.2 (π p) then p.val + 1 else 0) := by
    funext z
    rw [Finset.sup'_apply, Finset.sup'_eq_sup]
    rfl
  rw [he]
  apply Finset.measurable_sup'
  intro p _
  apply Measurable.ite _ measurable_const measurable_const
  apply measurableSet_lt measurable_const
  have hc : Continuous (fun z : Space d × Space d => |obsVec G z.1 z.2 (π p)|) := by
    have h1 : Continuous (fun z : Space d × Space d => |ball (2 * G.Bx) z.1 (π p)|) :=
      continuous_abs.comp ((PiLp.continuous_apply 2 _ (π p)).comp
        ((ball_continuous (by positivity)).comp continuous_fst))
    have h2 : Continuous (fun z : Space d × Space d => |ball (2 * G.By) z.2 (π p)|) :=
      continuous_abs.comp ((PiLp.continuous_apply 2 _ (π p)).comp
        ((ball_continuous (by positivity)).comp continuous_snd))
    exact continuous_abs.comp (h1.max h2)
  exact hc.measurable

theorem replyX_measurable (θ q : ℝ) :
    Measurable (Function.uncurry (fun (w : Space d × Space d) (ω : ℝ) =>
      replyX G π θ q w.1 w.2 ω)) := by
  let F : ((Space d × Space d) × ℝ) × ℕ → Space d := fun p =>
    knownGx G π p.2 p.1.1.1 p.1.1.2 + coin (qOf G q p.2) p.1.2 •
      (hardGx G π p.1.1.1 p.1.1.2 - knownGx G π p.2 p.1.1.1 p.1.1.2)
  have hF : Measurable F := by
    apply measurable_from_prod_countable_left
    intro s
    have hk : Measurable (fun z : (Space d × Space d) × ℝ => knownGx G π s z.1.1 z.1.2) :=
      ((knownGx_continuous G π s).comp continuous_fst).measurable
    have hh : Measurable (fun z : (Space d × Space d) × ℝ => hardGx G π z.1.1 z.1.2) :=
      ((hardGx_continuous G π).comp continuous_fst).measurable
    have hq : Measurable (fun z : (Space d × Space d) × ℝ => coin (qOf G q s) z.2) :=
      (coin_measurable _).comp measurable_snd
    exact hk.add (hq.smul (hh.sub hk))
  have he : Function.uncurry (fun (w : Space d × Space d) (ω : ℝ) => replyX G π θ q w.1 w.2 ω) =
      F ∘ (fun z : (Space d × Space d) × ℝ => (z, stage G π θ z.1.1 z.1.2)) := by
    funext z
    rfl
  rw [he]
  exact hF.comp (measurable_id.prodMk ((stage_measurable G π θ).comp measurable_fst))

theorem replyY_measurable (θ q : ℝ) :
    Measurable (Function.uncurry (fun (w : Space d × Space d) (ω : ℝ) =>
      replyY G π θ q w.1 w.2 ω)) := by
  let F : ((Space d × Space d) × ℝ) × ℕ → Space d := fun p =>
    knownGy G π p.2 p.1.1.1 p.1.1.2 + coin (qOf G q p.2) p.1.2 •
      (hardGy G π p.1.1.1 p.1.1.2 - knownGy G π p.2 p.1.1.1 p.1.1.2)
  have hF : Measurable F := by
    apply measurable_from_prod_countable_left
    intro s
    have hk : Measurable (fun z : (Space d × Space d) × ℝ => knownGy G π s z.1.1 z.1.2) :=
      ((knownGy_continuous G π s).comp continuous_fst).measurable
    have hh : Measurable (fun z : (Space d × Space d) × ℝ => hardGy G π z.1.1 z.1.2) :=
      ((hardGy_continuous G π).comp continuous_fst).measurable
    have hq : Measurable (fun z : (Space d × Space d) × ℝ => coin (qOf G q s) z.2) :=
      (coin_measurable _).comp measurable_snd
    exact hk.add (hq.smul (hh.sub hk))
  have he : Function.uncurry (fun (w : Space d × Space d) (ω : ℝ) => replyY G π θ q w.1 w.2 ω) =
      F ∘ (fun z : (Space d × Space d) × ℝ => (z, stage G π θ z.1.1 z.1.2)) := by
    funext z
    rfl
  rw [he]
  exact hF.comp (measurable_id.prodMk ((stage_measurable G π θ).comp measurable_fst))

end Measurable

end LongTails.Proofs.NcPlOracleStats
