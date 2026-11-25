import LongTails.Proofs.NcPlInstance

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.NcPlLipschitz

open LongTails.Proofs.AbcChainProfiles LongTails.Proofs.NcPlCalc
open LongTails.Proofs.NcPlBlockSmooth LongTails.Proofs.NcPlChain
open LongTails.Proofs.NcPlChainPL LongTails.Proofs.NcPlFlat LongTails.Proofs.NcPlCut
open LongTails.Proofs.NcPlInstance
open LongTails.Proofs.AbcChain (Chain)
open LongTails.Proofs.AbcHardFunction (Space sel sel_apply sel_norm adjoint_norm)
open LongTails.Proofs.MintyChainGeometry (ball ball_norm_le ball_lipschitz ball_of_le)

lemma sel_sub_norm {k d : ℕ} (π : Fin (k + 1) ↪ Fin d) (y y' : Space d) :
    ‖sel π y' - sel π y‖ ≤ ‖y' - y‖ := by
  rw [← map_sub]
  exact sel_norm π _

variable (G : Geo) {d : ℕ} (π : Fin (G.k + 1) ↪ Fin d)

lemma geo_hM : 2 ^ 19 * ((G.m : ℝ) + 1) ≤ G.By ^ 2 := by
  have h := G.hByM
  have hn : (0 : ℝ) ≤ G.n := Nat.cast_nonneg _
  have hm : (0 : ℝ) ≤ G.m := Nat.cast_nonneg _
  nlinarith


lemma chA_eq_ball (x : Space d) :
    chA G π x = cutv G.Bx x • sel π (ball (2 * G.Bx) x) :=
  cutv_smul_ball G.hBx (fun x => sel π x) x

lemma chA_lip (x x' : Space d) : ‖chA G π x' - chA G π x‖ ≤ 17 * ‖x' - x‖ := by
  have hB := G.hBx
  rw [chA_eq_ball, chA_eq_ball]
  refine (norm_smul_sub_le _ _ _ _).trans ?_
  have h1 := cutv_lip hB x' x
  have h2 : ‖sel π (ball (2 * G.Bx) x')‖ ≤ 2 * G.Bx :=
    (sel_norm π _).trans (ball_norm_le _ (by positivity) _)
  have h3 := cutv_abs G.Bx x
  have h4 : ‖sel π (ball (2 * G.Bx) x') - sel π (ball (2 * G.Bx) x)‖ ≤ ‖x' - x‖ :=
    (sel_sub_norm π _ _).trans (ball_lipschitz _ (by positivity) _ _)
  have t1 := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  have t2 := mul_le_mul h3 h4 (norm_nonneg _) zero_le_one
  have e : 8 / G.Bx * ‖x' - x‖ * (2 * G.Bx) = 16 * ‖x' - x‖ := by
    field_simp
    ring
  linarith

lemma gAvec_sq (a : Chain G.k) (b : ℕ → ℝ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ‖(WithLp.toLp 2 (fun p : Fin (G.k + 1) => gA G.m G.n G.r (seq a) b c p) : Chain G.k)‖ ^ 2 ≤
      2 ^ 16 * ((G.m : ℝ) + 1) := by
  rw [norm_sq_toLp]
  have h := gA_sq_le (m := G.m) (n := G.n) (r := G.r) hc0 hc1 (seq a) b
  rw [← G.hk, Finset.sum_range] at h
  exact h

lemma gAvec_norm (a : Chain G.k) (b : ℕ → ℝ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ‖(WithLp.toLp 2 (fun p : Fin (G.k + 1) => gA G.m G.n G.r (seq a) b c p) : Chain G.k)‖ ≤
      G.By / 2 := by
  have h := gAvec_sq G a b hc0 hc1
  have hM := geo_hM G
  have hB := G.hBy
  have h2 : ‖(WithLp.toLp 2 (fun p : Fin (G.k + 1) => gA G.m G.n G.r (seq a) b c p) :
      Chain G.k)‖ ^ 2 ≤ (G.By / 2) ^ 2 := by
    have e : (G.By / 2) ^ 2 = G.By ^ 2 / 4 := by ring
    rw [e, le_div_iff₀ (by norm_num)]
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

lemma gBvec_norm (a : ℕ → ℝ) (b : Chain G.k) :
    ‖(WithLp.toLp 2 (fun p : Fin (G.k + 1) => gB G.n G.r a (seq b) p) : Chain G.k)‖ ≤
      2 * G.By := by
  have hM := geo_hM G
  have hB := G.hBy
  have h := gB_sq_le (m := G.m) G.scales a (seq b)
  rw [← G.hk, Finset.sum_range] at h
  have h2 : ‖(WithLp.toLp 2 (fun p : Fin (G.k + 1) => gB G.n G.r a (seq b) p) :
      Chain G.k)‖ ^ 2 ≤ (2 * G.By) ^ 2 := by
    rw [norm_sq_toLp]
    have e : (2 * G.By) ^ 2 = 4 * G.By ^ 2 := by ring
    rw [e]
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

lemma gAvec_norm_Bx (a : Chain G.k) (b : ℕ → ℝ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ‖(WithLp.toLp 2 (fun p : Fin (G.k + 1) => gA G.m G.n G.r (seq a) b c p) : Chain G.k)‖ ≤
      G.Bx / 2 ^ 12 := by
  have h := gAvec_sq G a b hc0 hc1
  have hB := G.hBxM
  have hB0 := G.hBx
  have h2 : ‖(WithLp.toLp 2 (fun p : Fin (G.k + 1) => gA G.m G.n G.r (seq a) b c p) :
      Chain G.k)‖ ^ 2 ≤ (G.Bx / 2 ^ 12) ^ 2 := by
    have e : (G.Bx / 2 ^ 12) ^ 2 = G.Bx ^ 2 / 2 ^ 24 := by ring
    rw [e, le_div_iff₀ (by norm_num)]
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

lemma vA_norm_Bx (x y : Space d) : ‖vA G π x y‖ ≤ G.Bx / 2 ^ 8 := by
  have h := gAvec_norm_Bx G (chA G π x) (seq (sel π y)) (cutv_nonneg G.By y)
    (cutv_le_one G.By y)
  have hB0 := G.hBx
  have e : G.Bx / 2 ^ 12 ≤ G.Bx / 2 ^ 8 :=
    div_le_div_of_nonneg_left hB0.le (by norm_num) (by norm_num)
  exact h.trans e

lemma thetaA_lip_Bx (b : ℕ → ℝ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (a a' : Chain G.k) :
    |theta G.m G.n G.r (seq a') b c - theta G.m G.n G.r (seq a) b c| ≤
      G.Bx / 2 ^ 12 * ‖a' - a‖ :=
  lipschitz_of_grad_bound (fun a : Chain G.k => theta G.m G.n G.r (seq a) b c)
    (fun a => WithLp.toLp 2 (fun p : Fin (G.k + 1) => gA G.m G.n G.r (seq a) b c p))
    (G.Bx / 2 ^ 12) (fun a => thetaA_hasGradientAt G b hc0 hc1 a)
    (fun a => gAvec_norm_Bx G a b hc0 hc1) a' a

lemma geo_Bx_ge : 4 ≤ G.Bx := by
  have h := G.hBxM
  have h0 := G.hBx
  have hm : (0 : ℝ) ≤ G.m := Nat.cast_nonneg _
  by_contra hlt
  have : G.Bx < 4 := not_le.mp hlt
  nlinarith

lemma vB_norm (x y : Space d) : ‖vB G π x y‖ ≤ 2 * G.By :=
  gBvec_norm G (seq (chA G π x)) (sel π y)

lemma vA_lip (x y x' y' : Space d) :
    ‖vA G π x' y' - vA G π x y‖ ≤ 2 ^ 21 * (‖x' - x‖ + ‖y' - y‖) := by
  have hM := geo_hM G
  have hBy := G.hBy
  have h := gA_lip (m := G.m) G.scales (c := cutv G.By y) (c' := cutv G.By y')
    (cutv_abs G.By y') (seq (chA G π x)) (seq (chA G π x')) (seq (sel π y)) (seq (sel π y'))
  rw [← G.hk, sum_seq_sq, sum_seq_sq, Finset.sum_range] at h
  have e : ‖vA G π x' y' - vA G π x y‖ ^ 2 = ∑ p : Fin (G.k + 1),
      (gA G.m G.n G.r (seq (chA G π x')) (seq (sel π y')) (cutv G.By y') p -
        gA G.m G.n G.r (seq (chA G π x)) (seq (sel π y)) (cutv G.By y) p) ^ 2 :=
    norm_sub_sq_eq _ _
  have hA := chA_lip G π x x'
  have hS := sel_sub_norm π y y'
  have hc := cutv_lip hBy y' y
  have hx0 := norm_nonneg (x' - x)
  have hy0 := norm_nonneg (y' - y)
  have hA2 : ‖chA G π x' - chA G π x‖ ^ 2 ≤ 289 * ‖x' - x‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hA 2
    nlinarith
  have hS2 : ‖sel π y' - sel π y‖ ^ 2 ≤ ‖y' - y‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hS 2
  have h8 : |cutv G.By y' - cutv G.By y| * G.By ≤ 8 * ‖y' - y‖ := by
    have := mul_le_mul_of_nonneg_right hc hBy.le
    have e2 : 8 / G.By * ‖y' - y‖ * G.By = 8 * ‖y' - y‖ := by
      field_simp
    linarith
  have hc2 : (cutv G.By y' - cutv G.By y) ^ 2 * G.By ^ 2 ≤ 64 * ‖y' - y‖ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) h8 2
    rw [mul_pow, sq_abs] at this
    nlinarith
  have hc3 : 2 ^ 19 * (((G.m : ℝ) + 1) * (cutv G.By y' - cutv G.By y) ^ 2) ≤
      64 * ‖y' - y‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_right hM (sq_nonneg (cutv G.By y' - cutv G.By y))
    nlinarith
  have hfin : ‖vA G π x' y' - vA G π x y‖ ^ 2 ≤ (2 ^ 21 * (‖x' - x‖ + ‖y' - y‖)) ^ 2 := by
    rw [e]
    have hxy := mul_nonneg hx0 hy0
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hfin

lemma vB_lip (x y x' y' : Space d) :
    ‖vB G π x' y' - vB G π x y‖ ≤ 2 ^ 17 * (‖x' - x‖ + ‖y' - y‖) := by
  have h := gB_lip (m := G.m) G.scales (seq (chA G π x)) (seq (chA G π x')) (seq (sel π y))
    (seq (sel π y'))
  rw [← G.hk, sum_seq_sq, sum_seq_sq, Finset.sum_range] at h
  have e : ‖vB G π x' y' - vB G π x y‖ ^ 2 = ∑ p : Fin (G.k + 1),
      (gB G.n G.r (seq (chA G π x')) (seq (sel π y')) p -
        gB G.n G.r (seq (chA G π x)) (seq (sel π y)) p) ^ 2 :=
    norm_sub_sq_eq _ _
  have hA := chA_lip G π x x'
  have hS := sel_sub_norm π y y'
  have hx0 := norm_nonneg (x' - x)
  have hy0 := norm_nonneg (y' - y)
  have hA2 : ‖chA G π x' - chA G π x‖ ^ 2 ≤ 289 * ‖x' - x‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hA 2
    nlinarith
  have hS2 : ‖sel π y' - sel π y‖ ^ 2 ≤ ‖y' - y‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hS 2
  have hfin : ‖vB G π x' y' - vB G π x y‖ ^ 2 ≤ (2 ^ 17 * (‖x' - x‖ + ‖y' - y‖)) ^ 2 := by
    rw [e]
    have hxy := mul_nonneg hx0 hy0
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hfin

lemma thetaA_lip (b : ℕ → ℝ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (a a' : Chain G.k) :
    |theta G.m G.n G.r (seq a') b c - theta G.m G.n G.r (seq a) b c| ≤ G.By / 2 * ‖a' - a‖ :=
  lipschitz_of_grad_bound (fun a : Chain G.k => theta G.m G.n G.r (seq a) b c)
    (fun a => WithLp.toLp 2 (fun p : Fin (G.k + 1) => gA G.m G.n G.r (seq a) b c p)) (G.By / 2)
    (fun a => thetaA_hasGradientAt G b hc0 hc1 a) (fun a => gAvec_norm G a b hc0 hc1) a' a

lemma rF_lip_a (b : ℕ → ℝ) (a a' : Chain G.k) :
    |rF G.m G.n G.r (seq a') b - rF G.m G.n G.r (seq a) b| ≤ G.By * ‖a' - a‖ := by
  have h1 := thetaA_lip G b zero_le_one le_rfl a a'
  have h0 := thetaA_lip G b le_rfl zero_le_one a a'
  have e : rF G.m G.n G.r (seq a') b - rF G.m G.n G.r (seq a) b =
      (theta G.m G.n G.r (seq a') b 1 - theta G.m G.n G.r (seq a) b 1) -
        (theta G.m G.n G.r (seq a') b 0 - theta G.m G.n G.r (seq a) b 0) := by
    unfold theta
    ring
  rw [e]
  refine (abs_sub_le_sum _ _).trans ?_
  linarith

lemma rF_lip_b (a : ℕ → ℝ) (b b' : Chain G.k) :
    |rF G.m G.n G.r a (seq b') - rF G.m G.n G.r a (seq b)| ≤ 2 * G.By * ‖b' - b‖ :=
  lipschitz_of_grad_bound (fun b : Chain G.k => rF G.m G.n G.r a (seq b))
    (fun b => WithLp.toLp 2 (fun p : Fin (G.k + 1) => gB G.n G.r a (seq b) p)) (2 * G.By)
    (fun b => rB_hasGradientAt G a b) (fun b => gBvec_norm G a b) b' b

lemma rVal_nonneg (x y : Space d) : 0 ≤ rVal G π x y := rF_nonneg _ _

lemma rVal_le (x y : Space d) : rVal G π x y ≤ 6 * ((G.m : ℝ) + 1) :=
  (rF_le_cF _ _).trans (cF_le _)

lemma rVal_lip (x y x' y' : Space d) :
    |rVal G π x' y' - rVal G π x y| ≤ 17 * G.By * (‖x' - x‖ + ‖y' - y‖) := by
  have hBy := G.hBy
  have h1 := rF_lip_b G (seq (chA G π x')) (sel π y) (sel π y')
  have h2 := rF_lip_a G (seq (sel π y)) (chA G π x) (chA G π x')
  have hA := chA_lip G π x x'
  have hS := sel_sub_norm π y y'
  have e : rVal G π x' y' - rVal G π x y =
      (rF G.m G.n G.r (seq (chA G π x')) (seq (sel π y')) -
        rF G.m G.n G.r (seq (chA G π x')) (seq (sel π y))) +
      (rF G.m G.n G.r (seq (chA G π x')) (seq (sel π y)) -
        rF G.m G.n G.r (seq (chA G π x)) (seq (sel π y))) := by
    unfold rVal
    ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have t1 := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ 2 * G.By)
  have t2 := mul_le_mul_of_nonneg_left hA hBy.le
  have hx0 := norm_nonneg (x' - x)
  have hy0 := norm_nonneg (y' - y)
  nlinarith

lemma inner_sub_abs_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (a a' u u' : F) : |⟪a', u'⟫ - ⟪a, u⟫| ≤ ‖a' - a‖ * ‖u'‖ + ‖a‖ * ‖u' - u‖ := by
  have e : ⟪a', u'⟫ - ⟪a, u⟫ = ⟪a' - a, u'⟫ + ⟪a, u' - u⟫ := by
    rw [inner_sub_left, inner_sub_right]
    ring
  rw [e]
  exact (abs_add_le _ _).trans
    (add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _))

theorem hardGx_lip (x y x' y' : Space d) :
    ‖hardGx G π x' y' - hardGx G π x y‖ ≤ 2 ^ 26 * (‖x' - x‖ + ‖y' - y‖) := by
  have hB := G.hBx
  have hx0 := norm_nonneg (x' - x)
  have hy0 := norm_nonneg (y' - y)
  have hvl := vA_lip G π x y x' y'
  have hvn := vA_norm_Bx G π x y
  have hvn' := vA_norm_Bx G π x' y'
  have hadj : ‖(sel π).adjoint (vA G π x' y') - (sel π).adjoint (vA G π x y)‖ ≤
      2 ^ 21 * (‖x' - x‖ + ‖y' - y‖) := by
    rw [← map_sub]
    exact (adjoint_norm π _).trans hvl
  have hT2 : ‖cutv G.Bx x' • (sel π).adjoint (vA G π x' y') -
      cutv G.Bx x • (sel π).adjoint (vA G π x y)‖ ≤
      ‖x' - x‖ / 32 + 2 ^ 21 * (‖x' - x‖ + ‖y' - y‖) := by
    refine (norm_smul_sub_le _ _ _ _).trans ?_
    have h1 := cutv_lip hB x' x
    have h2 := (adjoint_norm π (vA G π x' y')).trans hvn'
    have h3 := cutv_abs G.Bx x
    have t1 := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    have t2 := mul_le_mul h3 hadj (norm_nonneg _) zero_le_one
    have e : 8 / G.Bx * ‖x' - x‖ * (G.Bx / 2 ^ 8) = ‖x' - x‖ / 32 := by
      field_simp
      ring
    linarith
  have hb := ball_norm_le (2 * G.Bx) (by positivity) x
  have hb' := ball_norm_le (2 * G.Bx) (by positivity) x'
  have hbl := ball_lipschitz (2 * G.Bx) (by positivity) x' x
  have hs' : |⟪vA G π x' y', sel π (ball (2 * G.Bx) x')⟫ -
      ⟪vA G π x y, sel π (ball (2 * G.Bx) x)⟫| ≤
      2 ^ 21 * (‖x' - x‖ + ‖y' - y‖) * (2 * G.Bx) + G.Bx / 2 ^ 8 * ‖x' - x‖ := by
    refine (inner_sub_abs_le _ _ _ _).trans ?_
    have h1 := (sel_norm π (ball (2 * G.Bx) x')).trans hb'
    have h2 := (sel_sub_norm π (ball (2 * G.Bx) x) (ball (2 * G.Bx) x')).trans hbl
    have t1 := mul_le_mul hvl h1 (norm_nonneg _) (by positivity)
    have t2 := mul_le_mul hvn h2 (norm_nonneg _) (by positivity)
    linarith
  have hsn : |⟪vA G π x y, sel π (ball (2 * G.Bx) x)⟫| ≤ G.Bx / 2 ^ 8 * (2 * G.Bx) :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul hvn ((sel_norm π _).trans hb) (norm_nonneg _) (by positivity))
  have hT3 : ‖⟪vA G π x' y', sel π x'⟫ • cutGrad G.Bx x' -
      ⟪vA G π x y, sel π x⟫ • cutGrad G.Bx x‖ ≤
      2 ^ 25 * (‖x' - x‖ + ‖y' - y‖) + 3 * ‖x' - x‖ := by
    rw [smul_cutGrad_ball hB (fun z => ⟪vA G π x' y', sel π z⟫) x',
      smul_cutGrad_ball hB (fun z => ⟪vA G π x y, sel π z⟫) x]
    refine (norm_smul_sub_le _ _ _ _).trans ?_
    have h1 := cutGrad_norm_le hB x'
    have h2 := cutGrad_lip hB x' x
    have t1 := mul_le_mul hs' h1 (norm_nonneg _) (by positivity)
    have t2 := mul_le_mul hsn h2 (norm_nonneg _) (by positivity)
    have e1 : (2 ^ 21 * (‖x' - x‖ + ‖y' - y‖) * (2 * G.Bx) + G.Bx / 2 ^ 8 * ‖x' - x‖) *
        (8 / G.Bx) = 2 ^ 25 * (‖x' - x‖ + ‖y' - y‖) + ‖x' - x‖ / 32 := by
      field_simp
      ring
    have e2 : G.Bx / 2 ^ 8 * (2 * G.Bx) * (260 / G.Bx ^ 2 * ‖x' - x‖) = 260 / 128 * ‖x' - x‖ := by
      field_simp
      ring
    linarith
  have hT1 : ‖(1 / 16 : ℝ) • x' - (1 / 16 : ℝ) • x‖ ≤ ‖x' - x‖ / 16 := by
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by norm_num)]
    linarith
  have e : hardGx G π x' y' - hardGx G π x y =
      ((1 / 16 : ℝ) • x' - (1 / 16 : ℝ) • x) +
      (cutv G.Bx x' • (sel π).adjoint (vA G π x' y') -
        cutv G.Bx x • (sel π).adjoint (vA G π x y)) +
      (⟪vA G π x' y', sel π x'⟫ • cutGrad G.Bx x' -
        ⟪vA G π x y, sel π x⟫ • cutGrad G.Bx x) := by
    unfold hardGx
    abel
  rw [e]
  refine (norm_add₃_le).trans ?_
  linarith

theorem hardGy_lip (x y x' y' : Space d) :
    ‖hardGy G π x' y' - hardGy G π x y‖ ≤ 2 ^ 26 * (‖x' - x‖ + ‖y' - y‖) := by
  have hB := G.hBy
  have hM := geo_hM G
  have hx0 := norm_nonneg (x' - x)
  have hy0 := norm_nonneg (y' - y)
  have hvl := vB_lip G π x y x' y'
  have hvn' := vB_norm G π x' y'
  have hT1 := baseGrad_lip (lamOf_pos G.n).le G.ρ y' y
  have hl1 := lamOf_le_one G.n
  have hadj : ‖(sel π).adjoint (vB G π x' y') - (sel π).adjoint (vB G π x y)‖ ≤
      2 ^ 17 * (‖x' - x‖ + ‖y' - y‖) := by
    rw [← map_sub]
    exact (adjoint_norm π _).trans hvl
  have hT2 : ‖cutv G.By y' • (sel π).adjoint (vB G π x' y') -
      cutv G.By y • (sel π).adjoint (vB G π x y)‖ ≤
      16 * ‖y' - y‖ + 2 ^ 17 * (‖x' - x‖ + ‖y' - y‖) := by
    refine (norm_smul_sub_le _ _ _ _).trans ?_
    have h1 := cutv_lip hB y' y
    have h2 := (adjoint_norm π (vB G π x' y')).trans hvn'
    have h3 := cutv_abs G.By y
    have t1 := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    have t2 := mul_le_mul h3 hadj (norm_nonneg _) zero_le_one
    have e : 8 / G.By * ‖y' - y‖ * (2 * G.By) = 16 * ‖y' - y‖ := by
      field_simp
      ring
    linarith
  have hT3 : ‖rVal G π x' y' • cutGrad G.By y' - rVal G π x y • cutGrad G.By y‖ ≤
      136 * (‖x' - x‖ + ‖y' - y‖) + ‖y' - y‖ := by
    refine (norm_smul_sub_le _ _ _ _).trans ?_
    have h1 := rVal_lip G π x y x' y'
    have h2 := cutGrad_norm_le hB y'
    have h3 := cutGrad_lip hB y' y
    have h4 : |rVal G π x y| ≤ 6 * ((G.m : ℝ) + 1) := by
      rw [abs_of_nonneg (rVal_nonneg G π x y)]
      exact rVal_le G π x y
    have t1 := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    have t2 := mul_le_mul h4 h3 (norm_nonneg _) (by positivity)
    have e1 : 17 * G.By * (‖x' - x‖ + ‖y' - y‖) * (8 / G.By) =
        136 * (‖x' - x‖ + ‖y' - y‖) := by
      field_simp
      ring
    have e2 : 6 * ((G.m : ℝ) + 1) * (260 / G.By ^ 2 * ‖y' - y‖) ≤ ‖y' - y‖ := by
      have hB2 : (0 : ℝ) < G.By ^ 2 := by positivity
      have e3 : 6 * ((G.m : ℝ) + 1) * (260 / G.By ^ 2 * ‖y' - y‖) =
          1560 * ((G.m : ℝ) + 1) * ‖y' - y‖ / G.By ^ 2 := by
        field_simp
        ring
      rw [e3, div_le_iff₀ hB2]
      nlinarith
    linarith
  have e : hardGy G π x' y' - hardGy G π x y =
      (baseGrad (lamOf G.n) G.ρ y' - baseGrad (lamOf G.n) G.ρ y) +
      (cutv G.By y' • (sel π).adjoint (vB G π x' y') -
        cutv G.By y • (sel π).adjoint (vB G π x y)) +
      (rVal G π x' y' • cutGrad G.By y' - rVal G π x y • cutGrad G.By y) := by
    unfold hardGy
    abel
  rw [e]
  refine (norm_add₃_le).trans ?_
  nlinarith

end LongTails.Proofs.NcPlLipschitz
