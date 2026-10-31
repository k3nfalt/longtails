import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CappedProximalGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma centered_sum {ι : Type*} [Fintype ι] (w : ι → ℝ) (u : ι → E) (U : E)
    (hw : ∑ i, w i = 1) (hU : ∑ i, w i • u i = U) :
    ∑ i, w i • (u i - U) = 0 := by
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw, one_smul, hU,
    sub_self]

lemma centered_inner_sum {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (u g : ι → E) (U G : E)
    (hw : ∑ i, w i = 1) (hU : ∑ i, w i • u i = U) :
    ∑ i, w i * ⟪g i - G, u i - U⟫ = ∑ i, w i * ⟪g i, u i - U⟫ := by
  have hz : ∑ i, w i * ⟪G, u i - U⟫ = 0 := by
    simp only [← inner_smul_right, ← inner_sum, centered_sum w u U hw hU, inner_zero_right]
  simp only [inner_sub_left, mul_sub, Finset.sum_sub_distrib, hz, sub_zero]

lemma variance_decomposition {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (u : ι → E) (U v : E)
    (hw : ∑ i, w i = 1) (hU : ∑ i, w i • u i = U) :
    ∑ i, w i * ‖u i - v‖ ^ 2 =
      (∑ i, w i * ‖u i - U‖ ^ 2) + ‖U - v‖ ^ 2 := by
  have hz : ∑ i, w i * ⟪U - v, u i - U⟫ = 0 := by
    simp only [← inner_smul_right, ← inner_sum, centered_sum w u U hw hU, inner_zero_right]
  have he (i : ι) : w i * ‖u i - v‖ ^ 2 =
      w i * ‖u i - U‖ ^ 2 + 2 * (w i * ⟪U - v, u i - U⟫) +
        w i * ‖U - v‖ ^ 2 := by
    rw [show u i - v = (u i - U) + (U - v) by abel, norm_add_sq_real,
      real_inner_comm (u i - U) (U - v)]
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hz,
    ← Finset.sum_mul, hw]
  ring

lemma proximal_bregman_sum {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (u gu gx gU : ι → E) (fu fU : ι → ℝ)
    (U x g : E) (lam : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1)
    (hU : ∑ i, w i • u i = U)
    (hf : ∀ i, fu i - fU i ≤ ⟪gu i, u i - U⟫)
    (hs : ∀ i, gu i + lam • (u i - x) = gx i - g) :
    ∑ i, w i * (fu i - fU i - ⟪gU i, u i - U⟫) ≤
      (∑ i, w i * ⟪gx i - gU i, u i - U⟫) -
        lam * ∑ i, w i * ‖u i - U‖ ^ 2 := by
  have hz : ∑ i, w i * ⟪g + lam • (U - x), u i - U⟫ = 0 := by
    simp only [← inner_smul_right, ← inner_sum, centered_sum w u U hw hU,
      inner_zero_right]
  have hp (i : ι) :
      w i * (fu i - fU i - ⟪gU i, u i - U⟫) ≤
        w i * ⟪gx i - gU i, u i - U⟫ - lam * (w i * ‖u i - U‖ ^ 2) -
          w i * ⟪g + lam • (U - x), u i - U⟫ := by
    have he : gu i = gx i - g - lam • (u i - x) := by
      exact eq_sub_of_add_eq (hs i)
    have hi := mul_le_mul_of_nonneg_left (hf i) (hw0 i)
    rw [he] at hi
    have hd : u i - x = (u i - U) + (U - x) := by abel
    have hid := congrArg (fun t : ℝ => w i * lam * t)
      (real_inner_self_eq_norm_sq (u i - U))
    simp only [inner_sub_left] at hid
    simp only [hd, smul_add, inner_sub_left, inner_add_left, real_inner_smul_left] at hi ⊢
    nlinarith only [hi, hid]
  have ht := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hp i)
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, hz, sub_zero] using ht

lemma sum_inner_le {ι : Type*} [Fintype ι] (d v : ι → E) :
    ∑ i, ⟪d i, v i⟫ ≤
      Real.sqrt (∑ i, ‖d i‖ ^ 2) * Real.sqrt (∑ i, ‖v i‖ ^ 2) := by
  calc
    _ ≤ ∑ i, ‖d i‖ * ‖v i‖ := Finset.sum_le_sum (fun i _ => real_inner_le_norm _ _)
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖d i‖) (fun i => ‖v i‖)

lemma average_inner_le {ι : Type*} [Fintype ι] (d v : ι → E)
    {m : ℝ} (hm : 0 < m) :
    (1 / m) * ∑ i, ⟪d i, v i⟫ ≤
      Real.sqrt ((1 / m) * ∑ i, ‖d i‖ ^ 2) *
        Real.sqrt ((1 / m) * ∑ i, ‖v i‖ ^ 2) := by
  have h := mul_le_mul_of_nonneg_left (sum_inner_le d v) (le_of_lt (one_div_pos.mpr hm))
  convert h using 1
  simp only [one_div_mul_eq_div, Real.sqrt_div' _ hm.le, div_mul_div_comm,
    ← sq, Real.sq_sqrt hm.le]

lemma common_point_bregman_bound {ι : Type*} [Fintype ι]
    (u gu gx gU : ι → E) (fu fU : ι → ℝ) (U x g G : E)
    {m delta lam : ℝ} (hm : 0 < m) (hd : 0 ≤ delta)
    (hw : ∑ _i : ι, (1 / m) = 1) (hU : ∑ i, (1 / m) • u i = U)
    (hf : ∀ i, fu i - fU i ≤ ⟪gu i, u i - U⟫)
    (hs : ∀ i, gu i + lam • (u i - x) = gx i - g)
    (hdelta : (1 / m) * ∑ i, ‖(gx i - gU i) - G‖ ^ 2 ≤
      delta ^ 2 * ‖x - U‖ ^ 2) :
    (1 / m) * ∑ i, (fu i - fU i - ⟪gU i, u i - U⟫) ≤
      delta * ‖x - U‖ * Real.sqrt ((1 / m) * ∑ i, ‖u i - U‖ ^ 2) -
        lam * ((1 / m) * ∑ i, ‖u i - U‖ ^ 2) := by
  have hb := proximal_bregman_sum (fun _ : ι => 1 / m) u gu gx gU fu fU U x g lam
    (fun _ => le_of_lt (one_div_pos.mpr hm)) hw hU hf hs
  have he := centered_inner_sum (fun _ : ι => 1 / m) u (fun i => gx i - gU i) U G hw hU
  simp only [← Finset.mul_sum] at hb he
  rw [← he] at hb
  have hc := average_inner_le (fun i => (gx i - gU i) - G) (fun i => u i - U) hm
  have hr : Real.sqrt ((1 / m) * ∑ i, ‖(gx i - gU i) - G‖ ^ 2) ≤
      delta * ‖x - U‖ := by
    apply (Real.sqrt_le_left (mul_nonneg hd (norm_nonneg _))).2
    simpa only [mul_pow] using hdelta
  have ht := mul_le_mul_of_nonneg_right hr
    (Real.sqrt_nonneg ((1 / m) * ∑ i, ‖u i - U‖ ^ 2))
  linarith

lemma common_point_reverse_bregman_bound {ι : Type*} [Fintype ι]
    (u gu gx gU : ι → E) (fu fU : ι → ℝ) (U x g G : E)
    {m delta lam : ℝ} (hm : 0 < m) (hd : 0 ≤ delta)
    (hw : ∑ _i : ι, (1 / m) = 1) (hU : ∑ i, (1 / m) • u i = U)
    (hf : ∀ i, ⟪gU i, u i - U⟫ ≤ fu i - fU i)
    (hs : ∀ i, gu i + lam • (u i - x) = gx i - g)
    (hdelta : (1 / m) * ∑ i, ‖(gx i - gU i) - G‖ ^ 2 ≤
      delta ^ 2 * ‖x - U‖ ^ 2) :
    (1 / m) * (∑ i, (fU i - fu i - ⟪gu i, U - u i⟫)) ≤
      delta * ‖x - U‖ * Real.sqrt ((1 / m) * ∑ i, ‖u i - U‖ ^ 2) -
        lam * ((1 / m) * ∑ i, ‖u i - U‖ ^ 2) := by
  have hb := common_point_bregman_bound u gu gx gU
    (fun i => ⟪gu i, u i - U⟫) (fun _ => 0) U x g G hm hd hw hU
    (fun _ => by simp) hs hdelta
  have hi (i : ι) : fU i - fu i - ⟪gu i, U - u i⟫ ≤
      ⟪gu i, u i - U⟫ - 0 - ⟪gU i, u i - U⟫ := by
    have hh := hf i
    simp only [inner_sub_right] at hh ⊢
    linarith
  exact (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i _ => hi i)) (by positivity)).trans hb

lemma weighted_reverse_support {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (u gu : ι → E) (fu fU fv : ι → ℝ) (U v : E)
    (hw : ∀ i, 0 ≤ w i)
    (hf : ∀ i, fu i - fv i ≤ ⟪gu i, u i - v⟫) :
    (∑ i, w i * (fU i - fv i)) ≤
      ⟪∑ i, w i • gu i, U - v⟫ +
        ∑ i, w i * (fU i - fu i - ⟪gu i, U - u i⟫) := by
  have hi (i : ι) : w i * (fU i - fv i) ≤
      w i * ⟪gu i, U - v⟫ + w i * (fU i - fu i - ⟪gu i, U - u i⟫) := by
    have hh := mul_le_mul_of_nonneg_left (hf i) (hw i)
    simp only [inner_sub_right] at hh ⊢
    linarith
  have ht := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  simpa only [Finset.sum_add_distrib, sum_inner, real_inner_smul_left] using ht

lemma mean_proximal_gradient {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (u gu gx : ι → E) (U x g : E) (lam : ℝ)
    (hw : ∑ i, w i = 1) (hU : ∑ i, w i • u i = U)
    (hs : ∀ i, gu i + lam • (u i - x) = gx i - g) :
    (∑ i, w i • gu i) = (∑ i, w i • gx i) - g + lam • (x - U) := by
  have he (i : ι) : gu i = gx i - g - lam • (u i - x) := eq_sub_of_add_eq (hs i)
  simp_rw [he]
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw, one_smul,
    smul_comm (w _) lam, ← Finset.smul_sum, hU]
  module

lemma proximal_variance_bound {B V a delta lam : ℝ}
    (hB : 0 ≤ B) (hV : 0 ≤ V) (ha : 0 ≤ a) (hd : 0 ≤ delta) (hl : 0 < lam)
    (h : B ≤ delta * a * Real.sqrt V - lam * V) :
    V ≤ delta ^ 2 * a ^ 2 / lam ^ 2 := by
  have hs := Real.sq_sqrt hV
  have hn := Real.sqrt_nonneg V
  have hv : lam * Real.sqrt V ≤ delta * a := by
    by_cases hz : Real.sqrt V = 0
    · rw [hz, mul_zero]
      positivity
    · have hp : 0 < Real.sqrt V := lt_of_le_of_ne hn (Ne.symm hz)
      nlinarith
  apply (le_div_iff₀ (sq_pos_of_pos hl)).2
  nlinarith [sq_nonneg (delta * a - lam * Real.sqrt V),
    mul_nonneg (show 0 ≤ delta * a + lam * Real.sqrt V by positivity)
      (sub_nonneg.mpr hv)]

lemma sampled_primal_certificate {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (u gU gz : ι → E) (fu fU fz : ι → ℝ)
    (U z GU Gz : E) (FU Fz : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1)
    (hz : ∑ i, w i • u i = z)
    (hc : ∀ i, fz i - fu i ≤ ⟪gz i, z - u i⟫) :
    Fz - FU ≤ (∑ i, w i * (fu i - fU i - ⟪gU i, u i - U⟫)) +
      ⟪GU, z - U⟫ +
      (∑ i, w i * ⟪(Gz - gz i) - (GU - gU i), u i - U⟫) -
      ∑ i, w i * (FU - fU i - (Fz - fz i) - ⟪Gz - gz i, U - z⟫) := by
  have hcenter : ∑ i, w i * ⟪Gz, u i - z⟫ = 0 := by
    simp only [← inner_smul_right, ← inner_sum, centered_sum w u z hw hz,
      inner_zero_right]
  have hmean : ∑ i, w i * ⟪GU, u i - U⟫ = ⟪GU, z - U⟫ := by
    simp only [← inner_smul_right, ← inner_sum, smul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_smul, hw, one_smul, hz]
  have hi (i : ι) : w i * (Fz - FU) ≤
      w i * (fu i - fU i - ⟪gU i, u i - U⟫) +
      w i * ⟪GU, u i - U⟫ +
      w i * ⟪(Gz - gz i) - (GU - gU i), u i - U⟫ -
      w i * (FU - fU i - (Fz - fz i) - ⟪Gz - gz i, U - z⟫) -
      w i * ⟪Gz, u i - z⟫ := by
    have hh := mul_le_mul_of_nonneg_left (hc i) (hw0 i)
    simp only [inner_sub_left, inner_sub_right] at hh ⊢
    nlinarith only [hh]
  have ht := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  simpa only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
    hw, one_mul, hmean, hcenter, sub_zero] using ht

lemma leave_one_out_replacement (D : E → E) {z zm v : E} {K c : ℝ}
    (hc : 0 ≤ c) (hz : z - zm = c • v)
    (hD : ‖D z - D zm‖ ≤ K * ‖z - zm‖) :
    ⟪D z, v⟫ ≤ ⟪D zm, v⟫ + K * c * ‖v‖ ^ 2 := by
  have hi := real_inner_le_norm (D z - D zm) v
  have hn : ‖z - zm‖ = c * ‖v‖ := by
    rw [hz, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  have hm := mul_le_mul_of_nonneg_right hD (norm_nonneg v)
  rw [hn] at hm
  rw [inner_sub_left] at hi
  nlinarith only [hi, hm]

lemma sampled_covariance {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (z : ι → E) (U x v : E)
    (hw : ∑ i, w i = 1) (hU : ∑ i, w i • z i = U) :
    (∑ i, w i * ⟪x - z i, z i - v⟫) =
      ⟪x - U, U - v⟫ - ∑ i, w i * ‖z i - U‖ ^ 2 := by
  have hleft : ∑ i, w i * ⟪x - U, z i - U⟫ = 0 := by
    simp only [← inner_smul_right, ← inner_sum, centered_sum w z U hw hU,
      inner_zero_right]
  have hright : ∑ i, w i * ⟪z i - U, U - v⟫ = 0 := by
    simp only [← real_inner_smul_left, ← sum_inner, centered_sum w z U hw hU,
      inner_zero_left]
  have he (i : ι) : w i * ⟪x - z i, z i - v⟫ =
      w i * ⟪x - U, z i - U⟫ + w i * ⟪x - U, U - v⟫ -
      w i * ‖z i - U‖ ^ 2 - w i * ⟪z i - U, U - v⟫ := by
    rw [show x - z i = (x - U) - (z i - U) by abel,
      show z i - v = (z i - U) + (U - v) by abel]
    rw [inner_sub_left, inner_add_right, inner_add_right, real_inner_self_eq_norm_sq]
    ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    hleft, hright, ← Finset.sum_mul, hw]
  ring

lemma proximal_variance_absorption {delta lam a V : ℝ}
    (hl : 0 ≤ lam) (ha : 0 ≤ a) (hV : 0 ≤ V) (hd : 16 * delta ≤ lam) :
    2 * delta * a * Real.sqrt V - 3 * lam * V / 4 ≤ lam * a ^ 2 / 192 := by
  have hq := mul_nonneg hl (sq_nonneg (a - 12 * Real.sqrt V))
  have hs := congrArg (fun t : ℝ => lam * t) (Real.sq_sqrt hV)
  have hc := mul_nonneg (sub_nonneg.mpr hd) (mul_nonneg ha (Real.sqrt_nonneg V))
  nlinarith only [hq, hs, hc]

lemma gradient_error_young {lam a b : ℝ} (hl : 0 < lam) :
    a * b ≤ lam / 16 * a ^ 2 + 4 / lam * b ^ 2 := by
  apply (mul_le_mul_iff_left₀ hl).mp
  calc
    a * b * lam ≤ lam ^ 2 / 16 * a ^ 2 + 4 * b ^ 2 := by
      nlinarith [sq_nonneg (lam * a - 8 * b)]
    _ = (lam / 16 * a ^ 2 + 4 / lam * b ^ 2) * lam := by
      field_simp

lemma gradient_error_split (e U x v : E) {lam : ℝ} (hl : 0 < lam) :
    -⟪e, U - v⟫ ≤ lam / 16 * ‖U - x‖ ^ 2 + 4 / lam * ‖e‖ ^ 2 - ⟪e, x - v⟫ := by
  have hi := real_inner_le_norm (-e) (U - x)
  simp only [inner_neg_left, norm_neg] at hi
  have hy := gradient_error_young (a := ‖U - x‖) (b := ‖e‖) hl
  rw [show U - v = (U - x) + (x - v) by abel, inner_add_right]
  nlinarith only [hi, hy]

lemma proximal_variance_coefficient {lam delta K s : ℝ}
    (hl : 0 ≤ lam) (hd : 0 ≤ delta) (hs : 1 ≤ s)
    (ht : 16 * delta + 6 * K / s ≤ lam) :
    -2 * lam + lam / s + delta + 3 * K / (2 * s) ≤ -3 * lam / 4 := by
  have hls : lam / s ≤ lam := (div_le_self hl hs)
  have he : 3 * K / (2 * s) = (6 * K / s) / 4 := by ring
  rw [he]
  linarith

lemma cohort_similarity_coefficient (k : ℕ) {delta : ℝ} (hd : 0 ≤ delta) :
    delta * Real.sqrt k / ((k : ℝ) + 1) ≤ delta := by
  have hr : Real.sqrt k ≤ (k : ℝ) + 1 := by
    apply (Real.sqrt_le_left (by positivity)).2
    nlinarith [Nat.cast_nonneg (α := ℝ) k, sq_nonneg (k : ℝ)]
  apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)).2
  exact mul_le_mul_of_nonneg_left hr hd

lemma sampled_variance_coefficient (k : ℕ) {lam delta K : ℝ}
    (hl : 0 ≤ lam) (hd : 0 ≤ delta)
    (ht : 16 * delta + 6 * K / ((k : ℝ) + 1) ≤ lam) :
    -2 * lam + lam / ((k : ℝ) + 1) +
      (delta * Real.sqrt k + 3 * K / 2) / ((k : ℝ) + 1) ≤ -3 * lam / 4 := by
  have hb := proximal_variance_coefficient hl hd
    (show 1 ≤ (k : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) k]) ht
  have hc := cohort_similarity_coefficient k hd
  have he : (delta * Real.sqrt k + 3 * K / 2) / ((k : ℝ) + 1) =
      delta * Real.sqrt k / ((k : ℝ) + 1) + 3 * K / (2 * ((k : ℝ) + 1)) := by
    field_simp
  rw [he]
  linarith

lemma proximal_error_absorption (e U x v : E) {lam delta V C : ℝ}
    (hl : 0 < lam) (hV : 0 ≤ V) (hd : 16 * delta ≤ lam) (hC : C ≤ -3 * lam / 4) :
    2 * delta * ‖x - U‖ * Real.sqrt V + C * V - ⟪e, U - v⟫ ≤
      lam / 8 * ‖x - U‖ ^ 2 + 4 / lam * ‖e‖ ^ 2 - ⟪e, x - v⟫ := by
  have hc := mul_le_mul_of_nonneg_right hC hV
  have ha := proximal_variance_absorption hl.le (norm_nonneg (x - U)) hV hd
  have he := gradient_error_split e U x v hl
  rw [norm_sub_rev U x] at he
  have hn := mul_nonneg hl.le (sq_nonneg ‖x - U‖)
  nlinarith only [hc, ha, he, hn]

lemma primal_dual_identity {A B a lam : ℝ} {x y v z : E}
    (ha : a ^ 2 * lam = A) (hx : A • x = B • y + a • v) :
    B • y + a • (v - (a * lam) • (x - z)) = A • z := by
  have hm : a * (a * lam) = A := by nlinarith [ha]
  calc
    B • y + a • (v - (a * lam) • (x - z)) =
        B • y + a • v - (a * (a * lam)) • (x - z) := by module
    _ = A • x - A • (x - z) := by rw [hm, ← hx]
    _ = A • z := by module

lemma weighted_certificate {A B a : ℝ} {x y z v xs r : E}
    (hA : A = B + a) (hx : A • x = B • y + a • v) :
    B * ⟪r, z - y⟫ + a * ⟪r, z - xs⟫ =
      A * ⟪r, z - x⟫ + a * ⟪r, v - xs⟫ := by
  have hv : B • (z - y) + a • (z - xs) =
      A • (z - x) + a • (v - xs) := by
    calc
      B • (z - y) + a • (z - xs) =
          A • z - (B • y + a • v) + a • (v - xs) := by rw [hA]; module
      _ = A • (z - x) + a • (v - xs) := by rw [← hx]; module
  simpa only [inner_add_right, inner_smul_right] using congrArg (inner ℝ r) hv

lemma potential_step {A B a lam fy fz fs errY errS : ℝ} {x y z v xs r : E}
    (hB : 0 ≤ B) (ha : 0 ≤ a) (hlam : 0 < lam)
    (hA : A = B + a) (haA : a ^ 2 * lam = A)
    (hx : A • x = B • y + a • v) (hr : r = lam • (x - z))
    (hy : fz - fy ≤ ⟪r, z - y⟫ + errY)
    (hs : fz - fs ≤ ⟪r, z - xs⟫ + errS) :
    A * (fz - fs) + ‖v - a • r - xs‖ ^ 2 / 2 ≤
      B * (fy - fs) + ‖v - xs‖ ^ 2 / 2 -
        A / (2 * lam) * ‖r‖ ^ 2 + B * errY + a * errS := by
  have hw := weighted_certificate hA hx (r := r) (z := z) (xs := xs)
  have hz : ⟪r, z - x⟫ = -(‖r‖ ^ 2 / lam) := by
    have he : z - x = -(lam⁻¹ • r) := by
      rw [hr, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
      abel
    rw [he, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hn : ‖v - a • r - xs‖ ^ 2 =
      ‖v - xs‖ ^ 2 - 2 * a * ⟪r, v - xs⟫ + a ^ 2 * ‖r‖ ^ 2 := by
    rw [show v - a • r - xs = (v - xs) - a • r by abel,
      norm_sub_sq_real, inner_smul_right, real_inner_comm (v - xs) r,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hc : A / (2 * lam) = a ^ 2 / 2 := by
    rw [← haA]
    field_simp
  have hy' := mul_le_mul_of_nonneg_left hy hB
  have hs' := mul_le_mul_of_nonneg_left hs ha
  rw [hz] at hw
  have hz' : A * (‖r‖ ^ 2 / lam) = a ^ 2 * ‖r‖ ^ 2 := by
    rw [← haA]
    field_simp
  rw [mul_neg, hz'] at hw
  rw [hn, hc, hA]
  nlinarith only [hy', hs', hw]

lemma accelerated_weight_properties {lam A : ℝ} (hl : 0 < lam) (hA : 0 ≤ A) :
    let a := (1 + Real.sqrt (1 + 4 * lam * A)) / (2 * lam)
    0 < a ∧ lam * a ^ 2 = A + a := by
  dsimp only
  have hr : 0 ≤ 1 + 4 * lam * A := by positivity
  have hs := Real.sq_sqrt hr
  constructor
  · positivity
  · apply (mul_right_cancel₀ (show (2 * lam) ^ 2 ≠ 0 by positivity))
    field_simp
    have he : 1 + 4 * lam * A = 1 + lam * 4 * A := by ring
    rw [he] at hs
    nlinarith

lemma common_gradient_shift {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (g : ι → E) (r : E) (hw : ∑ i, w i = 1) :
    (∑ i, w i • (g i + r)) = (∑ i, w i • g i) + r := by
  simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hw, one_smul]

lemma centered_gradient_shift {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (g : ι → E) (r : E) (hw : ∑ i, w i = 1) (i : ι) :
    (g i + r) - (∑ j, w j • (g j + r)) = g i - ∑ j, w j • g j := by
  rw [common_gradient_shift w g r hw]
  abel

lemma squared_convex_combination (x y center : E) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ‖a • x + b • y - center‖ ^ 2 =
      a * ‖x - center‖ ^ 2 + b * ‖y - center‖ ^ 2 - a * b * ‖x - y‖ ^ 2 := by
  have he : a • x + b • y - center = a • (x - center) + b • (y - center) := by
    rw [smul_sub, smul_sub]
    have hc : a • center + b • center = center := by rw [← add_smul, hab, one_smul]
    rw [show a • x - a • center + (b • y - b • center) =
      a • x + b • y - (a • center + b • center) by abel, hc]
  rw [he, norm_add_sq_real, norm_smul, norm_smul, Real.norm_of_nonneg ha,
    Real.norm_of_nonneg hb, real_inner_smul_left, inner_smul_right,
    show x - y = (x - center) - (y - center) by abel,
    norm_sub_sq_real (x - center) (y - center)]
  obtain rfl := eq_sub_of_add_eq hab
  ring

lemma accelerated_weight_upper {lam A t : ℝ} (hl : 0 < lam) (hA : 0 ≤ A)
    (ht : 0 ≤ t) (hbound : A ≤ t ^ 2 / lam) :
    (1 + Real.sqrt (1 + 4 * lam * A)) / (2 * lam) ≤ (t + 1) / lam := by
  have hmul := (le_div_iff₀ hl).mp hbound
  have hroot := Real.sq_sqrt (show 0 ≤ 1 + 4 * lam * A by positivity)
  have hs : Real.sqrt (1 + 4 * lam * A) ≤ 2 * t + 1 := by
    nlinarith [Real.sqrt_nonneg (1 + 4 * lam * A)]
  apply (div_le_div_iff₀ (show 0 < 2 * lam by positivity) hl).2
  nlinarith

lemma accelerated_weight_lower {lam A t : ℝ} (hl : 0 < lam) (hA : 0 ≤ A)
    (ht : 0 ≤ t) (hbound : t ^ 2 / (4 * lam) ≤ A) :
    (t + 1) / (2 * lam) ≤ (1 + Real.sqrt (1 + 4 * lam * A)) / (2 * lam) := by
  have hmul := (div_le_iff₀ (show 0 < 4 * lam by positivity)).mp hbound
  have hroot := Real.sq_sqrt (show 0 ≤ 1 + 4 * lam * A by positivity)
  have hs : t ≤ Real.sqrt (1 + 4 * lam * A) := by
    nlinarith [Real.sqrt_nonneg (1 + 4 * lam * A)]
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

lemma potential_bootstrap {M R S : ℝ} (hR : 0 ≤ R)
    (hs : S ≤ 1 / 12) (hM : R / 2 ≤ M)
    (hbound : M ≤ R / 2 + S * (4 * M + 2 * R)) : M ≤ R := by
  have hn : 0 ≤ 4 * M + 2 * R := by linarith
  have ht := mul_le_mul_of_nonneg_right hs hn
  nlinarith

lemma proximal_potential_step {A B a rho fy fz fs tau : ℝ} {x y z v xs r d : E}
    (hB : 0 ≤ B) (ha : 0 ≤ a) (hrho : 0 < rho)
    (hA : A = B + a) (haA : a ^ 2 * rho = A)
    (hx : A • x = B • y + a • v) (hr : r = rho • (x - z))
    (hy : fz - fy ≤ ⟪r, z - y⟫ + rho * ⟪d, z - y⟫ - rho / 2 * ‖d‖ ^ 2 + tau)
    (hs : fz - fs ≤ ⟪r, z - xs⟫ + rho * ⟪d, z - xs⟫ - rho / 2 * ‖d‖ ^ 2 + tau) :
    A * (fz - fs) + ‖v - a • r - xs‖ ^ 2 / 2 ≤
      B * (fy - fs) + ‖v - xs‖ ^ 2 / 2 + A * tau + a * rho * ⟪d, v - xs⟫ := by
  have hp := potential_step hB ha hrho hA haA hx hr
    (show fz - fy ≤ ⟪r, z - y⟫ + (rho * ⟪d, z - y⟫ - rho / 2 * ‖d‖ ^ 2 + tau) by linarith)
    (show fz - fs ≤ ⟪r, z - xs⟫ + (rho * ⟪d, z - xs⟫ - rho / 2 * ‖d‖ ^ 2 + tau) by linarith)
  have hw := weighted_certificate hA hx (r := d) (z := z) (xs := xs)
  have hi : ⟪d, z - x⟫ = -⟪d, x - z⟫ := by
    rw [← inner_neg_right, neg_sub]
  rw [hi] at hw
  have hw' := congrArg (fun t : ℝ => rho * t) hw
  have hnon : 0 ≤ A * rho / 2 * ‖d + (x - z)‖ ^ 2 := by
    have hA0 : 0 ≤ A := by rw [hA]; positivity
    positivity
  rw [norm_add_sq_real] at hnon
  have hnorm : ‖r‖ ^ 2 = rho ^ 2 * ‖x - z‖ ^ 2 := by
    rw [hr, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [hnorm] at hp
  have he : A / (2 * rho) * (rho ^ 2 * ‖x - z‖ ^ 2) = A * rho / 2 * ‖x - z‖ ^ 2 := by
    field_simp
  rw [he] at hp
  rw [hA] at hp hw' hnon ⊢
  nlinarith only [hp, hw', hnon]

lemma inner_young (d v : E) {theta : ℝ} (ht : 0 < theta) :
    ⟪d, v⟫ ≤ theta / 2 * ‖v‖ ^ 2 + ‖d‖ ^ 2 / (2 * theta) := by
  have hn := sq_nonneg ‖d - theta • v‖
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hn
  apply (mul_le_mul_iff_left₀ ht).mp
  calc
    ⟪d, v⟫ * theta ≤ theta ^ 2 / 2 * ‖v‖ ^ 2 + ‖d‖ ^ 2 / 2 := by nlinarith
    _ = (theta / 2 * ‖v‖ ^ 2 + ‖d‖ ^ 2 / (2 * theta)) * theta := by field_simp

lemma proximal_error_inner_bound (d v : E) {theta q tau P : ℝ}
    (ht : 0 < theta) (hq : 0 < q) (hv : ‖v‖ ^ 2 ≤ 2 * P)
    (hd : q / 2 * ‖d‖ ^ 2 ≤ tau) : ⟪d, v⟫ ≤ theta * P + tau / (q * theta) := by
  have hy := inner_young d v ht
  have hv' := mul_le_mul_of_nonneg_left hv (show 0 ≤ theta / 2 by positivity)
  have hd' : ‖d‖ ^ 2 / (2 * theta) ≤ tau / (q * theta) := by
    apply (div_le_div_iff₀ (show 0 < 2 * theta by positivity) (show 0 < q * theta by positivity)).2
    have hh := mul_le_mul_of_nonneg_right hd (show 0 ≤ 2 * theta by positivity)
    nlinarith only [hh]
  nlinarith only [hy, hv', hd']

lemma proximal_potential_young {A B a rho q theta fy fz fs tau : ℝ} {x y z v xs r d : E}
    (hB : 0 ≤ B) (ha : 0 ≤ a) (hrho : 0 < rho) (hq : 0 < q) (ht : 0 < theta)
    (hA : A = B + a) (haA : a ^ 2 * rho = A)
    (hx : A • x = B • y + a • v) (hr : r = rho • (x - z)) (hgap : fs ≤ fy)
    (hd : q / 2 * ‖d‖ ^ 2 ≤ tau)
    (hy : fz - fy ≤ ⟪r, z - y⟫ + rho * ⟪d, z - y⟫ - rho / 2 * ‖d‖ ^ 2 + tau)
    (hs : fz - fs ≤ ⟪r, z - xs⟫ + rho * ⟪d, z - xs⟫ - rho / 2 * ‖d‖ ^ 2 + tau) :
    A * (fz - fs) + ‖v - a • r - xs‖ ^ 2 / 2 ≤
      (1 + a * rho * theta) * (B * (fy - fs) + ‖v - xs‖ ^ 2 / 2) +
        (A + a * rho / (q * theta)) * tau := by
  have hp := proximal_potential_step hB ha hrho hA haA hx hr hy hs
  have hv : ‖v - xs‖ ^ 2 ≤ 2 * (B * (fy - fs) + ‖v - xs‖ ^ 2 / 2) := by
    have hn := mul_nonneg hB (sub_nonneg.mpr hgap)
    linarith
  have he := proximal_error_inner_bound d (v - xs) ht hq hv hd
  have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ a * rho by positivity)
  simp only [div_eq_mul_inv] at hm ⊢
  nlinarith only [hp, hm]

end LongTails.Proofs.CappedProximalGeometry
