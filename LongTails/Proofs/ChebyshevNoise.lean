import LongTails.Proofs.ChebyshevResidual
import LongTails.Proofs.OrderedResidualProducts

open scoped BigOperators

namespace OracleTemplate.BatchedChebyshev

noncomputable def suffix (T i : ℕ) (z : ℝ) : ℝ :=
  ∏ j ∈ Finset.Ico i T, (1 - z / root T (j + 1))

lemma suffix_abs_le_one (T i : ℕ) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    |suffix T i z| ≤ 1 := by
  have hfull : |∏ j ∈ Finset.range T, (1 - z * (root T (j + 1))⁻¹)| ≤ 1 := by
    simpa only [residualFactors_eval, div_eq_mul_inv] using (residualFactors_bounds T hz hz1).1
  have h := OrderedResidualProducts.abs_residual_suffix_le_one hz
    (η := fun j => (root T (j + 1))⁻¹)
    (fun j hj => inv_nonneg.mpr (root_nonneg _ _))
    (fun j k hjk hk => inv_le_inv₀ (root_pos (by omega) (by omega))
      (root_pos (by omega) (by omega)) |>.mpr
        (root_strictMono (Nat.add_lt_add_right hjk 1) (by omega)).le)
    hfull (i := i)
  simpa only [suffix, div_eq_mul_inv] using h

lemma suffix_gain_sq_le {T i : ℕ} (hi : 0 < i) (hiT : i ≤ T)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    z / root T i ^ 2 * suffix T i z ^ 2 ≤ 2 / root T i := by
  have hfull : |∏ j ∈ Finset.range T, (1 - z * (root T (j + 1))⁻¹)| ≤ 1 := by
    simpa only [residualFactors_eval, div_eq_mul_inv] using (residualFactors_bounds T hz hz1).1
  have h := OrderedResidualProducts.residual_suffix_gain_sq_le hz
    (η := fun j => (root T (j + 1))⁻¹)
    (fun j hj => inv_nonneg.mpr (root_nonneg _ _))
    (fun j k hjk hk => inv_le_inv₀ (root_pos (by omega) (by omega))
      (root_pos (by omega) (by omega)) |>.mpr
        (root_strictMono (Nat.add_lt_add_right hjk 1) (by omega)).le)
    hfull (i := i - 1) (by omega)
  simpa only [show i - 1 + 1 = i by omega, suffix, div_eq_mul_inv, inv_pow] using h

lemma suffix_gain_tail {T i : ℕ} (hi : 0 < i) (hiT : i ≤ T) (htail : T < 8 * i)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    z / root T i ^ 2 * suffix T i z ^ 2 ≤ weight T i ^ 2 := by
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
  have htail' : (T : ℝ) < 8 * (i : ℝ) := by exact_mod_cast htail
  have hm : 0 < 2 * (T : ℝ) + 1 := by positivity
  have hmle : 2 * (T : ℝ) + 1 ≤ 24 * (i : ℝ) := by linarith
  have hm2 := (sq_le_sq₀ hm.le (by positivity : 0 ≤ 24 * (i : ℝ))).mpr hmle
  have hr : (1 / 144 : ℝ) ≤ root T i := by
    apply le_trans _ (root_lower hiT)
    apply (le_div_iff₀ (sq_pos_of_pos hm)).mpr
    nlinarith [hm2]
  have hgain := suffix_gain_sq_le hi hiT hz hz1
  have hinv : 2 / root T i ≤ 288 := by
    apply (div_le_iff₀ (root_pos hi hiT)).mpr
    linarith
  have hw : 17 ≤ weight T i := by
    unfold weight
    have : 0 ≤ 4 * (2 * (T : ℝ) + 1) / ((i : ℝ) * Real.sqrt (i : ℝ)) := by positivity
    linarith
  nlinarith

lemma suffix_exp_bound {T i l u : ℕ}
    (hl : i ≤ l) (hu : u ≤ T) {z c : ℝ} (hz : 0 ≤ z)
    (hsmall : z ≤ 2 * root T i)
    (hblock : ∀ j ∈ Finset.Ico l u, c ≤ z / root T (j + 1) ∧
      z / root T (j + 1) ≤ 1) :
    |suffix T i z| ≤ Real.exp (-((u - l : ℕ) : ℝ) * c) := by
  have hsubset : Finset.Ico l u ⊆ Finset.Ico i T := by
    intro j hj
    obtain ⟨hjl, hju⟩ := Finset.mem_Ico.mp hj
    exact Finset.mem_Ico.mpr ⟨hl.trans hjl, hju.trans_le hu⟩
  have htail (j : ℕ) (hj : j ∈ Finset.Ico i T) : |1 - z / root T (j + 1)| ≤ 1 := by
    obtain ⟨hji, hjT⟩ := Finset.mem_Ico.mp hj
    have hr := root_pos (T := T) (i := j + 1) (by omega) (by omega)
    have hmono : root T i ≤ root T (j + 1) :=
      (root_strictMono (by omega) (by omega)).le
    have hratio0 : 0 ≤ z / root T (j + 1) := div_nonneg hz hr.le
    have hratio2 : z / root T (j + 1) ≤ 2 := by
      apply (div_le_iff₀ hr).mpr
      linarith
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hselected (j : ℕ) (hj : j ∈ Finset.Ico l u) :
      |1 - z / root T (j + 1)| ≤ Real.exp (-c) := by
    have h := hblock j hj
    rw [abs_of_nonneg (by linarith : 0 ≤ 1 - z / root T (j + 1))]
    have hexp := Real.add_one_le_exp (-c)
    linarith
  have h := OrderedResidualProducts.prod_le_exp_of_block hsubset
    (fun j _ => abs_nonneg (1 - z / root T (j + 1))) htail hselected
  simpa only [suffix, Finset.abs_prod, Nat.card_Ico] using h

lemma suffix_exp_small {T i : ℕ} (hi : 0 < i) (h2i : 2 * i ≤ T)
    {z : ℝ} (hz : 0 ≤ z) (hzi : z ≤ root T i) :
    |suffix T i z| ≤
      Real.exp (-(z * (2 * (T : ℝ) + 1) ^ 2 / (64 * (i : ℝ)))) := by
  have hiT : i ≤ T := by omega
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  have hm : 0 < (2 * (T : ℝ) + 1) ^ 2 := by positivity
  have h := suffix_exp_bound (l := i) (u := 2 * i) le_rfl h2i hz
    (show z ≤ 2 * root T i by linarith [root_nonneg T i])
    (c := z * (2 * (T : ℝ) + 1) ^ 2 / (64 * (i : ℝ) ^ 2)) (by
      intro j hj
      obtain ⟨hji, hj2⟩ := Finset.mem_Ico.mp hj
      have hjT : j + 1 ≤ T := by omega
      have hr := root_pos (T := T) (i := j + 1) (by omega) hjT
      have hrupper := (le_div_iff₀ hm).mp (root_upper hjT)
      have hj' : ((j + 1 : ℕ) : ℝ) ≤ 2 * (i : ℝ) := by exact_mod_cast (show j + 1 ≤ 2 * i by omega)
      have hj2' := (sq_le_sq₀ (Nat.cast_nonneg (j + 1)) (by positivity : 0 ≤ 2 * (i : ℝ))).mpr hj'
      have hroot : root T (j + 1) * (2 * (T : ℝ) + 1) ^ 2 ≤ 64 * (i : ℝ) ^ 2 := by
        nlinarith
      refine ⟨?_, ?_⟩
      · apply (le_div_iff₀ hr).mpr
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ (by positivity : 0 < 64 * (i : ℝ) ^ 2)).mpr
        nlinarith [mul_le_mul_of_nonneg_left hroot hz]
      · apply (div_le_one hr).mpr
        exact hzi.trans (root_strictMono (by omega) hjT).le)
  have hexp : -(((2 * i - i : ℕ) : ℝ)) *
      (z * (2 * (T : ℝ) + 1) ^ 2 / (64 * (i : ℝ) ^ 2)) =
      -(z * (2 * (T : ℝ) + 1) ^ 2 / (64 * (i : ℝ))) := by
    rw [show 2 * i - i = i by omega]
    field_simp
  rwa [hexp] at h

lemma scaled_exp_square_le {a z p : ℝ} (ha : 0 ≤ a) (hz : 0 ≤ z)
    (hp : |p| ≤ Real.exp (-(a * z))) : 2 * a * z * p ^ 2 ≤ 1 := by
  have hp2 : p ^ 2 ≤ Real.exp (-(2 * a * z)) := by
    calc
      p ^ 2 = |p| ^ 2 := (sq_abs p).symm
      _ ≤ Real.exp (-(a * z)) ^ 2 := pow_le_pow_left₀ (abs_nonneg p) hp 2
      _ = Real.exp (-(2 * a * z)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have he := Real.mul_exp_neg_le_exp_neg_one (2 * a * z)
  have he1 : Real.exp (-1) ≤ 1 := by simp
  exact (mul_le_mul_of_nonneg_left hp2 (by positivity)).trans (he.trans he1)

lemma suffix_gain_small {T i : ℕ} (hi : 0 < i) (h2i : 2 * i ≤ T)
    {z : ℝ} (hz : 0 ≤ z) (hzi : z ≤ root T i) :
    z / root T i ^ 2 * suffix T i z ^ 2 ≤
      2 * (2 * (T : ℝ) + 1) ^ 2 / (i : ℝ) ^ 3 := by
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  have hiT : i ≤ T := by omega
  have hm : 0 < (2 * (T : ℝ) + 1) ^ 2 := by positivity
  have hp := suffix_exp_small hi h2i hz hzi
  have he : |suffix T i z| ≤ Real.exp (-((2 * (T : ℝ) + 1) ^ 2 /
      (64 * (i : ℝ)) * z)) := by convert hp using 2; ring
  have hs := scaled_exp_square_le (by positivity) hz he
  have hn : z * suffix T i z ^ 2 ≤ 32 * (i : ℝ) / (2 * (T : ℝ) + 1) ^ 2 := by
    apply (le_div_iff₀ hm).mpr
    have h := (mul_le_mul_of_nonneg_right hs (show 0 ≤ 32 * (i : ℝ) by positivity))
    field_simp at h
    nlinarith
  calc
    z / root T i ^ 2 * suffix T i z ^ 2 = (z * suffix T i z ^ 2) / root T i ^ 2 := by ring
    _ ≤ (32 * (i : ℝ) / (2 * (T : ℝ) + 1) ^ 2) /
        (4 * (i : ℝ) ^ 2 / (2 * (T : ℝ) + 1) ^ 2) ^ 2 := by
      apply div_le_div₀ (by positivity) hn (by positivity)
      exact (sq_le_sq₀ (by positivity) (root_nonneg T i)).mpr (root_lower hiT)
    _ = _ := by field_simp; ring

lemma suffix_exp_middle {T i : ℕ} (hi : 0 < i) (h8i : 8 * i ≤ T)
    {z : ℝ} (hzi : root T i ≤ z) (hzi2 : z ≤ 2 * root T i) :
    |suffix T i z| ≤ Real.exp (-(i : ℝ) / 64) := by
  have hiT : i ≤ T := by omega
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  have h := suffix_exp_bound (l := 4 * i - 1) (u := 8 * i - 1)
    (by omega) (by omega) ((root_nonneg T i).trans hzi) hzi2
    (c := 1 / 256) (by
      intro j hj
      obtain ⟨hjl, hju⟩ := Finset.mem_Ico.mp hj
      have hjT : j + 1 ≤ T := by omega
      have hr := root_pos (T := T) (i := j + 1) (by omega) hjT
      have hjlo : 4 * (i : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (show 4 * i ≤ j + 1 by omega)
      have hjhi : ((j + 1 : ℕ) : ℝ) ≤ 8 * (i : ℝ) := by exact_mod_cast (show j + 1 ≤ 8 * i by omega)
      have hlo2 := (sq_le_sq₀ (by positivity : 0 ≤ 4 * (i : ℝ)) (Nat.cast_nonneg (j + 1))).mpr hjlo
      have hhi2 := (sq_le_sq₀ (Nat.cast_nonneg (j + 1)) (by positivity : 0 ≤ 8 * (i : ℝ))).mpr hjhi
      have hupper : root T (j + 1) ≤ 256 * root T i :=
        root_le_mul_root hjT hiT (by norm_num) (by nlinarith)
      have hlower : root T i ≤ (1 / 2 : ℝ) * root T (j + 1) :=
        root_le_mul_root hiT hjT (by norm_num) (by nlinarith)
      constructor
      · apply (le_div_iff₀ hr).mpr
        linarith
      · apply (div_le_one hr).mpr
        linarith)
  have hcard : 8 * i - 1 - (4 * i - 1) = 4 * i := by omega
  rw [hcard] at h
  convert h using 2; push_cast; ring

lemma suffix_gain_middle {T i : ℕ} (hi : 0 < i) (h8i : 8 * i ≤ T)
    {z : ℝ} (hzi : root T i ≤ z) (hzi2 : z ≤ 2 * root T i) :
    z / root T i ^ 2 * suffix T i z ^ 2 ≤
      16 * (2 * (T : ℝ) + 1) ^ 2 / (i : ℝ) ^ 3 := by
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  have hiT : i ≤ T := by omega
  have hr := root_pos hi hiT
  have hp := suffix_exp_middle hi h8i hzi hzi2
  have hs : |suffix T i z| ≤ Real.exp (-((1 / 64 : ℝ) * (i : ℝ))) := by
    convert hp using 2; ring
  have hb := scaled_exp_square_le (by norm_num : (0 : ℝ) ≤ 1 / 64) hi'.le hs
  have hp2 : suffix T i z ^ 2 ≤ 32 / (i : ℝ) := by
    apply (le_div_iff₀ hi').mpr
    nlinarith
  calc
    z / root T i ^ 2 * suffix T i z ^ 2 ≤
        (2 * root T i) / root T i ^ 2 * (32 / (i : ℝ)) := by
      apply mul_le_mul (div_le_div_of_nonneg_right hzi2 (sq_nonneg _)) hp2
        (sq_nonneg _) (by positivity)
    _ = 64 / ((i : ℝ) * root T i) := by field_simp; ring
    _ ≤ 64 / ((i : ℝ) * (4 * (i : ℝ) ^ 2 / (2 * (T : ℝ) + 1) ^ 2)) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact mul_le_mul_of_nonneg_left (root_lower hiT) hi'.le
    _ = _ := by field_simp; ring

lemma expanding_prefix_bound {T i : ℕ} (hi : 0 < i) (hiT : i ≤ T)
    {z : ℝ} (hzi : 2 * root T i ≤ z) :
    (7 : ℝ) ^ (i / 4) ≤
      ∏ j ∈ Finset.range (i - 1), |1 - z / root T (j + 1)| := by
  have hq : i / 4 ≤ i - 1 := by omega
  have hexpand (j : ℕ) (hj : j < i - 1) : 1 ≤ |1 - z / root T (j + 1)| := by
    have hr := root_pos (T := T) (i := j + 1) (by omega) (by omega)
    have hmono : root T (j + 1) ≤ root T i := (root_strictMono (by omega) hiT).le
    have hz : 2 ≤ z / root T (j + 1) := (le_div_iff₀ hr).mpr (by linarith)
    rw [abs_of_nonpos (by linarith : 1 - z / root T (j + 1) ≤ 0)]
    linarith
  calc
    (7 : ℝ) ^ (i / 4) = ∏ _j ∈ Finset.range (i / 4), (7 : ℝ) := by simp
    _ ≤ ∏ j ∈ Finset.range (i / 4), |1 - z / root T (j + 1)| := by
      apply Finset.prod_le_prod₀ (by intros; norm_num)
      intro j hj
      have hjq := Finset.mem_range.mp hj
      have hjT : j + 1 ≤ T := by omega
      have hr := root_pos (T := T) (i := j + 1) (by omega) hjT
      have hj' : 4 * ((j + 1 : ℕ) : ℝ) ≤ i := by exact_mod_cast (show 4 * (j + 1) ≤ i by omega)
      have hj2 := (sq_le_sq₀ (by positivity : 0 ≤ 4 * ((j + 1 : ℕ) : ℝ))
        (Nat.cast_nonneg i)).mpr hj'
      have hroot : root T (j + 1) ≤ (1 / 4 : ℝ) * root T i :=
        root_le_mul_root hjT hiT (by norm_num) (by nlinarith)
      have hz : 8 ≤ z / root T (j + 1) := (le_div_iff₀ hr).mpr (by linarith)
      rw [abs_of_nonpos (by linarith : 1 - z / root T (j + 1) ≤ 0)]
      linarith
    _ ≤ _ := Finset.prod_le_prod_of_subset_of_one_le₀
      (Finset.range_mono hq) (fun j _ => abs_nonneg _)
      (fun j hj _ => hexpand j (Finset.mem_range.mp hj))

lemma index_le_prefix_square (i : ℕ) : (i : ℝ) ≤ 4 * ((7 : ℝ) ^ (i / 4)) ^ 2 := by
  have hpow (q : ℕ) : (q : ℝ) + 1 ≤ ((7 : ℝ) ^ q) ^ 2 := by
    induction q with
    | zero => norm_num
    | succ q ih =>
      rw [pow_succ (7 : ℝ) q, mul_pow]
      push_cast
      nlinarith [sq_nonneg ((7 : ℝ) ^ q)]
  have hi : (i : ℝ) ≤ 4 * ((i / 4 : ℕ) : ℝ) + 4 := by
    exact_mod_cast (show i ≤ 4 * (i / 4) + 4 by omega)
  linarith [hpow (i / 4)]

lemma suffix_gain_large {T i : ℕ} (hi : 0 < i) (hiT : i ≤ T)
    {z : ℝ} (hzi : 2 * root T i ≤ z) (hz1 : z ≤ 1) :
    z / root T i ^ 2 * suffix T i z ^ 2 ≤
      2 * (2 * (T : ℝ) + 1) ^ 2 / (i : ℝ) ^ 3 := by
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  have hr := root_pos hi hiT
  have hz : 0 ≤ z := by linarith
  have hratio : 2 ≤ z / root T i := (le_div_iff₀ hr).mpr hzi
  have hratio0 : 0 ≤ z / root T i - 1 := by linarith
  have hf := (residualFactors_bounds T hz hz1).1
  rw [residualFactors_eval] at hf
  have hsplit := Finset.prod_range_mul_prod_Ico
    (fun j => 1 - z / root T (j + 1)) (show i - 1 ≤ T by omega)
  rw [Finset.prod_eq_prod_Ico_succ_bot (show i - 1 < T by omega)] at hsplit
  simp only [show i - 1 + 1 = i by omega] at hsplit
  rw [← hsplit, abs_mul, abs_mul, Finset.abs_prod] at hf
  rw [abs_of_nonpos (by linarith : 1 - z / root T i ≤ 0)] at hf
  have hpre := expanding_prefix_bound hi hiT hzi
  have hp : (7 : ℝ) ^ (i / 4) * ((z / root T i - 1) * |suffix T i z|) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hpre
      (show 0 ≤ (z / root T i - 1) * |suffix T i z| by positivity)
    simp only [neg_sub] at hf
    exact hh.trans hf
  have hp2 := (sq_le_sq₀ (show 0 ≤ (7 : ℝ) ^ (i / 4) *
    ((z / root T i - 1) * |suffix T i z|) by positivity) (by norm_num : (0 : ℝ) ≤ 1)).mpr hp
  simp only [mul_pow, sq_abs, one_pow] at hp2
  have hpoly : z / root T i ≤ 2 * (z / root T i - 1) ^ 2 := by
    nlinarith [sq_nonneg (z / root T i - 2)]
  have hmul := mul_le_mul_of_nonneg_right hpoly
    (show 0 ≤ ((7 : ℝ) ^ (i / 4)) ^ 2 * suffix T i z ^ 2 by positivity)
  have hgain : ((7 : ℝ) ^ (i / 4)) ^ 2 * (z / root T i) * suffix T i z ^ 2 ≤ 2 := by
    nlinarith [hp2]
  have hiq := index_le_prefix_square i
  have hmul2 := mul_le_mul_of_nonneg_right hiq
    (show 0 ≤ (z / root T i) * suffix T i z ^ 2 by positivity)
  have hshort : (i : ℝ) * (z / root T i) * suffix T i z ^ 2 ≤ 8 := by
    nlinarith
  calc
    z / root T i ^ 2 * suffix T i z ^ 2 =
        ((i : ℝ) * (z / root T i) * suffix T i z ^ 2) / ((i : ℝ) * root T i) := by
      field_simp
    _ ≤ 8 / ((i : ℝ) * root T i) :=
      div_le_div_of_nonneg_right hshort (by positivity)
    _ ≤ 8 / ((i : ℝ) * (4 * (i : ℝ) ^ 2 / (2 * (T : ℝ) + 1) ^ 2)) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact mul_le_mul_of_nonneg_left (root_lower hiT) hi'.le
    _ = _ := by field_simp; ring

lemma suffix_gain_bound {T i : ℕ} (hi : 0 < i) (hiT : i ≤ T)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    z / root T i ^ 2 * suffix T i z ^ 2 ≤ weight T i ^ 2 := by
  by_cases h8i : 8 * i ≤ T
  · have hi' : (0 : ℝ) < i := by exact_mod_cast hi
    have hb : z / root T i ^ 2 * suffix T i z ^ 2 ≤
        16 * (2 * (T : ℝ) + 1) ^ 2 / (i : ℝ) ^ 3 := by
      by_cases hsmall : z ≤ root T i
      · have h := suffix_gain_small hi (show 2 * i ≤ T by omega) hz hsmall
        exact h.trans (div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (2 * (T : ℝ) + 1)]) (by positivity))
      · by_cases hmiddle : z ≤ 2 * root T i
        · exact suffix_gain_middle hi h8i (le_of_not_ge hsmall) hmiddle
        · have h := suffix_gain_large hi hiT (le_of_not_ge hmiddle) hz1
          exact h.trans (div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (2 * (T : ℝ) + 1)]) (by positivity))
    have hs := Real.sq_sqrt hi'.le
    have hroot : 0 < Real.sqrt (i : ℝ) := Real.sqrt_pos.mpr hi'
    have he : (4 * (2 * (T : ℝ) + 1) / ((i : ℝ) * Real.sqrt (i : ℝ))) ^ 2 =
        16 * (2 * (T : ℝ) + 1) ^ 2 / (i : ℝ) ^ 3 := by
      rw [div_pow, mul_pow, mul_pow, hs]
      field_simp
      ring
    rw [← he] at hb
    unfold weight
    have hn : 0 ≤ 4 * (2 * (T : ℝ) + 1) / ((i : ℝ) * Real.sqrt (i : ℝ)) := by positivity
    nlinarith
  · exact suffix_gain_tail hi hiT (lt_of_not_ge h8i) hz hz1

end OracleTemplate.BatchedChebyshev
