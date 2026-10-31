import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic
import LongTails.Proofs.HiddenConvexBudget

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CohypomonotoneNewtonEnergy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma scaled_energy_identity (u w g h : E) (A a : ℝ) :
    ‖(A + a) • u - A • w + (a * (A + a)) • h‖ ^ 2 -
        ‖(A + a) • u - A • w + (a * A) • g‖ ^ 2 =
      2 * a ^ 2 * ((A + a) * ⟪h, u⟫ + (A + a) ^ 2 / 2 * ‖h‖ ^ 2 -
        (A * ⟪g, w⟫ + A ^ 2 / 2 * ‖g‖ ^ 2)) +
      2 * a * A * (A + a) * ⟪h - g, u - w⟫ := by
  simp only [norm_add_sq_real, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm u h, real_inner_comm w h, real_inner_comm u g,
    real_inner_comm w g]
  ring

lemma scaled_energy_step {u w g h d r : E} {A a : ℝ}
    (hA : 0 ≤ A) (ha : 0 ≤ a) (hmono : 0 ≤ A * ⟪h - g, u - w⟫)
    (hd : (A + a) • d = (A + a) • u - A • w + (a * A) • g)
    (hr : (A + a) • r = (A + a) • u - A • w + (a * (A + a)) • h) :
    2 * a ^ 2 * ((A + a) * ⟪h, u⟫ + (A + a) ^ 2 / 2 * ‖h‖ ^ 2 -
        (A * ⟪g, w⟫ + A ^ 2 / 2 * ‖g‖ ^ 2)) ≤
      (A + a) ^ 2 * (‖r‖ ^ 2 - ‖d‖ ^ 2) := by
  have hi := scaled_energy_identity u w g h A a
  rw [← hd, ← hr] at hi
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hi
  have hp : 0 ≤ 2 * a * A * (A + a) * ⟪h - g, u - w⟫ :=
    by
      have hp := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha)
        (add_nonneg hA ha)) hmono
      nlinarith only [hp]
  nlinarith only [hi, hp]

lemma perturbed_energy_step {u w g h d r : E} {A a e : ℝ}
    (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hmono : 0 ≤ A * ⟪h - g, u - w⟫)
    (hd : (A + a) • d = (A + a) • u - A • w + (a * A) • g)
    (hr : (A + a) • r = (A + a) • u - A • w + (a * (A + a)) • h)
    (herr : ‖r‖ ≤ ‖d‖ / 4 + e) :
    2 * a ^ 2 * ((A + a) * ⟪h, u⟫ + (A + a) ^ 2 / 2 * ‖h‖ ^ 2 -
        (A * ⟪g, w⟫ + A ^ 2 / 2 * ‖g‖ ^ 2)) +
      7 / 8 * (A + a) ^ 2 * ‖d‖ ^ 2 ≤ 2 * (A + a) ^ 2 * e ^ 2 := by
  have hs := pow_le_pow_left₀ (norm_nonneg r) herr 2
  have hb : ‖r‖ ^ 2 ≤ ‖d‖ ^ 2 / 8 + 2 * e ^ 2 := by
    nlinarith [sq_nonneg (‖d‖ / 4 - e)]
  have hp := mul_le_mul_of_nonneg_left hb (sq_nonneg (A + a))
  have ht := scaled_energy_step hA ha hmono hd hr
  nlinarith only [ht, hp]

lemma potential_quadratic_lower {g z anchor root : E} {A R : ℝ}
    (hA : 0 ≤ A) (hmono : 0 ≤ ⟪g, z - root⟫)
    (hR : ‖root - anchor‖ ≤ R) :
    (A * ‖g‖) ^ 2 / 2 - A * R * ‖g‖ ≤
      A * ⟪g, z - anchor⟫ + A ^ 2 / 2 * ‖g‖ ^ 2 := by
  have hi : -R * ‖g‖ ≤ ⟪g, z - anchor⟫ := by
    have he : z - anchor = (z - root) + (root - anchor) := by abel
    rw [he, inner_add_right]
    have hcs := abs_real_inner_le_norm g (root - anchor)
    have hp := mul_le_mul_of_nonneg_left hR (norm_nonneg g)
    have hab := neg_abs_le ⟪g, root - anchor⟫
    nlinarith only [hmono, hcs, hp, hab]
  have hp := mul_le_mul_of_nonneg_left hi hA
  nlinarith only [hp]

lemma potential_floor {g z anchor root : E} {A R : ℝ}
    (hA : 0 ≤ A) (hmono : 0 ≤ ⟪g, z - root⟫)
    (hR : ‖root - anchor‖ ≤ R) :
    -(R ^ 2 / 2) ≤ A * ⟪g, z - anchor⟫ + A ^ 2 / 2 * ‖g‖ ^ 2 := by
  have hh := potential_quadratic_lower hA hmono hR
  nlinarith [sq_nonneg (A * ‖g‖ - R)]

lemma potential_residual_bound {g z anchor root : E} {A R : ℝ}
    (hA : 0 ≤ A) (hmono : 0 ≤ ⟪g, z - root⟫)
    (hR : ‖root - anchor‖ ≤ R)
    (hV : A * ⟪g, z - anchor⟫ + A ^ 2 / 2 * ‖g‖ ^ 2 ≤ 2 * R ^ 2) :
    A * ‖g‖ ≤ 4 * R := by
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hR
  have hh := potential_quadratic_lower hA hmono hR
  have hq0 : 0 ≤ A * ‖g‖ := mul_nonneg hA (norm_nonneg g)
  by_contra hn
  have hq : 4 * R < A * ‖g‖ := lt_of_not_ge hn
  have hmul := mul_pos (sub_pos.mpr hq) (lt_of_le_of_lt (by positivity : 0 ≤ 4 * R) hq)
  have hsq := mul_self_lt_mul_self (by positivity : 0 ≤ 4 * R) hq
  nlinarith

lemma reciprocal_square_sum (N : ℕ) :
    ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) ^ 2 ≤ 2 := by
  cases N with
  | zero => simp
  | succ N =>
      rw [Finset.sum_range_succ']
      have hh := OracleTemplate.LocalHiddenConvex.sum_inv_sq_le N
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, one_pow, div_self
        (by norm_num : (1 : ℝ) ≠ 0)]
      have he : (fun k : ℕ => 1 / (((k : ℝ) + 1) + 1) ^ 2) =
          fun k : ℕ => 1 / ((k : ℝ) + 2) ^ 2 := by funext k; congr 2; ring
      simp only [he]
      have hp : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
      linarith

lemma cumulative_energy (V w error : ℕ → ℝ) (c : ℝ) {N : ℕ}
    (hstep : ∀ k < N, V (k + 1) + c * w k ≤ V k + error k) :
    V N + c * ∑ k ∈ Finset.range N, w k ≤ V 0 + ∑ k ∈ Finset.range N, error k := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hi := ih (fun k hk => hstep k (Nat.lt_succ_of_lt hk))
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith [hstep N (Nat.lt_succ_self N)]

lemma energy_bounds (V w : ℕ → ℝ) (R : ℝ) {N : ℕ} (hzero : V 0 = 0)
    (hw : ∀ k < N, 0 ≤ w k) (hlower : -(R ^ 2 / 2) ≤ V N)
    (hstep : ∀ k < N, V (k + 1) + 7 / 16 * w k ≤ V k + R ^ 2 / ((k : ℝ) + 1) ^ 2) : V N ≤ 2 * R ^ 2 ∧ ∑ k ∈ Finset.range N, w k ≤ 6 * R ^ 2 := by
  have hh := cumulative_energy V w (fun k => R ^ 2 / ((k : ℝ) + 1) ^ 2) (7 / 16) hstep
  rw [hzero, zero_add] at hh
  have he : (∑ k ∈ Finset.range N, R ^ 2 / ((k : ℝ) + 1) ^ 2) =
      R ^ 2 * ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he] at hh
  have hb := mul_le_mul_of_nonneg_left (reciprocal_square_sum N) (sq_nonneg R)
  have hn : 0 ≤ ∑ k ∈ Finset.range N, w k := Finset.sum_nonneg fun k hk => hw k (Finset.mem_range.mp hk)
  constructor <;> nlinarith [hlower, sq_nonneg R]

lemma fraction_le_log_increment {A a : ℝ} (hA : 0 < A) (ha : 0 ≤ a) :
    a / (A + a) ≤ Real.log (A + a) - Real.log A := by
  have hB : 0 < A + a := by positivity
  have hh := Real.one_sub_inv_le_log_of_pos (div_pos hB hA)
  rw [Real.log_div hB.ne' hA.ne'] at hh
  have he : 1 - ((A + a) / A)⁻¹ = a / (A + a) := by
    rw [inv_div]
    field_simp
    ring
  rwa [he] at hh

lemma fraction_sum_le_log (A a : ℕ → ℝ) (N : ℕ) (hA : ∀ k ≤ N, 0 < A k)
    (ha : ∀ k < N, 0 ≤ a k) (hrec : ∀ k < N, A (k + 1) = A k + a k) :
    ∑ k ∈ Finset.range N, a k / A (k + 1) ≤ Real.log (A N) - Real.log (A 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hi := ih (fun k hk => hA k (Nat.le_succ_of_le hk))
        (fun k hk => ha k (Nat.lt_succ_of_lt hk)) (fun k hk => hrec k (Nat.lt_succ_of_lt hk))
      have hh := fraction_le_log_increment (hA N (Nat.le_succ N)) (ha N (Nat.lt_succ_self N))
      rw [← hrec N (Nat.lt_succ_self N)] at hh
      linarith

lemma endpoint_path_bound (d alpha : ℕ → ℝ) {R L : ℝ} (hR : 0 < R)
    (henergy : ∑ k ∈ Finset.range N, (d k / alpha k) ^ 2 ≤ 6 * R ^ 2)
    (halpha : ∑ k ∈ Finset.range N, (alpha k) ^ 2 ≤ L)
    (hpositive : ∀ k < N, 0 < alpha k) :
    ∑ k ∈ Finset.range N, d k ≤ R * (3 + L / 2) := by
  have hp : ∀ k ∈ Finset.range N,
      d k ≤ R / 2 * (alpha k) ^ 2 + (d k / alpha k) ^ 2 / (2 * R) := by
    intro k hk
    have hak := (hpositive k (Finset.mem_range.mp hk)).ne'
    have he : alpha k * (d k / alpha k) = d k := by field_simp
    have hs := sq_nonneg (R * alpha k - d k / alpha k)
    have hd : (d k / alpha k) ^ 2 / (2 * R) * (2 * R) = (d k / alpha k) ^ 2 :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith [he]
  have hh := Finset.sum_le_sum hp
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div] at hh
  have h1 := mul_le_mul_of_nonneg_left halpha (by positivity : 0 ≤ R / 2)
  have h2 := (div_le_div_iff_of_pos_right (by positivity : 0 < 2 * R)).mpr henergy
  have he : 6 * R ^ 2 / (2 * R) = 3 * R := by field_simp; ring
  rw [he] at h2
  linarith

lemma fifth_power_from_moments {n B C D W : ℝ} (hn : 0 ≤ n) (hB : 0 ≤ B)
    (hW : 0 ≤ W)
    (h1 : n ^ 2 ≤ B * C) (h2 : C ^ 2 ≤ n * D) (h3 : D ^ 2 ≤ n * W) :
    n ^ 5 ≤ B ^ 4 * W := by
  have hh1 := pow_le_pow_left₀ (sq_nonneg n) h1 2
  have hh2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg B)
  have h4 : n ^ 4 ≤ B ^ 2 * n * D := by nlinarith only [hh1, hh2]
  have hh4 := pow_le_pow_left₀ (by positivity : 0 ≤ n ^ 4) h4 2
  have hh3 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ B ^ 4 * n ^ 2)
  have h8 : n ^ 3 * n ^ 5 ≤ n ^ 3 * (B ^ 4 * W) := by
    nlinarith only [hh4, hh3]
  rcases eq_or_lt_of_le hn with he | hp
  · rw [← he]; simpa using mul_nonneg (pow_nonneg hB 4) hW
  · exact (mul_le_mul_iff_right₀ (pow_pos hp 3)).mp h8

lemma reciprocal_fourth_moment {ι : Type*} (s : Finset ι) (b : ι → ℝ)
    (hb : ∀ i ∈ s, 0 < b i) :
    (s.card : ℝ) ^ 5 ≤ (∑ i ∈ s, b i) ^ 4 * ∑ i ∈ s, (b i)⁻¹ ^ 4 := by
  have h1 := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun i hi => (hb i hi).le) (fun i hi => (inv_pos.mpr (hb i hi)).le)
    (r := fun _ => (1 : ℝ)) (fun i hi => by simp [(hb i hi).ne'])
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => (b i)⁻¹)
  have h3 := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => (b i)⁻¹ ^ 2)
  simp only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, one_mul] at h1 h2 h3
  have he : (∑ i ∈ s, ((b i)⁻¹ ^ 2) ^ 2) = ∑ i ∈ s, (b i)⁻¹ ^ 4 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at h3
  exact fifth_power_from_moments (by positivity)
    (Finset.sum_nonneg fun i hi => (hb i hi).le)
    (Finset.sum_nonneg fun _ _ => by positivity) h1 h2 h3

lemma step_over_sqrt_le {A a : ℝ} (hA : 0 ≤ A) (ha : 0 < a) :
    a / Real.sqrt (A + a) ≤ 2 * (Real.sqrt (A + a) - Real.sqrt A) := by
  have hB : 0 < A + a := by positivity
  have hs : 0 < Real.sqrt (A + a) := Real.sqrt_pos.mpr hB
  have hmono := Real.sqrt_le_sqrt (le_add_of_nonneg_right ha.le : A ≤ A + a)
  have hsqA := Real.sq_sqrt hA
  have hsqB := Real.sq_sqrt hB.le
  apply (div_le_iff₀ hs).mpr
  nlinarith [sq_nonneg (Real.sqrt (A + a) - Real.sqrt A)]

lemma sum_step_over_sqrt (A a : ℕ → ℝ) (N : ℕ) (hA : ∀ k ≤ N, 0 ≤ A k)
    (ha : ∀ k < N, 0 < a k) (hrec : ∀ k < N, A (k + 1) = A k + a k) :
    ∑ k ∈ Finset.range N, a k / Real.sqrt (A (k + 1)) ≤
      2 * (Real.sqrt (A N) - Real.sqrt (A 0)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hi := ih (fun k hk => hA k (Nat.le_succ_of_le hk))
        (fun k hk => ha k (Nat.lt_succ_of_lt hk)) (fun k hk => hrec k (Nat.lt_succ_of_lt hk))
      have hh := step_over_sqrt_le (hA N (Nat.le_succ N)) (ha N (Nat.lt_succ_self N))
      rw [← hrec N (Nat.lt_succ_self N)] at hh
      linarith

lemma mass_growth (A a : ℕ → ℝ) {H R : ℝ} {N : ℕ} (hA : ∀ k ≤ N, 0 ≤ A k)
    (ha : ∀ k < N, 0 < a k) (hrec : ∀ k < N, A (k + 1) = A k + a k)
    (hbound : ∑ k ∈ Finset.range N, A (k + 1) ^ 2 / a k ^ 4 ≤ 98304 * H ^ 2 * R ^ 2) :
    (N : ℝ) ^ 5 ≤ 1572864 * (A N) ^ 2 * H ^ 2 * R ^ 2 := by
  have hAp : ∀ k < N, 0 < A (k + 1) := by
    intro k hk
    rw [hrec k hk]
    exact add_pos_of_nonneg_of_pos (hA k hk.le) (ha k hk)
  have hb : ∀ k < N, 0 < a k / Real.sqrt (A (k + 1)) := by
    intro k hk
    exact div_pos (ha k hk) (Real.sqrt_pos.mpr (hAp k hk))
  have hh := reciprocal_fourth_moment (Finset.range N)
    (fun k => a k / Real.sqrt (A (k + 1))) (fun k hk => hb k (Finset.mem_range.mp hk))
  simp only [Finset.card_range] at hh
  have he : (∑ k ∈ Finset.range N, (a k / Real.sqrt (A (k + 1)))⁻¹ ^ 4) =
      ∑ k ∈ Finset.range N, A (k + 1) ^ 2 / a k ^ 4 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [inv_div, div_pow]
    have hs := Real.sq_sqrt (hAp k (Finset.mem_range.mp hk)).le
    congr 1
    nlinarith only [sq_nonneg (Real.sqrt (A (k + 1)) ^ 2 - A (k + 1)), hs]
  rw [he] at hh
  have hs := sum_step_over_sqrt A a N hA ha hrec
  have hs' : (∑ k ∈ Finset.range N, a k / Real.sqrt (A (k + 1))) ≤ 2 * Real.sqrt (A N) := by
    linarith [Real.sqrt_nonneg (A 0)]
  have hp := pow_le_pow_left₀ (Finset.sum_nonneg fun k hk => (hb k (Finset.mem_range.mp hk)).le) hs' 4
  have hn : 0 ≤ ∑ k ∈ Finset.range N, A (k + 1) ^ 2 / a k ^ 4 :=
    Finset.sum_nonneg fun k _ => by positivity
  have hc := mul_le_mul hp hbound hn (by positivity : 0 ≤ (2 * Real.sqrt (A N)) ^ 4)
  have hsN := Real.sq_sqrt (hA N le_rfl)
  have heN : (2 * Real.sqrt (A N)) ^ 4 = 16 * (A N) ^ 2 := by
    calc
      _ = 16 * (Real.sqrt (A N) ^ 2) ^ 2 := by ring
      _ = _ := by rw [hsN]
  rw [heN] at hc
  nlinarith only [hh, hc]

lemma large_step_weight {B a H d : ℝ}
    (hd : 1 / 128 ≤ a * H * d) :
    B ^ 2 / a ^ 4 ≤ 16384 * H ^ 2 * ((B / a) ^ 2 * d ^ 2) := by
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 128) hd 2
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 16384 * B ^ 2 / a ^ 4)
  have he : (16384 * B ^ 2 / a ^ 4) * (1 / 128 : ℝ) ^ 2 = B ^ 2 / a ^ 4 := by ring
  have he' : (16384 * B ^ 2 / a ^ 4) * (a * H * d) ^ 2 =
      16384 * H ^ 2 * ((B / a) ^ 2 * d ^ 2) := by field_simp
  simpa only [he, he'] using hm

lemma large_step_sum (B a d : ℕ → ℝ) {H R : ℝ}
    (hd : ∀ k < N, 1 / 128 ≤ a k * H * d k)
    (henergy : ∑ k ∈ Finset.range N, (B k / a k) ^ 2 * d k ^ 2 ≤ 6 * R ^ 2) :
    ∑ k ∈ Finset.range N, B k ^ 2 / a k ^ 4 ≤ 98304 * H ^ 2 * R ^ 2 := by
  have hh := Finset.sum_le_sum fun k hk => large_step_weight
    (B := B k) (hd k (Finset.mem_range.mp hk))
  rw [← Finset.mul_sum] at hh
  have hp := mul_le_mul_of_nonneg_left henergy (by positivity : 0 ≤ 16384 * H ^ 2)
  nlinarith only [hh, hp]

lemma weighted_path_bound {ι : Type*} (s : Finset ι) (a t : ι → ℝ) {R A : ℝ}
    (hR : 0 ≤ R) (hA : 0 ≤ A) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hsum : ∑ i ∈ s, a i ≤ A) (henergy : ∑ i ∈ s, t i ^ 2 ≤ 6 * R ^ 2) :
    ∑ i ∈ s, a i * t i ≤ 3 * R * A := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq s a t
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg ha
  have hsum0 : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg ha
  have hp := pow_le_pow_left₀ hsum0 hsum 2
  have hss : ∑ i ∈ s, a i ^ 2 ≤ A ^ 2 := hsq.trans hp
  have hm := mul_le_mul hss henergy (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (sq_nonneg A)
  have hh : (∑ i ∈ s, a i * t i) ^ 2 ≤ 6 * (R * A) ^ 2 := by
    nlinarith only [hc, hm]
  have hRA : 0 ≤ R * A := mul_nonneg hR hA
  by_contra hn
  have hg : 3 * R * A < ∑ i ∈ s, a i * t i := lt_of_not_ge hn
  have hq := mul_self_lt_mul_self (by nlinarith : 0 ≤ 3 * R * A) hg
  nlinarith [sq_nonneg (R * A)]

lemma radius_recurrence (A a D d : ℕ → ℝ) {R : ℝ} {N : ℕ} (hzero : A 0 = 0)
    (hrec : ∀ k < N, A (k + 1) = A k + a k)
    (hstep : ∀ k < N, A (k + 1) * D (k + 1) ≤
      A k * D k + 2 * a k * R + A (k + 1) * d k / 4) :
    A N * D N ≤ 2 * A N * R + (∑ k ∈ Finset.range N, A (k + 1) * d k) / 4 := by
  induction N with
  | zero => simp [hzero]
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hi := ih (fun k hk => hrec k (Nat.lt_succ_of_lt hk))
        (fun k hk => hstep k (Nat.lt_succ_of_lt hk))
      have hh := hstep N (Nat.lt_succ_self N)
      rw [hrec N (Nat.lt_succ_self N)] at hh ⊢
      nlinarith only [hi, hh]

lemma sum_steps_eq_mass (A a : ℕ → ℝ) {N : ℕ} (hzero : A 0 = 0)
    (hrec : ∀ k < N, A (k + 1) = A k + a k) :
    ∑ k ∈ Finset.range N, a k = A N := by
  induction N with
  | zero => simp [hzero]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih (fun k hk => hrec k (Nat.lt_succ_of_lt hk)),
        hrec N (Nat.lt_succ_self N)]

lemma radius_energy_bound (A a D d : ℕ → ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hzero : A 0 = 0) (ha : ∀ k < N, 0 < a k) (hN : 0 < A N)
    (hrec : ∀ k < N, A (k + 1) = A k + a k)
    (hstep : ∀ k < N, A (k + 1) * D (k + 1) ≤
      A k * D k + 2 * a k * R + A (k + 1) * d k / 4)
    (henergy : ∑ k ∈ Finset.range N, (A (k + 1) / a k) ^ 2 * d k ^ 2 ≤ 6 * R ^ 2) :
    D N ≤ 3 * R := by
  have hsum := sum_steps_eq_mass A a hzero hrec
  have he : ∑ k ∈ Finset.range N, ((A (k + 1) / a k) * d k) ^ 2 ≤ 6 * R ^ 2 := by
    simpa only [mul_pow] using henergy
  have hp := weighted_path_bound (Finset.range N) a (fun k => A (k + 1) / a k * d k)
    hR hN.le (fun k hk => (ha k (Finset.mem_range.mp hk)).le) hsum.le he
  have hid : (∑ k ∈ Finset.range N, a k * (A (k + 1) / a k * d k)) =
      ∑ k ∈ Finset.range N, A (k + 1) * d k := by
    apply Finset.sum_congr rfl
    intro k hk
    field_simp [(ha k (Finset.mem_range.mp hk)).ne']
  rw [hid] at hp
  have hr := radius_recurrence A a D d hzero hrec hstep
  have hh : A N * D N ≤ A N * (3 * R) := by
    have hn := mul_nonneg hR hN.le
    nlinarith only [hr, hp, hn]
  exact (mul_le_mul_iff_right₀ hN).mp hh

lemma normalized_energy_step {A a R V W d : ℝ} (ha : 0 < a) (k : ℕ)
    (hstep : 2 * a ^ 2 * (W - V) + 7 / 8 * (A + a) ^ 2 * d ^ 2 ≤
      2 * (A + a) ^ 2 * ((a / (A + a)) * R / ((k : ℝ) + 1)) ^ 2)
    (hB : A + a ≠ 0) :
    W + 7 / 16 * ((A + a) / a) ^ 2 * d ^ 2 ≤ V + R ^ 2 / ((k : ℝ) + 1) ^ 2 := by
  have hk : (k : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
  have he : 2 * (A + a) ^ 2 * ((a / (A + a)) * R / ((k : ℝ) + 1)) ^ 2 =
      2 * a ^ 2 * (R ^ 2 / ((k : ℝ) + 1) ^ 2) := by field_simp
  rw [he] at hstep
  apply (mul_le_mul_iff_right₀ (by positivity : 0 < 2 * a ^ 2)).mp
  have hw : 2 * a ^ 2 * (7 / 16 * ((A + a) / a) ^ 2 * d ^ 2) =
      7 / 8 * (A + a) ^ 2 * d ^ 2 := by field_simp; ring
  nlinarith only [hstep, hw]

lemma local_displacement_bound {V W t R error : ℝ} (hR : 0 ≤ R)
    (hV : V ≤ 2 * R ^ 2) (hW : -(R ^ 2 / 2) ≤ W) (herror : error ≤ R ^ 2)
    (hstep : W + 7 / 16 * t ^ 2 ≤ V + error) : t ≤ 3 * R := by
  have ht : t ^ 2 ≤ 8 * R ^ 2 := by nlinarith only [hV, hW, herror, hstep]
  by_contra hn
  have hg : 3 * R < t := lt_of_not_ge hn
  have hh := mul_self_lt_mul_self (by positivity : 0 ≤ 3 * R) hg
  nlinarith [sq_nonneg R]

lemma local_radius_bound {A a D W t R : ℝ} (hA : 0 ≤ A) (ha : 0 < a) (hR : 0 ≤ R)
    (hD : D ≤ 3 * R) (ht : t ≤ 3 * R)
    (hstep : (A + a) * W ≤ A * D + 2 * a * R + a * t / 4) : W ≤ 3 * R := by
  have h1 := mul_le_mul_of_nonneg_left hD hA
  have h2 := mul_le_mul_of_nonneg_left ht ha.le
  have hh : (A + a) * W ≤ (A + a) * (3 * R) := by
    nlinarith [mul_nonneg ha.le hR]
  exact (mul_le_mul_iff_right₀ (by positivity : 0 < A + a)).mp hh

lemma fraction_sum_from_zero (A a : ℕ → ℝ) {N : ℕ} {base upper : ℝ}
    (hbase : 0 < base) (hupper : base ≤ upper) (hzero : A 0 = 0)
    (hA : ∀ k, 0 < k → k ≤ N → base ≤ A k)
    (ha : ∀ k < N, 0 < a k) (hrec : ∀ k < N, A (k + 1) = A k + a k)
    (hlast : A N ≤ upper) :
    ∑ k ∈ Finset.range N, a k / A (k + 1) ≤ 1 + Real.log (upper / base) := by
  have hu : 0 < upper := hbase.trans_le hupper
  cases N with
  | zero =>
      simp only [Finset.sum_range_zero]
      have hr : 1 ≤ upper / base := (le_div_iff₀ hbase).mpr (by simpa using hupper)
      have hl := Real.log_nonneg hr
      linarith
  | succ N =>
      have hA1 := hA 1 (by omega) (by omega)
      have ht := fraction_sum_le_log (fun k => A (k + 1)) (fun k => a (k + 1)) N
        (fun k hk => hbase.trans_le (hA _ (by omega) (by omega)))
        (fun k hk => (ha _ (by omega)).le) (fun k hk => hrec _ (by omega))
      have he : A 1 = a 0 := by simpa only [hzero, zero_add] using hrec 0 (by omega)
      have hfirst : a 0 / A 1 = 1 := by rw [he, div_self (ha 0 (by omega)).ne']
      have hlog1 := Real.log_le_log hbase hA1
      have hlogN := Real.log_le_log (hbase.trans_le (hA _ (by omega) le_rfl)) hlast
      rw [Real.log_div hu.ne' hbase.ne', Finset.sum_range_succ', hfirst]
      linarith only [ht, hlog1, hlogN]

end LongTails.Proofs.CohypomonotoneNewtonEnergy
