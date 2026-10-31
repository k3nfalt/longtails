import LongTails.Proofs.SeparationTrajectory
import LongTails.Proofs.GaussianLinear

namespace LongTails.Proofs.SgdSeparation

open MeasureTheory ProbabilityTheory
open LongTails.Proofs.SeparationInstance LongTails.Proofs.SeparationTrajectory
open LongTails.Proofs.GaussianBlocks LongTails.Proofs.GaussianLinear

noncomputable def weight (ρ κ : ℝ) (B : ℕ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | t + 1, k => if k < B * t then ρ * weight ρ κ B t k else -κ / B

lemma stiff_linear (ℓ c s η : ℝ) (φ : FlatShape) {B : ℕ} (ξ : ℕ → ℝ) (t : ℕ) :
    (sgdScalar ℓ c s η φ B ξ t).1 =
      ∑ k ∈ Finset.range (B * t), weight (1 - η * ℓ) (η * s) B t k * ξ k := by
  induction t with
  | zero => simp [sgdScalar]
  | succ t ih =>
      simp only [sgdScalar]
      rw [ih, Nat.mul_succ, Finset.sum_range_add]
      have h1 : (∑ k ∈ Finset.range (B * t), weight (1 - η * ℓ) (η * s) B (t + 1) k * ξ k) =
          (1 - η * ℓ) * ∑ k ∈ Finset.range (B * t), weight (1 - η * ℓ) (η * s) B t k * ξ k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        simp only [weight, Finset.mem_range.mp hk, ↓reduceIte]
        ring
      have h2 : (∑ j ∈ Finset.range B, weight (1 - η * ℓ) (η * s) B (t + 1) (B * t + j) *
          ξ (B * t + j)) = -(η * s) * blockMean B t ξ := by
        simp only [weight, show ∀ j, ¬ (B * t + j < B * t) from fun j => by omega, ↓reduceIte,
          blockMean, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [h1, h2]
      ring

lemma weight_sq_sum (ρ κ : ℝ) {B : ℕ} (hB : 0 < B) (t : ℕ) :
    (∑ k ∈ Finset.range (B * t), weight ρ κ B t k ^ 2) =
      κ ^ 2 / B * ∑ j ∈ Finset.range t, (ρ ^ 2) ^ j := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Nat.mul_succ, Finset.sum_range_add]
      have h1 : (∑ k ∈ Finset.range (B * t), weight ρ κ B (t + 1) k ^ 2) =
          ρ ^ 2 * ∑ k ∈ Finset.range (B * t), weight ρ κ B t k ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        simp only [weight, Finset.mem_range.mp hk, ↓reduceIte]
        ring
      have h2 : (∑ j ∈ Finset.range B, weight ρ κ B (t + 1) (B * t + j) ^ 2) = κ ^ 2 / B := by
        simp only [weight, show ∀ j, ¬ (B * t + j < B * t) from fun j => by omega, ↓reduceIte,
          Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hb : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
        field_simp
      rw [h1, h2, ih, Finset.sum_range_succ', pow_zero, mul_add, Finset.mul_sum, Finset.mul_sum,
        Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro j _
        ring
      · ring

lemma stiff_abs_integral (ℓ c s η : ℝ) (φ : FlatShape) {B : ℕ} (hB : 0 < B) (t : ℕ) :
    Integrable (fun ξ => |(sgdScalar ℓ c s η φ B ξ t).1|) stdStream ∧
    (4 / 9) * Real.sqrt ((η * s) ^ 2 / B * ∑ j ∈ Finset.range t, ((1 - η * ℓ) ^ 2) ^ j) ≤
      ∫ ξ, |(sgdScalar ℓ c s η φ B ξ t).1| ∂stdStream := by
  have hlaw := linear_law (weight (1 - η * ℓ) (η * s) B t) (B * t)
  rw [weight_sq_sum _ _ hB] at hlaw
  have he : (fun ξ => |(sgdScalar ℓ c s η φ B ξ t).1|) =
      fun ξ : ℕ → ℝ => |∑ k ∈ Finset.range (B * t),
        weight (1 - η * ℓ) (η * s) B t k * ξ k| := by
    funext ξ
    simp [stiff_linear ℓ c s η φ ξ t]
  have hV : 0 ≤ (η * s) ^ 2 / B * ∑ j ∈ Finset.range t, ((1 - η * ℓ) ^ 2) ^ j := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun j _ => pow_nonneg (sq_nonneg _) _
  have hmeas : Measurable (fun ξ : ℕ → ℝ => ∑ k ∈ Finset.range (B * t),
      weight (1 - η * ℓ) (η * s) B t k * ξ k) := by fun_prop
  rw [he]
  constructor
  · apply (integrable_map_measure (g := fun x : ℝ => |x|) (by fun_prop) hmeas.aemeasurable).mp
    rw [hlaw]
    exact ((memLp_id_gaussianReal 1).integrable le_rfl).abs
  · rw [← integral_map (f := fun x : ℝ => |x|) hmeas.aemeasurable (by fun_prop), hlaw]
    exact gaussian_abs_lower _ hV

lemma flat_le (ℓ c s η : ℝ) (φ : FlatShape) (hη : 0 ≤ η) (hc : 0 ≤ c) (B : ℕ) (ξ : ℕ → ℝ)
    (t : ℕ) : (sgdScalar ℓ c s η φ B ξ t).2 ≤ η * c * t := by
  induction t with
  | zero => simp [sgdScalar]
  | succ t ih =>
      simp only [sgdScalar]
      have hb := φ.bounded (sgdScalar ℓ c s η φ B ξ t).2
      have : -(η * (c * φ.slope (sgdScalar ℓ c s η φ B ξ t).2)) ≤ η * c := by
        have h1 : -(φ.slope (sgdScalar ℓ c s η φ B ξ t).2) ≤ 1 := by
          linarith [neg_abs_le (φ.slope (sgdScalar ℓ c s η φ B ξ t).2), abs_le.mp hb]
        nlinarith [mul_nonneg hη hc]
      push_cast
      linarith

lemma flat_independent (ℓ c s η : ℝ) (φ : FlatShape) (B : ℕ) (ξ ζ : ℕ → ℝ) (t : ℕ) :
    (sgdScalar ℓ c s η φ B ξ t).2 = (sgdScalar ℓ c s η φ B ζ t).2 := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [sgdScalar, ih]

lemma geometric_lower {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (h : ℕ) :
    (h : ℝ) / (1 + h * (1 - q)) ≤ ∑ j ∈ Finset.range h, q ^ j := by
  set δ := 1 - q with hδ
  have hδpos : 0 < δ := by linarith
  have hqle : q ≤ 1 / (1 + δ) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  have hpow : q ^ h ≤ 1 / (1 + h * δ) := by
    have h1 : q ^ h ≤ (1 / (1 + δ)) ^ h := pow_le_pow_left₀ hq hqle h
    have h2 : 1 + h * δ ≤ (1 + δ) ^ h := one_add_mul_le_pow (by linarith) h
    rw [div_pow, one_pow] at h1
    exact h1.trans (one_div_le_one_div_of_le (by positivity) h2)
  have hgeom : (∑ j ∈ Finset.range h, q ^ j) = (1 - q ^ h) / δ := by
    rw [geom_sum_eq hq1.ne, hδ, div_eq_div_iff (sub_ne_zero.mpr hq1.ne) (sub_ne_zero.mpr hq1.ne')]
    ring
  rw [hgeom, le_div_iff₀ hδpos]
  have hden : 0 < 1 + h * δ := by positivity
  have : (h : ℝ) / (1 + h * δ) * δ = 1 - 1 / (1 + h * δ) := by
    field_simp
    ring
  rw [this]
  linarith

lemma ratio_mono {ℓ u v : ℝ} (hℓ : 0 ≤ ℓ) (hv : 0 ≤ v) (huv : v ≤ u) :
    v / (1 + 2 * ℓ * v) ≤ u / (1 + 2 * ℓ * u) := by
  rw [div_le_div_iff₀ (by positivity) (by nlinarith)]
  nlinarith

lemma stiff_variance_lower {ℓ η s : ℝ} (hℓ : 0 ≤ ℓ) (hη : 0 ≤ η) {B : ℕ} (hB : 0 < B) (h : ℕ) :
    (η * s) ^ 2 / B * (h / (1 + 2 * (η * ℓ) * h)) ≤
      (η * s) ^ 2 / B * ∑ j ∈ Finset.range h, ((1 - η * ℓ) ^ 2) ^ j := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  by_cases hq : (1 - η * ℓ) ^ 2 < 1
  · have hg := geometric_lower (sq_nonneg (1 - η * ℓ)) hq h
    refine le_trans ?_ hg
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
    have : 1 - (1 - η * ℓ) ^ 2 ≤ 2 * (η * ℓ) := by nlinarith [sq_nonneg (η * ℓ)]
    nlinarith [Nat.cast_nonneg (α := ℝ) h]
  · push Not at hq
    have hge : (h : ℝ) ≤ ∑ j ∈ Finset.range h, ((1 - η * ℓ) ^ 2) ^ j := by
      calc (h : ℝ) = ∑ _j ∈ Finset.range h, (1 : ℝ) := by simp
        _ ≤ _ := Finset.sum_le_sum fun j _ => one_le_pow₀ hq
    refine le_trans ?_ hge
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hη hℓ) (Nat.cast_nonneg (α := ℝ) h), Nat.cast_nonneg (α := ℝ) h]

set_option maxHeartbeats 1000000 in
lemma sgd_scalar_bound {ℓ c s η ε w D : ℝ} {R B T : ℕ} (hℓ : 0 < ℓ) (hc : 0 < c) (hη : 0 < η)
    (hε : 0 < ε) (hw : 0 < w) (hB : 0 < B) (hRc : (R : ℝ) * c = 4 * ε)
    (hD : 3 / 4 ≤ ℓ * (D - w) / c) (hDw : 0 < D - w)
    (hsucc : (∑ t ∈ Finset.range (T + 1), ∫ ξ, (|ℓ * (sgdScalar ℓ c s η (valleyShape hw D) B ξ t).1| +
        R * |c * (valleyShape hw D).slope (sgdScalar ℓ c s η (valleyShape hw D) B ξ t).2|)
          ∂stdStream) ≤ (T + 1) * ε) :
    ℓ * s ^ 2 * (D - w) / (81 / 2 * c * ε ^ 2) ≤ (B : ℝ) * (T + 1) := by
  set φ := valleyShape hw D
  let X := fun t (ξ : ℕ → ℝ) => (sgdScalar ℓ c s η φ B ξ t).1
  let Y := fun t => (sgdScalar ℓ c s η φ B (fun _ => 0) t).2
  have hY (t : ℕ) (ξ : ℕ → ℝ) : (sgdScalar ℓ c s η φ B ξ t).2 = Y t :=
    flat_independent ℓ c s η φ B ξ (fun _ => 0) t
  have hXi (t : ℕ) := (stiff_abs_integral ℓ c s η φ hB t).1
  have hsplit (t : ℕ) : (∫ ξ, (|ℓ * (sgdScalar ℓ c s η φ B ξ t).1| +
      R * |c * φ.slope (sgdScalar ℓ c s η φ B ξ t).2|) ∂stdStream) =
        ℓ * (∫ ξ, |X t ξ| ∂stdStream) + R * |c * φ.slope (Y t)| := by
    simp_rw [hY t, abs_mul, abs_of_pos hℓ]
    rw [integral_add ((hXi t).const_mul ℓ) (integrable_const _), integral_const_mul,
      integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    rfl
  simp_rw [hsplit, Finset.sum_add_distrib] at hsucc
  have hstiff_nonneg (t : ℕ) : 0 ≤ ℓ * ∫ ξ, |X t ξ| ∂stdStream :=
    mul_nonneg hℓ.le (integral_nonneg fun _ => abs_nonneg _)
  have hflat_nonneg (t : ℕ) : 0 ≤ (R : ℝ) * |c * φ.slope (Y t)| :=
    mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  have hflat (t : ℕ) (ht : η * c * t ≤ D - w) : 2 * ε ≤ (R : ℝ) * |c * φ.slope (Y t)| := by
    have hy : Y t ≤ D - w := (flat_le ℓ c s η φ hη.le hc.le B (fun _ => 0) t).trans ht
    have hsl := valleySlope_far hw hy
    have : c / 2 ≤ |c * φ.slope (Y t)| := by
      change c / 2 ≤ |c * valleySlope w D (Y t)|
      rw [abs_mul, abs_of_pos hc]
      have : 1 / 2 ≤ |valleySlope w D (Y t)| := by
        rw [abs_of_neg (by linarith)]; linarith
      nlinarith
    nlinarith
  set K := ⌊(D - w) / (η * c)⌋₊
  have hKT : 2 * (K + 1) ≤ T + 1 := by
    by_contra hcon
    push Not at hcon
    set n0 := min (T + 1) (K + 1)
    have hsub : Finset.range n0 ⊆ Finset.range (T + 1) := Finset.range_mono (min_le_left _ _)
    have hcount : 2 * ε * n0 ≤ ∑ t ∈ Finset.range (T + 1), (R : ℝ) * |c * φ.slope (Y t)| := by
      calc 2 * ε * n0 = ∑ _t ∈ Finset.range n0, 2 * ε := by simp; ring
        _ ≤ ∑ t ∈ Finset.range n0, (R : ℝ) * |c * φ.slope (Y t)| := by
          apply Finset.sum_le_sum
          intro t ht
          apply hflat
          have ht' : t ≤ K := by
            have := Finset.mem_range.mp ht
            omega
          have hK : (K : ℝ) ≤ (D - w) / (η * c) := Nat.floor_le (by positivity)
          have : (t : ℝ) ≤ (D - w) / (η * c) := (Nat.cast_le.mpr ht').trans hK
          rw [le_div_iff₀ (by positivity)] at this
          linarith
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => hflat_nonneg t)
    have hstiff_sum := Finset.sum_nonneg (fun t (_ : t ∈ Finset.range (T + 1)) => hstiff_nonneg t)
    have hn0 : (T + 1 : ℝ) < 2 * n0 := by
      have : T + 1 < 2 * n0 := by
        simp only [n0]
        rcases le_total (T + 1) (K + 1) with h | h
        · rw [min_eq_left h]; omega
        · rw [min_eq_right h]; omega
      exact_mod_cast this
    nlinarith
  have hT1 : 1 ≤ T := by omega
  have htravel : 2 * (D - w) / c < η * (T + 1) := by
    have hlt : (D - w) / (η * c) < K + 1 := Nat.lt_floor_add_one _
    have h2 : (2 * (K + 1) : ℝ) ≤ T + 1 := by exact_mod_cast hKT
    rw [div_lt_iff₀ (by positivity)] at hlt
    rw [div_lt_iff₀ hc]
    nlinarith
  set h' := (T + 1) / 2
  have hh'1 : 1 ≤ h' := by omega
  have hh'3 : (T + 1 : ℝ) ≤ 3 * h' := by
    have : T + 1 ≤ 3 * h' := by omega
    exact_mod_cast this
  let V := fun t : ℕ => (η * s) ^ 2 / B * ∑ j ∈ Finset.range t, ((1 - η * ℓ) ^ 2) ^ j
  have hVmono : Monotone V := by
    intro a b hab
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
      (fun j _ _ => pow_nonneg (sq_nonneg _) _)
  have hXlow (t : ℕ) : (4 / 9) * Real.sqrt (V t) ≤ ∫ ξ, |X t ξ| ∂stdStream :=
    (stiff_abs_integral ℓ c s η φ hB t).2
  have hstiff_total : ((T + 1 : ℝ) - h') * (ℓ * ((4 / 9) * Real.sqrt (V h'))) ≤ (T + 1) * ε := by
    have hfs := Finset.sum_nonneg (fun t (_ : t ∈ Finset.range (T + 1)) => hflat_nonneg t)
    have hsub : Finset.Ico h' (T + 1) ⊆ Finset.range (T + 1) := by
      intro t ht; simp only [Finset.mem_Ico, Finset.mem_range] at ht ⊢; omega
    calc ((T + 1 : ℝ) - h') * (ℓ * ((4 / 9) * Real.sqrt (V h'))) =
          ∑ _t ∈ Finset.Ico h' (T + 1), ℓ * ((4 / 9) * Real.sqrt (V h')) := by
            rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
            push_cast [show h' ≤ T + 1 by omega]
            ring
      _ ≤ ∑ t ∈ Finset.Ico h' (T + 1), ℓ * ∫ ξ, |X t ξ| ∂stdStream := by
            apply Finset.sum_le_sum
            intro t ht
            apply mul_le_mul_of_nonneg_left _ hℓ.le
            refine le_trans ?_ (hXlow t)
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact Real.sqrt_le_sqrt (hVmono (Finset.mem_Ico.mp ht).1)
      _ ≤ ∑ t ∈ Finset.range (T + 1), ℓ * ∫ ξ, |X t ξ| ∂stdStream :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => hstiff_nonneg t)
      _ ≤ (T + 1) * ε := by linarith
  have hhalf : (T + 1 : ℝ) / 2 ≤ (T + 1 : ℝ) - h' := by
    have : (2 * h' : ℝ) ≤ T + 1 := by exact_mod_cast (show 2 * h' ≤ T + 1 by omega)
    linarith
  have hsqrt : ℓ * Real.sqrt (V h') ≤ 9 / 2 * ε := by
    have h1 : (T + 1 : ℝ) / 2 * (ℓ * ((4 / 9) * Real.sqrt (V h'))) ≤ (T + 1) * ε :=
      le_trans (mul_le_mul_of_nonneg_right hhalf (by positivity)) hstiff_total
    have hT : (0 : ℝ) < T + 1 := by positivity
    nlinarith
  have hVb : ℓ ^ 2 * V h' ≤ (9 / 2 * ε) ^ 2 := by
    have hv0 : 0 ≤ V h' := by
      apply mul_nonneg (by positivity)
      exact Finset.sum_nonneg fun j _ => pow_nonneg (sq_nonneg _) _
    have := pow_le_pow_left₀ (by positivity) hsqrt 2
    rwa [mul_pow, Real.sq_sqrt hv0] at this
  have hlow := stiff_variance_lower (s := s) hℓ.le hη.le hB h'
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hu : 2 * (D - w) / (3 * c) ≤ η * h' := by
    have : η * (T + 1) ≤ η * (3 * h') := mul_le_mul_of_nonneg_left hh'3 hη.le
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hc] at htravel
    nlinarith
  have hratio := ratio_mono hℓ.le (by positivity) hu
  have hden : 1 + 2 * ℓ * (2 * (D - w) / (3 * c)) ≤ 8 / 3 * (ℓ * (D - w) / c) := by
    have : ℓ * (2 * (D - w) / (3 * c)) = 2 / 3 * (ℓ * (D - w) / c) := by ring
    nlinarith
  have hquarter : 1 / (4 * ℓ) ≤ η * h' / (1 + 2 * ℓ * (η * h')) := by
    refine le_trans ?_ hratio
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 2 * (D - w) / (3 * c) * (4 * ℓ) = 8 / 3 * (ℓ * (D - w) / c) := by
      field_simp; ring
    nlinarith
  have hmain : ℓ ^ 2 * ((η * s) ^ 2 / B * (h' / (1 + 2 * (η * ℓ) * h'))) ≤ (9 / 2 * ε) ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_left hlow (by positivity)) hVb
  have hform : ℓ ^ 2 * ((η * s) ^ 2 / B * (h' / (1 + 2 * (η * ℓ) * h'))) =
      ℓ ^ 2 * s ^ 2 * η / B * (η * h' / (1 + 2 * ℓ * (η * h'))) := by
    field_simp
  rw [hform] at hmain
  have hstep : ℓ ^ 2 * s ^ 2 * η / B * (1 / (4 * ℓ)) ≤ (9 / 2 * ε) ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_left hquarter (by positivity)) hmain
  have hstep' : ℓ * s ^ 2 * η ≤ 81 * ε ^ 2 * B := by
    have : ℓ ^ 2 * s ^ 2 * η / B * (1 / (4 * ℓ)) = ℓ * s ^ 2 * η / (4 * B) := by
      field_simp
    rw [this, div_le_iff₀ (by positivity)] at hstep
    nlinarith
  rw [div_le_iff₀ (by positivity)]
  rw [div_lt_iff₀ hc] at htravel
  nlinarith [mul_le_mul_of_nonneg_left htravel.le (show 0 ≤ ℓ * s ^ 2 by positivity)]

end LongTails.Proofs.SgdSeparation
