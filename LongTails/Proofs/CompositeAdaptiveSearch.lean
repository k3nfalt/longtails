import LongTails.Proofs.CompositeAdaptiveInitialization
import LongTails.Algorithms.RadiusCompositeAccelerated

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.CompositeAdaptive

lemma initial_trial_safe {A S L1 H d : ℝ} (hA : 0 < A) (hL1 : 0 ≤ L1)
    (hcurvature : A * S ≤ 1) (hmovement : A * L1 * H ≤ 2)
    (hd : d ≤ (A / 16) * H) :
    (A / 16) ^ 2 * S / (A + A / 16) ≤ 1 / 32 ∧
      L1 * ((A / 16) / (A + A / 16)) * d ≤ 1 / 32 := by
  have hc : (A / 16) ^ 2 * S / (A + A / 16) = A * S / 272 := by
    field_simp
    ring
  have ht : (A / 16) / (A + A / 16) = 1 / 17 := by field_simp; ring
  rw [hc, ht]
  have hm := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ L1 * (1 / 17))
  constructor <;> nlinarith

open OracleTemplate.CompositeGeneralized

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma query_parameter_difference {A a b : ℝ} (hA : 0 < A) (ha : 0 < a)
    (hb : 0 < b) (x v : E) :
    mixPoint A b x v - mixPoint A a x v =
      (A * (b - a) / ((A + a) * (A + b))) • (v - x) := by
  have hAa : 0 < A + a := by positivity
  have hAb : 0 < A + b := by positivity
  have he : b / (A + b) - a / (A + a) = A * (b - a) / ((A + a) * (A + b)) := by
    field_simp
    ring
  calc
    _ = (mixPoint A b x v - x) - (mixPoint A a x v - x) := by abel
    _ = (b / (A + b) - a / (A + a)) • (v - x) := by
      rw [mix_sub_left hAb, mix_sub_left hAa, sub_smul]
    _ = _ := by rw [he]

lemma query_parameter_distance {A a b δ r : ℝ} (hA : 0 < A) (ha : 0 < a)
    (hab : a ≤ b) (hδ : 0 ≤ δ) (hb : b ≤ (1 + δ) * a)
    {x v xs : E} (hx : ‖x - xs‖ ≤ r) (hv : ‖v - xs‖ ≤ r) :
    ‖mixPoint A b x v - mixPoint A a x v‖ ≤ 2 * r * δ * a / (A + a) := by
  have hb0 : 0 < b := ha.trans_le hab
  have hAa : 0 < A + a := by positivity
  have hAb : 0 < A + b := by positivity
  have hc0 : 0 ≤ A * (b - a) / ((A + a) * (A + b)) := by positivity
  have hn : ‖v - x‖ ≤ 2 * r := by
    have hh := norm_sub_le (v - xs) (x - xs)
    rw [show (v - xs) - (x - xs) = v - x by abel] at hh
    linarith
  have hc : A * (b - a) / ((A + a) * (A + b)) ≤ δ * a / (A + a) := by
    apply (div_le_div_iff₀ (mul_pos hAa hAb) hAa).mpr
    have hh : b - a ≤ δ * a := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hh (mul_nonneg hA.le hAa.le)
    nlinarith [mul_nonneg (mul_nonneg hδ ha.le) (mul_nonneg hAa.le hb0.le)]
  rw [query_parameter_difference hA ha hb0, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
  have hh := mul_le_mul hc hn (norm_nonneg _) (by positivity : 0 ≤ δ * a / (A + a))
  convert hh using 1
  ring

lemma query_parameter_distance_small {A a b δ r : ℝ} (hA : 0 < A) (ha : 0 < a)
    (haA : a ≤ A) (hab : a ≤ b) (hδ : 0 ≤ δ) (hb : b ≤ (1 + δ) * a)
    {x v xs : E} (hx : ‖x - xs‖ ≤ r) (hv : ‖v - xs‖ ≤ r) :
    ‖mixPoint A b x v - mixPoint A a x v‖ ≤ r * δ := by
  have hr : 0 ≤ r := (norm_nonneg _).trans hx
  have hh := query_parameter_distance hA ha hab hδ hb hx hv
  have hbound : 2 * r * δ * a / (A + a) ≤ r * δ := by
    apply (div_le_iff₀ (by positivity : 0 < A + a)).mpr
    nlinarith [mul_le_mul_of_nonneg_left haA (mul_nonneg hr hδ)]
  exact hh.trans hbound

lemma exp_small {t : ℝ} (ht : t ≤ 1 / 4) : Real.exp t ≤ 4 / 3 := by
  have hb := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 : ℝ) / 4 < 1)
  norm_num at hb
  exact (Real.exp_le_exp.mpr ht).trans hb

lemma query_curvature_stability {g : E → E} {L0 L1 A a b δ r : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hg : Continuous g)
    (hs : SymmetricSmooth g L0 L1) (hA : 0 < A) (ha : 0 < a) (haA : a ≤ A)
    (hab : a ≤ b) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 10)
    (hb : b ≤ (1 + δ) * a) (hlocal : L1 * r * δ ≤ 1 / 4)
    {x v xs : E} (hx : ‖x - xs‖ ≤ r) (hv : ‖v - xs‖ ≤ r) :
    b ^ 2 * (L0 + L1 * ‖g (mixPoint A b x v)‖) / (A + b) ≤
      2 * (a ^ 2 * (L0 + L1 * ‖g (mixPoint A a x v)‖) / (A + a)) := by
  have hb0 : 0 < b := ha.trans_le hab
  have hd := query_parameter_distance_small hA ha haA hab hδ hb hx hv
  have he : Real.exp (L1 * ‖mixPoint A b x v - mixPoint A a x v‖) ≤ 4 / 3 := by
    apply exp_small
    nlinarith [mul_le_mul_of_nonneg_left hd hL1]
  have hgrowth := symmetric_gradient_growth_nonneg hg hL1 hs
    (mixPoint A b x v) (mixPoint A a x v)
  have hSa : 0 ≤ L0 + L1 * ‖g (mixPoint A a x v)‖ := by positivity
  have hSb : L0 + L1 * ‖g (mixPoint A b x v)‖ ≤
      (4 / 3) * (L0 + L1 * ‖g (mixPoint A a x v)‖) := by
    nlinarith [mul_le_mul_of_nonneg_left he hSa]
  have hba : b ≤ (11 / 10) * a := by nlinarith
  have hsq : b ^ 2 ≤ (3 / 2) * a ^ 2 := by nlinarith [sq_nonneg (b - 11 / 10 * a)]
  calc
    _ ≤ ((3 / 2) * a ^ 2 * ((4 / 3) * (L0 + L1 * ‖g (mixPoint A a x v)‖))) /
        (A + a) := by
      gcongr
    _ = _ := by ring

lemma trial_weight_ratio_bounds {A a b δ : ℝ} (hA : 0 < A) (ha : 0 < a)
    (hab : a ≤ b) (hδsmall : δ ≤ 1 / 10) (hb : b ≤ (1 + δ) * a) :
    (b / (A + b)) * (1 + δ) ≤ (3 / 2) * (a / (A + a)) ∧
      b ^ 2 / (A + b) ≤ (3 / 2) * (a ^ 2 / (A + a)) := by
  have hb0 : 0 < b := ha.trans_le hab
  have hba : b ≤ (11 / 10) * a := by nlinarith
  have hsq : b ^ 2 ≤ (3 / 2) * a ^ 2 := by nlinarith [sq_nonneg (b - 11 / 10 * a)]
  have hlin : b * (1 + δ) ≤ (3 / 2) * a := by
    have hh := mul_le_mul_of_nonneg_left hδsmall hb0.le
    nlinarith
  constructor
  · calc
      _ = (b * (1 + δ)) / (A + b) := by ring
      _ ≤ ((3 / 2) * a) / (A + a) := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ ((3 / 2) * a ^ 2) / (A + a) := by gcongr
      _ = _ := by ring

lemma trial_displacement_stability {A a b δ r S da db : ℝ}
    (hA : 0 < A) (ha : 0 < a) (hab : a ≤ b) (hδ : 0 ≤ δ)
    (hδsmall : δ ≤ 1 / 10) (hb : b ≤ (1 + δ) * a)
    (hr : 0 ≤ r) (hS : 0 ≤ S) (hda : 0 ≤ da)
    (hprox : db ≤ (1 + δ) * da + b * S * (4 / 3) * (r * δ)) :
    (b / (A + b)) * db ≤ (3 / 2) * ((a / (A + a)) * da) +
      2 * (a ^ 2 * S / (A + a)) * (r * δ) := by
  have hb0 : 0 < b := ha.trans_le hab
  have ht : 0 ≤ b / (A + b) := by positivity
  have hp := mul_le_mul_of_nonneg_left hprox ht
  have hrat := trial_weight_ratio_bounds hA ha hab hδsmall hb
  have hfirst := mul_le_mul_of_nonneg_right hrat.1 hda
  have hsecond := mul_le_mul_of_nonneg_right hrat.2
    (by positivity : 0 ≤ S * (4 / 3) * (r * δ))
  have hid : (b / (A + b)) * (b * S * (4 / 3) * (r * δ)) =
      (b ^ 2 / (A + b)) * (S * (4 / 3) * (r * δ)) := by ring
  have hie : ((3 / 2) * (a ^ 2 / (A + a))) * (S * (4 / 3) * (r * δ)) =
      2 * (a ^ 2 * S / (A + a)) * (r * δ) := by ring
  rw [hie] at hsecond
  rw [mul_add, hid] at hp
  nlinarith

lemma query_prox_displacement_stability {g : E → E} {ψ : E → ℝ} {Q : Set E}
    {L0 L1 A a b δ r : ℝ} (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hg : Continuous g)
    (hs : SymmetricSmooth g L0 L1) (hQ : Convex ℝ Q) (hψ : ConvexOn ℝ Q ψ)
    (hA : 0 < A) (ha : 0 < a) (haA : a ≤ A) (hab : a ≤ b)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 10) (hb : b ≤ (1 + δ) * a)
    (hlocal : L1 * r * δ ≤ 1 / 4) {x v xs p q : E}
    (hx : ‖x - xs‖ ≤ r) (hv : ‖v - xs‖ ≤ r) (hp : p ∈ Q) (hq : q ∈ Q)
    (hpa : IsMinOn (fun w => ‖w - v‖ ^ 2 / (2 * a) +
      ⟪g (mixPoint A a x v), w - v⟫ + ψ w) Q p)
    (hqb : IsMinOn (fun w => ‖w - v‖ ^ 2 / (2 * b) +
      ⟪g (mixPoint A b x v), w - v⟫ + ψ w) Q q) :
    (b / (A + b)) * ‖q - v‖ ≤ (3 / 2) * ((a / (A + a)) * ‖p - v‖) +
      2 * (a ^ 2 * (L0 + L1 * ‖g (mixPoint A a x v)‖) / (A + a)) * (r * δ) := by
  have hb0 : 0 < b := ha.trans_le hab
  have hr : 0 ≤ r := (norm_nonneg _).trans hx
  have hd := query_parameter_distance_small hA ha haA hab hδ hb hx hv
  have he : Real.exp (L1 * ‖mixPoint A b x v - mixPoint A a x v‖) ≤ 4 / 3 := by
    apply exp_small
    nlinarith [mul_le_mul_of_nonneg_left hd hL1]
  have hSa : 0 ≤ L0 + L1 * ‖g (mixPoint A a x v)‖ := by positivity
  have hgd : ‖g (mixPoint A a x v) - g (mixPoint A b x v)‖ ≤
      (L0 + L1 * ‖g (mixPoint A a x v)‖) * (4 / 3) * (r * δ) := by
    rw [norm_sub_rev]
    have hh := symmetric_gradient_difference_nonneg hg hL0 hL1 hs
      (mixPoint A b x v) (mixPoint A a x v)
    exact hh.trans (by gcongr)
  have hratio0 : 0 ≤ b / a - 1 := by rw [sub_nonneg, le_div_iff₀ ha]; linarith
  have hratio : |b / a - 1| ≤ δ := by
    rw [abs_of_nonneg hratio0]
    have hh := (div_le_iff₀ ha).mpr hb
    linarith
  have hpq := prox_parameter_sensitivity hQ hψ ha hb0 hp hq hpa hqb
  have htri : ‖q - v‖ ≤ ‖q - p‖ + ‖p - v‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (q - p) (p - v)
  have hrat := mul_le_mul_of_nonneg_right hratio (norm_nonneg (p - v))
  have hdiff := mul_le_mul_of_nonneg_left hgd hb0.le
  apply trial_displacement_stability hA ha hab hδ hδsmall hb hr hSa (norm_nonneg _)
  nlinarith

lemma half_threshold_safe {Ca Cb Da Db L1 r δ : ℝ} (hL1 : 0 ≤ L1)
    (hCa : 0 ≤ Ca) (hlocal : L1 * r * δ ≤ 1 / 4)
    (hC : Ca ≤ 1 / 64) (hD : L1 * Da ≤ 1 / 64)
    (hcurve : Cb ≤ 2 * Ca) (hmove : Db ≤ (3 / 2) * Da + 2 * Ca * (r * δ)) :
    Cb ≤ 1 / 32 ∧ L1 * Db ≤ 1 / 32 := by
  have hm := mul_le_mul_of_nonneg_left hmove hL1
  have hl := mul_le_mul_of_nonneg_left hlocal hCa
  constructor <;> nlinarith

lemma nearby_trial_safe {g : E → E} {ψ : E → ℝ} {Q : Set E}
    {L0 L1 A a b δ r : ℝ} (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hg : Continuous g)
    (hs : SymmetricSmooth g L0 L1) (hQ : Convex ℝ Q) (hψ : ConvexOn ℝ Q ψ)
    (hA : 0 < A) (ha : 0 < a) (haA : a ≤ A) (hab : a ≤ b)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 10) (hb : b ≤ (1 + δ) * a)
    (hlocal : L1 * r * δ ≤ 1 / 4) {x v xs p q : E}
    (hx : ‖x - xs‖ ≤ r) (hv : ‖v - xs‖ ≤ r) (hp : p ∈ Q) (hq : q ∈ Q)
    (hpa : IsMinOn (fun w => ‖w - v‖ ^ 2 / (2 * a) +
      ⟪g (mixPoint A a x v), w - v⟫ + ψ w) Q p)
    (hqb : IsMinOn (fun w => ‖w - v‖ ^ 2 / (2 * b) +
      ⟪g (mixPoint A b x v), w - v⟫ + ψ w) Q q)
    (hC : a ^ 2 * (L0 + L1 * ‖g (mixPoint A a x v)‖) / (A + a) ≤ 1 / 64)
    (hD : L1 * ((a / (A + a)) * ‖p - v‖) ≤ 1 / 64) :
    b ^ 2 * (L0 + L1 * ‖g (mixPoint A b x v)‖) / (A + b) ≤ 1 / 32 ∧
      L1 * ((b / (A + b)) * ‖q - v‖) ≤ 1 / 32 := by
  apply half_threshold_safe hL1 (by positivity) hlocal hC hD
  · exact query_curvature_stability hL0 hL1 hg hs hA ha haA hab hδ hδsmall hb hlocal hx hv
  · exact query_prox_displacement_stability hL0 hL1 hg hs hQ hψ hA ha haA hab hδ
      hδsmall hb hlocal hx hv hp hq hpa hqb

lemma scaled_gradient_nearby {g : E → E} {L0 L1 : ℝ} (hL0 : 0 ≤ L0)
    (hL1 : 0 ≤ L1) (hg : Continuous g) (hs : SymmetricSmooth g L0 L1)
    {x y : E} (hd : L1 * ‖x - y‖ ≤ 3 / 64) :
    L0 + L1 * ‖g x‖ ≤ 2 * (L0 + L1 * ‖g y‖) ∧
      L1 * ‖g x - g y‖ ≤ (L0 + L1 * ‖g y‖) / 8 := by
  have hS : 0 ≤ L0 + L1 * ‖g y‖ := by positivity
  have he := exp_small (by linarith : L1 * ‖x - y‖ ≤ 1 / 4)
  have hE : (L0 + L1 * ‖g y‖) * Real.exp (L1 * ‖x - y‖) ≤
      (4 / 3) * (L0 + L1 * ‖g y‖) := by
    nlinarith [mul_le_mul_of_nonneg_left he hS]
  have hc := symmetric_gradient_growth_nonneg hg hL1 hs x y
  have hh := symmetric_gradient_difference_nonneg hg hL0 hL1 hs x y
  have hmul := mul_le_mul_of_nonneg_left hh hL1
  have hbound := mul_le_mul_of_nonneg_right hE (mul_nonneg hL1 (norm_nonneg (x - y)))
  have hdist := mul_le_mul_of_nonneg_left hd hS
  constructor <;> nlinarith

lemma restart_query_distance {A a L1 r : ℝ} (hA : 0 < A) (ha : 0 < a)
    (haA : a ≤ A) (hL1 : 0 ≤ L1) {x v xs y : E}
    (hx : ‖x - xs‖ ≤ r) (hv : ‖v - xs‖ ≤ r) (hprevious : L1 * ‖x - y‖ ≤ 1 / 32) :
    L1 * ‖mixPoint A (a / (128 * (1 + L1 * r))) x v - y‖ ≤ 3 / 64 := by
  let Q := 128 * (1 + L1 * r)
  have hr : 0 ≤ r := (norm_nonneg _).trans hx
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hb : 0 < a / Q := div_pos ha hQ
  have hsum : 0 < A + a / Q := by positivity
  have hn : ‖v - x‖ ≤ 2 * r := by
    have hh := norm_sub_le (v - xs) (x - xs)
    rw [show (v - xs) - (x - xs) = v - x by abel] at hh
    linarith
  have ht : (a / Q) / (A + a / Q) ≤ 1 / Q := by
    apply (div_le_div_iff₀ hsum hQ).mpr
    have he : a / Q * Q = a := div_mul_cancel₀ a hQ.ne'
    rw [he]
    linarith
  have hsmall : L1 * (1 / Q * (2 * r)) ≤ 1 / 64 := by
    have he : L1 * (1 / Q * (2 * r)) = (2 * L1 * r) / Q := by ring
    rw [he, div_le_iff₀ hQ]
    dsimp [Q]
    linarith
  have hquery : L1 * ‖mixPoint A (a / Q) x v - x‖ ≤ 1 / 64 := by
    rw [mix_sub_left hsum, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hb hsum)]
    have hh := mul_le_mul ht hn (norm_nonneg _) (one_div_nonneg.mpr hQ.le)
    exact (mul_le_mul_of_nonneg_left hh hL1).trans hsmall
  have htri : ‖mixPoint A (a / Q) x v - y‖ ≤
      ‖mixPoint A (a / Q) x v - x‖ + ‖x - y‖ := by
    simpa only [sub_add_sub_cancel] using
      norm_add_le (mixPoint A (a / Q) x v - x) (x - y)
  have hm := mul_le_mul_of_nonneg_left htri hL1
  change L1 * ‖mixPoint A (a / Q) x v - y‖ ≤ 3 / 64
  linarith

lemma restart_trial_safe {A a b S Sb L1 d dg db : ℝ} (hA : 0 < A)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a / 2) (hS : 0 ≤ S)
    (hSb0 : 0 ≤ Sb) (hSb : Sb ≤ 2 * S) (hL1 : 0 ≤ L1) (hd : 0 ≤ d)
    (hdg : 0 ≤ dg) (hgrad : L1 * dg ≤ S / 8)
    (hcurvature : a ^ 2 * S / A ≤ 1 / 32) (hmovement : L1 * a * d / A ≤ 1 / 32)
    (hprox : db ≤ b * (dg + d / a)) :
    b ^ 2 * Sb / (A + b) ≤ 1 / 32 ∧ L1 * (b / (A + b)) * db ≤ 1 / 32 := by
  have hsq : b ^ 2 ≤ a ^ 2 / 4 := by nlinarith
  have hcurv : b ^ 2 * Sb / (A + b) ≤ (1 / 2) * (a ^ 2 * S / A) := by
    calc
      _ ≤ (a ^ 2 / 4) * (2 * S) / A := by gcongr; linarith
      _ = _ := by ring
  have hmove : L1 * (b / (A + b)) * db ≤
      (1 / 32) * (a ^ 2 * S / A) + (1 / 4) * (L1 * a * d / A) := by
    calc
      _ ≤ L1 * (b / (A + b)) * (b * (dg + d / a)) := by gcongr
      _ = (b ^ 2 / (A + b)) * (L1 * dg + L1 * d / a) := by ring
      _ ≤ ((a ^ 2 / 4) / A) * (S / 8 + L1 * d / a) := by gcongr; linarith
      _ = _ := by field_simp; ring
  constructor <;> nlinarith

lemma restart_query_safe {g : E → E} {ψ : E → ℝ} {D : Set E}
    {L0 L1 A a r : ℝ} (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hg : Continuous g)
    (hs : SymmetricSmooth g L0 L1) (hD : Convex ℝ D) (hψ : ConvexOn ℝ D ψ)
    (hA : 0 < A) (ha : 0 < a) (haA : a ≤ A) {x v xs y z p : E}
    (hx : ‖x - xs‖ ≤ r) (hv : ‖v - xs‖ ≤ r)
    (hprevious : L1 * ‖x - y‖ ≤ 1 / 32) (hvD : v ∈ D) (hpD : p ∈ D)
    (hold : IsMinOn (fun w => ‖w - z‖ ^ 2 / (2 * a) + ⟪g y, w - z⟫ + ψ w) D v)
    (hcurvature : a ^ 2 * (L0 + L1 * ‖g y‖) / A ≤ 1 / 32)
    (hmovement : L1 * a * ‖v - z‖ / A ≤ 1 / 32)
    (hnew : IsMinOn (fun w => ‖w - v‖ ^ 2 / (2 * (a / (128 * (1 + L1 * r)))) +
      ⟪g (mixPoint A (a / (128 * (1 + L1 * r))) x v), w - v⟫ + ψ w) D p) :
    let b := a / (128 * (1 + L1 * r))
    b ^ 2 * (L0 + L1 * ‖g (mixPoint A b x v)‖) / (A + b) ≤ 1 / 32 ∧
      L1 * (b / (A + b)) * ‖p - v‖ ≤ 1 / 32 := by
  let b := a / (128 * (1 + L1 * r))
  have hr : 0 ≤ r := (norm_nonneg _).trans hx
  have hden : 0 < 128 * (1 + L1 * r) := by positivity
  have hb : 0 < b := div_pos ha hden
  have hba : b ≤ a / 2 := by
    apply div_le_div_of_nonneg_left ha.le (by norm_num)
    nlinarith [mul_nonneg hL1 hr]
  have hnear := restart_query_distance hA ha haA hL1 hx hv hprevious
  have hgrad := scaled_gradient_nearby hL0 hL1 hg hs hnear
  have hprox := prox_displacement_from_previous hD hψ ha hb hvD hpD hold hnew
  exact restart_trial_safe hA ha hb hba (by positivity) (by positivity) hgrad.1 hL1
    (norm_nonneg _) (norm_nonneg _) hgrad.2 hcurvature hmovement hprox

lemma first_query_safe {g : E → E} {ψ : E → ℝ} {D : Set E}
    {L0 L1 R : ℝ} (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (hR : 0 ≤ R)
    (hg : Continuous g) (hs : SymmetricSmooth g L0 L1)
    (hD : Convex ℝ D) (hψ : ConvexOn ℝ D ψ) {x0 u p : E}
    (hu : u ∈ D) (hp : p ∈ D) (hd : ‖u - x0‖ ≤ 3 * R) :
    let a := 1 / ((L0 + L1 * ‖g x0‖) * Real.exp (L1 * R) + L0)
    let A := 1 / (8 * (L0 + L1 * ‖g x0‖) * Real.exp (4 * (L1 * R)))
    IsMinOn (fun w => ‖w - x0‖ ^ 2 / (2 * a) + ⟪g x0, w - x0⟫ + ψ w) D u →
    IsMinOn (fun w => ‖w - u‖ ^ 2 / (2 * (A / 16)) + ⟪g u, w - u⟫ + ψ w) D p →
    (A / 16) ^ 2 * (L0 + L1 * ‖g u‖) / (A + A / 16) ≤ 1 / 32 ∧
      L1 * ((A / 16) / (A + A / 16)) * ‖p - u‖ ≤ 1 / 32 := by
  intro a A hold hnew
  have hS : 0 < L0 + L1 * ‖g x0‖ := by positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hdata := initial_gradient_data hL0 hL1 hR hg hs hd
  have hsc := initial_trial_scales hS (mul_nonneg hL1 hR) hL1 rfl hdata.1 hdata.2
  have hprox := prox_displacement_from_previous hD hψ ha
    (by positivity : 0 < A / 16) hu hp hold hnew
  exact initial_trial_safe hA hL1 hsc.1 hsc.2 hprox

lemma refinement_bracket (P : ℝ → Prop) [DecidablePred P] {lo hi : ℝ}
    (hlo : 0 < lo) (horder : lo ≤ hi) (hsafe : P lo) (hunsafe : ¬ P hi) :
    let mid := (lo + hi) / 2
    let nextLo := if P mid then mid else lo
    let nextHi := if P mid then hi else mid
    0 < nextLo ∧ lo ≤ nextLo ∧ nextLo ≤ nextHi ∧ nextHi ≤ hi ∧
      nextHi - nextLo = (hi - lo) / 2 ∧ P nextLo ∧ ¬ P nextHi := by
  dsimp only
  by_cases hm : P ((lo + hi) / 2)
  · simp only [hm, ↓reduceIte]
    exact ⟨by linarith, by linarith, by linarith, le_rfl, by ring, trivial, hunsafe⟩
  · simp only [hm, ↓reduceIte]
    exact ⟨hlo, le_rfl, by linarith, by linarith, by ring, hsafe, by simp⟩

lemma refinement_count_precision {X : ℝ} (hX : 0 < X) :
    X ≤ (2 : ℝ) ^ (1 + ⌈Real.log X / Real.log 2⌉₊) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : Real.log X / Real.log 2 ≤ (⌈Real.log X / Real.log 2⌉₊ : ℝ) := Nat.le_ceil _
  have hh := (div_le_iff₀ hlog2).mp hc
  have he := Real.exp_le_exp.mpr hh
  rw [Real.exp_log hX, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he
  have hpow : (0 : ℝ) ≤ 2 ^ ⌈Real.log X / Real.log 2⌉₊ := by positivity
  rw [pow_add, pow_one]
  exact he.trans (by nlinarith)

end OracleTemplate.CompositeAdaptive
