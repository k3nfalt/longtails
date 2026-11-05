import LongTails.Algorithms.FiniteSumNondual
import LongTails.Proofs.FiniteSumNondualExecution
import LongTails.Proofs.FiniteSumNondualDomain
import LongTails.Proofs.FiniteSumNondualOuterGeometry
import LongTails.Proofs.FiniteSumNondualSampling

open Set Classical
open scoped RealInnerProductSpace

namespace LongTails.Proofs.FiniteSumNondualLineSearch

open LongTails.Setups.FiniteSumNondualSmoothConvex
open LongTails.Algorithms.FiniteSumNondual
open FiniteSumNondualExecution FiniteSumNondualDomain FiniteSumNondualOuterGeometry
open FiniteSumNondualSampling
open RecursiveEnvelopeGeometry (Model)
open OracleTemplate.ComponentEnvelope (Program)

lemma linePoint_val (p : Params) (z y : Feasible p) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (linePoint p z y t).val = z.val + t • (y.val - z.val) := by
  rw [linePoint, feasiblePoint_val p _
    (domain_convex p z.property y.property (sub_nonneg.mpr ht1) ht0 (by ring))]
  module

lemma linePoint_zero (p : Params) (z y : Feasible p) : linePoint p z y 0 = z := by
  apply Subtype.ext
  simp only [linePoint_val p z y le_rfl (by norm_num : (0 : ℝ) ≤ 1), zero_smul, add_zero]

lemma linePoint_one (p : Params) (z y : Feasible p) : linePoint p z y 1 = y := by
  apply Subtype.ext
  simp only [linePoint_val p z y (by norm_num : (0 : ℝ) ≤ 1) le_rfl, one_smul]
  module

lemma linePoint_sub (p : Params) (z y : Feasible p) {s t : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (linePoint p z y t).val - (linePoint p z y s).val = (t - s) • (y.val - z.val) := by
  rw [linePoint_val p z y ht0 ht1, linePoint_val p z y hs0 hs1]
  module

lemma line_coupling (p : Params) (μ : ℝ) (z y : Feasible p) (e : LineEndpoint p)
    (ht0 : 0 ≤ e.time) (ht1 : e.time ≤ 1) :
    ⟪μ • ((linePoint p z y e.time).val - e.certificate.point),
      (linePoint p z y e.time).val - z.val⟫ = e.time * lineSlope p μ z y e := by
  unfold lineSlope
  rw [linePoint_val p z y ht0 ht1, add_sub_cancel_left, inner_smul_right]

lemma slope_error (p : Params) {μ ρ : ℝ} (z y : Feasible p) (e : LineEndpoint p)
    (G : Point p → Point p)
    (herr : ‖μ • ((linePoint p z y e.time).val - e.certificate.point) - G (linePoint p z y e.time).val‖ ≤ ρ) :
    |lineSlope p μ z y e - ⟪G (linePoint p z y e.time).val, y.val - z.val⟫| ≤ 2 * p.R * ρ := by
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans herr
  have hd := domain_distance p y.property z.property
  unfold lineSlope
  rw [← inner_sub_left]
  have hh := (abs_real_inner_le_norm _ (y.val - z.val)).trans
    ((mul_le_mul_of_nonneg_right herr (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left hd hρ))
  nlinarith

lemma directional_difference (p : Params) {μ : ℝ} {F : Point p → ℝ} {G : Point p → Point p}
    (hf : Model μ F G) (z y : Feasible p) {s t : ℝ}
    (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) :
    ⟪G (linePoint p z y t).val, y.val - z.val⟫ -
      ⟪G (linePoint p z y s).val, y.val - z.val⟫ ≤ 4 * μ * p.R ^ 2 * (t - s) := by
  have hs1 := hst.trans ht1
  have ht0 := hs0.trans hst
  rw [← inner_sub_left]
  have hh := (real_inner_le_norm _ (y.val - z.val)).trans
    (mul_le_mul_of_nonneg_right (hf.lipschitz (linePoint p z y t).val (linePoint p z y s).val) (norm_nonneg _))
  rw [linePoint_sub p z y hs0 hs1 ht0 ht1, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hst)] at hh
  have hd := domain_distance p y.property z.property
  have hs := (sq_le_sq₀ (norm_nonneg _) (show 0 ≤ 2 * p.R by positivity [p.hR])).mpr hd
  have hm := mul_le_mul_of_nonneg_left hs (mul_nonneg hf.pos.le (sub_nonneg.mpr hst))
  nlinarith

lemma line_value (p : Params) {μ η : ℝ} {F : Point p → ℝ} {G : Point p → Point p}
    (hf : Model μ F G) (z y : Feasible p) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hη : 0 ≤ η) (hd : -η ≤ ⟪G (linePoint p z y t).val, y.val - z.val⟫) :
    F (linePoint p z y t).val ≤ F y.val + η := by
  have hh := hf.lower (linePoint p z y t).val y.val
  have he : y.val - (linePoint p z y t).val = (1 - t) • (y.val - z.val) := by
    rw [linePoint_val p z y ht0 ht1]
    module
  rw [he, inner_smul_right] at hh
  have hm := mul_le_mul_of_nonneg_left hd (sub_nonneg.mpr ht1)
  nlinarith

structure Bracket (p : Params) (μ : ℝ) (z y : Feasible p)
    (good : Feasible p → LongTails.Algorithms.FiniteSumNondualProx.Certificate (Point p) → Prop)
    (lo hi : LineEndpoint p) : Prop where
  lo_nonneg : 0 ≤ lo.time
  hi_le : hi.time ≤ 1
  ordered : lo.time ≤ hi.time
  lo_valid : good (linePoint p z y lo.time) lo.certificate
  hi_valid : good (linePoint p z y hi.time) hi.certificate
  lo_sign : lineSlope p μ z y lo ≤ 0
  hi_sign : 0 < lineSlope p μ z y hi

lemma bisect_contract (p : Params) (μ : ℝ) (z y : Feasible p)
    (good : Feasible p → LongTails.Algorithms.FiniteSumNondualProx.Certificate (Point p) → Prop)
    (k : ℕ) (lo hi : LineEndpoint p) (hb : Bracket p μ z y good lo hi) :
    Contract good (fun out => ∃ last, Bracket p μ z y good out last ∧
      last.time - out.time = (hi.time - lo.time) / (2 : ℝ) ^ k) (bisectPlan p μ z y k lo hi) := by
  induction k generalizing lo hi with
  | zero => exact ⟨hi, hb, by simp⟩
  | succ k ih =>
    change ∀ certificate, good (linePoint p z y ((lo.time + hi.time) / 2)) certificate → _
    intro certificate hc
    let mid : LineEndpoint p := ⟨(lo.time + hi.time) / 2, certificate⟩
    change Contract good _ (if lineSlope p μ z y mid ≤ 0 then
      bisectPlan p μ z y k mid hi else bisectPlan p μ z y k lo mid)
    have hlo := hb.lo_nonneg
    have hhi := hb.hi_le
    have hord := hb.ordered
    split_ifs with hs
    · have hm : Bracket p μ z y good mid hi :=
        ⟨by dsimp [mid]; linarith, hhi, by dsimp [mid]; linarith, hc, hb.hi_valid, hs, hb.hi_sign⟩
      apply contract_mono (ih mid hi hm)
      intro out hout
      obtain ⟨last, hlast, he⟩ := hout
      refine ⟨last, hlast, ?_⟩
      rw [he]
      dsimp only [mid]
      rw [pow_succ]
      field_simp
      ring
    · have hm : Bracket p μ z y good lo mid :=
        ⟨hlo, by dsimp [mid]; linarith, by dsimp [mid]; linarith, hb.lo_valid, hc, hb.lo_sign,
          lt_of_not_ge hs⟩
      apply contract_mono (ih lo mid hm)
      intro out hout
      obtain ⟨last, hlast, he⟩ := hout
      refine ⟨last, hlast, ?_⟩
      rw [he]
      dsimp only [mid]
      rw [pow_succ]
      field_simp
      ring

lemma bisect_within (p : Params) (μ : ℝ) (z y : Feasible p) (k : ℕ) (lo hi : LineEndpoint p) :
    Within k (bisectPlan p μ z y k lo hi) := by
  induction k generalizing lo hi with
  | zero => trivial
  | succ k ih =>
    change ∀ certificate, Within k _
    intro certificate
    dsimp only
    split_ifs <;> exact ih _ _

lemma line_within (p : Params) (μ : ℝ) (z y : Feasible p) (k : ℕ) :
    Within (k + 2) (linePlan p μ z y k) := by
  change ∀ first, Within (k + 1) _
  intro first
  dsimp only
  split_ifs
  · trivial
  · change ∀ last, Within k _
    intro last
    split_ifs
    · simp [Within]
    · exact bisect_within p μ z y k _ _

def LineResult (p : Params) (μ η : ℝ) (z y : Feasible p) (F : Point p → ℝ)
    (good : Feasible p → LongTails.Algorithms.FiniteSumNondualProx.Certificate (Point p) → Prop)
    (out : LineEndpoint p) : Prop :=
  0 ≤ out.time ∧ out.time ≤ 1 ∧ good (linePoint p z y out.time) out.certificate ∧
    ⟪μ • ((linePoint p z y out.time).val - out.certificate.point),
      (linePoint p z y out.time).val - z.val⟫ ≤ 0 ∧
    F (linePoint p z y out.time).val ≤ F y.val + η

lemma bracket_result (p : Params) {μ ρ η : ℝ} {F : Point p → ℝ} {G : Point p → Point p}
    (hf : Model μ F G) (z y : Feasible p)
    (good : Feasible p → LongTails.Algorithms.FiniteSumNondualProx.Certificate (Point p) → Prop)
    (herr : ∀ q out, good q out → ‖μ • (q.val - out.point) - G q.val‖ ≤ ρ)
    (hη : 0 ≤ η) (hρ : 2 * p.R * ρ ≤ η / 2)
    (lo hi : LineEndpoint p) (hb : Bracket p μ z y good lo hi)
    (hwidth : 4 * μ * p.R ^ 2 * (hi.time - lo.time) ≤ η / 2) :
    LineResult p μ η z y F good lo := by
  have hlo1 := hb.ordered.trans hb.hi_le
  refine ⟨hb.lo_nonneg, hlo1, hb.lo_valid, ?_, ?_⟩
  · rw [line_coupling p μ z y lo hb.lo_nonneg hlo1]
    exact mul_nonpos_of_nonneg_of_nonpos hb.lo_nonneg hb.lo_sign
  · have he := slope_error p z y hi G (herr _ _ hb.hi_valid)
    have he' := (abs_le.mp he).2
    have hd := directional_difference p hf z y hb.lo_nonneg hb.ordered hb.hi_le
    apply line_value p hf z y hb.lo_nonneg hlo1 hη
    have hs := hb.hi_sign
    linarith

lemma line_contract (p : Params) {μ ρ η : ℝ} {F : Point p → ℝ} {G : Point p → Point p}
    (hf : Model μ F G) (z y : Feasible p)
    (good : Feasible p → LongTails.Algorithms.FiniteSumNondualProx.Certificate (Point p) → Prop)
    (herr : ∀ q out, good q out → ‖μ • (q.val - out.point) - G q.val‖ ≤ ρ)
    (hη : 0 ≤ η) (hρ : 2 * p.R * ρ ≤ η / 2) (k : ℕ)
    (hprecision : 4 * μ * p.R ^ 2 / (2 : ℝ) ^ k ≤ η / 2) :
    Contract good (LineResult p μ η z y F good) (linePlan p μ z y k) := by
  change ∀ first, good z first → _
  intro first hfirst
  let lo : LineEndpoint p := ⟨0, first⟩
  change Contract good _ (if 0 ≤ lineSlope p μ z y lo then .done lo else _)
  split_ifs with hlo
  · change LineResult p μ η z y F good lo
    have ht0 : 0 ≤ lo.time := le_rfl
    have ht1 : lo.time ≤ 1 := by norm_num [lo]
    have hv : good (linePoint p z y lo.time) lo.certificate := by simpa only [lo, linePoint_zero] using hfirst
    refine ⟨ht0, ht1, hv, ?_, ?_⟩
    · rw [line_coupling p μ z y lo ht0 ht1]
      simp [lo]
    · have he := slope_error p z y lo G (herr _ _ hv)
      have he' := (abs_le.mp he).2
      apply line_value p hf z y ht0 ht1 hη
      linarith
  · change ∀ last, good y last → _
    intro last hlast
    let hi : LineEndpoint p := ⟨1, last⟩
    change Contract good _ (if lineSlope p μ z y hi ≤ 0 then .done hi else _)
    split_ifs with hhi
    · change LineResult p μ η z y F good hi
      have ht0 : 0 ≤ hi.time := by norm_num [hi]
      have ht1 : hi.time ≤ 1 := le_rfl
      refine ⟨ht0, ht1, ?_, ?_, ?_⟩
      · simpa only [hi, linePoint_one] using hlast
      · rw [line_coupling p μ z y hi ht0 ht1]
        simpa only [hi, one_mul] using hhi
      · simpa only [hi, linePoint_one] using le_add_of_nonneg_right hη
    · have hb : Bracket p μ z y good lo hi :=
        ⟨le_rfl, le_rfl, by norm_num [lo, hi], by simpa only [lo, linePoint_zero] using hfirst,
          by simpa only [hi, linePoint_one] using hlast, (lt_of_not_ge hlo).le, lt_of_not_ge hhi⟩
      apply contract_mono (bisect_contract p μ z y good k lo hi hb)
      intro out hout
      obtain ⟨last, hb', hw⟩ := hout
      apply bracket_result p hf z y good herr hη hρ out last hb'
      rw [hw]
      simpa only [lo, hi, sub_zero, mul_one_div] using hprecision

end LongTails.Proofs.FiniteSumNondualLineSearch
