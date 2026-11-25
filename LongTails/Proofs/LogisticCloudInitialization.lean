import LongTails.Proofs.LogisticCloudCoordinates
import LongTails.Proofs.GatedEscapeGaussian

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
open LongTails.Setups.LogisticDefectCloud

namespace LongTails.Proofs.LogisticCloudInitialization

variable {d : ℕ}

lemma strip (w : Weights d) (hw : ‖w‖ = 1) {r : ℝ} :
    stdGaussian (Weights d) {g | |⟪w,g⟫| < r} ≤ ENNReal.ofReal r := by
  let L := innerSL ℝ w
  have hm : (stdGaussian (Weights d)).map L = gaussianReal 0 1 := by
    rw [IsGaussian.map_eq_gaussianReal,integral_strongDual_stdGaussian,variance_dual_stdGaussian]
    simp [L,innerSL_apply_norm,hw]
  change stdGaussian (Weights d) (L ⁻¹' {z : ℝ | |z| < r}) ≤ _
  rw [← Measure.map_apply L.measurable (measurableSet_lt (by fun_prop) measurable_const),hm]
  refine (GatedEscapeGaussian.gaussianReal_le_of_diam _ (D := 2*r) ?_).trans ?_
  · intro x hx y hy
    change |x| < r at hx
    change |y| < r at hy
    linarith [abs_sub x y]
  · exact ENNReal.ofReal_le_ofReal (by linarith)

def Good {d : ℕ} (u v : Weights d) (ρ : ℝ) (g : Weights d) : Prop :=
  ρ/4 ≤ |⟪u,g⟫| ∧ ρ/4 ≤ |⟪v,g⟫| ∧ ‖g‖^2 ≤ 4/ρ*(d+2)

lemma failure (u v : Weights d) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {ρ : ℝ} (hρ : 0 < ρ) :
    stdGaussian (Weights d) {g | ¬Good u v ρ g} ≤ ENNReal.ofReal ρ := by
  let T := {g : Weights d | 4/ρ*(d+2) < ‖g‖^2}
  let A := {g : Weights d | |⟪u,g⟫| < ρ/4}
  let B := {g : Weights d | |⟪v,g⟫| < ρ/4}
  have hs : {g | ¬Good u v ρ g} ⊆ A ∪ B ∪ T := by
    intro g
    simp only [Good,Set.mem_ofPred_eq,Set.mem_union,A,B,T]
    grind
  have H := GatedEscapeGaussian.norm_sq_tail (E := Weights d) (4/ρ) (by positivity)
  have hd : Module.finrank ℝ (Weights d) = d+2 := by
    simp [Weights,add_comm]
  rw [hd,Nat.cast_add,Nat.cast_ofNat] at H
  have he : (fun z : Weights d => if 4/ρ*((d:ℝ)+2) < ‖z‖^2 then (1:ℝ) else 0) =
      T.indicator (fun _ => 1) := rfl
  rw [he,integral_indicator_const _ (measurableSet_lt measurable_const (by fun_prop)),
    smul_eq_mul,mul_one,measureReal_def] at H
  have hT : stdGaussian (Weights d) T ≤ ENNReal.ofReal (ρ/4) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ T)]
    apply ENNReal.ofReal_le_ofReal
    convert H using 1
    field_simp
  refine (measure_mono hs).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add ((measure_union_le A B).trans
    (add_le_add (strip u hu (r := ρ/4)) (strip v hv (r := ρ/4)))) hT).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

lemma projection {u v g : Weights d} {ρ r : ℝ} (hρ : 0 < ρ) (hρ' : ρ ≤ 1)
    (hr : 0 < r) (h : Good u v ρ g) :
    let w := (r/‖g‖) • g
    ‖w‖ = r ∧ ρ^2*r/(16*(d+2)) ≤ |⟪u,w⟫| ∧ ρ^2*r/(16*(d+2)) ≤ |⟪v,w⟫| := by
  obtain ⟨hu,hv,hg⟩ := h
  have hn : 0 < ‖g‖ := norm_pos_iff.mpr (by rintro rfl; simp at hu; linarith)
  have hd : (1:ℝ) ≤ d+2 := by linarith [Nat.cast_nonneg (α := ℝ) d]
  have hcap : ‖g‖ ≤ 4/ρ*((d:ℝ)+2) := by
    have hlarge : 1 ≤ 4/ρ*((d:ℝ)+2) := by
      rw [div_mul_eq_mul_div,le_div_iff₀ hρ]
      linarith
    by_contra! hn'
    have h1 := hlarge.trans hn'.le
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) hn.le]
  have hdir (a : Weights d) (ha : ρ/4 ≤ |⟪a,g⟫|) :
      ρ^2*r/(16*(d+2)) ≤ |⟪a,(r/‖g‖) • g⟫| := by
    rw [real_inner_smul_right,abs_mul,abs_of_pos (div_pos hr hn)]
    apply le_trans _ (mul_le_mul_of_nonneg_left ha (div_pos hr hn).le)
    rw [div_le_iff₀ (by positivity)]
    field_simp [hn.ne',hρ.ne'] at hcap ⊢
    nlinarith [mul_le_mul_of_nonneg_right hcap (mul_nonneg hρ.le hr.le)]
  refine ⟨?_,hdir u hu,hdir v hv⟩
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hr hn),div_mul_cancel₀ _ hn.ne']

end LongTails.Proofs.LogisticCloudInitialization
