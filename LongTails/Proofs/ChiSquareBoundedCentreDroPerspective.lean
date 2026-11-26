import LongTails.Algorithms.ChiSquareBoundedCentreDro
import LongTails.Proofs.ChiSquareObjective
import LongTails.Proofs.ChiSquarePerspective

open MeasureTheory Set
namespace OracleTemplate.ChiSquareBoundedCentreDro
open ChiSquareDro LongTails.Setups.ChiSquareConstrainedDro
noncomputable section

def payoff (ρ z a l w : ℝ) := w*z + (1-w)*a + l*(ρ - (w-1)^2/2)

def majorant (ρ z a l : ℝ) := a-l + max (z-(a-l)) 0 ^ 2 / (2*l) + (1+2*ρ)*l/2

lemma weight_nonneg {z a l : ℝ} (hl : 0 < l) : 0 ≤ weight z a l :=
  div_nonneg (le_max_right _ _) hl.le

lemma payoff_gap {ρ z a l w : ℝ} (hl : 0 < l) (hw : 0 ≤ w) :
    payoff ρ z a l w + l/2*(weight z a l-w)^2 ≤ majorant ρ z a l := by
  unfold majorant payoff weight
  rcases le_total (z-(a-l)) 0 with h | h
  · rw [max_eq_right h]
    simp only [zero_div, zero_sub, even_two.neg_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hw h]
  · rw [max_eq_left h]
    apply le_of_eq
    field_simp
    ring

lemma payoff_weight {ρ z a l : ℝ} (hl : 0 < l) :
    payoff ρ z a l (weight z a l) = majorant ρ z a l := by
  unfold payoff weight majorant
  rcases le_total (z-(a-l)) 0 with h|h
  · rw [max_eq_right h]; simp; ring
  · rw [max_eq_left h]; field_simp; ring

lemma payoff_le {ρ z a l w : ℝ} (hl : 0 < l) (hw : 0 ≤ w) :
    payoff ρ z a l w ≤ majorant ρ z a l := by
  linarith [payoff_gap (ρ := ρ) (z := z) (a := a) hl hw,
    mul_nonneg (show 0 ≤ l/2 by positivity) (sq_nonneg (weight z a l-w))]

lemma scale_rise {ρ z a l l' : ℝ} (hl : 0 < l) (hle : l ≤ l') :
    majorant ρ z a l' ≤ majorant ρ z a l + ρ*(l'-l) := by
  let v := weight z a l'
  have h := payoff_le (ρ := ρ) (z := z) (a := a) hl (weight_nonneg (z := z) (a := a) (hl.trans_le hle))
  rw [← payoff_weight (hl.trans_le hle)]
  change payoff ρ z a l' v ≤ _
  change payoff ρ z a l v ≤ _ at h
  unfold payoff at *
  nlinarith [mul_nonneg (sub_nonneg.mpr hle) (sq_nonneg (v-1))]

lemma clamp_centre {ρ z a l B : ℝ} (hl : 0 < l) (hz : z ∈ Icc 0 B) :
    majorant ρ z (max 0 (min B a)) l ≤ majorant ρ z a l := by
  let b := max 0 (min B a)
  let v := weight z b l
  have h := payoff_le (ρ := ρ) (z := z) (a := a) hl (weight_nonneg (z := z) (a := b) hl)
  change majorant ρ z b l ≤ _
  rw [← payoff_weight hl]
  change payoff ρ z b l v ≤ _
  refine le_trans ?_ h
  suffices (1-v)*b ≤ (1-v)*a by unfold payoff; linarith
  rcases le_total a 0 with ha|ha
  · have hb : b = 0 := max_eq_left ((min_le_right _ _).trans ha)
    have hv : 1 ≤ v := by
      dsimp [v, weight]; rw [hb, le_div_iff₀ hl]; linarith [le_max_left (z-(0-l)) 0, hz.1]
    exact mul_le_mul_of_nonpos_left (hb ▸ ha) (by linarith)
  · rcases le_total a B with haB|haB
    · simp [b, min_eq_right haB, max_eq_right ha]
    · have hb : b = B := by simp [b, min_eq_left haB, max_eq_right (hz.1.trans hz.2)]
      have hv : v ≤ 1 := by
        dsimp [v, weight]; rw [hb, div_le_iff₀ hl]; apply max_le <;> linarith [hz.2]
      exact mul_le_mul_of_nonneg_left (hb ▸ haB) (by linarith)

lemma weight_width {z a l B : ℝ} (hl : 0 < l) (hz : z ∈ Icc 0 B) (ha : a ∈ Icc 0 B) :
    |weight z a l - 1| ≤ B / l := by
  unfold weight
  rw [abs_le]
  constructor
  · field_simp [hl]
    linarith [le_max_left (z-(a-l)) 0, hz.1, ha.2]
  · have hu : max (z-(a-l)) 0 ≤ B+l := max_le (by linarith [hz.2, ha.1]) (by linarith [hz.1, hz.2])
    field_simp [hl]
    linarith

lemma support {ρ z z' a a' l l' b : ℝ} (hl : 0 < l) (hl' : 0 < l') (h : z + b ≤ z') :
    let v := weight z a l
    majorant ρ z a l + v*b + (1-v)*(a'-a) + (ρ-(v-1)^2/2)*(l'-l) ≤ majorant ρ z' a' l' := by
  dsimp only
  rw [← payoff_weight hl]
  refine le_trans ?_ (payoff_le hl' (weight_nonneg (z := z) (a := a) hl))
  unfold payoff
  nlinarith [mul_le_mul_of_nonneg_left h (weight_nonneg (z := z) (a := a) hl)]

variable {Ω : Type*} [MeasurableSpace Ω] (p : Measure Ω) [IsProbabilityMeasure p]

def Q (ρ : ℝ) (Z : Ω → ℝ) (a l : ℝ) := ∫ ω, majorant ρ (Z ω) a l ∂p

lemma majorant_integrable {Z : Ω → ℝ} {B : ℝ} (hm : Measurable Z) (hb : ∀ ω, Z ω ≤ B)
    (ρ a l : ℝ) : Integrable (fun ω => majorant ρ (Z ω) a l) p :=
  ((integrable_const _).add ((integrable_tail_sq p hm hb (a-l)).div_const _)).add (integrable_const _)

lemma Q_eq {Z : Ω → ℝ} {B : ℝ} (hm : Measurable Z) (hb : ∀ ω, Z ω ≤ B) (ρ a l : ℝ) :
    Q p ρ Z a l = a-l + sq p Z (a-l)/(2*l) + (1+2*ρ)*l/2 := by
  have hi := (integrable_tail_sq p hm hb (a-l)).div_const (2*l)
  unfold Q majorant
  change (∫ ω, (a-l + tail Z (a-l) ω ^ 2 / (2*l)) + _ ∂p) = _
  rw [integral_add (f := fun ω => a-l + tail Z (a-l) ω ^ 2 / (2*l)) (g := fun _ => (1+2*ρ)*l/2) ((integrable_const _).add hi) (integrable_const _),
    integral_add (integrable_const _) hi, integral_div]
  simp [ChiSquareDro.sq]

lemma Q_ge {Z : Ω → ℝ} {B : ℝ} (hm : Measurable Z) (hb : ∀ ω, Z ω ≤ B)
    (hz : ∀ ω, 0 ≤ Z ω) (ρ a : ℝ) {l : ℝ} (hl : 0 < l) : ρ*l ≤ Q p ρ Z a l := by
  have h := integral_mono (μ := p) (integrable_const (ρ*l)) (majorant_integrable p hm hb ρ a l)
    fun ω => show ρ*l ≤ majorant ρ (Z ω) a l by
      have H := payoff_le (ρ := ρ) (z := Z ω) (a := a) hl (show (0:ℝ) ≤ 1 by norm_num)
      simp [payoff] at H
      linarith [hz ω]
  simpa [Q] using h

end
end OracleTemplate.ChiSquareBoundedCentreDro
