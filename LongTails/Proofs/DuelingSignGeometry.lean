import LongTails.Proofs.DuelingSignFamily
import LongTails.Proofs.DuelingReferenceDrift

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped RealInnerProductSpace
open LongTails.Setups.StronglyConvexDueling
open LongTails.Setups.FlatTransferDueling (model)

namespace LongTails.Proofs.DuelingSignFamily

open FiniteSumNondualLowerComponents DuelingReferenceDrift

noncomputable def scale (p : LongTails.Setups.FlatTransferDueling.Params) : ℝ :=
  Real.sqrt (1024*p.ε / p.d)

lemma scale_pos {p : LongTails.Setups.FlatTransferDueling.Params} (hε : 0 < p.ε) :
    0 < scale p := by
  have hd : 0 < (p.d : ℝ) := by exact_mod_cast NeZero.pos p.d
  unfold scale; positivity

lemma scale_sq (p : LongTails.Setups.FlatTransferDueling.Params) (hε : 0 ≤ p.ε) :
    (p.d : ℝ) * scale p ^ 2 = 1024*p.ε := by
  unfold scale
  rw [Real.sq_sqrt (by positivity)]
  have hd : (p.d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p.d
  field_simp

lemma center_ball {p : LongTails.Setups.FlatTransferDueling.Params} (hp : 0 < p.ε ∧ p.ε ≤ 1/64)
    (θ : Fin p.d → Bool) : center (scale p) θ ∈ Ball p.d := by
  apply mem_ball
  have he : ‖center (scale p) θ‖^2 = (p.d:ℝ) * scale p^2 / 16 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have ht (i : Fin p.d) : (center (scale p) θ i)^2 = scale p^2 /16 := by
      cases h : θ i <;> simp [center, sign, h] <;> ring
    simp_rw [ht]
    simp
    ring
  nlinarith only [he, scale_sq p hp.1.le, hp.2, norm_nonneg (center (scale p) θ)]

lemma field_lip {d : ℕ} {h : ℝ} (hh : 0 < h) (θ : Fin d → Bool) (x y : Point d) :
    ‖field h θ x - field h θ y‖ ≤ 2 * ‖x-y‖ :=
  separableSlope_lipschitz _ (fun i => profile_lipschitz hh (θ i)) _ _

lemma objective {p : LongTails.Setups.FlatTransferDueling.Params} (hp : 0 < p.ε ∧ p.ε ≤ 1/64)
    (θ : Fin p.d → Bool) : Objective (model p) (loss (scale p) θ) := by
  let h := scale p
  have hh : 0 < h := scale_pos hp.1
  have he : gradient (loss h θ) = field h θ := funext fun x => (gradient_loss hh θ x).gradient
  have hl := field_lip hh θ
  have hbound (x : Point p.d) (hx : x ∈ Ball p.d) : ‖field h θ x‖ ≤ 4 := by
    have ha := hl x (center h θ)
    rw [field_center,sub_zero] at ha
    have hu := norm_ball (center_ball hp θ)
    change ‖center h θ‖ ≤ 1 at hu
    linarith [norm_sub_le x (center h θ), norm_ball hx]
  constructor <;> dsimp only [model]
  · rw [he]; exact gradient_loss hh θ
  · rw [he]; exact (LipschitzWith.of_dist_le_mul (K := 2) (by simpa [dist_eq_norm] using hl)).continuous
  · intro x hx y hy
    have ha (a b : Point p.d) (hb : b ∈ Ball p.d) : loss h θ a - loss h θ b ≥ -4*‖a-b‖ := by
      have hs := strong_loss hh θ b a
      have hi := (abs_le.mp (abs_real_inner_le_norm (field h θ b) (a-b))).1
      have ht := mul_le_mul_of_nonneg_right (hbound b hb) (norm_nonneg (a-b))
      nlinarith [sq_nonneg ‖a-b‖]
    have h1 := ha x y hy
    have h2 := ha y x hx
    rw [norm_sub_rev y x] at h2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [he]; exact fun x _ y _ => hl x y
  · rw [he]
    intro x _ y _
    have := strong_loss hh θ x y
    change _ + _ + (1/2:ℝ)/2 * _ ≤ _
    linarith

noncomputable def mistakes {d : ℕ} (θ : Fin d → Bool) (x : Point d) : ℝ :=
  ∑ i, if decide (0 ≤ x i) = θ i then 0 else 1

lemma mistakes_gap {d : ℕ} {h : ℝ} (hh : 0 < h) (θ : Fin d → Bool) (x : Point d) :
    h^2 / 64 * mistakes θ x ≤ loss h θ x - loss h θ (center h θ) := by
  have hs := strong_loss hh θ (center h θ) x
  rw [field_center, inner_zero_left, add_zero, EuclideanSpace.real_norm_sq_eq] at hs
  have ha (i : Fin d) : h^2 / 16 * (if decide (0 ≤ x i) = θ i then (0:ℝ) else 1) ≤
      (x i - (center h θ) i)^2 := by
    by_cases hb : 0 ≤ x i
    · have hprod := mul_nonneg hh.le hb
      cases ht : θ i <;> simp [hb,ht,center,sign] <;> nlinarith [sq_nonneg (x i)]
    · have hprod := mul_nonpos_of_nonneg_of_nonpos hh.le (le_of_not_ge hb)
      cases ht : θ i <;> simp [hb,ht,center,sign] <;> nlinarith [sq_nonneg (x i)]
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun i _ => ha i)
  rw [← Finset.mul_sum] at ht
  change _ * mistakes θ x ≤ _ at ht
  simp only [PiLp.sub_apply] at hs
  linarith

end LongTails.Proofs.DuelingSignFamily
