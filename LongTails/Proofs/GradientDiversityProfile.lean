import LongTails.Algorithms.GradientDiversityDesign
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

namespace LongTails.Proofs.GradientDiversityProfile

open LongTails.Setups.DistributedGradientDiversity LongTails.Algorithms.GradientDiversityDesign
open Set

variable {p : Params}

lemma speed_pos (hp : spec.valid p) (i : Fin p.n) : 0 < (p.h i : ℝ) := by
  exact_mod_cast hp.1 i

lemma denominator_pos (hp : spec.valid p) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (i : Fin p.n) :
    0 < 1 - t + t * (p.h i : ℝ) := by
  by_cases hz : t = 0
  · simp [hz]
  · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ht.2)
      (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm hz)) (speed_pos hp i))

lemma share_pos (hp : spec.valid p) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (i : Fin p.n) :
    0 < share p t i := div_pos (speed_pos hp i) (denominator_pos hp ht i)

lemma mass_pos (hp : spec.valid p) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < ∑ i, share p t i := Finset.sum_pos (fun i _ => share_pos hp ht i) Finset.univ_nonempty

lemma profile_sum (hp : spec.valid p) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∑ i, profile p t i = (p.n : ℝ) := by
  simp only [profile, ← Finset.sum_div, ← Finset.mul_sum]
  field_simp [(mass_pos hp ht).ne']

lemma profile_one (hp : spec.valid p) (i : Fin p.n) : profile p 1 i = 1 := by
  have h (j : Fin p.n) : share p 1 j = 1 := by simp [share, (speed_pos hp j).ne']
  simp [profile, h, Nat.ne_of_gt p.n.pos]

lemma parameter_spec (hp : spec.valid p) :
    parameter p ∈ Icc (0 : ℝ) 1 ∧ moment p (parameter p) ≤ (p.n : ℝ) * p.ρ ∧
    (parameter p = 0 ∨ moment p (parameter p) = (p.n : ℝ) * p.ρ) := by
  classical
  unfold parameter
  split
  next h =>
    obtain ⟨hl,hu,he⟩ := h.choose_spec
    exact ⟨⟨hl,hu⟩, he.le, Or.inr he⟩
  next h =>
    refine ⟨⟨le_rfl,zero_le_one⟩, ?_, Or.inl rfl⟩
    by_contra! hzero
    have hs (i : Fin p.n) : ContinuousOn (fun t => share p t i) (Icc 0 1) :=
      continuousOn_const.div (by fun_prop) (fun t ht => (denominator_pos hp ht i).ne')
    have hsum : ContinuousOn (fun t => ∑ i, share p t i) (Icc 0 1) :=
      continuousOn_finsetSum _ (fun i _ => hs i)
    have hm : ContinuousOn (moment p) (Icc 0 1) :=
      continuousOn_finsetSum _ fun i _ =>
        ((continuousOn_const.mul (hs i)).div hsum (fun _ ht => (mass_pos hp ht).ne')).pow 2
    have he : moment p 1 = p.n := by simp [moment, profile_one hp]
    have h1 : moment p 1 ≤ (p.n : ℝ) * p.ρ := by
      rw [he]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hp.2.2.2.1 (show 0 ≤ (p.n : ℝ) by positivity)
    obtain ⟨t, ht, hroot⟩ := intermediate_value_Icc' (zero_le_one : (0 : ℝ) ≤ 1) hm
      (show (p.n : ℝ)*p.ρ ∈ Icc (moment p 1) (moment p 0) from ⟨h1,hzero.le⟩)
    exact h ⟨t, ht.1, ht.2, hroot⟩

lemma amplitude_pos (hp : spec.valid p) (i : Fin p.n) : 0 < amplitude p i :=
  div_pos (mul_pos (by exact_mod_cast p.n.pos) (share_pos hp (parameter_spec hp).1 i))
    (mass_pos hp (parameter_spec hp).1)

lemma weight_pos (hp : spec.valid p) (i : Fin p.n) : 0 < weight p i :=
  div_pos (amplitude_pos hp i) (speed_pos hp i)

lemma information_pos (hp : spec.valid p) : 0 < information p :=
  Finset.sum_pos (fun i _ => mul_pos (weight_pos hp i) (amplitude_pos hp i)) Finset.univ_nonempty

lemma support (hp : spec.valid p) (v : Fin p.n → ℝ)
    (hv : ∑ i, v i = (p.n : ℝ)) (hv2 : ∑ i, v i ^ 2 ≤ (p.n : ℝ) * p.ρ) :
    information p ≤ ∑ i, weight p i * v i := by
  classical
  let t := parameter p
  let a := amplitude p
  let w := weight p
  obtain ⟨ht, _, hactive⟩ := parameter_spec hp
  change t ∈ Icc (0 : ℝ) 1 at ht
  have ha : ∑ i, a i = (p.n : ℝ) := profile_sum hp ht
  have hzero : ∑ i, (v i - a i) = 0 := by rw [Finset.sum_sub_distrib, hv, ha, sub_self]
  have hinner (he : moment p t = (p.n : ℝ) * p.ρ) :
      ∑ i, a i * (v i - a i) ≤ 0 := by
    change ∑ i, a i ^ 2 = (p.n : ℝ) * p.ρ at he
    have hs := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => show 2 * (a i * (v i - a i)) ≤ v i ^ 2 - a i ^ 2 by nlinarith [sq_nonneg (v i - a i)])
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, he] at hs
    linarith
  by_cases h1 : t = 1
  · have he : ∑ i, v i ^ 2 ≤ (p.n : ℝ) := by
      rcases hactive with h | h
      · change t = 0 at h; linarith
      · change moment p t = _ at h
        rw [h1] at h
        simpa [← h, moment, profile_one hp] using hv2
    have hz : ∑ i, (v i - 1)^2 ≤ 0 := by
      simp_rw [show ∀ z : ℝ, (z-1)^2 = z^2 - 2*z + 1 by intro; ring]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hv,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      linarith
    have hv' (i : Fin p.n) : v i = a i := by
      have := (Finset.single_le_sum (fun j _ => sq_nonneg (v j - 1)) (Finset.mem_univ i)).trans hz
      change v i = profile p t i
      rw [h1, profile_one hp]; nlinarith
    simp_rw [hv']
    exact le_rfl
  · let C := (p.n : ℝ) / ∑ j, share p t j
    have hrel (i : Fin p.n) : (1 - t) * w i + t * a i = C := by
      change (1-t) * (profile p t i / (p.h i : ℝ)) + t * profile p t i = C
      unfold profile C
      unfold share
      field_simp [(speed_pos hp i).ne', (denominator_pos hp ht i).ne']
    have hh (i : Fin p.n) : (1-t) * (w i * (v i - a i)) +
        t * (a i * (v i - a i)) = C * (v i - a i) := by
      linear_combination (v i - a i) * hrel i
    have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hh i)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hzero, mul_zero] at hs
    have hn : t * (∑ i, a i * (v i - a i)) ≤ 0 := by
      rcases hactive with h | h
      · change t = 0 at h; simp [h]
      · exact mul_nonpos_of_nonneg_of_nonpos ht.1 (hinner h)
    have hpos : 0 < 1-t := sub_pos.mpr (lt_of_le_of_ne ht.2 h1)
    have hgood : 0 ≤ ∑ i, w i * (v i - a i) :=
      nonneg_of_mul_nonneg_right (by linarith only [hs, hn] : 0 ≤ (1-t) * _) hpos
    simp only [mul_sub, Finset.sum_sub_distrib, sub_nonneg] at hgood
    exact hgood

lemma least_energy (hp : spec.valid p) (v : Fin p.n → ℝ)
    (hv : ∑ i, v i = (p.n : ℝ)) (hv2 : ∑ i, v i^2 ≤ (p.n : ℝ)*p.ρ) :
    information p ≤ ∑ i, v i^2 / p.h i := by
  have h (i : Fin p.n) : 2 * (weight p i * v i) ≤ v i^2 / p.h i + weight p i * amplitude p i := by
    unfold weight
    field_simp [(speed_pos hp i).ne', speed_pos hp i]
    nlinarith only [sq_nonneg (v i - amplitude p i)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hs
  change _ ≤ _ + information p at hs
  linarith only [hs, support hp v hv hv2]

end LongTails.Proofs.GradientDiversityProfile
