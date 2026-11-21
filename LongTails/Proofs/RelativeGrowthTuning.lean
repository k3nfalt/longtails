import LongTails.Algorithms.RelativeGrowthBatches
import LongTails.Proofs.RelativeGrowthProfile
import LongTails.Proofs.WeightedInterpolationPrecision

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.RelativeGrowthTuning

open LongTails.Setups.DistributedRelativeGrowth
open LongTails.Algorithms.RelativeGrowthBatches
open LongTails.Algorithms.WeakInterpolationDesign
open LongTails.Algorithms.WeightedInterpolationSgd (stepSize fraction)

variable {p : Params}

lemma signal_pos (hp : spec.valid p) (i : Fin p.n) : 0 < signal p i :=
  mul_pos hp.2.2.1 (RelativeGrowthProfile.normalized_pos (fun j => by exact_mod_cast hp.1 j)
    (RelativeGrowthProfile.parameter_spec (fun j => by exact_mod_cast hp.1 j) hp.2.2.2.1).1 i)

lemma signal_sum (hp : spec.valid p) : ∑ i, signal p i = (p.n : ℝ)*p.μ := by
  simp only [signal, ← Finset.mul_sum]
  rw [mul_comm]
  congr 1
  exact RelativeGrowthProfile.mass (fun j => by exact_mod_cast hp.1 j)
    (RelativeGrowthProfile.parameter_spec (fun j => by exact_mod_cast hp.1 j) hp.2.2.2.1).1

lemma scale_bound (hp : spec.valid p) (i : Fin p.n) :
    signal p i ^ 2 ≤ scale p ∧ signal p i * p.L i ≤ scale p := by
  have h := Finset.le_sup' (fun j => signal p j * max (signal p j) (p.L j)) (Finset.mem_univ i)
  constructor
  · rw [sq]
    exact (mul_le_mul_of_nonneg_left (le_max_left _ _) (signal_pos hp i).le).trans h
  · exact (mul_le_mul_of_nonneg_left (le_max_right _ _) (signal_pos hp i).le).trans h

lemma cap_ge (hp : spec.valid p) (i : Fin p.n) : signal p i ≤ (tuning p).L i := by
  change _ ≤ if _ then _ else _
  split
  · exact (le_div_iff₀ (signal_pos hp i)).mpr (by simpa [sq] using (scale_bound hp i).1)
  · exact le_rfl

lemma valid (hp : spec.valid p) : Setups.DistributedWeakInterpolation.spec.valid (tuning p) :=
  ⟨hp.1, fun i => (signal_pos hp i).le.trans (cap_ge hp i), hp.2.2.1,
    (signal_sum hp).symm.le.trans (Finset.sum_le_sum (fun i _ => cap_ge hp i)), hp.2.2.2.2⟩

lemma profile_eq (hp : spec.valid p) (i : Fin p.n) : profile (tuning p) i = signal p i := by
  let c := Finset.univ.sup' Finset.univ_nonempty (gain p)
  have hh (i : Fin p.n) : 0 < (p.h i : ℝ) := by exact_mod_cast hp.1 i
  have hc (j : Fin p.n) : curvature (tuning p).L (fun j => p.h j) c j = signal p j := by
    have hgain := Finset.le_sup' (gain p) (Finset.mem_univ j)
    change gain p j ≤ c at hgain
    by_cases he : gain p j = c
    · have hm : c * (p.h j : ℝ) = signal p j := by rw [← he, gain]; field_simp [(hh j).ne']
      change min ((tuning p).L j) (c*(p.h j : ℝ)) = signal p j
      rw [hm, min_eq_right (cap_ge hp j)]
    · have hm := (div_le_iff₀ (hh j)).mp hgain
      simp [curvature, tuning, c, he, min_eq_left hm]
  let r := threshold (tuning p)
  have hsum : (∑ j, profile (tuning p) j) = ∑ j, signal p j :=
    (WeakInterpolationDesign.threshold_spec (valid hp)).2.trans (signal_sum hp).symm
  have monotone (a b : ℝ) (hab : a ≤ b) (j : Fin p.n) :
      curvature (tuning p).L (fun j => p.h j) a j ≤ curvature (tuning p).L (fun j => p.h j) b j :=
    min_le_min_left _ (mul_le_mul_of_nonneg_right hab (hh j).le)
  have same {a b : Fin p.n → ℝ} (hab : ∀ j, a j ≤ b j) (h : ∑ j, a j = ∑ j, b j) :
      a i = b i := by
    have hz : ∑ j, (b j-a j) = 0 := by rw [Finset.sum_sub_distrib, h, sub_self]
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sub_nonneg.mpr (hab j))).mp hz i (Finset.mem_univ i)
    linarith
  rcases le_total r c with hl | hl
  · exact same (fun j => (monotone r c hl j).trans_eq (hc j)) hsum
  · exact (same (fun j => (hc j).symm.le.trans (monotone c r hl j)) hsum.symm).symm

lemma weight_eq (hp : spec.valid p) (i : Fin p.n) : weights (tuning p) i = gain p i := by
  change profile (tuning p) i / (p.h i : ℝ) = _
  rw [profile_eq hp]
  rfl

lemma scale_eq (hp : spec.valid p) : largestCurvature (tuning p) = scale p := by
  let c := Finset.univ.sup' Finset.univ_nonempty (gain p)
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (gain p)
  apply le_antisymm
  · apply Finset.sup'_le
    intro j _
    rw [profile_eq hp j]
    change signal p j * (if _ then _ else _) ≤ _
    split
    · exact le_of_eq (by field_simp [(signal_pos hp j).ne'])
    · simpa [sq] using (scale_bound hp j).1
  · have hh := Finset.le_sup' (fun j => profile (tuning p) j * (tuning p).L j) hi
    rw [profile_eq hp] at hh
    change signal p i * (if gain p i = _ then _ else _) ≤ _ at hh
    rw [ite_eq_left he.symm] at hh
    have heq : signal p i * (scale p / signal p i) = scale p := by field_simp [(signal_pos hp i).ne']
    rw [heq] at hh
    exact hh

lemma energy_eq (hp : spec.valid p) :
    information (tuning p) = ∑ i, (signal p i / p.h i) * signal p i := by
  apply Finset.sum_congr rfl
  intro i _
  rw [weight_eq hp i, profile_eq hp i]
  rfl

lemma local_factor (hp : spec.valid p) (k : ℕ) (i : Fin p.n) :
    stepSize (tuning p) k * weights (tuning p) i / fraction (tuning p) i * p.L i ≤ 1 := by
  let q := tuning p
  let S := ∑ j, ((q.h j : ℝ))⁻¹
  have ht := WeightedInterpolationAllocation.step_bounds (valid hp) k
  have ha := WeightedInterpolationPrecision.alpha_profile (valid hp) i
  change weights q i / fraction q i ≤ 2*S*profile q i at ha
  have hcap : profile q i * p.L i ≤ largestCurvature q := by
    rw [scale_eq hp, profile_eq hp]; exact (scale_bound hp i).2
  have hl := mul_le_mul_of_nonneg_right ha (hp.2.1 i)
  have hS : 0 ≤ S := (WeakInterpolationDesign.speed_pos (valid hp)).le
  have hc := mul_le_mul_of_nonneg_left hcap (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hS)
  have hb : (weights q i / fraction q i) * p.L i ≤ smoothness q := by
    change _ ≤ 2 * S * largestCurvature q
    linarith only [hl, hc]
  have hh := mul_le_mul_of_nonneg_left hb ht.1
  change stepSize q k * weights q i / fraction q i * p.L i ≤ 1
  rw [mul_div_assoc, mul_assoc]
  exact hh.trans (ht.2.trans (by norm_num))

end LongTails.Proofs.RelativeGrowthTuning
