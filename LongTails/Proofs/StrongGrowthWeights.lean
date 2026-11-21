import LongTails.Algorithms.StrongGrowthWeights
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

namespace LongTails.Proofs.StrongGrowthWeights

open Set
open LongTails.Setups.DistributedMeanStrongGrowth LongTails.Algorithms.StrongGrowthWeights

variable {p : Params}

lemma speed (hp : spec.valid p) (i : Fin p.n) : 0 < (p.h i : ℝ) := by exact_mod_cast hp.1 i

lemma denominator_pos (hp : spec.valid p) {t : ℝ} (ht : t ∈ Icc 0 1) (i : Fin p.n) :
    0 < (1-t) * (p.h i : ℝ) + t := by
  by_cases h : t = 0
  · simpa [h] using speed hp i
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith [ht.2]) (speed hp i).le)
      (lt_of_le_of_ne ht.1 (Ne.symm h))

lemma total_pos (hp : spec.valid p) {t : ℝ} (ht : t ∈ Icc 0 1) :
    0 < ∑ i, service p t i := by
  apply Finset.sum_pos
  · intro i _
    exact div_pos (speed hp i) (denominator_pos hp ht i)
  · exact Finset.univ_nonempty

lemma sum_normalized (hp : spec.valid p) {t : ℝ} (ht : t ∈ Icc 0 1) :
    ∑ i, normalized p t i = (p.n : ℝ) := by
  simp only [normalized, ← Finset.sum_div, ← Finset.mul_sum]
  field_simp [(total_pos hp ht).ne']

lemma at_zero (hp : spec.valid p) (i : Fin p.n) : normalized p 0 i = 1 := by
  have hs (j : Fin p.n) : service p 0 j = 1 := by simp [service, (speed hp j).ne']
  simp [normalized, hs, (show (p.n : ℝ) ≠ 0 by exact_mod_cast p.n.ne_zero)]

lemma continuous_energy (hp : spec.valid p) :
    ContinuousOn (fun t => ∑ i, normalized p t i ^ 2) (Icc 0 1) := by
  have hs (i : Fin p.n) : ContinuousOn (fun t => service p t i) (Icc 0 1) :=
    continuousOn_const.div (by fun_prop) (fun t ht => (denominator_pos hp ht i).ne')
  have hn (i : Fin p.n) : ContinuousOn (fun t => normalized p t i) (Icc 0 1) :=
    (continuousOn_const.mul (hs i)).div (continuousOn_finsetSum _ fun j _ => hs j)
      (fun t ht => (total_pos hp ht).ne')
  exact continuousOn_finsetSum _ fun i _ => (hn i).pow 2

lemma mixing_spec (hp : spec.valid p) :
    mixing p ∈ Icc 0 1 ∧ (∑ i, signal p i ^ 2) ≤ p.n * p.ρ ∧
      (mixing p = 1 ∨ (∑ i, signal p i ^ 2) = p.n * p.ρ) := by
  let E := fun t => ∑ i, normalized p t i ^ 2
  have hc : ContinuousOn E (Icc 0 1) := continuous_energy hp
  have hz : E 0 ≤ p.n*p.ρ := by
    simpa [E, at_zero hp] using mul_le_mul_of_nonneg_left hp.2.2.2.1
      (show (0:ℝ) ≤ p.n by positivity)
  have ex : ∃ t : ℝ, 0 ≤ t ∧ min (1-t) (p.n*p.ρ - E t) = 0 := by
    by_cases h : E 1 ≤ p.n*p.ρ
    · exact ⟨1,zero_le_one,by rw [sub_self,min_eq_left (sub_nonneg.mpr h)]⟩
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc zero_le_one hc ⟨hz,(le_of_not_ge h)⟩
    exact ⟨t,ht.1,by rw [he,sub_self,min_eq_right (sub_nonneg.mpr ht.2)]⟩
  have ht : 0 ≤ mixing p ∧ min (1-mixing p) (p.n*p.ρ - E (mixing p)) = 0 := by
    have hmix : mixing p = ex.choose := dite_eq_left ex
    rw [hmix]
    exact ex.choose_spec
  have hle := le_min_iff.mp ht.2.ge
  refine ⟨⟨ht.1,by linarith [hle.1]⟩,sub_nonneg.mp hle.2,?_⟩
  change mixing p = 1 ∨ E (mixing p) = _
  rcases le_total (1-mixing p) (p.n*p.ρ - E (mixing p)) with ha | ha
  · have h := (min_eq_left ha).symm.trans ht.2
    left; linarith
  · have h := (min_eq_right ha).symm.trans ht.2
    right; linarith

lemma signal_pos (hp : spec.valid p) (i : Fin p.n) : 0 < signal p i :=
  div_pos (mul_pos (by exact_mod_cast p.n.pos)
    (div_pos (speed hp i) (denominator_pos hp (mixing_spec hp).1 i)))
    (total_pos hp (mixing_spec hp).1)

lemma signal_sum (hp : spec.valid p) : ∑ i, signal p i = (p.n : ℝ) :=
  sum_normalized hp (mixing_spec hp).1

lemma information_pos (hp : spec.valid p) : 0 < information p :=
  Finset.sum_pos (fun i _ => mul_pos (div_pos (signal_pos hp i) (speed hp i)) (signal_pos hp i))
    Finset.univ_nonempty

lemma support (hp : spec.valid p) (a : Fin p.n → ℝ) (hm : ∑ i, a i = p.n)
    (he : ∑ i, a i ^ 2 ≤ p.n * p.ρ) :
    information p ≤ ∑ i, weight p i * a i := by
  let t := mixing p
  have ht := mixing_spec hp
  have scale_id (i : Fin p.n) :
      t * weight p i + (1-t) * signal p i = p.n / (∑ j, service p t j) := by
    let h : ℝ := p.h i
    let d := (1-t)*h+t
    let S := ∑ j, service p t j
    have hd : 0 < d := denominator_pos hp ht.1 i
    have hh : 0 < h := speed hp i
    have hS : 0 < S := total_pos hp ht.1
    change t * ((p.n*(h/d)/S)/h) + (1-t)*(p.n*(h/d)/S) = p.n/S
    calc
      _ = ((p.n:ℝ)/S/d) * ((1-t)*h+t) := by field_simp [hh.ne',hd.ne',hS.ne']; ring
      _ = _ := div_mul_cancel₀ _ hd.ne'
  have hs := signal_sum hp
  have hdiff : ∑ i, (a i - signal p i) = 0 := by rw [Finset.sum_sub_distrib,hm,hs,sub_self]
  have hsum : t * (∑ i, weight p i * a i - information p) +
      (1-t) * (∑ i, signal p i * a i - ∑ i, signal p i^2) = 0 := by
    have hh := congrArg (fun r : ℝ => (p.n / (∑ j, service p t j)) * r) hdiff
    rw [Finset.mul_sum, mul_zero] at hh
    rw [← hh]
    simp only [information, mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← scale_id i]
    ring
  rcases eq_or_ne t 0 with hzero | hnonzero
  · have hu (i : Fin p.n) : signal p i = 1 := by
      change normalized p t i = 1
      rw [hzero,at_zero hp]
    have hc := ht.2.2.resolve_left (by change t ≠ 1; rw [hzero]; norm_num)
    simp [hu] at hc
    rw [hc, mul_one] at he
    have hsum0 := Finset.sum_nonneg (s := Finset.univ) (fun (i : Fin p.n) _ => sq_nonneg (a i-1))
    have hexp : (∑ i, (a i-1)^2) = ∑ i, a i^2 - 2*(∑ i, a i) + p.n := by
      simp only [sub_sq, one_pow, mul_one, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hz : ∑ i, (a i-1)^2 = 0 := by rw [hexp, hm]; linarith
    have ha (i : Fin p.n) : a i = 1 := by
      have hh := Finset.single_le_sum (s := Finset.univ) (fun j _ => sq_nonneg (a j-1)) (Finset.mem_univ i)
      rw [hz] at hh
      nlinarith
    simp [information, ha, hu]
  · have hpos : 0 < t := lt_of_le_of_ne ht.1.1 (Ne.symm hnonzero)
    have hterm : (1-t) * (∑ i, signal p i * a i - ∑ i, signal p i^2) ≤ 0 := by
      rcases ht.2.2 with h | h
      · change t = 1 at h
        simp [h]
      · have hc := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin p.n) _ =>
          show 2 * (signal p i * a i) ≤ signal p i^2 + a i^2 by nlinarith [sq_nonneg (signal p i-a i)])
        rw [← Finset.mul_sum, Finset.sum_add_distrib] at hc
        apply mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.1.2)
        linarith
    have hh : 0 ≤ t * (∑ i, weight p i * a i - information p) := by linarith
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hh hpos)

lemma least_energy (hp : spec.valid p) (a : Fin p.n → ℝ) (hm : ∑ i, a i = p.n)
    (he : ∑ i, a i ^ 2 ≤ p.n * p.ρ) :
    information p ≤ ∑ i, a i ^ 2 / p.h i := by
  have hs := support hp a hm he
  have h := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin p.n) _ =>
    show 2 * (weight p i * a i) ≤ a i ^ 2 / p.h i + weight p i * signal p i by
      unfold weight
      field_simp [(speed hp i).ne',speed hp i]
      nlinarith [sq_nonneg (a i - signal p i)])
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at h
  change 2 * _ ≤ _ + information p at h
  linarith

end LongTails.Proofs.StrongGrowthWeights
