import Mathlib.Tactic

namespace LongTails.Proofs.SpikedSoftCutBisection

lemma small_estimate_gap (gap s estimate a z ε r : ℝ)
    (hr : 0 < r) (hε : 0 ≤ ε)
    (hcertificate : gap + s * (z-a) ≤ ε / 16)
    (hlocation : |z-a| ≤ r) (hnoise : |estimate-s| ≤ ε / (8*r))
    (hsmall : |estimate| ≤ ε / (2*r)) : gap ≤ 11*ε/16 := by
  have hs : |s| ≤ 5*ε/(8*r) := by
    have h := abs_add_le estimate (s-estimate)
    rw [add_sub_cancel, abs_sub_comm s estimate] at h
    have he : ε/(2*r)+ε/(8*r) = 5*ε/(8*r) := by ring
    linarith
  have hm := mul_le_mul hs hlocation (abs_nonneg _) (by positivity : 0 ≤ 5*ε/(8*r))
  rw [← abs_mul] at hm
  have he : 5*ε/(8*r)*r = 5*ε/8 := by field_simp
  rw [he] at hm
  have hn := neg_abs_le (s*(z-a))
  linarith

lemma positive_estimate_location (gap s estimate a z ε r : ℝ)
    (hr : 0 < r) (hε : 0 < ε) (hgap : 0 ≤ gap)
    (hcertificate : gap + s * (z-a) ≤ ε / 16)
    (hnoise : |estimate-s| ≤ ε / (8*r))
    (hlarge : ε / (2*r) < estimate) : z ≤ a+r/6 := by
  have hn := abs_le.mp hnoise
  have hs : 3*ε/(8*r) < s := by
    have he : ε/(2*r)-ε/(8*r) = 3*ε/(8*r) := by ring
    linarith
  by_contra hz
  have hz' : r/6 < z-a := by linarith
  have hspos : 0 < s := lt_trans (by positivity) hs
  have hp : (3*ε/(8*r))*(r/6) < s*(z-a) :=
    mul_lt_mul hs hz'.le (by positivity) hspos.le
  have he : (3*ε/(8*r))*(r/6) = ε/16 := by field_simp; ring
  rw [he] at hp
  linarith

lemma negative_estimate_location (gap s estimate a z ε r : ℝ)
    (hr : 0 < r) (hε : 0 < ε) (hgap : 0 ≤ gap)
    (hcertificate : gap + s * (z-a) ≤ ε / 16)
    (hnoise : |estimate-s| ≤ ε / (8*r))
    (hlarge : estimate < -(ε / (2*r))) : a-r/6 ≤ z := by
  have hc : gap + (-s)*((-z)-(-a)) ≤ ε/16 := by nlinarith
  have hn : |(-estimate)-(-s)| ≤ ε/(8*r) := by
    simpa only [neg_sub_neg, abs_sub_comm] using hnoise
  have hl : ε/(2*r) < -estimate := by linarith
  have hh := positive_estimate_location gap (-s) (-estimate) (-a) (-z) ε r
    hr hε hgap hc hn hl
  linarith

lemma left_shift_contains (a z r : ℝ) (hr : 0 ≤ r)
    (hlocation : |z-a| ≤ r) (hcut : z ≤ a+r/6) :
    |z-(a-3*r/8)| ≤ 5*r/8 := by
  obtain ⟨hl, hu⟩ := abs_le.mp hlocation
  apply abs_le.mpr
  constructor <;> linarith

lemma right_shift_contains (a z r : ℝ) (hr : 0 ≤ r)
    (hlocation : |z-a| ≤ r) (hcut : a-r/6 ≤ z) :
    |z-(a+3*r/8)| ≤ 5*r/8 := by
  obtain ⟨hl, hu⟩ := abs_le.mp hlocation
  apply abs_le.mpr
  constructor <;> linarith

lemma final_midpoint_gap (gap s a z δ G r : ℝ) (hG : 0 ≤ G)
    (hcertificate : gap + s*(z-a) ≤ δ) (hlocation : |z-a| ≤ r) (hs : |s| ≤ G) :
    gap ≤ δ+G*r := by
  have hm := mul_le_mul hs hlocation (abs_nonneg _) hG
  rw [← abs_mul] at hm
  have hn := neg_abs_le (s*(z-a))
  linarith

end LongTails.Proofs.SpikedSoftCutBisection
