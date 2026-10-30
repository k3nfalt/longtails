import LongTails.Proofs.ProjectedClippedInvariant

open MeasureTheory
open scoped BigOperators

namespace LongTails.Proofs.GapNoiseOuter

open OracleTemplate OracleTemplate.ConstrainedMonotone OracleTemplate.ProjectedClippedExtragradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def RefinedGood {X : Set E} {P F : E → E} (hP : Proj X P)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) {x0 : E} (hx0 : x0 ∈ X) (s : E)
    (state : ProcessState E) : Prop :=
  StageGood hP t hF hR hε hx0 s state ∧
    ‖analysisRoot hP t hF hR hε hx0 (min state.1 (stageCount t - 1)) state.2.1 - s‖ ≤
      t.R / 2 + (∑ i ∈ Finset.range (min state.1 (stageCount t - 1)), radius t i) / 4

lemma refinedGood_initial {X : Set E} {P F : E → E} (hP : Proj X P)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) {x0 s : E} (hx0 : x0 ∈ X)
    (hs : s ∈ X) (hns : Normal X s (-F s)) (hd : ‖x0 - s‖ ≤ t.R / 2) :
    RefinedGood hP t hF hR hε hx0 s (0, x0, x0) := by
  refine ⟨stageGood_initial hP t hF hR hε hx0 hs hns (hd.trans (by linarith)), ?_⟩
  have hp := analysisRoot_spec hP t hF hR hε hx0 0 x0
  have hh := regularized_root_distance (regularization_pos t hR hε 0) hF.mono hp.1 hs hp.2 hns
  simpa only [Nat.zero_min, Finset.range_zero, Finset.sum_empty, zero_div, add_zero] using hh.1.trans hd

lemma refinedGood_root_distance {X : Set E} {P F : E → E} (hP : Proj X P)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) {x0 s : E} (hx0 : x0 ∈ X)
    (state : ProcessState E) (hg : RefinedGood hP t hF hR hε hx0 s state) :
    ‖analysisRoot hP t hF hR hε hx0 (min state.1 (stageCount t - 1)) state.2.1 - s‖ ≤ t.R := by
  have hh := hg.2
  rw [radius_geometric_sum] at hh
  have hn := mul_nonneg hR.le (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (min state.1 (stageCount t - 1)))
  nlinarith

lemma refinedGood_transition {X : Set E} {P F : E → E} (hP : Proj X P)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) {x0 s : E} (hx0 : x0 ∈ X)
    (j : ℕ) (anchor center z : E) (hj : j < stageCount t)
    (hg : RefinedGood hP t hF hR hε hx0 s (j, anchor, center)) (hz : z ∈ X)
    (hclose : ‖z - analysisRoot hP t hF hR hε hx0 j anchor‖ ≤ radius t j / 2) :
    RefinedGood hP t hF hR hε hx0 s
      (j + 1, (if j + 1 < stageCount t then (1 / 2 : ℝ) • (anchor + z) else anchor), z) := by
  refine ⟨stageGood_transition hP t hF hR hε hx0 j anchor center z hj hg.1 hz hclose, ?_⟩
  have hmin : min j (stageCount t - 1) = j := Nat.min_eq_left (by omega)
  have hb := hg.2
  simp only [hmin] at hb
  by_cases hn : j + 1 < stageCount t
  · have hmin' : min (j + 1) (stageCount t - 1) = j + 1 := Nat.min_eq_left (by omega)
    simp only [hn, ite_true, hmin', Finset.sum_range_succ]
    let p := analysisRoot hP t hF hR hε hx0 j anchor
    let q := analysisRoot hP t hF hR hε hx0 (j + 1) ((1 / 2 : ℝ) • (anchor + z))
    have hp := analysisRoot_spec hP t hF hR hε hx0 j anchor
    have hq := analysisRoot_spec hP t hF hR hε hx0 (j + 1) ((1 / 2 : ℝ) • (anchor + z))
    have ht := regularized_stage_transport t hF.mono hR hε j hp.1 hq.1 hp.2 hq.2 hclose
    have hd := norm_sub_le_norm_sub_add_norm_sub q p s
    change ‖p - s‖ ≤ _ at hb
    change ‖q - s‖ ≤ _
    linarith [ht.1]
  · have hmin' : min (j + 1) (stageCount t - 1) = j := by omega
    simpa only [hn, ite_false, hmin'] using hb

variable [MeasurableSpace E] [BorelSpace E]

lemma measurableSet_refinedGood {X : Set E} {P F : E → E} (hP : Proj X P)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) {x0 : E} (hx0 : x0 ∈ X) (s : E) :
    MeasurableSet {state | RefinedGood hP t hF hR hε hx0 s state} := by
  have hp := measurable_processRoot hP t hF hR hε hx0
  have hd : Measurable (fun state : ProcessState E =>
      t.R / 2 + (∑ i ∈ Finset.range (min state.1 (stageCount t - 1)), radius t i) / 4) :=
    (measurable_of_countable (fun j : ℕ => t.R / 2 +
      (∑ i ∈ Finset.range (min j (stageCount t - 1)), radius t i) / 4)).comp measurable_fst
  exact (measurableSet_stageGood hP t hF hR hε hx0 s).inter
    (measurableSet_le (hp.sub measurable_const).norm hd)

end LongTails.Proofs.GapNoiseOuter
