import LongTails.Proofs.ProjectedClippedRegularization
import LongTails.Proofs.ProjectedClippedStage

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.ProjectedClippedExtragradient

open ConstrainedMonotone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def analysisRoot {X : Set E} {P F : E → E} (hP : Proj X P)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) {x0 : E} (hx0 : x0 ∈ X) (s : ℕ) (c : E) : E :=
  regularizedRoot hP hF.cont hF.mono hx0 (regularization_pos t hR hε s) c

def StageGood {X : Set E} {P F : E → E} (hP : Proj X P)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) {x0 : E} (hx0 : x0 ∈ X) (xstar : E)
    (state : ProcessState E) : Prop :=
  let s := min state.1 (stageCount t - 1)
  let p := analysisRoot hP t hF hR hε hx0 s state.2.1
  state.2.2 ∈ X ∧
    ‖p - state.2.2‖ ≤ (if state.1 < stageCount t then radius t s else radius t s / 2) ∧
    ‖p - xstar‖ ≤ t.R + (∑ i ∈ Finset.range s, radius t i) / 4 ∧
    regularization t s * ‖p - state.2.1‖ ≤ (s + 1 : ℝ) * (t.ε / (2 ^ 20 * stageCount t))

lemma analysisRoot_spec {X : Set E} {P F : E → E} (hP : Proj X P)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) {x0 : E} (hx0 : x0 ∈ X) (s : ℕ) (c : E) :
    let p := analysisRoot hP t hF hR hε hx0 s c
    p ∈ X ∧ Normal X p (-(F p + regularization t s • (p - c))) :=
  regularizedRoot_spec hP hF.cont hF.mono hx0 (regularization_pos t hR hε s) c

lemma stageGood_initial {X : Set E} {P F : E → E} (hP : Proj X P)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) {x0 xstar : E} (hx0 : x0 ∈ X)
    (hstar : xstar ∈ X) (hnstar : Normal X xstar (-F xstar)) (hd : ‖x0 - xstar‖ ≤ t.R) :
    StageGood hP t hF hR hε hx0 xstar (0, x0, x0) := by
  have hp := analysisRoot_spec hP t hF hR hε hx0 0 x0
  have hh := regularized_root_distance (regularization_pos t hR hε 0) hF.mono hp.1 hstar hp.2 hnstar
  have hN := stageCount_pos t
  simp only [StageGood, Nat.zero_min, ite_eq_left hN, Finset.range_zero, Finset.sum_empty,
    zero_div, add_zero, Nat.cast_zero, zero_add, one_mul]
  refine ⟨hx0, ?_, hh.1.trans hd, ?_⟩
  · simpa only [radius, pow_zero, div_one] using hh.2.trans hd
  · have hm := mul_le_mul_of_nonneg_left (hh.2.trans hd) (regularization_pos t hR hε 0).le
    have he := regularization_radius t hR 0
    simp only [radius, pow_zero, div_one] at he
    exact hm.trans_eq he

lemma stageGood_bounds {X : Set E} {P F : E → E} (hP : Proj X P)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) {x0 xstar : E} (hx0 : x0 ∈ X)
    (hstar : xstar ∈ X) (hnstar : Normal X xstar (-F xstar)) (hG : ‖F xstar‖ ≤ t.G)
    (state : ProcessState E) (hgood : StageGood hP t hF hR hε hx0 xstar state) :
    let s := min state.1 (stageCount t - 1)
    let p := analysisRoot hP t hF hR hε hx0 s state.2.1
    regularization t s * ‖p - state.2.1‖ ≤ t.ε / 2 ^ 20 ∧ ‖F p‖ ≤ rootBound t := by
  dsimp only
  let s := min state.1 (stageCount t - 1)
  let p := analysisRoot hP t hF hR hε hx0 s state.2.1
  have hp := analysisRoot_spec hP t hF hR hε hx0 s state.2.1
  have hN : (0 : ℝ) < stageCount t := Nat.cast_pos.mpr (stageCount_pos t)
  have hs : s + 1 ≤ stageCount t := by dsimp [s]; have := stageCount_pos t; omega
  have hs' : (s + 1 : ℝ) ≤ stageCount t := by exact_mod_cast hs
  have hm := mul_le_mul_of_nonneg_right hs' (by positivity : 0 ≤ t.ε / (2 ^ 20 * stageCount t))
  have he : (stageCount t : ℝ) * (t.ε / (2 ^ 20 * stageCount t)) = t.ε / 2 ^ 20 := by field_simp
  rw [he] at hm
  have hb : regularization t s * ‖p - state.2.1‖ ≤ t.ε / 2 ^ 20 := hgood.2.2.2.trans hm
  refine ⟨hb, ?_⟩
  have hd := hgood.2.2.1
  change ‖p - xstar‖ ≤ t.R + (∑ i ∈ Finset.range s, radius t i) / 4 at hd
  rw [radius_geometric_sum] at hd
  have hnon := mul_nonneg hR.le (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) s)
  exact regularized_root_operator_bound t hF hR (regularization_pos t hR hε s).le hp.1 hstar hp.2
    hnstar hG (by nlinarith) (by nlinarith)

lemma stageGood_transition {X : Set E} {P F : E → E} (hP : Proj X P)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) {x0 xstar : E} (hx0 : x0 ∈ X)
    (s : ℕ) (c w z : E) (hs : s < stageCount t)
    (hgood : StageGood hP t hF hR hε hx0 xstar (s, c, w)) (hz : z ∈ X)
    (hclose : ‖z - analysisRoot hP t hF hR hε hx0 s c‖ ≤ radius t s / 2) :
    StageGood hP t hF hR hε hx0 xstar
      (s + 1, (if s + 1 < stageCount t then (1 / 2 : ℝ) • (c + z) else c), z) := by
  have hmin : min s (stageCount t - 1) = s := Nat.min_eq_left (by omega)
  simp only [StageGood, hmin, ite_eq_left hs] at hgood
  by_cases hnext : s + 1 < stageCount t
  · have hmin' : min (s + 1) (stageCount t - 1) = s + 1 := Nat.min_eq_left (by omega)
    simp only [StageGood, hmin', ite_eq_left hnext]
    let p := analysisRoot hP t hF hR hε hx0 s c
    let q := analysisRoot hP t hF hR hε hx0 (s + 1) ((1 / 2 : ℝ) • (c + z))
    have hp := analysisRoot_spec hP t hF hR hε hx0 s c
    have hq := analysisRoot_spec hP t hF hR hε hx0 (s + 1) ((1 / 2 : ℝ) • (c + z))
    have ht := regularized_stage_transport t hF.mono hR hε s hp.1 hq.1 hp.2 hq.2 hclose
    refine ⟨hz, ht.2.1, ?_, ?_⟩
    · have hdist := norm_sub_le_norm_sub_add_norm_sub q p xstar
      have hb := hgood.2.2.1
      rw [Finset.sum_range_succ]
      change ‖q - xstar‖ ≤ _
      change ‖p - xstar‖ ≤ _ at hb
      linarith [ht.1]
    · have hn := norm_le_norm_sub_add
        (regularization t (s + 1) • (q - (1 / 2 : ℝ) • (c + z)))
        (regularization t s • (p - c))
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (regularization_pos t hR hε (s + 1)),
        abs_of_pos (regularization_pos t hR hε s)] at hn
      have hb := hgood.2.2.2
      change regularization t s * ‖p - c‖ ≤ _ at hb
      change regularization t (s + 1) * ‖q - (1 / 2 : ℝ) • (c + z)‖ ≤ _
      push_cast
      linarith [ht.2.2]
  · have heq : s + 1 = stageCount t := by omega
    have hmin' : min (s + 1) (stageCount t - 1) = s := by omega
    simp only [StageGood, hmin', ite_eq_right hnext]
    refine ⟨hz, ?_, hgood.2.2.1, hgood.2.2.2⟩
    simpa only [norm_sub_rev] using hclose

variable [MeasurableSpace E] [BorelSpace E]

lemma measurable_processRoot {X : Set E} {P F : E → E} (hP : Proj X P)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) {x0 : E} (hx0 : x0 ∈ X) :
    Measurable (fun state : ProcessState E =>
      analysisRoot hP t hF hR hε hx0 (min state.1 (stageCount t - 1)) state.2.1) := by
  apply measurable_from_prod_countable_right
  intro s
  exact (regularizedRoot_continuous hP hF.cont hF.mono hx0
    (regularization_pos t hR hε (min s (stageCount t - 1)))).measurable.comp measurable_fst

lemma measurableSet_stageGood {X : Set E} {P F : E → E} (hP : Proj X P)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) {x0 : E} (hx0 : x0 ∈ X) (xstar : E) :
    MeasurableSet {state | StageGood hP t hF hR hε hx0 xstar state} := by
  have hp := measurable_processRoot hP t hF hR hε hx0
  have hm : Measurable (fun state : ProcessState E => state.2.2) := by fun_prop
  have ha : Measurable (fun state : ProcessState E => state.2.1) := by fun_prop
  have hrad : Measurable (fun state : ProcessState E =>
      if state.1 < stageCount t then radius t (min state.1 (stageCount t - 1))
      else radius t (min state.1 (stageCount t - 1)) / 2) :=
    (measurable_of_countable (fun s : ℕ => if s < stageCount t then
      radius t (min s (stageCount t - 1)) else radius t (min s (stageCount t - 1)) / 2)).comp measurable_fst
  have hdist : Measurable (fun state : ProcessState E =>
      t.R + (∑ i ∈ Finset.range (min state.1 (stageCount t - 1)), radius t i) / 4) :=
    (measurable_of_countable (fun s : ℕ => t.R +
      (∑ i ∈ Finset.range (min s (stageCount t - 1)), radius t i) / 4)).comp measurable_fst
  have hb : Measurable (fun state : ProcessState E =>
      ((min state.1 (stageCount t - 1) : ℕ) + 1 : ℝ) * (t.ε / (2 ^ 20 * stageCount t))) :=
    (measurable_of_countable (fun s : ℕ => ((min s (stageCount t - 1) : ℕ) + 1 : ℝ) *
      (t.ε / (2 ^ 20 * stageCount t)))).comp measurable_fst
  have hr : Measurable (fun state : ProcessState E => regularization t (min state.1 (stageCount t - 1))) :=
    (measurable_of_countable (fun s : ℕ => regularization t (min s (stageCount t - 1)))).comp measurable_fst
  exact (hP.closed.measurableSet.preimage hm).inter
    ((measurableSet_le (hp.sub hm).norm hrad).inter
      ((measurableSet_le (hp.sub measurable_const).norm hdist).inter
        (measurableSet_le (hr.mul (hp.sub ha).norm) hb)))

end OracleTemplate.ProjectedClippedExtragradient
