import LongTails.Proofs.CoupledCubicExecution
import LongTails.Proofs.CoupledCubicGeometry
import LongTails.Proofs.CoupledCubicStability
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CoupledCubicSelection

open LongTails.Setups.StrongGrowthFiniteSumSecondOrder
open LongTails.Algorithms.CoupledCubicTournament
open LongTails.Proofs.CoupledCubicExecution

lemma majority_intersection {α : Type*} [DecidableEq α] (U s t : Finset α)
    (hs : s ⊆ U) (ht : t ⊆ U) (hsc : U.card < 2 * s.card)
    (htc : U.card < 2 * t.card) : (s ∩ t).Nonempty := by
  by_contra hn
  have hz : (s ∩ t).card = 0 := by
    rw [Finset.not_nonempty_iff_eq_empty.mp hn]
    rfl
  have hu : (s ∪ t).card ≤ U.card :=
    Finset.card_le_card (Finset.union_subset hs ht)
  have hc := Finset.card_union_add_card_inter s t
  omega

lemma selected_has_good_neighbor (p : Params) (models : List (Model p))
    (good : Finset ℕ) (hsub : good ⊆ Finset.range models.length)
    (hmajor : models.length < 2 * good.card)
    (hpairs : ∀ i ∈ good, ∀ j ∈ good,
      compatible p (modelAt p models i) (modelAt p models j)) :
    selectedIndex p models < models.length ∧
      ∃ j ∈ good, compatible p (modelAt p models (selectedIndex p models)) (modelAt p models j) := by
  classical
  let neighbors (i : ℕ) := (Finset.range models.length).filter
    (fun j => compatible p (modelAt p models i) (modelAt p models j))
  have hqual (i : ℕ) (hi : i ∈ good) : qualifies p models i := by
    have hs : good ⊆ neighbors i := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨hsub hj, hpairs i hi j hj⟩
    have hc := Finset.card_le_card hs
    change models.length < 2 * (neighbors i).card
    omega
  have hnonempty : good.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i, hi⟩ := hnonempty
  have hex : ∃ j, j < models.length ∧ qualifies p models j :=
    ⟨i, Finset.mem_range.mp (hsub hi), hqual i hi⟩
  obtain ⟨hindex, hselected⟩ := selectedIndex_spec p models hex
  have hselected' : (Finset.range models.length).card <
      2 * (neighbors (selectedIndex p models)).card := by
    simpa only [Finset.card_range, qualifies, neighbors] using hselected
  obtain ⟨j, hj⟩ := majority_intersection (Finset.range models.length) good
    (neighbors (selectedIndex p models)) hsub (Finset.filter_subset _ _)
    (by simpa only [Finset.card_range] using hmajor) hselected'
  refine ⟨hindex, j, (Finset.mem_inter.mp hj).1, ?_⟩
  exact (Finset.mem_filter.mp (Finset.mem_inter.mp hj).2).2


lemma compatible_with_zero_model (p : Params) (hρ : 0 < p.ρ) (a b : Model p)
    (ha : a.2.toLinearMap.IsSymmetric) (hb : b.2.toLinearMap.IsSymmetric)
    (hg : a.1 = 0) (hpsd : ∀ v : p.E, 0 ≤ ⟪v, a.2 v⟫)
    (hc : compatible p a b) : modelStep p b = 0 := by
  have hstep := modelStep_zero p hρ a hg hpsd
  have hgb : b.1 = 0 := by
    have hh := hc.1.2
    simpa [hstep, hg] using hh
  have hD : (b.2 - a.2).toLinearMap.IsSymmetric := by
    intro x y
    change ⟪(b.2 - a.2) x, y⟫ = ⟪x, (b.2 - a.2) y⟫
    simp only [sub_apply, inner_sub_left, inner_sub_right]
    have hax : ⟪a.2 x, y⟫ = ⟪x, a.2 y⟫ := ha x y
    have hbx : ⟪b.2 x, y⟫ = ⟪x, b.2 y⟫ := hb x y
    rw [hax, hbx]
  have hrel (v : p.E) : ‖(b.2 - a.2) v‖ ≤ (1 / 1000000 : ℝ) * ‖a.2 v‖ := by
    have hh := hc.1.1 v
    simp only [graphNorm, hstep, norm_zero, mul_zero, zero_mul, add_zero] at hh
    rw [sub_apply, norm_sub_rev]
    simpa only [sub_apply] using hh
  apply modelStep_zero p hρ b hgb
  intro v
  have hh := CoupledCubicGeometry.relative_perturbation_nonnegative a.2 (b.2 - a.2)
    (1 / 1000000 : ℝ) (by norm_num) (by norm_num) ha hD hpsd hrel v
  have he : a.2 + (b.2 - a.2) = b.2 := by abel
  simpa only [he] using hh

lemma graphNorm_comparison (p : Params) (m : Model p)
    (H A : p.E →L[ℝ] p.E) (r η : ℝ)
    (hρ : 0 ≤ p.ρ) (hηsmall : η ≤ 1 / 2)
    (hlower : r / 2 ≤ ‖modelStep p m‖) (hupper : ‖modelStep p m‖ ≤ 2 * r)
    (hH : ∀ v, ‖H v‖ ≤ ‖A v‖)
    (hrA : ∀ v, p.ρ * r * ‖v‖ ≤ ‖A v‖)
    (hA : ∀ v, ‖A v‖ ≤ ‖H v‖ + p.ρ * r * ‖v‖)
    (herr : ∀ v, ‖(m.2 - H) v‖ ≤ η * ‖A v‖) (v : p.E) :
    graphNorm p m v ≤ 4 * ‖A v‖ ∧ ‖A v‖ ≤ 4 * graphNorm p m v := by
  have hn := norm_nonneg (A v)
  have hscale := mul_nonneg hρ (norm_nonneg v)
  have hu : p.ρ * ‖modelStep p m‖ * ‖v‖ ≤ 2 * ‖A v‖ := by
    have hh := mul_le_mul_of_nonneg_right hupper hscale
    nlinarith [hrA v]
  have hl : p.ρ * r * ‖v‖ ≤ 2 * (p.ρ * ‖modelStep p m‖ * ‖v‖) := by
    have hh := mul_le_mul_of_nonneg_right hlower hscale
    nlinarith
  have he : ‖(m.2 - H) v‖ ≤ ‖A v‖ / 2 := by
    exact (herr v).trans (by nlinarith)
  have ht : ‖m.2 v‖ ≤ ‖H v‖ + ‖(m.2 - H) v‖ := by
    have hh := norm_add_le (H v) ((m.2 - H) v)
    simpa only [sub_apply, add_sub_cancel] using hh
  have ht' : ‖H v‖ ≤ ‖m.2 v‖ + ‖(m.2 - H) v‖ := by
    have hh := norm_sub_le (m.2 v) ((m.2 - H) v)
    simpa only [sub_apply, sub_sub_cancel] using hh
  dsimp [graphNorm]
  constructor
  · nlinarith [hH v]
  · nlinarith [hA v, norm_nonneg (m.2 v)]

lemma model_difference_bound (p : Params) (a b : Model p)
    (H A : p.E →L[ℝ] p.E) (η : ℝ)
    (ha : ∀ v, ‖(a.2 - H) v‖ ≤ η * ‖A v‖)
    (hb : ∀ v, ‖(b.2 - H) v‖ ≤ η * ‖A v‖) (v : p.E) :
    ‖(a.2 - b.2) v‖ ≤ 2 * η * ‖A v‖ := by
  have he : (a.2 - b.2) v = (a.2 - H) v - (b.2 - H) v := by
    simp only [sub_apply]
    abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith [ha v, hb v])

lemma coupled_difference_bound (p : Params) (a b : Model p)
    (g s u : p.E) (H A : p.E →L[ℝ] p.E) (η R : ℝ)
    (ha : ‖a.1 - g + (a.2 - H) s‖ ≤ R)
    (hb : ‖b.1 - g + (b.2 - H) s‖ ≤ R)
    (haH : ∀ v, ‖(a.2 - H) v‖ ≤ η * ‖A v‖)
    (hbH : ∀ v, ‖(b.2 - H) v‖ ≤ η * ‖A v‖) :
    ‖a.1 - b.1 + (a.2 - b.2) u‖ ≤ 2 * R + 2 * η * ‖A (u - s)‖ := by
  have he : a.1 - b.1 + (a.2 - b.2) u =
      (a.1 - g + (a.2 - H) s) - (b.1 - g + (b.2 - H) s) +
        (a.2 - b.2) (u - s) := by
    simp only [sub_apply, map_sub]
    abel
  rw [he]
  have hfirst := norm_sub_le (a.1 - g + (a.2 - H) s) (b.1 - g + (b.2 - H) s)
  have hlast := model_difference_bound p a b H A η haH hbH (u - s)
  exact (norm_add_le _ _).trans (by linarith)

lemma good_models_anchored_compatible (p : Params) (a b : Model p)
    (g s : p.E) (H A : p.E →L[ℝ] p.E) (η : ℝ)
    (hρ : 0 ≤ p.ρ) (hη : 0 ≤ η) (hηsmall : 56 * η ≤ 1 / 1000000)
    (ha : ‖a.1 - g + (a.2 - H) s‖ ≤ η * p.ρ * ‖s‖ ^ 2)
    (hb : ‖b.1 - g + (b.2 - H) s‖ ≤ η * p.ρ * ‖s‖ ^ 2)
    (haH : ∀ v, ‖(a.2 - H) v‖ ≤ η * ‖A v‖)
    (hbH : ∀ v, ‖(b.2 - H) v‖ ≤ η * ‖A v‖)
    (hgraph : ∀ v, ‖A v‖ ≤ 4 * graphNorm p a v)
    (hradius : ‖s‖ / 2 ≤ ‖modelStep p a‖)
    (hdisp : ‖A (modelStep p a - s)‖ ≤ 6 * p.ρ * ‖s‖ ^ 2) :
    anchoredCompatible p a b := by
  constructor
  · intro v
    have hd := model_difference_bound p a b H A η haH hbH v
    have hg : 0 ≤ graphNorm p a v := by
      exact add_nonneg (norm_nonneg _) (mul_nonneg (mul_nonneg hρ (norm_nonneg _)) (norm_nonneg _))
    have hh := mul_le_mul_of_nonneg_left (hgraph v) (by positivity : 0 ≤ 2 * η)
    have hc := mul_le_mul_of_nonneg_right (show 8 * η ≤ (1 / 1000000 : ℝ) by linarith) hg
    change ‖(a.2 - b.2) v‖ ≤ (1 / 1000000 : ℝ) * graphNorm p a v
    nlinarith
  · have hd := coupled_difference_bound p a b g s (modelStep p a) H A η
      (η * p.ρ * ‖s‖ ^ 2) ha hb haH hbH
    have he := mul_le_mul_of_nonneg_left hdisp (by positivity : 0 ≤ 2 * η)
    have hs : ‖s‖ ^ 2 ≤ 4 * ‖modelStep p a‖ ^ 2 := by
      nlinarith [norm_nonneg s, norm_nonneg (modelStep p a)]
    have hscale := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 14 * η * p.ρ)
    have hc := mul_le_mul_of_nonneg_right hηsmall
      (by positivity : 0 ≤ p.ρ * ‖modelStep p a‖ ^ 2)
    change ‖a.1 - b.1 + (a.2 - b.2) (modelStep p a)‖ ≤
      (1 / 1000000 : ℝ) * p.ρ * ‖modelStep p a‖ ^ 2
    nlinarith

lemma compatible_transfers_error (p : Params) (a b : Model p)
    (g s : p.E) (H A : p.E →L[ℝ] p.E) (η : ℝ)
    (hρ : 0 ≤ p.ρ)
    (hb : ‖b.1 - g + (b.2 - H) s‖ ≤ η * p.ρ * ‖s‖ ^ 2)
    (hbH : ∀ v, ‖(b.2 - H) v‖ ≤ η * ‖A v‖)
    (hgraph : ∀ v, graphNorm p b v ≤ 4 * ‖A v‖)
    (hradius : ‖modelStep p b‖ ≤ 2 * ‖s‖)
    (hdisp : ‖A (modelStep p b - s)‖ ≤ 6 * p.ρ * ‖s‖ ^ 2)
    (hc : anchoredCompatible p b a) :
    (∀ v, ‖(a.2 - H) v‖ ≤ (η + 4 / 1000000) * ‖A v‖) ∧
      ‖a.1 - g + (a.2 - H) s‖ ≤ (η + 28 / 1000000) * p.ρ * ‖s‖ ^ 2 := by
  have hdiff (v : p.E) : ‖(a.2 - b.2) v‖ ≤ (4 / 1000000 : ℝ) * ‖A v‖ := by
    have hh := hc.1 v
    have hg := hgraph v
    rw [sub_apply, norm_sub_rev, ← sub_apply] at hh
    linarith
  constructor
  · intro v
    have he : (a.2 - H) v = (a.2 - b.2) v + (b.2 - H) v := by
      simp only [sub_apply]
      abel
    rw [he]
    exact (norm_add_le _ _).trans (by linarith [hdiff v, hbH v])
  · have hr : ‖modelStep p b‖ ^ 2 ≤ 4 * ‖s‖ ^ 2 := by
      nlinarith [norm_nonneg s, norm_nonneg (modelStep p b)]
    have hanchor : ‖a.1 - b.1 + (a.2 - b.2) (modelStep p b)‖ ≤
        (4 / 1000000 : ℝ) * p.ρ * ‖s‖ ^ 2 := by
      have hh := hc.2
      have he : a.1 - b.1 + (a.2 - b.2) (modelStep p b) =
          -(b.1 - a.1 + (b.2 - a.2) (modelStep p b)) := by
        simp only [sub_apply]
        abel
      rw [he, norm_neg]
      have hs := mul_le_mul_of_nonneg_left hr hρ
      nlinarith
    have hd := hdiff (modelStep p b - s)
    have he : a.1 - g + (a.2 - H) s =
        (b.1 - g + (b.2 - H) s) +
        (a.1 - b.1 + (a.2 - b.2) (modelStep p b)) -
        (a.2 - b.2) (modelStep p b - s) := by
      simp only [sub_apply, map_sub]
      abel
    rw [he]
    have ht := norm_add_le (b.1 - g + (b.2 - H) s)
      (a.1 - b.1 + (a.2 - b.2) (modelStep p b))
    exact (norm_sub_le _ _).trans (by nlinarith)

lemma graph_displacement_bound (p : Params) (H A : p.E →L[ℝ] p.E) (s u : p.E)
    (hρ : 0 ≤ p.ρ) (hradius : ‖u‖ ≤ 2 * ‖s‖)
    (hH : ‖H (u - s)‖ ≤ 3 * p.ρ * ‖s‖ ^ 2)
    (hA : ∀ v, ‖A v‖ ≤ ‖H v‖ + p.ρ * ‖s‖ * ‖v‖) :
    ‖A (u - s)‖ ≤ 6 * p.ρ * ‖s‖ ^ 2 := by
  have hd : ‖u - s‖ ≤ 3 * ‖s‖ := (norm_sub_le u s).trans (by linarith)
  have hh := mul_le_mul_of_nonneg_left hd (mul_nonneg hρ (norm_nonneg s))
  nlinarith [hA (u - s)]

lemma modelStep_stable_decrease (p : Params) (reference sampled : Model p) (η : ℝ)
    (hρ : 0 < p.ρ) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 10000)
    (href : reference.2.toLinearMap.IsSymmetric)
    (hsampled : sampled.2.toLinearMap.IsSymmetric)
    (hpos : 0 < ‖modelStep p reference‖)
    (hq : ‖sampled.1 - reference.1 +
      (sampled.2 - reference.2) (modelStep p reference)‖ ≤
        η * p.ρ * ‖modelStep p reference‖ ^ 2)
    (hform : ∀ v : p.E, |⟪v, (sampled.2 - reference.2) v⟫| ≤
      η * (⟪v, reference.2 v⟫ + 2 * p.ρ * ‖modelStep p reference‖ * ‖v‖ ^ 2)) :
    ‖modelStep p reference‖ / 2 < ‖modelStep p sampled‖ ∧
      ‖modelStep p sampled‖ < 2 * ‖modelStep p reference‖ ∧
      CappedCubicModel.model reference.2 reference.1 0 (p.ρ / 2)
        (modelStep p sampled) ≤ -p.ρ * ‖modelStep p reference‖ ^ 3 / 16 := by
  have hH (x y : p.E) : ⟪x, reference.2 y⟫ = ⟪reference.2 x, y⟫ := (href x y).symm
  have hD (x y : p.E) : ⟪x, (sampled.2 - reference.2) y⟫ =
      ⟪(sampled.2 - reference.2) x, y⟫ := by
    simp only [sub_apply, inner_sub_left, inner_sub_right]
    have hsx : ⟪sampled.2 x, y⟫ = ⟪x, sampled.2 y⟫ := hsampled x y
    have hrx : ⟪reference.2 x, y⟫ = ⟪x, reference.2 y⟫ := href x y
    rw [hsx, hrx]
  have hs := modelStep_stationary p hρ reference hH
  have hpsd (v : p.E) : 0 ≤ ⟪v, reference.2 v⟫ +
      p.ρ * ‖modelStep p reference‖ / 2 * ‖v‖ ^ 2 := by
    have hh := modelStep_psd p hρ reference hH v
    simp only [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq] at hh
    nlinarith
  apply CoupledCubicStability.stable_model_decrease reference.2 (sampled.2 - reference.2)
    reference.1 (sampled.1 - reference.1) (modelStep p reference) (modelStep p sampled)
    p.ρ η hρ hpos hη0 hη hH hD hs hpsd hq hform
  have heH : reference.2 + (sampled.2 - reference.2) = sampled.2 := by abel
  have heg : reference.1 + (sampled.1 - reference.1) = sampled.1 := by abel
  rw [heH, heg]
  exact modelStep_min p hρ sampled (modelStep p reference)

lemma modelStep_relative_error_form (p : Params) (reference sampled : Model p) (η : ℝ)
    (hρ : 0 < p.ρ) (hη : 0 ≤ η)
    (href : reference.2.toLinearMap.IsSymmetric)
    (hsampled : sampled.2.toLinearMap.IsSymmetric)
    (hrelative : ∀ v : p.E, ‖(sampled.2 - reference.2) v‖ ≤ η *
      ‖OracleTemplate.TemporalDiscrepancy.diagonalMap (href.eigenvectorBasis rfl)
        (fun i => |href.eigenvalues rfl i| + p.ρ * ‖modelStep p reference‖) v‖) :
    ∀ v : p.E, |⟪v, (sampled.2 - reference.2) v⟫| ≤
      η * (⟪v, reference.2 v⟫ + 2 * p.ρ * ‖modelStep p reference‖ * ‖v‖ ^ 2) := by
  have hD : (sampled.2 - reference.2).toLinearMap.IsSymmetric := by
    intro x y
    change ⟪(sampled.2 - reference.2) x, y⟫ = ⟪x, (sampled.2 - reference.2) y⟫
    simp only [sub_apply, inner_sub_left, inner_sub_right]
    have hsx : ⟪sampled.2 x, y⟫ = ⟪x, sampled.2 y⟫ := hsampled x y
    have hrx : ⟪reference.2 x, y⟫ = ⟪x, reference.2 y⟫ := href x y
    rw [hsx, hrx]
  have hshift (v : p.E) : -(p.ρ * ‖modelStep p reference‖) / 2 * ‖v‖ ^ 2 ≤
      ⟪v, reference.2 v⟫ := by
    have hh := modelStep_psd p hρ reference (fun x y => (href x y).symm) v
    simp only [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq] at hh
    nlinarith
  intro v
  have hh := CoupledCubicGeometry.cubic_relative_form reference.2 (sampled.2 - reference.2)
    (p.ρ * ‖modelStep p reference‖) η (by positivity) hη href hD hshift hrelative v
  convert hh using 1
  ring

lemma modelStep_hessian_displacement (p : Params) (reference sampled : Model p) (η : ℝ)
    (hρ : 0 < p.ρ) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 10000)
    (href : reference.2.toLinearMap.IsSymmetric)
    (hsampled : sampled.2.toLinearMap.IsSymmetric)
    (hradius : ‖modelStep p sampled‖ ≤ 2 * ‖modelStep p reference‖)
    (hq : ‖sampled.1 - reference.1 +
      (sampled.2 - reference.2) (modelStep p reference)‖ ≤
        η * p.ρ * ‖modelStep p reference‖ ^ 2)
    (herror : ∀ v : p.E, ‖(sampled.2 - reference.2) v‖ ≤
      η * (‖reference.2 v‖ + p.ρ * ‖modelStep p reference‖ * ‖v‖)) :
    ‖reference.2 (modelStep p sampled - modelStep p reference)‖ ≤
      3 * p.ρ * ‖modelStep p reference‖ ^ 2 := by
  have hs := modelStep_stationary p hρ reference (fun x y => (href x y).symm)
  have hu := modelStep_stationary p hρ sampled (fun x y => (hsampled x y).symm)
  have heH : reference.2 + (sampled.2 - reference.2) = sampled.2 := by abel
  have heg : reference.1 + (sampled.1 - reference.1) = sampled.1 := by abel
  apply CoupledCubicStability.stable_hessian_displacement reference.2
    (sampled.2 - reference.2) reference.1 (sampled.1 - reference.1)
    (modelStep p reference) (modelStep p sampled) p.ρ η hρ.le hη0 hη hs
  · simpa only [heH, heg] using hu
  · exact hradius
  · exact hq
  · exact herror _

lemma spectral_metric_bounds (p : Params) (reference : Model p)
    (href : reference.2.toLinearMap.IsSymmetric) (hρ : 0 ≤ p.ρ) (v : p.E) :
    let A := OracleTemplate.TemporalDiscrepancy.diagonalMap (href.eigenvectorBasis rfl)
      (fun i => |href.eigenvalues rfl i| + p.ρ * ‖modelStep p reference‖)
    ‖reference.2 v‖ ≤ ‖A v‖ ∧ p.ρ * ‖modelStep p reference‖ * ‖v‖ ≤ ‖A v‖ ∧
      ‖A v‖ ≤ ‖reference.2 v‖ + p.ρ * ‖modelStep p reference‖ * ‖v‖ := by
  dsimp only
  have he := OracleTemplate.TemporalDiscrepancy.spectral_diagonalization reference.2 href
  have hd := CoupledCubicGeometry.shifted_absolute_dominates (href.eigenvectorBasis rfl)
    (href.eigenvalues rfl) (p.ρ * ‖modelStep p reference‖) (by positivity) v
  have hu := CoupledCubicGeometry.shifted_absolute_norm (href.eigenvectorBasis rfl)
    (href.eigenvalues rfl) (p.ρ * ‖modelStep p reference‖) (by positivity) v
  rw [← he] at hd hu
  exact ⟨hd.1, hd.2, hu⟩

noncomputable def referenceMetric (p : Params) (reference : Model p)
    (href : reference.2.toLinearMap.IsSymmetric) : p.E →L[ℝ] p.E :=
  OracleTemplate.TemporalDiscrepancy.diagonalMap (href.eigenvectorBasis rfl)
    (fun i => |href.eigenvalues rfl i| + p.ρ * ‖modelStep p reference‖)

lemma positive_good_model_geometry (p : Params) (reference sampled : Model p) (η : ℝ)
    (hρ : 0 < p.ρ) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 10000)
    (href : reference.2.toLinearMap.IsSymmetric)
    (hsampled : sampled.2.toLinearMap.IsSymmetric)
    (hpos : 0 < ‖modelStep p reference‖)
    (hq : ‖sampled.1 - reference.1 +
      (sampled.2 - reference.2) (modelStep p reference)‖ ≤
        η * p.ρ * ‖modelStep p reference‖ ^ 2)
    (hrelative : ∀ v : p.E, ‖(sampled.2 - reference.2) v‖ ≤
      η * ‖referenceMetric p reference href v‖) :
    (‖modelStep p reference‖ / 2 ≤ ‖modelStep p sampled‖ ∧
      ‖modelStep p sampled‖ ≤ 2 * ‖modelStep p reference‖) ∧
    (∀ v : p.E, graphNorm p sampled v ≤ 4 * ‖referenceMetric p reference href v‖ ∧
      ‖referenceMetric p reference href v‖ ≤ 4 * graphNorm p sampled v) ∧
    ‖referenceMetric p reference href (modelStep p sampled - modelStep p reference)‖ ≤
      6 * p.ρ * ‖modelStep p reference‖ ^ 2 := by
  have hform := modelStep_relative_error_form p reference sampled η hρ hη0 href hsampled hrelative
  have hstable := modelStep_stable_decrease p reference sampled η hρ hη0 hη
    href hsampled hpos hq hform
  have hb (v : p.E) := spectral_metric_bounds p reference href hρ.le v
  have herror (v : p.E) : ‖(sampled.2 - reference.2) v‖ ≤
      η * (‖reference.2 v‖ + p.ρ * ‖modelStep p reference‖ * ‖v‖) :=
    (hrelative v).trans (mul_le_mul_of_nonneg_left (hb v).2.2 hη0)
  have hd := modelStep_hessian_displacement p reference sampled η hρ hη0 hη
    href hsampled hstable.2.1.le hq herror
  refine ⟨⟨hstable.1.le, hstable.2.1.le⟩, ?_, ?_⟩
  · intro v
    exact graphNorm_comparison p sampled reference.2 (referenceMetric p reference href)
      ‖modelStep p reference‖ η hρ.le (by linarith) hstable.1.le hstable.2.1.le
      (fun v => (hb v).1) (fun v => (hb v).2.1) (fun v => (hb v).2.2) hrelative v
  · exact graph_displacement_bound p reference.2 (referenceMetric p reference href)
      (modelStep p reference) (modelStep p sampled) hρ.le hstable.2.1.le hd
      (fun v => (hb v).2.2)

lemma zero_good_model_step (p : Params) (reference sampled : Model p) (η : ℝ)
    (hρ : 0 < p.ρ) (hη0 : 0 ≤ η) (hη : η ≤ 1)
    (href : reference.2.toLinearMap.IsSymmetric)
    (hsampled : sampled.2.toLinearMap.IsSymmetric)
    (hzero : modelStep p reference = 0)
    (hq : ‖sampled.1 - reference.1 +
      (sampled.2 - reference.2) (modelStep p reference)‖ ≤
        η * p.ρ * ‖modelStep p reference‖ ^ 2)
    (hrelative : ∀ v : p.E, ‖(sampled.2 - reference.2) v‖ ≤
      η * ‖referenceMetric p reference href v‖) :
    sampled.1 = 0 ∧ (∀ v : p.E, 0 ≤ ⟪v, sampled.2 v⟫) ∧ modelStep p sampled = 0 := by
  have hg : reference.1 = 0 := by
    have hh := modelStep_stationary p hρ reference (fun x y => (href x y).symm)
    simpa [hzero] using hh
  have hsg : sampled.1 = 0 := by simpa [hzero, hg] using hq
  have hpsd (v : p.E) : 0 ≤ ⟪v, reference.2 v⟫ := by
    have hh := modelStep_psd p hρ reference (fun x y => (href x y).symm) v
    simpa [hzero] using hh
  have hD : (sampled.2 - reference.2).toLinearMap.IsSymmetric := by
    intro x y
    change ⟪(sampled.2 - reference.2) x, y⟫ = ⟪x, (sampled.2 - reference.2) y⟫
    simp only [sub_apply, inner_sub_left, inner_sub_right]
    have hsx : ⟪sampled.2 x, y⟫ = ⟪x, sampled.2 y⟫ := hsampled x y
    have hrx : ⟪reference.2 x, y⟫ = ⟪x, reference.2 y⟫ := href x y
    rw [hsx, hrx]
  have he (v : p.E) : ‖referenceMetric p reference href v‖ = ‖reference.2 v‖ := by
    have hb := spectral_metric_bounds p reference href hρ.le v
    exact le_antisymm (by simpa [hzero, referenceMetric] using hb.2.2) hb.1
  have hsp (v : p.E) : 0 ≤ ⟪v, sampled.2 v⟫ := by
    have hh := CoupledCubicGeometry.relative_perturbation_nonnegative reference.2
      (sampled.2 - reference.2) η hη0 hη href hD hpsd
      (fun v => by simpa only [he v] using hrelative v) v
    have hsum : reference.2 + (sampled.2 - reference.2) = sampled.2 := by abel
    simpa only [hsum] using hh
  exact ⟨hsg, hsp, modelStep_zero p hρ sampled hsg hsp⟩

lemma good_model_geometry (p : Params) (reference sampled : Model p) (η : ℝ)
    (hρ : 0 < p.ρ) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 10000)
    (href : reference.2.toLinearMap.IsSymmetric)
    (hsampled : sampled.2.toLinearMap.IsSymmetric)
    (hq : ‖sampled.1 - reference.1 +
      (sampled.2 - reference.2) (modelStep p reference)‖ ≤
        η * p.ρ * ‖modelStep p reference‖ ^ 2)
    (hrelative : ∀ v : p.E, ‖(sampled.2 - reference.2) v‖ ≤
      η * ‖referenceMetric p reference href v‖) :
    (‖modelStep p reference‖ / 2 ≤ ‖modelStep p sampled‖ ∧
      ‖modelStep p sampled‖ ≤ 2 * ‖modelStep p reference‖) ∧
    (∀ v : p.E, graphNorm p sampled v ≤ 4 * ‖referenceMetric p reference href v‖ ∧
      ‖referenceMetric p reference href v‖ ≤ 4 * graphNorm p sampled v) ∧
    ‖referenceMetric p reference href (modelStep p sampled - modelStep p reference)‖ ≤
      6 * p.ρ * ‖modelStep p reference‖ ^ 2 := by
  by_cases hz : modelStep p reference = 0
  · have hsz := (zero_good_model_step p reference sampled η hρ hη0 (by linarith)
      href hsampled hz hq hrelative).2.2
    have hb (v : p.E) := spectral_metric_bounds p reference href hρ.le v
    have hlo : ‖modelStep p reference‖ / 2 ≤ ‖modelStep p sampled‖ := by simp [hz, hsz]
    have hup : ‖modelStep p sampled‖ ≤ 2 * ‖modelStep p reference‖ := by simp [hz, hsz]
    refine ⟨⟨hlo, hup⟩, ?_, ?_⟩
    · intro v
      exact graphNorm_comparison p sampled reference.2 (referenceMetric p reference href)
        ‖modelStep p reference‖ η hρ.le (by linarith) hlo hup
        (fun v => (hb v).1) (fun v => (hb v).2.1) (fun v => (hb v).2.2) hrelative v
    · simp [hz, hsz]
  · exact positive_good_model_geometry p reference sampled η hρ hη0 hη href hsampled
      (norm_pos_iff.mpr hz) hq hrelative

lemma good_models_compatible (p : Params) (reference a b : Model p) (η : ℝ)
    (hρ : 0 < p.ρ) (hη0 : 0 ≤ η) (hη : 56 * η ≤ 1 / 1000000)
    (href : reference.2.toLinearMap.IsSymmetric)
    (ha : a.2.toLinearMap.IsSymmetric) (hb : b.2.toLinearMap.IsSymmetric)
    (haq : ‖a.1 - reference.1 + (a.2 - reference.2) (modelStep p reference)‖ ≤
      η * p.ρ * ‖modelStep p reference‖ ^ 2)
    (hbq : ‖b.1 - reference.1 + (b.2 - reference.2) (modelStep p reference)‖ ≤
      η * p.ρ * ‖modelStep p reference‖ ^ 2)
    (haH : ∀ v : p.E, ‖(a.2 - reference.2) v‖ ≤ η * ‖referenceMetric p reference href v‖)
    (hbH : ∀ v : p.E, ‖(b.2 - reference.2) v‖ ≤ η * ‖referenceMetric p reference href v‖) :
    compatible p a b := by
  have hsmall : η ≤ 1 / 10000 := by linarith
  have hga := good_model_geometry p reference a η hρ hη0 hsmall href ha haq haH
  have hgb := good_model_geometry p reference b η hρ hη0 hsmall href hb hbq hbH
  constructor
  · exact good_models_anchored_compatible p a b reference.1 (modelStep p reference)
      reference.2 (referenceMetric p reference href) η hρ.le hη0 hη haq hbq haH hbH
      (fun v => (hga.2.1 v).2) hga.1.1 hga.2.2
  · exact good_models_anchored_compatible p b a reference.1 (modelStep p reference)
      reference.2 (referenceMetric p reference href) η hρ.le hη0 hη hbq haq hbH haH
      (fun v => (hgb.2.1 v).2) hgb.1.1 hgb.2.2

def relativeModelAccurate (p : Params) (reference sampled : Model p)
    (href : reference.2.toLinearMap.IsSymmetric) (η : ℝ) : Prop :=
  ‖sampled.1 - reference.1 + (sampled.2 - reference.2) (modelStep p reference)‖ ≤
    η * p.ρ * ‖modelStep p reference‖ ^ 2 ∧
  ∀ v : p.E, ‖(sampled.2 - reference.2) v‖ ≤ η * ‖referenceMetric p reference href v‖

lemma selected_model_accurate (p : Params) (reference : Model p) (models : List (Model p))
    (good : Finset ℕ) (η : ℝ) (hρ : 0 < p.ρ) (hη0 : 0 ≤ η)
    (hη : 56 * η ≤ 1 / 1000000) (href : reference.2.toLinearMap.IsSymmetric)
    (hsym : ∀ i ∈ good, (modelAt p models i).2.toLinearMap.IsSymmetric)
    (hsub : good ⊆ Finset.range models.length) (hmajor : models.length < 2 * good.card)
    (hgood : ∀ i ∈ good, relativeModelAccurate p reference (modelAt p models i) href η) :
    selectedIndex p models < models.length ∧
      relativeModelAccurate p reference (modelAt p models (selectedIndex p models)) href
        (η + 28 / 1000000) := by
  have hpairs (i : ℕ) (hi : i ∈ good) (j : ℕ) (hj : j ∈ good) :
      compatible p (modelAt p models i) (modelAt p models j) :=
    good_models_compatible p reference (modelAt p models i) (modelAt p models j) η
      hρ hη0 hη href (hsym i hi) (hsym j hj)
      (hgood i hi).1 (hgood j hj).1 (hgood i hi).2 (hgood j hj).2
  obtain ⟨hindex, j, hj, hc⟩ := selected_has_good_neighbor p models good hsub hmajor hpairs
  have hg := good_model_geometry p reference (modelAt p models j) η hρ hη0
    (by linarith) href (hsym j hj) (hgood j hj).1 (hgood j hj).2
  have ht := compatible_transfers_error p (modelAt p models (selectedIndex p models))
    (modelAt p models j) reference.1 (modelStep p reference) reference.2
    (referenceMetric p reference href) η hρ.le (hgood j hj).1 (hgood j hj).2
    (fun v => (hg.2.1 v).1) hg.1.2 hg.2.2 hc.2
  refine ⟨hindex, ht.2, ?_⟩
  intro v
  exact (ht.1 v).trans (by nlinarith [norm_nonneg (referenceMetric p reference href v)])

end LongTails.Proofs.CoupledCubicSelection
