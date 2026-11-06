import LongTails.Algorithms.SpikedSoftCut
import LongTails.Proofs.SoftCutCertificateMinimax
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.SpikedSoftCutSelection

lemma measurable_list_argmax {Z A : Type*} [MeasurableSpace Z]
    [MeasurableSpace (Option A)] [Countable A] [DecidableEq A]
    (l : List A) (score : Z → A → ℝ) (hs : ∀ a, Measurable (fun z => score z a)) :
    Measurable (fun z => l.argmax (score z)) := by
  apply measurable_to_countable'
  intro o
  cases o with
  | none =>
      change MeasurableSet {z | l.argmax (score z) = none}
      simp only [List.argmax_eq_none]
      exact MeasurableSet.const _
  | some a =>
      change MeasurableSet {z | l.argmax (score z) = some a}
      simp only [List.argmax_eq_some_iff, Set.ofPred_and, Set.ofPred_forall]
      apply MeasurableSet.inter (MeasurableSet.const _)
      apply MeasurableSet.inter
      · exact MeasurableSet.iInter fun b => MeasurableSet.iInter fun _ =>
          measurableSet_le (hs b) (hs a)
      · apply MeasurableSet.iInter
        intro b
        apply MeasurableSet.iInter
        intro _
        have heq : {z | score z a ≤ score z b → l.idxOf a ≤ l.idxOf b} =
            {z | score z a ≤ score z b}ᶜ ∪ {z : Z | l.idxOf a ≤ l.idxOf b} := by
          ext z
          simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, imp_iff_not_or]
        rw [heq]
        exact (measurableSet_le (hs a) (hs b)).compl.union (MeasurableSet.const _)

open LongTails.Setups.SpikedSubGaussianConvex
open LongTails.Algorithms.SpikedSoftCut

@[fun_prop] lemma continuous_certificateScore (q : Params) (α : ℝ) (T : ℕ)
    (θ : Fin T → ℝ) : Continuous (fun data :
      (Fin T → InnerSpace q) × (Fin T → InnerSpace q) =>
        certificateScore q α data.1 data.2 θ) := by
  unfold certificateScore
  fun_prop

@[fun_prop] lemma measurable_selectedCoefficients (q : Params) (α : ℝ) (T n : ℕ) :
    Measurable (fun data : (Fin T → InnerSpace q) × (Fin T → InnerSpace q) =>
      selectedCoefficients q α T n data.1 data.2) := by
  let : MeasurableSpace (Option (Fin T → Fin (n + 1))) := ⊤
  have hs := measurable_list_argmax (coefficientGrid T n)
    (fun (data : (Fin T → InnerSpace q) × (Fin T → InnerSpace q)) k =>
      certificateScore q α data.1 data.2 (gridCoefficients k))
    (fun k => (continuous_certificateScore q α T (gridCoefficients k)).measurable)
  exact (measurable_of_countable (fun o : Option (Fin T → Fin (n + 1)) =>
    gridCoefficients (o.getD (fun _ => 0)))).comp hs

@[fun_prop] lemma measurable_certificateWeights (q : Params) (α : ℝ) (T n : ℕ) :
    Measurable (fun data : (Fin T → InnerSpace q) × (Fin T → InnerSpace q) =>
      certificateWeights q α T n data.1 data.2) := by
  let θ := fun data : (Fin T → InnerSpace q) × (Fin T → InnerSpace q) =>
    selectedCoefficients q α T n data.1 data.2
  have hθ : Measurable θ := measurable_selectedCoefficients q α T n
  have hS : Measurable (fun data => ∑ i, θ data i) := by fun_prop
  change Measurable (fun data => if 0 < ∑ i, θ data i then
    (fun i => θ data i / ∑ j, θ data j) else (fun i => if i.val = 0 then 1 else 0))
  apply Measurable.ite (measurableSet_lt measurable_const hS)
  · exact Measurable.of_eval fun i => ((measurable_pi_apply i).comp hθ).div hS
  · exact measurable_const

lemma gridCoefficients_bounds {T n : ℕ} (hn : 0 < n) (k : Fin T → Fin (n + 1))
    (i : Fin T) : 0 ≤ gridCoefficients k i ∧ gridCoefficients k i ≤ 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : ((k i).val : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ (k i).isLt
  exact ⟨div_nonneg (Nat.cast_nonneg _) hn'.le, (div_le_one hn').2 hk⟩

lemma selectedCoefficients_bounds (q : Params) (α : ℝ) (T n : ℕ) (hn : 0 < n)
    (points estimates : Fin T → InnerSpace q) (i : Fin T) :
    0 ≤ selectedCoefficients q α T n points estimates i ∧
      selectedCoefficients q α T n points estimates i ≤ 1 :=
  gridCoefficients_bounds hn _ i

lemma certificateWeights_nonneg (q : Params) (α : ℝ) (T n : ℕ) (hn : 0 < n)
    (points estimates : Fin T → InnerSpace q) (i : Fin T) :
    0 ≤ certificateWeights q α T n points estimates i := by
  unfold certificateWeights
  split_ifs with hs
  · exact div_nonneg (selectedCoefficients_bounds q α T n hn points estimates i).1 hs.le
  · dsimp only
    split_ifs <;> norm_num

lemma certificateWeights_sum (q : Params) (α : ℝ) (T n : ℕ) (hT : 0 < T)
    (points estimates : Fin T → InnerSpace q) :
    ∑ i, certificateWeights q α T n points estimates i = 1 := by
  let : NeZero T := ⟨Nat.ne_of_gt hT⟩
  unfold certificateWeights
  split_ifs with hs
  · rw [← Finset.sum_div, div_self (ne_of_gt hs)]
  · have heq (i : Fin T) : i.val = 0 ↔ i = 0 := by
      exact ⟨fun h => Fin.ext h, fun h => by simp [h]⟩
    simp_rw [heq]
    simp

lemma selectedCoefficients_maximal (q : Params) (α : ℝ) (T n : ℕ)
    (points estimates : Fin T → InnerSpace q) (k : Fin T → Fin (n + 1)) :
    certificateScore q α points estimates (gridCoefficients k) ≤
      certificateScore q α points estimates (selectedCoefficients q α T n points estimates) := by
  classical
  have hne : coefficientGrid T n ≠ [] := by
    intro he
    have hk : k ∈ coefficientGrid T n := by simp [coefficientGrid]
    rw [he] at hk
    exact List.not_mem_nil hk
  cases harg : (coefficientGrid T n).argmax
      (fun j => certificateScore q α points estimates (gridCoefficients j)) with
  | none => exact False.elim (hne (List.argmax_eq_none.mp harg))
  | some j =>
      have hj : j ∈ (coefficientGrid T n).argmax
          (fun j => certificateScore q α points estimates (gridCoefficients j)) := by simp [harg]
      have hk : k ∈ coefficientGrid T n := by simp [coefficientGrid]
      simpa only [selectedCoefficients, harg, Option.getD_some] using List.le_of_mem_argmax hk hj

lemma exists_grid_approximation {T n : ℕ} (hn : 0 < n) (θ : Fin T → ℝ)
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1) :
    ∃ k : Fin T → Fin (n + 1), ∀ i, |gridCoefficients k i - θ i| ≤ 1 / (n : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hfloor (i : Fin T) : ⌊(n : ℝ) * θ i⌋₊ ≤ n :=
    Nat.floor_le_of_le (by nlinarith [(hθ i).2])
  let k : Fin T → Fin (n + 1) := fun i => ⟨⌊(n : ℝ) * θ i⌋₊, Nat.lt_succ_of_le (hfloor i)⟩
  refine ⟨k, ?_⟩
  intro i
  have hlo := Nat.floor_le (mul_nonneg hn'.le (hθ i).1)
  have hhi := Nat.lt_floor_add_one ((n : ℝ) * θ i)
  have hc : (⌊(n : ℝ) * θ i⌋₊ : ℝ) / n * n = ⌊(n : ℝ) * θ i⌋₊ :=
    div_mul_cancel₀ _ hn'.ne'
  have hunit : (1 / (n : ℝ)) * n = 1 := div_mul_cancel₀ _ hn'.ne'
  change |(⌊(n : ℝ) * θ i⌋₊ : ℝ) / n - θ i| ≤ 1 / (n : ℝ)
  apply abs_le.mpr
  constructor <;> nlinarith

lemma affine_sum_decomposition (q : Params) (α : ℝ) {T : ℕ}
    (points estimates : Fin T → InnerSpace q) (θ : Fin T → ℝ) (y : InnerSpace q) :
    (∑ i, θ i * (⟪estimates i, y - points i⟫ + α / 2)) =
      (∑ i, θ i * (α / 2 - ⟪estimates i, points i⟫)) +
        ⟪∑ i, θ i • estimates i, y⟫ := by
  simp only [inner_sub_right, sum_inner, real_inner_smul_left,
    mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

lemma certificateScore_le_affine (q : Params) (α : ℝ) {T : ℕ}
    (points estimates : Fin T → InnerSpace q) (θ : Fin T → ℝ)
    (y : InnerSpace q) (hy : ‖y‖ ≤ q.R) :
    certificateScore q α points estimates θ ≤
      ∑ i, θ i * (⟪estimates i, y - points i⟫ + α / 2) := by
  rw [affine_sum_decomposition]
  have h := (abs_real_inner_le_norm (∑ i, θ i • estimates i) y).trans
    (mul_le_mul_of_nonneg_left hy (norm_nonneg _))
  have hn := (abs_le.mp h).1
  unfold certificateScore
  nlinarith

lemma certificateScore_attained (q : Params) (α : ℝ) {T : ℕ}
    (points estimates : Fin T → InnerSpace q) (θ : Fin T → ℝ) (hR : 0 ≤ q.R) :
    ∃ y : InnerSpace q, ‖y‖ ≤ q.R ∧
      certificateScore q α points estimates θ =
        ∑ i, θ i * (⟪estimates i, y - points i⟫ + α / 2) := by
  let g := ∑ i, θ i • estimates i
  by_cases hg : g = 0
  · refine ⟨0, by simpa using hR, ?_⟩
    rw [affine_sum_decomposition]
    simp only [certificateScore, ← show g = ∑ i, θ i • estimates i from rfl, hg,
      norm_zero, mul_zero, sub_zero, inner_zero_right, add_zero]
  · have hn : 0 < ‖g‖ := norm_pos_iff.mpr hg
    refine ⟨(-q.R / ‖g‖) • g, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg hR,
        abs_of_nonneg hn.le, div_mul_cancel₀ _ hn.ne']
    · rw [affine_sum_decomposition]
      change _ = _ + ⟪g, (-q.R / ‖g‖) • g⟫
      rw [inner_smul_right, real_inner_self_eq_norm_sq]
      unfold certificateScore
      change _ - q.R * ‖g‖ = _ + (-q.R / ‖g‖) * ‖g‖ ^ 2
      field_simp
      ring

lemma affine_coordinate_bound (q : Params) (α M : ℝ) {T : ℕ}
    (points estimates : Fin T → InnerSpace q) (y : InnerSpace q) (i : Fin T)
    (hα : 0 ≤ α) (hM : 0 ≤ M)
    (hp : ‖points i‖ ≤ q.R) (he : ‖estimates i‖ ≤ M) (hy : ‖y‖ ≤ q.R) :
    |⟪estimates i, y - points i⟫ + α / 2| ≤ α / 2 + 2 * q.R * M := by
  have hd : ‖y - points i‖ ≤ 2 * q.R := (norm_sub_le _ _).trans (by linarith)
  have hi := (abs_real_inner_le_norm (estimates i) (y - points i)).trans
    (mul_le_mul he hd (norm_nonneg _) hM)
  have ha := abs_add_le ⟪estimates i, y - points i⟫ (α / 2)
  rw [abs_of_nonneg (show 0 ≤ α / 2 by positivity)] at ha
  linarith

lemma affine_grid_error (q : Params) (α M τ : ℝ) {T : ℕ}
    (points estimates : Fin T → InnerSpace q) (θ ψ : Fin T → ℝ)
    (y : InnerSpace q) (hα : 0 ≤ α) (hM : 0 ≤ M) (hτ : 0 ≤ τ)
    (hp : ∀ i, ‖points i‖ ≤ q.R) (he : ∀ i, ‖estimates i‖ ≤ M) (hy : ‖y‖ ≤ q.R)
    (hclose : ∀ i, |ψ i - θ i| ≤ τ) :
    (∑ i, θ i * (⟪estimates i, y - points i⟫ + α / 2)) -
      (α / 2 + 2 * q.R * M) * (T : ℝ) * τ ≤
        ∑ i, ψ i * (⟪estimates i, y - points i⟫ + α / 2) := by
  have hpoint (i : Fin T) : (θ i - ψ i) * (⟪estimates i, y - points i⟫ + α / 2) ≤
      τ * (α / 2 + 2 * q.R * M) := by
    apply (le_abs_self _).trans
    rw [abs_mul, abs_sub_comm (θ i) (ψ i)]
    exact mul_le_mul (hclose i)
      (affine_coordinate_bound q α M points estimates y i hα hM (hp i) (he i) hy)
      (abs_nonneg _) hτ
  have h := Finset.sum_le_sum (s := Finset.univ) fun i _ => hpoint i
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at h
  nlinarith

lemma selected_margin_from_certificate (q : Params) (α M margin : ℝ) (T n : ℕ)
    (points estimates : Fin T → InnerSpace q) (θ : Fin T → ℝ)
    (hα : 0 ≤ α) (hR : 0 ≤ q.R) (hM : 0 ≤ M) (hn : 0 < n)
    (hp : ∀ i, ‖points i‖ ≤ q.R) (he : ∀ i, ‖estimates i‖ ≤ M)
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1)
    (hmargin : ∀ y, ‖y‖ ≤ q.R →
      margin ≤ ∑ i, θ i * (⟪estimates i, y - points i⟫ + α / 2)) :
    margin - (α / 2 + 2 * q.R * M) * T / n ≤
      certificateScore q α points estimates (selectedCoefficients q α T n points estimates) := by
  obtain ⟨k, hk⟩ := exists_grid_approximation hn θ hθ
  obtain ⟨y, hy, heq⟩ := certificateScore_attained q α points estimates (gridCoefficients k) hR
  have herror := affine_grid_error q α M (1 / (n : ℝ)) points estimates θ (gridCoefficients k)
    y hα hM (by positivity) hp he hy hk
  have hcert := hmargin y hy
  have hmax := selectedCoefficients_maximal q α T n points estimates k
  rw [heq] at hmax
  have hid : (α / 2 + 2 * q.R * M) * (T : ℝ) * (1 / (n : ℝ)) =
      (α / 2 + 2 * q.R * M) * T / n := by ring
  rw [hid] at herror
  linarith

lemma selected_margin_of_hinge (q : Params) (α M margin : ℝ) (T n : ℕ)
    (points estimates : Fin T → InnerSpace q)
    (hα : 0 ≤ α) (hR : 0 ≤ q.R) (hM : 0 ≤ M) (hn : 0 < n)
    (hp : ∀ i, ‖points i‖ ≤ q.R) (he : ∀ i, ‖estimates i‖ ≤ M)
    (hhinge : ∀ y, ‖y‖ ≤ q.R →
      margin ≤ ∑ i, max 0 (⟪estimates i, y - points i⟫ + α / 2)) :
    margin - (α / 2 + 2 * q.R * M) * T / n ≤
      certificateScore q α points estimates (selectedCoefficients q α T n points estimates) := by
  let Y := Metric.closedBall (0 : InnerSpace q) q.R
  have hY : Y.Nonempty := ⟨0, by simpa [Y] using hR⟩
  have hcontinuous (i : Fin T) : Continuous
      (fun y : InnerSpace q => ⟪estimates i, y - points i⟫ + α / 2) := by fun_prop
  have hconvex (i : Fin T) : ConvexOn ℝ Y
      (fun y : InnerSpace q => ⟪estimates i, y - points i⟫ + α / 2) := by
    refine ⟨convex_closedBall _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [inner_sub_right, inner_add_right, inner_smul_right, smul_eq_mul]
    have hc : (a + b) * (α / 2 - ⟪estimates i, points i⟫) =
        α / 2 - ⟪estimates i, points i⟫ := by rw [hab, one_mul]
    nlinarith [hc]
  obtain ⟨θ, hθ, hcert⟩ := SoftCutCertificateMinimax.capped_certificate_exists Y hY
    (convex_closedBall _ _) (isCompact_closedBall _ _)
    (fun y i => ⟪estimates i, y - points i⟫ + α / 2) hcontinuous hconvex margin
    (fun y hy => hhinge y (by simpa [Y] using hy))
  exact selected_margin_from_certificate q α M margin T n points estimates θ hα hR hM hn hp he hθ
    (fun y hy => hcert y (by simpa [Y] using hy))

lemma selected_sum_pos_of_score_pos (q : Params) (α : ℝ) (T n : ℕ) (hn : 0 < n)
    (points estimates : Fin T → InnerSpace q)
    (hscore : 0 < certificateScore q α points estimates
      (selectedCoefficients q α T n points estimates)) :
    0 < ∑ i, selectedCoefficients q α T n points estimates i := by
  let θ := selectedCoefficients q α T n points estimates
  have hθ : ∀ i, 0 ≤ θ i := fun i => (selectedCoefficients_bounds q α T n hn points estimates i).1
  have hnonneg : 0 ≤ ∑ i, θ i := Finset.sum_nonneg fun i _ => hθ i
  by_contra hnot
  have hzero : ∑ i, θ i = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
  have heach := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => hθ i)).mp hzero
  have hfun : θ = fun _ => 0 := funext fun i => heach i (Finset.mem_univ i)
  change 0 < certificateScore q α points estimates θ at hscore
  simp [certificateScore, hfun] at hscore

end LongTails.Proofs.SpikedSoftCutSelection
