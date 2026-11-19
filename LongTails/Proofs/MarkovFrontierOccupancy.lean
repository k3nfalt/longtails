import Mathlib.Data.Nat.Basic
import LongTails.Proofs.CountdownCalibration
import LongTails.Proofs.CountdownPath

namespace LongTails.Proofs.MarkovFrontierProgress

def advance (k : ℕ) (phase : Option (Fin 2)) : ℕ :=
  if phase = some ⟨k % 2, Nat.mod_lt _ (by decide)⟩ then k + 1 else k

def level (phase : ℕ → Option (Fin 2)) : ℕ → ℕ
  | 0 => 0
  | t + 1 => advance (level phase t) (phase t)

def entries (phase : ℕ → Option (Fin 2)) : ℕ → ℕ
  | 0 => 0
  | 1 => if (phase 0).isSome then 1 else 0
  | t + 2 => entries phase (t + 1) +
      if (phase (t + 1)).isSome ∧ phase (t + 1) ≠ phase t then 1 else 0

lemma advance_bounds (k : ℕ) (c : Option (Fin 2)) :
    k ≤ advance k c ∧ advance k c ≤ k + 1 := by
  unfold advance
  split <;> omega

lemma level_mono (phase : ℕ → Option (Fin 2)) {s t : ℕ} (hst : s ≤ t) :
    level phase s ≤ level phase t := by
  induction hst with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (advance_bounds _ _).1

lemma advance_idempotent (k : ℕ) (c : Option (Fin 2)) :
    advance (advance k c) c = advance k c := by
  unfold advance
  split <;> rename_i h
  · split <;> rename_i h'
    · have he := Option.some.inj (h.symm.trans h')
      have hv := congrArg Fin.val he
      dsimp at hv
      omega
    · rfl
  · simp

lemma level_le_entries (phase : ℕ → Option (Fin 2)) (t : ℕ) :
    level phase t ≤ entries phase t := by
  induction t with
  | zero => exact Nat.le_refl 0
  | succ t ih =>
    cases t with
    | zero =>
      cases h : phase 0 with
      | none => simp [level, advance, entries, h]
      | some c => simpa [level, entries, h] using (advance_bounds 0 (some c)).2
    | succ t =>
      by_cases he : phase (t + 1) = phase t
      · simpa [entries, level, he, advance_idempotent] using ih
      · cases h : phase (t + 1) with
        | none => simpa [entries, level, h, advance] using ih
        | some c =>
          have hb := (advance_bounds (level phase (t + 1)) (some c)).2
          have hn : some c ≠ phase t := h ▸ he
          simpa [level, entries, h, hn] using Nat.le_trans hb (Nat.add_le_add_right ih 1)

end LongTails.Proofs.MarkovFrontierProgress

open MeasureTheory OracleTemplate.CountdownMarkov
open scoped BigOperators

namespace LongTails.Proofs.MarkovFrontierPhases

abbrev Color := Option (Fin 2)

noncomputable def color (h : ℕ) (z : ℝ) : Color :=
  if z ≤ 0 then none else if z ≤ h then some 0 else some 1

lemma measurable_of_color {E : Type*} [MeasurableSpace E] (h : ℕ) (f : Color → E) :
    Measurable (fun z => f (color h z)) := by
  simp only [color, apply_ite f]
  exact Measurable.ite measurableSet_Iic measurable_const
    (Measurable.ite measurableSet_Iic measurable_const measurable_const)

lemma color_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (h : ℕ) (hh : 0 < h) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1 / 2) (f : Color → E) :
    let p := calibratedJump (h + h) q (by omega) hq hq1
    (∫ z, f (color h z) ∂stationaryMeasure (h + h) p) =
      (1 - q) • f none + (q / 2) • f (some 0) + (q / 2) • f (some 1) := by
  intro p
  have hp := calibratedJump_entry (h + h) q (by omega) hq hq1
  change (p : ℝ) / (1 + (h + h : ℕ) * (p : ℝ)) = _ at hp
  have hm := calibratedJump_mass (h + h) q (by omega) hq hq1
  change (h + h : ℕ) * (p : ℝ) / (1 + (h + h : ℕ) * (p : ℝ)) = _ at hm
  have hd : 0 < 1 + (h + h : ℕ) * (p : ℝ) := by
    have := p.property.1
    positivity
  have hw : 1 / (1 + (h + h : ℕ) * (p : ℝ)) = 1 - q := by
    apply (div_eq_iff hd.ne').mpr
    have := (div_eq_iff hd.ne').mp hm
    linarith
  have hs : (∑ i : Fin (h + h), f (color h ((i.val : ℝ) + 1))) =
      h • f (some 0) + h • f (some 1) := by
    rw [Fin.sum_univ_add]
    have ha (i : Fin h) : color h (((Fin.castAdd h i).val : ℝ) + 1) = some 0 := by
      have hi : (i.val : ℝ) + 1 ≤ h := by exact_mod_cast Nat.succ_le_of_lt i.isLt
      have hp : 0 < (i.val : ℝ) + 1 := by positivity
      simp only [Fin.val_castAdd, color, ite_eq_right (not_le.mpr hp), ite_eq_left hi]
    have hb (i : Fin h) : color h (((Fin.natAdd h i).val : ℝ) + 1) = some 1 := by
      simp only [Fin.val_natAdd, Nat.cast_add, color]
      split_ifs <;> first | rfl | linarith [Nat.cast_nonneg (α := ℝ) h, Nat.cast_nonneg (α := ℝ) i.val]
    simp only [ha, hb, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hhalf : q / ((h + h : ℕ) : ℝ) * (h : ℝ) = q / 2 := by
    push_cast
    field_simp
    ring
  rw [integral_stationary_split, hw, hp, hs, smul_add,
    ← Nat.cast_smul_eq_nsmul ℝ h (f (some 0)), ← Nat.cast_smul_eq_nsmul ℝ h (f (some 1)),
    smul_smul, smul_smul, hhalf, show color h 0 = none by simp [color], add_assoc]

end LongTails.Proofs.MarkovFrontierPhases

open MeasureTheory ProbabilityTheory Function Preorder
open scoped BigOperators

namespace LongTails.Proofs.MarkovFrontierOccupancy

open OracleTemplate.CountdownMarkov OracleTemplate.HeavyTailedMarkovGradient
open LongTails.Setups.HeavyTailedMarkovSmoothAndConvex
open MarkovFrontierPhases MarkovFrontierProgress

local instance : MeasurableSpace Color := ⊤
local instance : MeasurableSingletonClass Color := ⟨fun _ => trivial⟩

lemma color_measurable (h : ℕ) : Measurable (color h) :=
  measurable_of_color h id

def phaseCost (a b : Color) : ℝ := if b.isSome ∧ b ≠ a then 1 else 0

lemma phaseCost_measurable : Measurable (Function.uncurry phaseCost) :=
  measurable_of_countable _

lemma phaseCost_abs (a b : Color) : |phaseCost a b| ≤ 1 := by
  unfold phaseCost
  split <;> norm_num

lemma stationary_pair_integral (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (π : ProbabilityMeasure ℝ)
    (hπ : κ ∘ₘ (π : Measure ℝ) = (π : Measure ℝ)) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hm : Measurable (Function.uncurry F)) (hb : ∀ x y, |F x y| ≤ 1) :
    (∫ ξ, F (ξ k) (ξ (k + 1)) ∂(pathLaw κ π : Measure (ℕ → ℝ))) =
      ∫ x, ∫ y, F x y ∂κ x ∂(π : Measure ℝ) := by
  let P : Measure (ℕ → ℝ) := pathLaw κ π
  let last : (Finset.Iic k → ℝ) → ℝ := fun s => s ⟨k, Finset.mem_Iic.mpr le_rfl⟩
  have hl : Measurable last := measurable_pi_apply _
  have h := pathLaw_integral_future κ π k 1
    (W := fun s y => F (last s) y)
    (hm.comp ((hl.comp measurable_fst).prodMk measurable_snd)) (fun s y => hb (last s) y)
  rw [pow_one] at h
  refine h.trans ?_
  have hmarg : (P.map (frestrictLe k)).map last = (π : Measure ℝ) := by
    rw [Measure.map_map hl (by fun_prop)]
    exact pathLaw_stationary_marginal κ π hπ k
  rw [← hmarg, integral_map hl.aemeasurable]
  exact (hm.stronglyMeasurable.integral_kernel_prod_right (κ := κ)).aestronglyMeasurable

lemma cost_decrement (h : ℕ) (hh : 0 < h) (j : ℕ) :
    phaseCost (color h ((j : ℝ) + 1)) (color h (j : ℝ)) = if j = h then 1 else 0 := by
  have hj : (0 : ℝ) < ↑j + 1 := by positivity
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  by_cases hz : j = 0
  · subst j
    simp [phaseCost, color, Ne.symm (Nat.ne_of_gt hh)]
  by_cases he : j = h
  · subst j
    simp [phaseCost, color, not_le.mpr hj, not_le.mpr hh']
  rcases lt_or_gt_of_ne he with hl | hg
  · have ha : (j : ℝ) + 1 ≤ h := by exact_mod_cast Nat.succ_le_of_lt hl
    have hb : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hz
    simp [phaseCost, color, not_le.mpr hj, not_le.mpr hb, ha, (by linarith : (j : ℝ) ≤ h), he]
  · have ha : (h : ℝ) < j := by exact_mod_cast hg
    have hb : (0 : ℝ) < j := by linarith
    simp [phaseCost, color, not_le.mpr hj, not_le.mpr hb, not_le.mpr ha,
      (by linarith : ¬ (j : ℝ) + 1 ≤ h), he]

set_option maxHeartbeats 900000 in
lemma step_cost (h : ℕ) (hh : 0 < h) (p : unitInterval) (k : ℕ) :
    let P : Measure (ℕ → ℝ) := pathLaw (kernel (h + h) p) (stationaryLaw (h + h) p)
    (∫ ξ, phaseCost (color h (ξ k)) (color h (ξ (k + 1))) ∂P) =
      2 * (p : ℝ) / (1 + (h + h : ℕ) * (p : ℝ)) := by
  intro P
  let F : ℝ → ℝ → ℝ := fun x y => phaseCost (color h x) (color h y)
  have hm : Measurable (Function.uncurry F) := phaseCost_measurable.comp
    (((color_measurable h).comp measurable_fst).prodMk ((color_measurable h).comp measurable_snd))
  change (∫ ξ, F (ξ k) (ξ (k + 1)) ∂P) = _
  refine (stationary_pair_integral (kernel (h+h) p) (stationaryLaw (h+h) p) (stationary _ _) k F hm (fun _ _ => phaseCost_abs _ _)).trans ?_
  change (∫ x, ∫ y, F x y ∂kernel (h + h) p x ∂stationaryMeasure (h + h) p) = _
  rw [integral_stationary_split, kernel_zero, integral_bernoulliMeasure]
  have hz : F 0 0 = 0 := by simp [F, phaseCost, color]
  have hbig : F 0 (h + h : ℕ) = 1 := by
    have hpos : (0 : ℝ) < h := by exact_mod_cast hh
    simp [F, phaseCost, color, show ¬ (h : ℝ) + h ≤ 0 by linarith,
      show ¬ (h : ℝ) + h ≤ h by linarith]
  have hs (i : Fin (h + h)) :
      (∫ y, F ((i.val : ℝ) + 1) y ∂kernel (h + h) p ((i.val : ℝ) + 1)) =
        if i.val = h then 1 else 0 := by
    rw [← Nat.cast_succ, kernel_succ, integral_dirac]
    simpa only [F, Nat.cast_succ] using cost_decrement h hh i.val
  simp_rw [hs]
  have hsum : (∑ i : Fin (h + h), if i.val = h then (1 : ℝ) else 0) = 1 := by
    let j : Fin (h + h) := ⟨h, by omega⟩
    have he (i : Fin (h + h)) : i.val = h ↔ i = j := ⟨fun hi => Fin.ext hi, fun hi => congrArg Fin.val hi⟩
    simp_rw [he]
    simp
  rw [hsum, hbig, hz]
  simp only [smul_eq_mul, mul_zero, add_zero, mul_one]
  ring

noncomputable def count (h N : ℕ) (ξ : ℕ → ℝ) : ℕ := entries (fun t => color h (ξ t)) N

lemma count_measurable (h N : ℕ) : Measurable (count h N) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih =>
    cases N with
    | zero =>
      exact ((measurable_of_color h (fun c => if c.isSome then (1 : ℕ) else 0)).comp
        (measurable_pi_apply 0))
    | succ N =>
      let f : Color × Color → ℕ := fun z => if z.2.isSome ∧ z.2 ≠ z.1 then 1 else 0
      exact ih.add ((measurable_of_countable f).comp
        (((color_measurable h).comp (measurable_pi_apply N)).prodMk
          ((color_measurable h).comp (measurable_pi_apply (N + 1)))))

lemma count_le (h N : ℕ) (ξ : ℕ → ℝ) : count h N ξ ≤ N := by
  induction N with
  | zero => exact le_rfl
  | succ N ih =>
    cases N with
    | zero => simp only [count, entries]; split <;> omega
    | succ N => unfold count at *; rw [entries]; split <;> omega

lemma count_integrable (P : Measure (ℕ → ℝ)) [IsProbabilityMeasure P] (h N : ℕ) :
    Integrable (fun ξ => (count h N ξ : ℝ)) P :=
  Integrable.of_bound ((measurable_of_countable (fun i : ℕ => (i : ℝ))).comp (count_measurable h N)).aestronglyMeasurable N
    (.of_forall fun ξ => by rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast count_le h N ξ)

lemma count_expectation (h : ℕ) (hh : 0 < h) (p : unitInterval) (N : ℕ) :
    let P : Measure (ℕ → ℝ) := pathLaw (kernel (h + h) p) (stationaryLaw (h + h) p)
    (∫ ξ, (count h N ξ : ℝ) ∂P) ≤ 1 + N * (2 * (p : ℝ) / (1 + (h + h : ℕ) * (p : ℝ))) := by
  intro P
  have : IsProbabilityMeasure P :=
    (pathLaw (kernel (h + h) p) (stationaryLaw (h + h) p)).property
  let v := 2 * (p : ℝ) / (1 + (h + h : ℕ) * (p : ℝ))
  have hv : 0 ≤ v := by dsimp [v]; have := p.property.1; positivity
  induction N with
  | zero => simp [count, entries]
  | succ N ih =>
    cases N with
    | zero =>
      have hmono := integral_mono (count_integrable P h 1) (integrable_const (1 : ℝ))
        (fun ξ => (by exact_mod_cast count_le h 1 ξ : (count h 1 ξ : ℝ) ≤ 1))
      simp only [integral_const, probReal_univ, one_smul] at hmono
      change _ ≤ 1 + ((1 : ℕ) : ℝ) * v
      norm_num
      linarith
    | succ N =>
      let c := fun ξ : ℕ → ℝ => phaseCost (color h (ξ N)) (color h (ξ (N + 1)))
      have hm : Measurable c := phaseCost_measurable.comp
        (((color_measurable h).comp (measurable_pi_apply N)).prodMk
          ((color_measurable h).comp (measurable_pi_apply (N + 1))))
      have hi : Integrable c P := Integrable.of_bound hm.aestronglyMeasurable 1
        (.of_forall fun _ => phaseCost_abs _ _)
      have he (ξ : ℕ → ℝ) : (count h (N + 2) ξ : ℝ) = count h (N + 1) ξ + c ξ := by
        simp only [count, entries, c, phaseCost, Nat.cast_add]
        split <;> simp
      simp_rw [he]
      rw [integral_add (count_integrable P h (N + 1)) hi, show (∫ ξ, c ξ ∂P) = v from step_cost h hh p N]
      change _ ≤ 1 + ((N + 1 + 1 : ℕ) : ℝ) * v
      change _ ≤ 1 + ((N + 1 : ℕ) : ℝ) * v at ih
      push_cast at ih ⊢
      linarith

end LongTails.Proofs.MarkovFrontierOccupancy
