import LongTails.Proofs.BlockLowerBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory OracleTemplate
open scoped BigOperators

namespace LongTails.Proofs.BlockLowerParameters

open Classical
open LongTails.Proofs.AbcLowerParameters LongTails.Proofs.BlockEmbedding
open LongTails.Proofs.BlockLowerInstance

noncomputable def smoothTotal (q : QParams) : ℝ := ∑ j, q.L j

noncomputable def wt (q : QParams) (j : Fin q.B) : ℝ := (q.L j * q.σ j ^ 2) ^ ((1 : ℝ) / 3)

noncomputable def hetero (q : QParams) : ℝ := ∑ j, wt q j

noncomputable def lowerTarget (q : QParams) : ℝ :=
  ((∑ j, q.L j) * q.Δ / q.ε ^ 2 + (∑ j, (q.L j * q.σ j ^ 2) ^ ((1 : ℝ) / 3)) ^ 3 * q.Δ / q.ε ^ 4) /
    2 ^ 57

lemma lowerTarget_eq (q : QParams) :
    lowerTarget q = (smoothTotal q * q.Δ / q.ε ^ 2 + hetero q ^ 3 * q.Δ / q.ε ^ 4) / 2 ^ 57 := rfl

def active (q : QParams) (j : Fin q.B) : Prop := hetero q ≤ 2 * q.B * wt q j

noncomputable def ratio (q : QParams) : ℝ := q.ε ^ 2 * smoothTotal q / hetero q ^ 3

noncomputable def detAlloc (q : QParams) : Alloc q.B where
  Δ j := q.Δ * q.L j / smoothTotal q
  ε j := q.ε * q.L j / smoothTotal q
  C _ := 0

noncomputable def noiseAlloc (q : QParams) : Alloc q.B where
  Δ j := if active q j then q.Δ / 2 * wt q j / hetero q
    else q.Δ * ratio q * q.L j / (2 * smoothTotal q)
  ε j := if active q j then q.ε * wt q j / hetero q else q.ε * ratio q * q.L j / smoothTotal q
  C j := if active q j then q.σ j ^ 2 else 0

lemma block_valid (qj : BParams) (hA : qj.A = 0) (hB : qj.B = 0) (hL : 0 < qj.L)
    (hC : 0 ≤ qj.C) (hε : 0 < qj.ε) (hreg : 2 ^ 26 * qj.ε ^ 2 ≤ qj.L * qj.Δ) (X : ℝ)
    (hX : qj.L * qj.Δ / qj.ε ^ 2 + qj.L * qj.Δ * qj.C / qj.ε ^ 4 ≤ X)
    (hd : 2 ^ 40 * (1 + X) ^ 4 ≤ (qj.d : ℝ)) : BSpec.valid qj := by
  refine ⟨hL, by rw [hA], by rw [hB], hC, hε, hreg, ?_⟩
  have he : qj.L * qj.Δ * (1 + qj.B + qj.A * qj.Δ / qj.ε ^ 2 + qj.C / qj.ε ^ 2) / qj.ε ^ 2 =
      qj.L * qj.Δ / qj.ε ^ 2 + qj.L * qj.Δ * qj.C / qj.ε ^ 4 := by
    rw [hA, hB]; field_simp; ring
  rw [he]
  have hΔ : 0 ≤ qj.Δ := by
    have : 0 ≤ qj.L * qj.Δ := le_trans (by positivity) hreg
    exact nonneg_of_mul_nonneg_right (by linarith) hL
  have h0 : 0 ≤ 1 + (qj.L * qj.Δ / qj.ε ^ 2 + qj.L * qj.Δ * qj.C / qj.ε ^ 4) := by positivity
  refine le_trans ?_ hd
  gcongr

lemma block_budget (qj : BParams) (hA : qj.A = 0) (hB : qj.B = 0) (N : ℕ) (Y : ℝ)
    (hN : (N : ℝ) ≤ Y)
    (hY : 2 ^ 53 * Y ≤ qj.L * qj.Δ / qj.ε ^ 2 + qj.L * qj.Δ * qj.C / qj.ε ^ 4)
    (hε : 0 < qj.ε) : N ≤ lowerBudget qj := by
  unfold lowerBudget
  apply Nat.le_floor
  have he : qj.L * qj.Δ * (1 + qj.B + qj.A * qj.Δ / qj.ε ^ 2 + qj.C / qj.ε ^ 2) /
      (2 ^ 53 * qj.ε ^ 2) = (qj.L * qj.Δ / qj.ε ^ 2 + qj.L * qj.Δ * qj.C / qj.ε ^ 4) / 2 ^ 53 := by
    rw [hA, hB]; field_simp; ring
  rw [he, le_div_iff₀ (by positivity)]
  linarith

section Valid

variable (q : QParams) (hv : QSpec.valid q)
include hv

lemma smoothTotal_pos : 0 < smoothTotal q := by
  have hB := hv.1
  have hj : (⟨0, hB⟩ : Fin q.B) ∈ Finset.univ := Finset.mem_univ _
  exact Finset.sum_pos (fun j _ => hv.2.1 j) ⟨_, hj⟩

lemma L_le_total (j : Fin q.B) : q.L j ≤ smoothTotal q :=
  Finset.single_le_sum (f := q.L) (fun i _ => (hv.2.1 i).le) (Finset.mem_univ j)

lemma wt_nonneg (j : Fin q.B) : 0 ≤ wt q j :=
  Real.rpow_nonneg (mul_nonneg (hv.2.1 j).le (sq_nonneg _)) _

lemma wt_cube (j : Fin q.B) : wt q j ^ 3 = q.L j * q.σ j ^ 2 := by
  have h0 : 0 ≤ q.L j * q.σ j ^ 2 := mul_nonneg (hv.2.1 j).le (sq_nonneg _)
  unfold wt
  rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
  norm_num

lemma hetero_nonneg : 0 ≤ hetero q := Finset.sum_nonneg (fun j _ => wt_nonneg q hv j)

lemma wt_le_hetero (j : Fin q.B) : wt q j ≤ hetero q :=
  Finset.single_le_sum (f := wt q) (fun i _ => wt_nonneg q hv i) (Finset.mem_univ j)

lemma reg_block (j : Fin q.B) : 2 ^ 57 * q.ε ^ 2 ≤ q.L j * q.Δ := hv.2.2.2.2.1 j

lemma Δ_pos : 0 < q.Δ := by
  have h := reg_block q hv ⟨0, hv.1⟩
  have hε := hv.2.2.2.1
  have hL := hv.2.1 ⟨0, hv.1⟩
  have : 0 < q.L ⟨0, hv.1⟩ * q.Δ := lt_of_lt_of_le (by positivity) h
  exact pos_of_mul_pos_right this hL.le

lemma dim_block (j : Fin q.B) : 2 ^ 40 * (1 + q.B * smoothTotal q * q.Δ / q.ε ^ 2 +
    hetero q ^ 3 * q.Δ / q.ε ^ 4) ^ 4 ≤ (blockSize q.blk j : ℝ) := hv.2.2.2.2.2 j

lemma total_reg : 2 ^ 57 * q.ε ^ 2 ≤ smoothTotal q * q.Δ := by
  have h := reg_block q hv ⟨0, hv.1⟩
  have hle := L_le_total q hv ⟨0, hv.1⟩
  have hΔ := Δ_pos q hv
  nlinarith

lemma dim_mono (j : Fin q.B) (X : ℝ) (hX0 : 0 ≤ X)
    (hX : X ≤ q.B * smoothTotal q * q.Δ / q.ε ^ 2 + hetero q ^ 3 * q.Δ / q.ε ^ 4) :
    2 ^ 40 * (1 + X) ^ 4 ≤ (blockSize q.blk j : ℝ) := by
  refine le_trans ?_ (dim_block q hv j)
  have : 1 + X ≤ 1 + q.B * smoothTotal q * q.Δ / q.ε ^ 2 + hetero q ^ 3 * q.Δ / q.ε ^ 4 := by
    linarith
  gcongr

lemma B_ge_one : (1 : ℝ) ≤ q.B := by exact_mod_cast hv.1

lemma det_valid (hdet : hetero q ^ 3 ≤ smoothTotal q * q.ε ^ 2) (N : ℕ)
    (hN : (N : ℝ) ≤ lowerTarget q) : AllocValid q (detAlloc q) N := by
  have hε := hv.2.2.2.1
  have hT := smoothTotal_pos q hv
  have hΔ := Δ_pos q hv
  have hS := hetero_nonneg q hv
  have hTr := total_reg q hv
  have hB1 := B_ge_one q hv
  have hcore : ∀ j, (blockParams q (detAlloc q) j).L * (blockParams q (detAlloc q) j).Δ /
      (blockParams q (detAlloc q) j).ε ^ 2 + (blockParams q (detAlloc q) j).L *
      (blockParams q (detAlloc q) j).Δ * (blockParams q (detAlloc q) j).C /
      (blockParams q (detAlloc q) j).ε ^ 4 = smoothTotal q * q.Δ / q.ε ^ 2 := by
    intro j
    have hL := (hv.2.1 j).ne'
    simp only [detAlloc]
    field_simp
    ring
  have hval : ∀ j, BSpec.valid (blockParams q (detAlloc q) j) := by
    intro j
    have hL := hv.2.1 j
    refine block_valid _ rfl rfl hL (le_refl _) (by
      show 0 < q.ε * q.L j / smoothTotal q; positivity) ?_ _ (le_of_eq (hcore j))
      (dim_mono q hv j _ (by positivity) ?_)
    · show 2 ^ 26 * (q.ε * q.L j / smoothTotal q) ^ 2 ≤ q.L j * (q.Δ * q.L j / smoothTotal q)
      rw [div_pow, mul_div_assoc', mul_div_assoc', div_le_div_iff₀ (pow_pos hT 2) hT]
      have hZ : 0 ≤ q.ε ^ 2 * q.L j ^ 2 * smoothTotal q := by positivity
      have b2 := mul_le_mul_of_nonneg_left hTr (by positivity : (0 : ℝ) ≤ q.L j ^ 2 * smoothTotal q)
      nlinarith
    · have h1 : smoothTotal q * q.Δ / q.ε ^ 2 ≤ q.B * smoothTotal q * q.Δ / q.ε ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [mul_pos hT hΔ]
      have h2 : 0 ≤ hetero q ^ 3 * q.Δ / q.ε ^ 4 := by positivity
      linarith
  refine ⟨hval, ?_, ?_, ?_, ?_⟩
  · intro j
    refine block_budget _ rfl rfl N (lowerTarget q) hN ?_ (hval j).2.2.2.2.1
    rw [hcore j, lowerTarget_eq]
    have h3 : hetero q ^ 3 * q.Δ / q.ε ^ 4 ≤ smoothTotal q * q.Δ / q.ε ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left hdet (by positivity : (0 : ℝ) ≤ q.Δ * q.ε ^ 2)
      nlinarith
    have : (2 : ℝ) ^ 53 * ((smoothTotal q * q.Δ / q.ε ^ 2 + hetero q ^ 3 * q.Δ / q.ε ^ 4) /
        2 ^ 57) = (smoothTotal q * q.Δ / q.ε ^ 2 + hetero q ^ 3 * q.Δ / q.ε ^ 4) / 16 := by
      ring
    rw [this]
    have h4 : 0 ≤ hetero q ^ 3 * q.Δ / q.ε ^ 4 := by positivity
    linarith
  · intro j
    show (0 : ℝ) ≤ q.σ j ^ 2
    positivity
  · show ∑ j, q.Δ * q.L j / smoothTotal q ≤ q.Δ
    rw [← Finset.sum_div, ← Finset.mul_sum]
    rw [show ∑ j, q.L j = smoothTotal q from rfl, mul_div_assoc, div_self hT.ne', mul_one]
  · show q.ε ≤ 2 * ∑ j, q.ε * q.L j / smoothTotal q
    rw [← Finset.sum_div, ← Finset.mul_sum]
    rw [show ∑ j, q.L j = smoothTotal q from rfl, mul_div_assoc, div_self hT.ne', mul_one]
    linarith

lemma noise_valid (hnoise : smoothTotal q * q.ε ^ 2 < hetero q ^ 3) (N : ℕ)
    (hN : (N : ℝ) ≤ lowerTarget q) : AllocValid q (noiseAlloc q) N := by
  have hε := hv.2.2.2.1
  have hT := smoothTotal_pos q hv
  have hΔ := Δ_pos q hv
  have hS0 := hetero_nonneg q hv
  have hTr := total_reg q hv
  have hB1 := B_ge_one q hv
  have hS : 0 < hetero q := by
    by_contra h
    push Not at h
    have : hetero q = 0 := le_antisymm h hS0
    rw [this] at hnoise
    have : 0 < smoothTotal q * q.ε ^ 2 := by positivity
    norm_num at hnoise
    linarith
  have hρ0 : 0 < ratio q := by unfold ratio; positivity
  have hρ1 : ratio q ≤ 1 := by
    unfold ratio
    rw [div_le_one (by positivity)]
    linarith
  have hY : ∀ j, hetero q ^ 3 * q.Δ / (2 * q.ε ^ 4) ≤
      (blockParams q (noiseAlloc q) j).L * (blockParams q (noiseAlloc q) j).Δ /
        (blockParams q (noiseAlloc q) j).ε ^ 2 + (blockParams q (noiseAlloc q) j).L *
        (blockParams q (noiseAlloc q) j).Δ * (blockParams q (noiseAlloc q) j).C /
        (blockParams q (noiseAlloc q) j).ε ^ 4 ∧
      (blockParams q (noiseAlloc q) j).L * (blockParams q (noiseAlloc q) j).Δ /
        (blockParams q (noiseAlloc q) j).ε ^ 2 + (blockParams q (noiseAlloc q) j).L *
        (blockParams q (noiseAlloc q) j).Δ * (blockParams q (noiseAlloc q) j).C /
        (blockParams q (noiseAlloc q) j).ε ^ 4 ≤
          q.B * smoothTotal q * q.Δ / q.ε ^ 2 + hetero q ^ 3 * q.Δ / q.ε ^ 4 := by
    intro j
    have hL := hv.2.1 j
    have hc := wt_cube q hv j
    simp only [noiseAlloc]
    by_cases ha : active q j
    · simp only [ha, ↓reduceIte]
      have hw : 0 < wt q j := by
        have h := ha
        unfold active at h
        by_contra hw
        push Not at hw
        have : wt q j = 0 := le_antisymm hw (wt_nonneg q hv j)
        rw [this, mul_zero] at h
        linarith
      have hσ : q.L j * q.σ j ^ 2 = wt q j ^ 3 := hc.symm
      have he2 : q.L j * (q.Δ / 2 * wt q j / hetero q) * q.σ j ^ 2 /
          (q.ε * wt q j / hetero q) ^ 4 = hetero q ^ 3 * q.Δ / (2 * q.ε ^ 4) := by
        rw [show q.L j * (q.Δ / 2 * wt q j / hetero q) * q.σ j ^ 2 =
          (q.L j * q.σ j ^ 2) * (q.Δ / 2 * wt q j / hetero q) by ring, hσ]
        field_simp
      have he1 : q.L j * (q.Δ / 2 * wt q j / hetero q) / (q.ε * wt q j / hetero q) ^ 2 =
          q.L j * q.Δ * hetero q / (2 * q.ε ^ 2 * wt q j) := by
        field_simp
      have hact : hetero q ≤ 2 * q.B * wt q j := ha
      have h1le : q.L j * q.Δ * hetero q / (2 * q.ε ^ 2 * wt q j) ≤
          q.B * smoothTotal q * q.Δ / q.ε ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hLT := L_le_total q hv j
        have := mul_le_mul_of_nonneg_left hact (by positivity : (0 : ℝ) ≤ q.L j * q.Δ * q.ε ^ 2)
        have h5 : q.L j * q.Δ * q.ε ^ 2 * (2 * q.B * wt q j) ≤
            smoothTotal q * q.Δ * q.ε ^ 2 * (2 * q.B * wt q j) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have := mul_le_mul_of_nonneg_right hLT (by positivity : (0 : ℝ) ≤ q.Δ * q.ε ^ 2)
          nlinarith
        nlinarith
      rw [he1, he2]
      have h0 : 0 ≤ q.L j * q.Δ * hetero q / (2 * q.ε ^ 2 * wt q j) := by positivity
      have h6 : hetero q ^ 3 * q.Δ / (2 * q.ε ^ 4) ≤ hetero q ^ 3 * q.Δ / q.ε ^ 4 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith [pow_pos hε 4]
      constructor <;> linarith
    · simp only [ha, ↓reduceIte, mul_zero, zero_div, add_zero]
      have he : q.L j * (q.Δ * ratio q * q.L j / (2 * smoothTotal q)) /
          (q.ε * ratio q * q.L j / smoothTotal q) ^ 2 = hetero q ^ 3 * q.Δ / (2 * q.ε ^ 4) := by
        unfold ratio
        field_simp
      rw [he]
      have h6 : hetero q ^ 3 * q.Δ / (2 * q.ε ^ 4) ≤ hetero q ^ 3 * q.Δ / q.ε ^ 4 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith [pow_pos hε 4]
      have h7 : 0 ≤ q.B * smoothTotal q * q.Δ / q.ε ^ 2 := by positivity
      constructor <;> linarith
  have hreg : ∀ j, 2 ^ 26 * (blockParams q (noiseAlloc q) j).ε ^ 2 ≤
      (blockParams q (noiseAlloc q) j).L * (blockParams q (noiseAlloc q) j).Δ := by
    intro j
    have hL := hv.2.1 j
    have hr := reg_block q hv j
    simp only [noiseAlloc]
    by_cases ha : active q j
    · simp only [ha, ↓reduceIte]
      have hw := wt_nonneg q hv j
      have hwS := wt_le_hetero q hv j
      rw [div_pow, mul_div_assoc', mul_div_assoc', div_le_div_iff₀ (pow_pos hS 2) hS]
      have a1 := mul_le_mul_of_nonneg_left hwS
        (mul_nonneg (mul_nonneg (sq_nonneg q.ε) hw) hS0 : (0 : ℝ) ≤ q.ε ^ 2 * wt q j * hetero q)
      have a2 := mul_le_mul_of_nonneg_right hr
        (mul_nonneg hw (sq_nonneg (hetero q)) : (0 : ℝ) ≤ wt q j * hetero q ^ 2)
      have hA : 0 ≤ q.ε ^ 2 * wt q j * hetero q ^ 2 :=
        mul_nonneg (mul_nonneg (sq_nonneg q.ε) hw) (sq_nonneg _)
      nlinarith
    · simp only [ha, ↓reduceIte]
      rw [div_pow, mul_div_assoc', mul_div_assoc',
        div_le_div_iff₀ (pow_pos hT 2) (by positivity : (0 : ℝ) < 2 * smoothTotal q)]
      have b1 : ratio q ^ 2 ≤ ratio q := by nlinarith
      have b1' := mul_le_mul_of_nonneg_left b1
        (by positivity : (0 : ℝ) ≤ q.ε ^ 2 * q.L j ^ 2 * smoothTotal q)
      have b2 := mul_le_mul_of_nonneg_left hTr
        (by positivity : (0 : ℝ) ≤ ratio q * q.L j ^ 2 * smoothTotal q)
      have hZ : 0 ≤ ratio q * q.ε ^ 2 * q.L j ^ 2 * smoothTotal q := by positivity
      nlinarith
  have hεj : ∀ j, 0 < (blockParams q (noiseAlloc q) j).ε := by
    intro j
    have hL := hv.2.1 j
    simp only [noiseAlloc]
    by_cases ha : active q j
    · simp only [ha, ↓reduceIte]
      have hw : 0 < wt q j := by
        have h : hetero q ≤ 2 * q.B * wt q j := ha
        by_contra hw
        push Not at hw
        have : wt q j = 0 := le_antisymm hw (wt_nonneg q hv j)
        rw [this, mul_zero] at h
        linarith
      positivity
    · simp only [ha, ↓reduceIte]
      positivity
  have hCj : ∀ j, 0 ≤ (blockParams q (noiseAlloc q) j).C := by
    intro j
    simp only [noiseAlloc]
    split_ifs <;> positivity
  have hval : ∀ j, BSpec.valid (blockParams q (noiseAlloc q) j) := by
    intro j
    exact block_valid _ rfl rfl (hv.2.1 j) (hCj j) (hεj j) (hreg j) _ (hY j).2
      (dim_mono q hv j _ (by positivity) le_rfl)
  refine ⟨hval, ?_, ?_, ?_, ?_⟩
  · intro j
    refine block_budget _ rfl rfl N (hetero q ^ 3 * q.Δ / (2 ^ 54 * q.ε ^ 4)) ?_ ?_ (hεj j)
    · refine hN.trans ?_
      rw [lowerTarget_eq, div_le_div_iff₀ (by positivity) (by positivity)]
      have h3 : smoothTotal q * q.Δ / q.ε ^ 2 ≤ hetero q ^ 3 * q.Δ / q.ε ^ 4 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have := mul_le_mul_of_nonneg_left hnoise.le (by positivity : (0 : ℝ) ≤ q.Δ * q.ε ^ 2)
        nlinarith
      have h4 : hetero q ^ 3 * q.Δ / q.ε ^ 4 * (2 ^ 54 * q.ε ^ 4) = 2 ^ 54 * (hetero q ^ 3 * q.Δ) := by
        field_simp
      nlinarith [pow_pos hε 4]
    · have h := (hY j).1
      have : (2 : ℝ) ^ 53 * (hetero q ^ 3 * q.Δ / (2 ^ 54 * q.ε ^ 4)) =
          hetero q ^ 3 * q.Δ / (2 * q.ε ^ 4) := by
        field_simp
      rw [this]
      exact h
  · intro j
    simp only [noiseAlloc]
    split_ifs
    · exact le_refl _
    · positivity
  · simp only [noiseAlloc]
    have hsplit : ∀ j, (if active q j then q.Δ / 2 * wt q j / hetero q
        else q.Δ * ratio q * q.L j / (2 * smoothTotal q)) ≤
        q.Δ / 2 * wt q j / hetero q + q.Δ / 2 * q.L j / smoothTotal q := by
      intro j
      have hw := wt_nonneg q hv j
      have hL := hv.2.1 j
      split_ifs
      · have : 0 ≤ q.Δ / 2 * q.L j / smoothTotal q := by positivity
        linarith
      · have : 0 ≤ q.Δ / 2 * wt q j / hetero q := by positivity
        have h2 : q.Δ * ratio q * q.L j / (2 * smoothTotal q) ≤ q.Δ / 2 * q.L j / smoothTotal q := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have := mul_le_mul_of_nonneg_left hρ1 (by positivity : (0 : ℝ) ≤ q.Δ * q.L j)
          nlinarith [mul_pos hT hT]
        linarith
    refine (Finset.sum_le_sum (fun j _ => hsplit j)).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, ← Finset.mul_sum,
      ← Finset.mul_sum]
    rw [show ∑ j, wt q j = hetero q from rfl, show ∑ j, q.L j = smoothTotal q from rfl]
    field_simp
    ring
  · simp only [noiseAlloc]
    have hinact : ∑ j, (if active q j then (0 : ℝ) else wt q j) ≤ hetero q / 2 := by
      have hb : ∀ j, (if active q j then (0 : ℝ) else wt q j) ≤ hetero q / (2 * q.B) := by
        intro j
        split_ifs with ha
        · positivity
        · unfold active at ha
          push Not at ha
          rw [le_div_iff₀ (by positivity)]
          linarith
      refine (Finset.sum_le_sum (fun j _ => hb j)).trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have hact : hetero q / 2 ≤ ∑ j, (if active q j then wt q j else 0) := by
      have hsum : ∑ j, ((if active q j then wt q j else 0) +
          (if active q j then (0 : ℝ) else wt q j)) = hetero q := by
        refine Finset.sum_congr rfl (fun j _ => ?_) |>.trans rfl
        split_ifs <;> simp
      rw [Finset.sum_add_distrib] at hsum
      linarith
    have hterm : ∀ j, q.ε / hetero q * (if active q j then wt q j else 0) ≤
        (if active q j then q.ε * wt q j / hetero q else q.ε * ratio q * q.L j / smoothTotal q) := by
      intro j
      have hL := hv.2.1 j
      split_ifs
      · rw [div_mul_eq_mul_div]
      · rw [mul_zero]; positivity
    have h1 := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hterm j)
    rw [← Finset.mul_sum] at h1
    have h2 : q.ε / hetero q * (hetero q / 2) ≤ q.ε / hetero q * ∑ j,
        (if active q j then wt q j else 0) :=
      mul_le_mul_of_nonneg_left hact (by positivity)
    have h3 : q.ε / hetero q * (hetero q / 2) = q.ε / 2 := by field_simp
    linarith

end Valid

lemma exists_alloc (q : QParams) (hv : QSpec.valid q) (N : ℕ)
    (hN : N ≤ ⌊((∑ j, q.L j) * q.Δ / q.ε ^ 2 +
      (∑ j, (q.L j * q.σ j ^ 2) ^ ((1 : ℝ) / 3)) ^ 3 * q.Δ / q.ε ^ 4) / 2 ^ 57⌋₊) :
    ∃ a : Alloc q.B, AllocValid q a N := by
  have hN' : (N : ℝ) ≤ lowerTarget q := by
    have h0 : 0 ≤ lowerTarget q := by
      have hT := smoothTotal_pos q hv
      have hΔ := Δ_pos q hv
      have hS := hetero_nonneg q hv
      have hε := hv.2.2.2.1
      rw [lowerTarget_eq]
      positivity
    exact (Nat.le_floor_iff h0).mp hN
  rcases le_or_gt (hetero q ^ 3) (smoothTotal q * q.ε ^ 2) with h | h
  · exact ⟨_, det_valid q hv h N hN'⟩
  · exact ⟨_, noise_valid q hv h N hN'⟩

end LongTails.Proofs.BlockLowerParameters
