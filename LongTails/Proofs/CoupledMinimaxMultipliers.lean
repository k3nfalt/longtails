import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CoupledMinimaxMultipliers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma directional_bound {g s n d : E} {G Z e : ℝ}
    (hG : ‖g‖ ≤ G) (hZ : ‖d‖ ≤ Z) (he : ‖g - s - n‖ ≤ e)
    (hn : ⟪n, d⟫ ≤ 0) : -⟪s, d⟫ ≤ Z * (G + e) := by
  have hG0 : 0 ≤ G := (norm_nonneg g).trans hG
  have he0 : 0 ≤ e := (norm_nonneg _).trans he
  have h1 := real_inner_le_norm (g - s - n) d
  have h2 := real_inner_le_norm (-g) d
  have h3 : ‖g - s - n‖ * ‖d‖ ≤ e * Z :=
    mul_le_mul he hZ (norm_nonneg _) he0
  have h4 : ‖g‖ * ‖d‖ ≤ G * Z :=
    mul_le_mul hG hZ (norm_nonneg _) hG0
  simp only [inner_sub_left, inner_neg_left, norm_neg] at h1 h2
  nlinarith

lemma weighted_directional_bound {ι : Type*} [Fintype ι]
    {a : ι → E} {w : ι → ℝ} {g n d : E} {δ G Z e : ℝ}
    (hw : ∀ i, 0 ≤ w i)
    (ha : ∀ i, 0 < w i → ⟪a i, d⟫ ≤ -δ)
    (hG : ‖g‖ ≤ G) (hZ : ‖d‖ ≤ Z)
    (he : ‖g - (∑ i, w i • a i) - n‖ ≤ e)
    (hn : ⟪n, d⟫ ≤ 0) : δ * (∑ i, w i) ≤ Z * (G + e) := by
  have hi : ∀ i, w i * ⟪a i, d⟫ ≤ -δ * w i := by
    intro i
    by_cases hz : w i = 0
    · simp [hz]
    · have hp : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hz)
      have hh := mul_le_mul_of_nonneg_left (ha i hp) (hw i)
      nlinarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  have hb := directional_bound hG hZ he hn
  simp only [sum_inner, real_inner_smul_left] at hb
  rw [← Finset.mul_sum] at hs
  nlinarith

lemma cap_multiplier {ι : Type*} [Fintype ι] {c w : ι → ℝ}
    {β e M δ Z G ey : ℝ}
    (he : 0 ≤ e)
    (hcap : Z * (G + ey) < δ * M)
    (hactive : 0 < β → ∑ i, w i = M)
    (hres : ∀ i, 0 < w i → |c i - β| ≤ e)
    (hcq : (∀ i, 0 < w i → 0 < c i) → δ * (∑ i, w i) ≤ Z * (G + ey)) :
    β ≤ e := by
  by_contra h
  have hb : e < β := lt_of_not_ge h
  have hs : ∀ i, 0 < w i → 0 < c i := by
    intro i hi
    have hh := (abs_le.mp (hres i hi)).1
    linarith
  have hh := hcq hs
  rw [hactive (lt_of_le_of_lt he hb)] at hh
  linarith

lemma cap_accuracy {ι : Type*} [Fintype ι] {c w : ι → ℝ} {β e M : ℝ}
    (hw : ∀ i, 0 ≤ w i) (he : 0 ≤ e) (hβ : 0 ≤ β) (hbe : β ≤ e)
    (hsum : ∑ i, w i ≤ M)
    (hupper : ∀ i, c i ≤ β + e)
    (hsupport : ∀ i, 0 < w i → |c i - β| ≤ e) :
    (∀ i, max (c i) 0 ≤ 2 * e) ∧ ∑ i, |w i * c i| ≤ 2 * M * e := by
  constructor
  · intro i
    exact max_le (by linarith [hupper i]) (by positivity)
  · have hi : ∀ i, |w i * c i| ≤ w i * (2 * e) := by
      intro i
      by_cases hz : w i = 0
      · simp [hz]
      · have hp : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hz)
        have hc := abs_le.mp (hsupport i hp)
        have ha : |c i| ≤ 2 * e := abs_le.mpr ⟨by linarith [hc.1], by linarith [hc.2]⟩
        rw [abs_mul, abs_of_nonneg (hw i)]
        exact mul_le_mul_of_nonneg_left ha (hw i)
    calc
      ∑ i, |w i * c i| ≤ ∑ i, w i * (2 * e) := Finset.sum_le_sum fun i _ => hi i
      _ = (∑ i, w i) * (2 * e) := (Finset.sum_mul ..).symm
      _ ≤ M * (2 * e) := mul_le_mul_of_nonneg_right hsum (by positivity)
      _ = 2 * M * e := by ring

lemma simplex_normal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {w n : ι → ℝ} {M : ℝ} (hM : 0 < M)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i ≤ M)
    (hn : ∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → (∑ i, v i) ≤ M →
      ∑ i, n i * (v i - w i) ≤ 0) :
    ∃ β : ℝ, 0 ≤ β ∧ (∀ i, n i ≤ β) ∧
      (∀ i, 0 < w i → n i = β) ∧ (0 < β → ∑ i, w i = M) := by
  let S := ∑ i, n i * w i
  have hS : 0 ≤ S := by
    have hh := hn (fun _ => 0) (by simp) (by simpa using hM.le)
    simpa [S] using hh
  have hi : ∀ i, n i * M ≤ S := by
    intro i
    have hh := hn (fun j => if j = i then M else 0)
      (fun j => by split_ifs <;> positivity) (by simp)
    simp only [mul_sub, Finset.sum_sub_distrib] at hh
    have heq : (∑ j, n j * (if j = i then M else 0)) = n i * M := by simp
    rw [heq] at hh
    dsimp [S]
    linarith
  let β := S / M
  have hb : 0 ≤ β := div_nonneg hS hM.le
  have hbm : β * M = S := div_mul_cancel₀ _ hM.ne'
  have hni : ∀ i, n i ≤ β := fun i => (le_div_iff₀ hM).mpr (hi i)
  have hterm : ∀ i, 0 ≤ w i * (β - n i) := fun i =>
    mul_nonneg (hw i) (sub_nonneg.mpr (hni i))
  have htotal : (∑ i, w i * (β - n i)) = β * (∑ i, w i) - S := by
    dsimp [S]
    simp only [mul_sub, Finset.sum_sub_distrib]
    congr 1
    · rw [← Finset.sum_mul, mul_comm]
    · apply Finset.sum_congr rfl
      intro i _
      ring
  have hz : (∑ i, w i * (β - n i)) ≤ 0 := by
    rw [htotal]
    nlinarith [mul_le_mul_of_nonneg_left hsum hb]
  refine ⟨β, hb, hni, ?_, ?_⟩
  · intro i hwi
    have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hterm j)
      (Finset.mem_univ i)
    have hzero : w i * (β - n i) ≤ 0 := hh.trans hz
    nlinarith [hni i]
  · intro hbp
    have hh := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hterm i)
    rw [htotal] at hh
    nlinarith

lemma transfer_from_direction {ι : Type*} [Fintype ι]
    {c w : ι → ℝ} {a : ι → E} {g n d : E} {β e M δ Z G ey : ℝ}
    (hw : ∀ i, 0 ≤ w i) (he : 0 ≤ e) (hβ : 0 ≤ β)
    (hcap : Z * (G + ey) < δ * M)
    (hsum : ∑ i, w i ≤ M) (hactive : 0 < β → ∑ i, w i = M)
    (hupper : ∀ i, c i ≤ β + e)
    (hsupport : ∀ i, 0 < w i → |c i - β| ≤ e)
    (hG : ‖g‖ ≤ G) (hZ : ‖d‖ ≤ Z)
    (hstationary : ‖g - (∑ i, w i • a i) - n‖ ≤ ey)
    (hn : ⟪n, d⟫ ≤ 0) (hd : ∀ i, 0 < c i → ⟪a i, d⟫ ≤ -δ) :
    (∀ i, max (c i) 0 ≤ 2 * e) ∧ ∑ i, |w i * c i| ≤ 2 * M * e := by
  have hb : β ≤ e := cap_multiplier he hcap hactive hsupport fun hc =>
    weighted_directional_bound hw (fun i hi => hd i (hc i hi)) hG hZ hstationary hn
  exact cap_accuracy hw he hβ hb hsum hupper hsupport

lemma transfer {ι : Type*} [Fintype ι] [DecidableEq ι]
    {c w v : ι → ℝ} {a : ι → E} {g n d : E} {e M δ Z G ey : ℝ}
    (hM : 0 < M) (hw : ∀ i, 0 ≤ w i) (he : 0 ≤ e)
    (hcap : Z * (G + ey) < δ * M) (hsum : ∑ i, w i ≤ M)
    (hv : ∀ u : ι → ℝ, (∀ i, 0 ≤ u i) → (∑ i, u i) ≤ M →
      ∑ i, v i * (u i - w i) ≤ 0)
    (hres : ∀ i, |v i - c i| ≤ e)
    (hG : ‖g‖ ≤ G) (hZ : ‖d‖ ≤ Z)
    (hstationary : ‖g - (∑ i, w i • a i) - n‖ ≤ ey)
    (hn : ⟪n, d⟫ ≤ 0) (hd : ∀ i, 0 < c i → ⟪a i, d⟫ ≤ -δ) :
    (∀ i, max (c i) 0 ≤ 2 * e) ∧ ∑ i, |w i * c i| ≤ 2 * M * e := by
  obtain ⟨β, hb, hvb, hsupport, hactive⟩ := simplex_normal hM hw hsum hv
  apply transfer_from_direction hw he hb hcap hsum hactive
    (fun i => ?_) (fun i hi => ?_) hG hZ hstationary hn hd
  · have hh := (abs_le.mp (hres i)).1
    linarith [hvb i]
  · have hh := hres i
    rw [hsupport i hi] at hh
    rwa [abs_sub_comm]

end LongTails.Proofs.CoupledMinimaxMultipliers
