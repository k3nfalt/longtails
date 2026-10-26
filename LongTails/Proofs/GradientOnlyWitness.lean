import LongTails.Proofs.GradientOnlyGeometry
import LongTails.Proofs.QuarticWitnessValues

namespace LongTails.Proofs.GradientOnlyWitness

open scoped RealInnerProductSpace
open LongTails.Algorithms.GradientOnlyGuarded LongTails.Algorithms.GuardedMetricAcceleration
open LongTails.Proofs.GradientOnlyAgd LongTails.Proofs.GradientOnlyTests

section Choose

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma fold_spec (c : E) (pts : Fin 6 → E) (s : Fin 6 → ℝ) (l : List (Fin 6)) (b₀ : E) (v₀ : ℝ)
    (h₀ : (b₀ = c ∧ v₀ = 0) ∨ ∃ i, b₀ = pts i ∧ v₀ = s i) :
    let r := l.foldl (fun (best : E × ℝ) i => if s i < best.2 then (pts i, s i) else best) (b₀, v₀)
    r.2 ≤ v₀ ∧ (∀ i ∈ l, r.2 ≤ s i) ∧ ((r.1 = c ∧ r.2 = 0) ∨ ∃ i, r.1 = pts i ∧ r.2 = s i) := by
  induction l generalizing b₀ v₀ with
  | nil => simpa using h₀
  | cons i l ih =>
    simp only [List.foldl_cons]
    split_ifs with h
    · obtain ⟨h₁, h₂, h₃⟩ := ih (pts i) (s i) (Or.inr ⟨i, rfl, rfl⟩)
      refine ⟨by linarith, ?_, h₃⟩
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact h₁
      · exact h₂ j hj
    · obtain ⟨h₁, h₂, h₃⟩ := ih b₀ v₀ h₀
      refine ⟨h₁, ?_, h₃⟩
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · push Not at h
        linarith
      · exact h₂ j hj

lemma choose_spec (t : Tuning) (c : E) (pts : Fin 6 → E) (rC : Fin 6 × (Fin t.m × Fin 2) → E) :
    ∃ v : ℝ, v ≤ 0 ∧ (∀ i, v ≤ surrogateOf (fun j => rC (i, j)) c (pts i)) ∧
      ((choose t c pts rC = c ∧ v = 0) ∨
        ∃ i, choose t c pts rC = pts i ∧ v = surrogateOf (fun j => rC (i, j)) c (pts i)) := by
  have h := fold_spec c pts (fun i => surrogateOf (fun j => rC (i, j)) c (pts i))
    (List.finRange 6) c 0 (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨h₁, h₂, h₃⟩ := h
  exact ⟨_, h₁, fun i => h₂ i (List.mem_finRange i), h₃⟩

lemma choose_progress {f : E → ℝ} (t : Tuning) (c : E) (pts : Fin 6 → E)
    (rC : Fin 6 × (Fin t.m × Fin 2) → E) {e q : ℝ} (heq : e < q)
    (herr : ∀ i, |surrogateOf (fun j => rC (i, j)) c (pts i) - (f (pts i) - f c)| ≤ e)
    (hgood : ∃ i, f (pts i) ≤ f c - q) :
    f (choose t c pts rC) ≤ f c - q + 2 * e := by
  obtain ⟨v, hv0, hvall, hv⟩ := choose_spec t c pts rC
  obtain ⟨i, hi⟩ := hgood
  have hei := abs_le.mp (herr i)
  rcases hv with ⟨_, hv⟩ | ⟨i', hb, hv⟩
  · have := hvall i
    linarith
  · rw [hb]
    have hei' := abs_le.mp (herr i')
    have := hvall i
    linarith

end Choose

section Candidates

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma witness_candidates {f : E → ℝ} (hf : ContDiff ℝ 3 f) {L₃ : ℝ} (hL₃ : 0 ≤ L₃)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L₃ * ‖x - y‖)
    {α q η R θ Fc : ℝ} (hα : 0 ≤ α) (hq : 0 ≤ q) (hθ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (x prev u v : E) (hvx : v = x + θ • (x - prev))
    (hx : f x ≤ Fc) (hp : f prev ≤ Fc) (hu : f u ≤ Fc) (hne : u ≠ v)
    (hdef : f u - f v - ⟪gradient f v, u - v⟫ ≤ -α * ‖u - v‖ ^ 2 / 2)
    (hshort : 3 * L₃ * ‖u - v‖ ^ 2 ≤ α / 4) (hη : L₃ * η ^ 2 ≤ α / 16)
    (hstep : ‖x - prev‖ ≤ 2 * R) (hR : 0 ≤ R)
    (hbudget : 14 * q + 384 * L₃ * R ^ 4 ≤ α * η ^ 2 / 4) :
    ∃ i : Fin 6, f (![(1 / 2 : ℝ) • (x + prev), (-2 : ℝ) • x + (3 : ℝ) • prev,
      escapePoints η u v 0, escapePoints η u v 1, escapePoints η u v 2,
      escapePoints η u v 3] i) ≤ Fc - q := by
  by_cases h₀ : f ((1 / 2 : ℝ) • (x + prev)) ≤ Fc - q
  · exact ⟨0, by simpa using h₀⟩
  by_cases h₁ : f ((-2 : ℝ) • x + (3 : ℝ) • prev) ≤ Fc - q
  · exact ⟨1, by simpa using h₁⟩
  push Not at h₀ h₁
  have hint := QuarticWitnessValues.interpolation_on_line hf hL₃ hq hθ hθ₁ hT x prev hx hp
    h₀.le h₁.le
  rw [← hvx] at hint
  have hd4 : ‖x - prev‖ ^ 4 ≤ (2 * R) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hstep 4
  have hfv : f v ≤ Fc + 13 * q + 384 * L₃ * R ^ 4 := by
    have := mul_le_mul_of_nonneg_left hd4 (by positivity : (0 : ℝ) ≤ 24 * L₃)
    nlinarith
  have hesc := QuarticWitnessGeometry.escape_values_bound hf hL₃ hα hT u v hne hdef hshort hη
  have hmax : max (f u) (f v) ≤ Fc + 13 * q + 384 * L₃ * R ^ 4 :=
    max_le (by nlinarith [mul_nonneg hL₃ (pow_nonneg hR 4)]) hfv
  have hmin : min (min (f (escapePoints η u v 0)) (f (escapePoints η u v 1)))
      (min (f (escapePoints η u v 2)) (f (escapePoints η u v 3))) ≤ Fc - q := by linarith
  rcases min_le_iff.mp hmin with h | h
  · rcases min_le_iff.mp h with h | h
    · exact ⟨2, by simpa using h⟩
    · exact ⟨3, by simpa using h⟩
  · rcases min_le_iff.mp h with h | h
    · exact ⟨4, by simpa using h⟩
    · exact ⟨5, by simpa using h⟩

end Candidates

end LongTails.Proofs.GradientOnlyWitness
