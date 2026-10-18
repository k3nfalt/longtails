import Mathlib.Analysis.InnerProductSpace.Basic
import LongTails.Algorithms.CompositeGuardedSearch
import LongTails.Proofs.CurvatureMetric
import Mathlib.Tactic

namespace LongTails.Proofs.CompositeGuardedSearch

open scoped RealInnerProductSpace
open LongTails.Algorithms.CompositeGuardedSearch
open LongTails.Proofs.CurvatureMetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma residual_certificate {h ψ : E → ℝ} {y z u gy gz r : E} {e : ℝ}
    (hy : h y + ⟪gy, u - y⟫ ≤ h u)
    (hz : h z + ⟪gz, y - z⟫ ≤ h y)
    (hp : ψ z ≤ ψ u + ⟪gy - r, u - z⟫)
    (he : ⟪r, y - z⟫ = e)
    (hc : ⟪gz - gy, z - y⟫ ≤ e / 2) :
    h z + ψ z - (h u + ψ u) ≤ ⟪r, y - u⟫ - e / 2 := by
  simp only [inner_sub_left, inner_sub_right] at hy hz hp he hc ⊢
  linarith

lemma segment_residual {r x v : E} {s ζ : ℝ}
    (hs : 0 ≤ s)
    (hq : -ζ ≤ ⟪r, v - x⟫) (hq0 : ⟪r, v - x⟫ ≤ 0) :
    ⟪r, x + s • (v - x) - v⟫ ≤ ζ := by
  have he : ⟪r, x + s • (v - x) - v⟫ = (s - 1) * ⟪r, v - x⟫ := by
    simp only [inner_sub_right, inner_add_right, inner_smul_right]
    ring
  rw [he]
  nlinarith

lemma certified_segment_descent {h ψ : E → ℝ} {x v z gy gz r : E}
    {s e : ℝ} (hs : 0 ≤ s)
    (hy : h (x + s • (v - x)) + ⟪gy, x - (x + s • (v - x))⟫ ≤ h x)
    (hz : h z + ⟪gz, (x + s • (v - x)) - z⟫ ≤ h (x + s • (v - x)))
    (hp : ψ z ≤ ψ x + ⟪gy - r, x - z⟫)
    (he : ⟪r, (x + s • (v - x)) - z⟫ = e)
    (hc : ⟪gz - gy, z - (x + s • (v - x))⟫ ≤ e / 2)
    (hq : ⟪r, v - x⟫ ≤ 0) :
    h z + ψ z + e / 2 ≤ h x + ψ x := by
  have hr := residual_certificate hy hz hp he hc
  have hi : ⟪r, x + s • (v - x) - x⟫ = s * ⟪r, v - x⟫ := by
    simp only [add_sub_cancel_left, inner_smul_right]
  rw [hi] at hr
  have hn := mul_nonpos_of_nonneg_of_nonpos hs hq
  linarith

lemma bracket_accuracy {Q : ℝ → ℝ} {good : ℝ → Prop} {l u δ L ζ : ℝ}
    (hl : good l) (hu : 0 ≤ Q u ∨ ¬good u)
    (hsafe : good l → u - l ≤ δ → good u)
    (hwidth : u - l ≤ δ) (hmod : |Q u - Q l| ≤ L * (u - l))
    (hsmall : L * (u - l) ≤ ζ) : -ζ ≤ Q l := by
  have hgu := hsafe hl hwidth
  have hqu : 0 ≤ Q u := hu.resolve_right (not_not_intro hgu)
  have hdiff := (abs_le.mp hmod).2
  linarith

lemma advance_width (b : Bracket) (certified : Bool) (residual : ℝ) :
    (advance b certified residual).upper - (advance b certified residual).lower =
      (b.upper - b.lower) / 2 := by
  simp only [advance]
  split <;> simp only [Bracket.midpoint] <;> ring

lemma runBracket_width (evaluate : ℝ → Bool × ℝ) (n : ℕ) (b : Bracket) :
    (runBracket evaluate n b).upper - (runBracket evaluate n b).lower =
      (b.upper - b.lower) / 2 ^ n := by
  induction n generalizing b with
  | zero => simp [runBracket]
  | succ n ih =>
    simp only [runBracket]
    rw [ih, advance_width, pow_succ]
    ring

lemma advance_interval (b : Bracket) (certified : Bool) (residual : ℝ)
    (h : b.lower ≤ b.upper) :
    b.lower ≤ (advance b certified residual).lower ∧
      (advance b certified residual).lower ≤ (advance b certified residual).upper ∧
      (advance b certified residual).upper ≤ b.upper := by
  simp only [advance]
  split <;> simp only [Bracket.midpoint] <;> refine ⟨?_, ?_, ?_⟩ <;> linarith

lemma advance_certificates (evaluate : ℝ → Bool × ℝ) (b : Bracket)
    (hl : (evaluate b.lower).1 = true ∧ (evaluate b.lower).2 ≤ 0)
    (hu : 0 ≤ (evaluate b.upper).2 ∨ (evaluate b.upper).1 ≠ true) :
    let next := advance b (evaluate b.midpoint).1 (evaluate b.midpoint).2
    ((evaluate next.lower).1 = true ∧ (evaluate next.lower).2 ≤ 0) ∧
      (0 ≤ (evaluate next.upper).2 ∨ (evaluate next.upper).1 ≠ true) := by
  dsimp only [advance]
  split
  · exact ⟨by assumption, hu⟩
  · rename_i hn
    refine ⟨hl, ?_⟩
    by_cases hc : (evaluate b.midpoint).1 = true
    · exact Or.inl (le_of_lt (lt_of_not_ge fun hq => hn ⟨hc, hq⟩))
    · exact Or.inr hc

lemma runBracket_certificates (evaluate : ℝ → Bool × ℝ) (n : ℕ) (b : Bracket)
    (hl : (evaluate b.lower).1 = true ∧ (evaluate b.lower).2 ≤ 0)
    (hu : 0 ≤ (evaluate b.upper).2 ∨ (evaluate b.upper).1 ≠ true) :
    ((evaluate (runBracket evaluate n b).lower).1 = true ∧
      (evaluate (runBracket evaluate n b).lower).2 ≤ 0) ∧
      (0 ≤ (evaluate (runBracket evaluate n b).upper).2 ∨
        (evaluate (runBracket evaluate n b).upper).1 ≠ true) := by
  induction n generalizing b with
  | zero => exact ⟨hl, hu⟩
  | succ n ih =>
    have hnext := advance_certificates evaluate b hl hu
    exact ih _ hnext.1 hnext.2

lemma runBracket_interval (evaluate : ℝ → Bool × ℝ) (n : ℕ) (b : Bracket)
    (h : b.lower ≤ b.upper) :
    b.lower ≤ (runBracket evaluate n b).lower ∧
      (runBracket evaluate n b).lower ≤ (runBracket evaluate n b).upper ∧
      (runBracket evaluate n b).upper ≤ b.upper := by
  induction n generalizing b with
  | zero => exact ⟨le_rfl, h, le_rfl⟩
  | succ n ih =>
      have hn := advance_interval b (evaluate b.midpoint).1 (evaluate b.midpoint).2 h
      have ht := ih _ hn.2.1
      exact ⟨hn.1.trans ht.1, ht.2.1, ht.2.2.trans hn.2.2⟩

lemma runBracket_accuracy (evaluate : ℝ → Bool × ℝ) (n : ℕ) {δ L ζ : ℝ}
    (hl : (evaluate 0).1 = true ∧ (evaluate 0).2 ≤ 0)
    (hu : 0 ≤ (evaluate 1).2 ∨ (evaluate 1).1 ≠ true)
    (hsafe : ∀ l u, 0 ≤ l → l ≤ u → u ≤ 1 →
      (evaluate l).1 = true → (evaluate l).2 ≤ 0 → u - l ≤ δ → (evaluate u).1 = true)
    (hmod : ∀ l u, 0 ≤ l → l ≤ u → u ≤ 1 →
      (evaluate l).1 = true → (evaluate l).2 ≤ 0 → u - l ≤ δ →
      |(evaluate u).2 - (evaluate l).2| ≤ L * (u - l))
    (hwidth : (1 : ℝ) / 2 ^ n ≤ δ) (hsmall : L / 2 ^ n ≤ ζ) :
    let b := runBracket evaluate n ⟨0, 1⟩
    (evaluate b.lower).1 = true ∧ -ζ ≤ (evaluate b.lower).2 ∧ (evaluate b.lower).2 ≤ 0 := by
  let b := runBracket evaluate n ⟨0, 1⟩
  have hb := runBracket_interval evaluate n (⟨0, 1⟩ : Bracket) (by norm_num)
  have hc := runBracket_certificates evaluate n (⟨0, 1⟩ : Bracket) hl hu
  have hw : b.upper - b.lower = (1 : ℝ) / 2 ^ n := by
    simpa [b] using runBracket_width evaluate n (⟨0, 1⟩ : Bracket)
  have hn := bracket_accuracy (Q := fun t => (evaluate t).2)
    (good := fun t => (evaluate t).1 = true) hc.1.1 hc.2
    (fun hgood hnear => hsafe b.lower b.upper hb.1 hb.2.1 hb.2.2 hgood hc.1.2 hnear)
    (hw.trans_le hwidth)
    (hmod b.lower b.upper hb.1 hb.2.1 hb.2.2 hc.1.1 hc.1.2 (hw.trans_le hwidth))
    (show L * (b.upper - b.lower) ≤ ζ by rw [hw]; simpa [div_eq_mul_inv] using hsmall)
  exact ⟨hc.1.1, hn, hc.1.2⟩

lemma accelerated_potential (B : E →L[ℝ] E) (hB : IsUnit B)
    (hs : ∀ x y, ⟪x, B y⟫ = ⟪B x, y⟫) (hp : ∀ x, 0 ≤ ⟪x, B x⟫)
    {x v y u r : E} {A a Fx Fz Fu ζ : ℝ}
    (hA : 0 ≤ A) (ha : 0 ≤ a) (ha2 : a ^ 2 ≤ A + a)
    (hcx : Fz - Fx ≤ ⟪r, y - x⟫ - metricNorm B (Ring.inverse B r) ^ 2 / 2)
    (hcu : Fz - Fu ≤ ⟪r, y - u⟫ - metricNorm B (Ring.inverse B r) ^ 2 / 2)
    (hrx : ⟪r, y - x⟫ ≤ 0) (hrv : ⟪r, y - v⟫ ≤ ζ) :
    (A + a) * (Fz - Fu) + metricNorm B (v - a • Ring.inverse B r - u) ^ 2 / 2 ≤
      A * (Fx - Fu) + metricNorm B (v - u) ^ 2 / 2 + a * ζ := by
  have h₁ := mul_le_mul_of_nonneg_left hcx hA
  have h₂ := mul_le_mul_of_nonneg_left hcu ha
  have h₃ := mul_le_mul_of_nonneg_left hrx hA
  have h₄ := mul_le_mul_of_nonneg_left hrv ha
  have hm := metric_momentum_identity B hB hs hp v u r a
  have hsq := mul_le_mul_of_nonneg_right ha2 (sq_nonneg (metricNorm B (Ring.inverse B r)))
  have he : ⟪r, y - u⟫ = ⟪r, y - v⟫ + ⟪r, v - u⟫ := by
    simp only [inner_sub_right]
    ring
  rw [he] at h₂
  nlinarith only [h₁, h₂, h₃, h₄, hm, hsq]

lemma accelerated_telescoping {F V : ℕ → ℝ} {Fu ζ : ℝ}
    (hstep : ∀ k : ℕ,
      ((k : ℝ) + 1) * ((k : ℝ) + 2) / 4 * (F (k + 1) - Fu) + V (k + 1) ≤
        (k : ℝ) * ((k : ℝ) + 1) / 4 * (F k - Fu) + V k + ((k : ℝ) + 1) / 2 * ζ)
    (n : ℕ) :
    (n : ℝ) * ((n : ℝ) + 1) / 4 * (F n - Fu) + V n ≤
      V 0 + (n : ℝ) * ((n : ℝ) + 1) / 4 * ζ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := hstep n
    push_cast
    nlinarith only [h, ih]

lemma accelerated_accuracy {F V : ℕ → ℝ} {Fu ζ R : ℝ} {n : ℕ} (hn : 0 < n)
    (hV : 0 ≤ V n) (hV0 : V 0 ≤ R / 2)
    (henergy : (n : ℝ) * ((n : ℝ) + 1) / 4 * (F n - Fu) + V n ≤
      V 0 + (n : ℝ) * ((n : ℝ) + 1) / 4 * ζ) :
    F n - Fu ≤ 2 * R / ((n : ℝ) * ((n : ℝ) + 1)) + ζ := by
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hd : 0 < (n : ℝ) * ((n : ℝ) + 1) := by positivity
  apply (mul_le_mul_iff_right₀ hd).mp
  have he : (n : ℝ) * ((n : ℝ) + 1) *
      (2 * R / ((n : ℝ) * ((n : ℝ) + 1)) + ζ) =
      2 * R + (n : ℝ) * ((n : ℝ) + 1) * ζ := by field_simp
  rw [he]
  nlinarith only [henergy, hV, hV0]

lemma comparator_momentum_bound {A F Fu Fref V V0 ζ Δ : ℝ}
    (hA : 0 ≤ A) (hF : Fref ≤ F) (hu : Fu - Fref ≤ Δ)
    (henergy : A * (F - Fu) + V ≤ V0 + A * ζ) :
    V ≤ V0 + A * (Δ + ζ) := by
  have hgap : -Δ ≤ F - Fu := by linarith
  have hmul := mul_le_mul_of_nonneg_left hgap hA
  nlinarith only [henergy, hmul]

end LongTails.Proofs.CompositeGuardedSearch
