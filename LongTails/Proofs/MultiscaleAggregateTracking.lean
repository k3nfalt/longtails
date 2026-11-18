import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp

open MeasureTheory

namespace LongTails.Proofs.MultiscaleAggregateTracking

noncomputable def overflow (decoded raw radius : ℝ) : ℝ :=
  if decoded ≤ raw then 0 else decoded + 5 * radius

lemma error_le_raw_add_overflow {e a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) :
    e ≤ a + overflow e a s := by
  unfold overflow
  split <;> linarith

lemma overflow_step {e₀ a₀ r₀ e a r : ℝ}
    (hr : 0 < r) (hscale : 2 * r ≤ r₀) (ha : 0 ≤ a) (ha₀ : 0 ≤ a₀)
    (hmove : e ≤ e₀ + 5 * r)
    (hdecode : e₀ ≤ r → a ≤ r → e ≤ a) :
    overflow e a r ≤ overflow e₀ a₀ r₀ + 12 * (a₀ ^ 2 + a ^ 2) / r := by
  have hcharge : 0 ≤ 12 * (a₀ ^ 2 + a ^ 2) / r := by positivity
  unfold overflow
  split_ifs with h h₀ h₀
  · linarith
  · linarith
  · rw [zero_add, le_div_iff₀ hr]
    by_cases hp : a₀ ≤ r
    · have hx : r < a := lt_of_not_ge fun hx => h (hdecode (h₀.trans hp) hx)
      nlinarith [mul_le_mul_of_nonneg_right (hmove.trans (add_le_add (h₀.trans hp) le_rfl)) hr.le,
        mul_nonneg (sub_nonneg.mpr hx.le) (add_nonneg ha hr.le), sq_nonneg a₀]
    · have hx := lt_of_not_ge hp
      nlinarith [mul_le_mul_of_nonneg_right (hmove.trans (add_le_add h₀ le_rfl)) hr.le,
        mul_nonneg (sub_nonneg.mpr hx.le) ha₀, mul_nonneg (sub_nonneg.mpr hx.le) hr.le,
        sq_nonneg a]
  · linarith

lemma overflow_root {e a r : ℝ} (hr : 0 < r) (hcap : e ≤ 4 * r)
    (hdecode : a ≤ r → e ≤ a) : overflow e a r ≤ 9 * a ^ 2 / r := by
  unfold overflow
  split_ifs with h
  · positivity
  · have ha : r < a := lt_of_not_ge fun h₁ => h (hdecode h₁)
    rw [le_div_iff₀ hr]
    nlinarith [mul_le_mul_of_nonneg_right hcap hr.le,
      mul_nonneg (sub_nonneg.mpr ha.le) (show 0 ≤ a + r by linarith)]

lemma expected_overflow_step {e₀ e v r₀ r : ℝ}
    (hr : 0 < r) (hscale : 2 * r ≤ r₀) (hv : 0 ≤ v)
    (hp : e₀ ≤ 48 * v / r₀) (hs : e ≤ e₀ + 24 * v / r) :
    e ≤ 48 * v / r := by
  have h : 48 * v / r₀ ≤ 24 * v / r := by
    apply (div_le_div_iff₀ (by linarith) hr).mpr
    nlinarith [mul_le_mul_of_nonneg_right hscale hv]
  calc
    e ≤ 24 * v / r + 24 * v / r := hs.trans (add_le_add (hp.trans h) le_rfl)
    _ = 48 * v / r := by ring

lemma tree_envelope {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (e a q : ℕ → Ω → ℝ) (r : ℕ → ℝ) (parent : ℕ → ℕ) (N : ℕ) (v : ℝ)
    (hv : 0 ≤ v) (hr : ∀ k < N, 0 < r k)
    (hparent : ∀ k < N, k ≠ 0 → parent k < k)
    (hscale : ∀ k < N, k ≠ 0 → 2 * r k ≤ r (parent k))
    (hmajor : ∀ k < N, ∀ s, a k s ^ 2 ≤ q k s)
    (hI : ∀ k < N, Integrable (q k) P)
    (hQ : ∀ k < N, (∫ s, q k s ∂P) ≤ v)
    (hroot : ∀ s, overflow (e 0 s) (a 0 s) (r 0) ≤ 9 * a 0 s ^ 2 / r 0)
    (hstep : ∀ k < N, k ≠ 0 → ∀ s, overflow (e k s) (a k s) (r k) ≤
      overflow (e (parent k) s) (a (parent k) s) (r (parent k)) +
        12 * (a (parent k) s ^ 2 + a k s ^ 2) / r k)
    (k : ℕ) (hk : k < N) :
    ∃ u : Ω → ℝ, Integrable u P ∧ (∫ s, u s ∂P) ≤ 48 * v / r k ∧
      ∀ s, overflow (e k s) (a k s) (r k) ≤ u s := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have hpos := hr k hk
    by_cases hz : k = 0
    · subst k
      refine ⟨fun s => (9 / r 0) * q 0 s, (hI 0 hk).const_mul _, ?_, ?_⟩
      · rw [integral_const_mul]
        calc
          _ ≤ 9 / r 0 * v := mul_le_mul_of_nonneg_left (hQ 0 hk) (by positivity)
          _ ≤ 48 * v / r 0 := by field_simp; linarith
      · intro s
        calc
          _ ≤ 9 * a 0 s ^ 2 / r 0 := hroot s
          _ = (9 / r 0) * a 0 s ^ 2 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hmajor 0 hk s) (by positivity)
    · let j := parent k
      have hj := hparent k hk hz
      have hjN := hj.trans hk
      obtain ⟨u, hUi, hU, hu⟩ := ih j hj hjN
      let c := 12 / r k
      have hc : 0 ≤ c := div_nonneg (by norm_num) hpos.le
      have hi : Integrable (fun s => q j s + q k s) P := (hI j hjN).add (hI k hk)
      refine ⟨fun s => u s + c * (q j s + q k s), hUi.add (hi.const_mul _), ?_, ?_⟩
      · rw [integral_add hUi (hi.const_mul c), integral_const_mul, integral_add (hI j hjN) (hI k hk)]
        apply expected_overflow_step (e₀ := ∫ s, u s ∂P) hpos (hscale k hk hz) hv hU
        have hcq := mul_le_mul_of_nonneg_left (add_le_add (hQ j hjN) (hQ k hk)) hc
        have he : c * (v + v) = 24 * v / r k := by dsimp [c]; ring
        linarith
      · intro s
        apply (hstep k hk hz s).trans
        apply add_le_add (hu s)
        have h := mul_le_mul_of_nonneg_left (add_le_add (hmajor j hjN s) (hmajor k hk s)) hc
        calc
          _ = c * (a j s ^ 2 + a k s ^ 2) := by dsimp [c, j]; ring
          _ ≤ _ := h

end LongTails.Proofs.MultiscaleAggregateTracking
