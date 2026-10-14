import LongTails.Proofs.MultiStepAnchoredStep
import LongTails.Proofs.Execution
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped RealInnerProductSpace

namespace OracleTemplate.CohypomonotoneInclusion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def run (F : E → E) (J : ℝ → E → E) (η s : ℝ) (m : ℕ) (x0 : E) : ℕ → E × E
  | 0 => fb F J η x0 x0
  | n + 1 => next F J η s m (yval F η (fb F J η x0 x0)) n (run F J η s m x0 n)

lemma run_resolvent (F : E → E) (J : ℝ → E → E) (η s : ℝ) (m : ℕ) (x0 : E) (n : ℕ) :
    (run F J η s m x0 n).2 = J η (run F J η s m x0 n).1 := by
  cases n <;> rfl

lemma pot_run {F : E → E} {H : E → Set E} {J : ℝ → E → E} {L ρ η s : ℝ} {m : ℕ}
    (h : Hyp F H J L ρ) (hL : 0 ≤ L) (hη : 0 < η) (hq : η * L ≤ 1)
    (hP : (η * L) ^ (m + 1) * (2 + η * L) < 1)
    (hσ : (η * L) ^ (m + 1) * (1 + η * L) * η ≤
      (η - ρ - s / 2) * (1 - (η * L) ^ (m + 1) * (2 + η * L)))
    (x0 : E) (n : ℕ) :
    pot F η (η - ρ) (s / 2) (yval F η (fb F J η x0 x0)) n (run F J η s m x0 n) ≤ 0 := by
  induction n with
  | zero =>
    have hgap : 0 < 1 - (η * L) ^ (m + 1) * (2 + η * L) := by linarith
    have hnum : 0 ≤ (η * L) ^ (m + 1) * (1 + η * L) * η := by
      have := mul_nonneg hη.le hL
      positivity
    have hμ : 0 ≤ η - ρ - s / 2 := by
      by_contra hneg
      rw [not_le] at hneg
      have := mul_neg_of_neg_of_pos hneg hgap
      linarith
    have hsq : 0 ≤ ‖gval F η (fb F J η x0 x0)‖ ^ 2 := by positivity
    simp only [pot, run, sub_self, inner_zero_right, mul_zero, add_zero, Nat.cast_zero, zero_add,
      one_mul]
    nlinarith
  | succ n ih =>
    exact (pot_step h hL hη hq hP hσ _ n (run_resolvent F J η s m x0 n)).trans ih

lemma run_residual {F : E → E} {H : E → Set E} {J : ℝ → E → E} {L ρ η s : ℝ} {m : ℕ}
    (h : Hyp F H J L ρ) (hL : 0 ≤ L) (hη : 0 < η) (hq : η * L ≤ 1)
    (hP : (η * L) ^ (m + 1) * (2 + η * L) < 1)
    (hσ : (η * L) ^ (m + 1) * (1 + η * L) * η ≤
      (η - ρ - s / 2) * (1 - (η * L) ^ (m + 1) * (2 + η * L)))
    (x0 : E) {xs : E} (hxs : -F xs ∈ H xs) (n : ℕ) :
    ((n : ℝ) + 1) * (s / 2) * ‖gval F η (run F J η s m x0 n)‖ ≤ 4 * ‖x0 - xs‖ := by
  set p := run F J η s m x0 n with hp
  set a := yval F η (fb F J η x0 x0) with ha
  have hres := run_resolvent F J η s m x0 n
  rw [← hp] at hres
  have hpot := pot_run h hL hη hq hP hσ x0 n
  rw [← hp, ← ha] at hpot
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hq0 : 0 ≤ η * L := mul_nonneg hη.le hL
  have hroot : (η - ρ) * ‖gval F η p‖ ^ 2 ≤ ⟪gval F η p, yval F η p - xs⟫ := by
    have hc := h.cohypo p.2 xs _ (h.mem hη hres) _ hxs
    have e0 : F p.2 + η⁻¹ • (p.1 - p.2) - (F xs + -F xs) = gval F η p := by
      rw [add_neg_cancel, sub_zero, gval]
    rw [e0] at hc
    rw [yval_eq F hη.ne' p]
    have e1 : p.2 + η • gval F η p - xs = (p.2 - xs) + η • gval F η p := by abel
    rw [e1, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    linarith
  have hanchor : ‖a - xs‖ ≤ 4 * ‖x0 - xs‖ := by
    have hfix := h.fixed hη hxs
    have hu : ‖J η (x0 - η • F x0) - xs‖ ≤ (1 + η * L) * ‖x0 - xs‖ := by
      have h1 := h.nonexpansive hη (x0 - η • F x0) (xs - η • F xs)
      rw [hfix] at h1
      have e : x0 - η • F x0 - (xs - η • F xs) = (x0 - xs) - η • (F x0 - F xs) := by
        rw [smul_sub]; abel
      rw [e] at h1
      have h2 := norm_sub_le (x0 - xs) (η • (F x0 - F xs))
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη] at h2
      have h3 := mul_le_mul_of_nonneg_left (h.lip x0 xs) hη.le
      linarith
    have e : a - xs = (x0 - xs) + η • (F (J η (x0 - η • F x0)) - F x0) := by
      rw [ha]
      change x0 - η • F x0 + η • F (J η (x0 - η • F x0)) - xs = _
      module
    have h4 := norm_add_le (x0 - xs) (η • (F (J η (x0 - η • F x0)) - F x0))
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη] at h4
    have h5 := mul_le_mul_of_nonneg_left (h.lip (J η (x0 - η • F x0)) x0) hη.le
    have h6 : ‖J η (x0 - η • F x0) - x0‖ ≤ ‖J η (x0 - η • F x0) - xs‖ + ‖x0 - xs‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub (J η (x0 - η • F x0)) xs x0
      rwa [norm_sub_rev xs x0] at this
    have hR : 0 ≤ ‖x0 - xs‖ := norm_nonneg _
    have h7 : η * L * ‖J η (x0 - η • F x0) - x0‖ ≤ (η * L) * ((2 + η * L) * ‖x0 - xs‖) := by
      apply mul_le_mul_of_nonneg_left _ hq0
      linarith
    have h8 : (η * L) * ((2 + η * L) * ‖x0 - xs‖) ≤ 1 * ((2 + 1) * ‖x0 - xs‖) := by
      apply mul_le_mul hq _ (by positivity) (by norm_num)
      exact mul_le_mul_of_nonneg_right (by linarith) hR
    rw [e]
    nlinarith
  have hsplit : ⟪gval F η p, yval F η p - a⟫ =
      ⟪gval F η p, yval F η p - xs⟫ - ⟪gval F η p, a - xs⟫ := by
    rw [← inner_sub_right]; congr 1; abel
  have hcs := real_inner_le_norm (gval F η p) (a - xs)
  have hG : 0 ≤ ‖gval F η p‖ := norm_nonneg _
  have hmain : ((n : ℝ) + 1) * (s / 2) * ‖gval F η p‖ ^ 2 ≤ ‖gval F η p‖ * ‖a - xs‖ := by
    unfold pot at hpot
    rw [hsplit] at hpot
    have h1 : (((n : ℝ) + 1) * (s / 2) - (η - ρ)) * ‖gval F η p‖ ^ 2 +
        (⟪gval F η p, yval F η p - xs⟫ - ⟪gval F η p, a - xs⟫) ≤ 0 := by
      by_contra hneg
      rw [not_le] at hneg
      have := mul_pos hn hneg
      nlinarith
    nlinarith
  rcases eq_or_lt_of_le hG with h0 | hpos
  · rw [← h0, mul_zero]
    exact mul_nonneg (by norm_num) (norm_nonneg _)
  · have h1 : ((n : ℝ) + 1) * (s / 2) * ‖gval F η p‖ ≤ ‖a - xs‖ := by
      have h2 : ‖gval F η p‖ * (((n : ℝ) + 1) * (s / 2) * ‖gval F η p‖) ≤
          ‖gval F η p‖ * ‖a - xs‖ := by
        calc _ = ((n : ℝ) + 1) * (s / 2) * ‖gval F η p‖ ^ 2 := by ring
          _ ≤ _ := hmain
      exact le_of_mul_le_mul_left h2 hpos
    exact h1.trans hanchor

lemma parameter_bounds {L ρ : ℝ} (hL : 0 < L) (hρ : 0 ≤ ρ) (hr : ρ * L < 1) (m : ℕ)
    (hm : 2 / (1 - ρ * L) * Real.log (16 / (1 - ρ * L)) ≤ m) :
    0 < (1 + ρ * L) / (2 * L) ∧ (1 + ρ * L) / (2 * L) * L ≤ 1 ∧
    ((1 + ρ * L) / (2 * L) * L) ^ (m + 1) * (2 + (1 + ρ * L) / (2 * L) * L) < 1 ∧
    ((1 + ρ * L) / (2 * L) * L) ^ (m + 1) * (1 + (1 + ρ * L) / (2 * L) * L) *
        ((1 + ρ * L) / (2 * L)) ≤
      ((1 + ρ * L) / (2 * L) - ρ - (1 - ρ * L) / (2 * L) / 2) *
        (1 - ((1 + ρ * L) / (2 * L) * L) ^ (m + 1) * (2 + (1 + ρ * L) / (2 * L) * L)) := by
  have hr0 : 0 ≤ ρ * L := mul_nonneg hρ hL.le
  set δ := 1 - ρ * L with hδ
  have hδ0 : 0 < δ := by linarith
  have hδ1 : δ ≤ 1 := by linarith
  have hq : (1 + ρ * L) / (2 * L) * L = 1 - δ / 2 := by
    rw [hδ]; field_simp; ring
  have hμ : (1 + ρ * L) / (2 * L) - ρ - (1 - ρ * L) / (2 * L) / 2 = δ / (4 * L) := by
    rw [hδ]; field_simp; ring
  have hη : (1 + ρ * L) / (2 * L) = (2 - δ) / (2 * L) := by rw [hδ]; ring_nf
  have hη0 : 0 < (1 + ρ * L) / (2 * L) := by positivity
  have hq0 : 0 ≤ 1 - δ / 2 := by linarith
  have hq1 : 1 - δ / 2 ≤ 1 := by linarith
  have hexp : 1 - δ / 2 ≤ Real.exp (-(δ / 2)) := by
    have := Real.add_one_le_exp (-(δ / 2))
    linarith
  have hpow : (1 - δ / 2) ^ m ≤ δ / 16 := by
    calc (1 - δ / 2) ^ m ≤ Real.exp (-(δ / 2)) ^ m := pow_le_pow_left₀ hq0 hexp m
      _ = Real.exp ((m : ℝ) * (-(δ / 2))) := (Real.exp_nat_mul _ m).symm
      _ ≤ Real.exp (-Real.log (16 / δ)) := by
          apply Real.exp_le_exp.mpr
          have h1 : Real.log (16 / δ) ≤ (m : ℝ) * (δ / 2) := by
            have h2 := mul_le_mul_of_nonneg_right hm (show 0 ≤ δ / 2 by positivity)
            have h3 : 2 / δ * Real.log (16 / δ) * (δ / 2) = Real.log (16 / δ) := by
              field_simp
            linarith
          linarith
      _ = δ / 16 := by
          rw [Real.exp_neg, Real.exp_log (by positivity)]
          field_simp
  have hP : (1 - δ / 2) ^ (m + 1) ≤ δ / 16 := by
    rw [pow_succ]
    have h0 : 0 ≤ (1 - δ / 2) ^ m := pow_nonneg hq0 m
    nlinarith
  have hP0 : 0 ≤ (1 - δ / 2) ^ (m + 1) := pow_nonneg hq0 _
  refine ⟨hη0, by rw [hq]; exact hq1, ?_, ?_⟩
  · rw [hq]
    nlinarith
  · rw [hq, hμ, hη]
    have hLinv : 0 < 1 / L := by positivity
    have e1 : (2 - δ) / (2 * L) = (2 - δ) / 2 * (1 / L) := by field_simp
    have e2 : δ / (4 * L) = δ / 4 * (1 / L) := by field_simp
    rw [e1, e2]
    generalize (1 - δ / 2) ^ (m + 1) = P at hP hP0
    generalize 1 / L = i at hLinv
    have h1 : P * (1 + (1 - δ / 2)) * ((2 - δ) / 2) ≤ δ / 4 * (1 - P * (2 + (1 - δ / 2))) := by
      nlinarith [mul_nonneg hP0 hδ0.le]
    have := mul_le_mul_of_nonneg_right h1 hLinv.le
    nlinarith

section Execution

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma execute_multiStep (F : E → E) (J : ℝ → E → E) (η s : ℝ) (m : ℕ) (x0 : E) (n : ℕ) :
    execute { answer := fun _ (_, query) _ => Sum.elim F (fun z : ℝ × E => J z.1 z.2) query }
        (multiStepAnchored η s m x0) (fun _ => (2 + (2 * m + 3) * n)) =
      (run F J η s m x0 n).2 := by
  let A := multiStepAnchored η s m x0
  let T : MultiStepState E → MultiStepState E :=
    fun st => A.update st (Sum.elim F (fun z : ℝ × E => J z.1 z.2) ((A.query st).2))
  have hfb : ∀ (j k : ℕ) (a t c v : E),
      T^[2 * (j + 1)] ⟨k, j + 1, false, a, t, c, v⟩ =
        ⟨k, 0, false, a, t,
          (fb F J η t ((fun v => (fb F J η t v).2)^[j] v)).1,
          (fb F J η t ((fun v => (fb F J η t v).2)^[j] v)).2⟩ := by
    intro j
    induction j with
    | zero => intro k a t c v; rfl
    | succ j ih =>
      intro k a t c v
      rw [show 2 * (j + 1 + 1) = 2 * (j + 1) + 2 by ring, Function.iterate_add_apply]
      have h2 : T^[2] ⟨k, j + 1 + 1, false, a, t, c, v⟩ =
          ⟨k, j + 1, false, a, t, t - η • F v, (fb F J η t v).2⟩ := rfl
      rw [h2, ih]
      rfl
  have hi : ∀ n, ∃ a t, T^[2 + (2 * m + 3) * n] (A.initial ()) =
      ⟨n, 0, false, a, t, (run F J η s m x0 n).1, (run F J η s m x0 n).2⟩ ∧
      (n ≠ 0 → a = yval F η (fb F J η x0 x0)) := by
    intro n
    induction n with
    | zero => exact ⟨0, x0, rfl, fun hn => absurd rfl hn⟩
    | succ n ih =>
      obtain ⟨a, t, hst, ha⟩ := ih
      refine ⟨yval F η (fb F J η x0 x0),
        target s n (yval F η (fb F J η x0 x0)) (yval F η (run F J η s m x0 n))
          (gval F η (run F J η s m x0 n)), ?_, fun _ => rfl⟩
      rw [show 2 + (2 * m + 3) * (n + 1) = 2 * (m + 1) + (1 + (2 + (2 * m + 3) * n)) by ring]
      erw [Function.iterate_add_apply T (2 * (m + 1)) (1 + (2 + (2 * m + 3) * n)),
        Function.iterate_add_apply T 1 (2 + (2 * m + 3) * n), hst]
      have h1 : T^[1] (⟨n, 0, false, a, t, (run F J η s m x0 n).1, (run F J η s m x0 n).2⟩ :
            MultiStepState E) =
          ⟨n + 1, m + 1, false, yval F η (fb F J η x0 x0),
            target s n (yval F η (fb F J η x0 x0)) (yval F η (run F J η s m x0 n))
              (gval F η (run F J η s m x0 n)),
            (run F J η s m x0 n).1,
            predictor η s n (yval F η (fb F J η x0 x0)) (yval F η (run F J η s m x0 n))
              (gval F η (run F J η s m x0 n))⟩ := by
        cases n with
        | zero => rfl
        | succ n' =>
          have ha' := ha (Nat.succ_ne_zero n')
          subst ha'
          rfl
      rw [h1, hfb]
      rfl
  erw [execute_iterate]
  obtain ⟨a, t, hst, -⟩ := hi n
  change A.output (T^[2 + (2 * m + 3) * n] (A.initial ())) = _
  rw [hst]
  rfl

end Execution

end OracleTemplate.CohypomonotoneInclusion
