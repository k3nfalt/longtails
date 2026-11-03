import LongTails.Proofs.AuxiliaryEpoch
import LongTails.Proofs.AuxiliaryTuning
import LongTails.Proofs.AuxiliaryCalls
import LongTails.Setups.AuxiliarySimilarityNonconvex

namespace LongTails.Proofs.AuxiliaryConvergence

open OracleTemplate
open LongTails.Algorithms.AuxiliaryPlan LongTails.Algorithms.AuxiliarySimilarity
open LongTails.Algorithms.AuxiliaryPlan.TwoPlan LongTails.Proofs.AuxiliaryPlan.TwoPlan LongTails.Proofs.AuxiliaryEval
open LongTails.Proofs.AuxiliaryDane LongTails.Proofs.AuxiliaryAppa LongTails.Proofs.AuxiliaryEpoch
open LongTails.Proofs.AuxiliaryTuning LongTails.Proofs.AuxiliaryCalls

section Run

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {t : Tuning} {f h : E → ℝ} {L δ ρ Δ : ℝ}

lemma grad_sq_le (hyp : Hyp t f h L δ ρ Δ) (x0 y : E) (hΔ : ∀ x, f x0 - f x ≤ Δ)
    (hy : f y ≤ f x0) : ‖gradient f y‖ ^ 2 ≤ 2 * (L + δ) * Δ := by
  have hℓ : 0 < L + δ := by linarith [hyp.hL, hyp.hδ]
  have hd := OracleTemplate.Gradient.descent hℓ hyp.gradf hyp.gradf_lip y
  have h1 := hΔ (y - (1 / (L + δ)) • gradient f y)
  have h2 : ‖gradient f y‖ ^ 2 / (2 * (L + δ)) ≤ Δ := by linarith
  rwa [div_le_iff₀ (by positivity), mul_comm] at h2

lemma method_stationary [FiniteDimensional ℝ E] (hyp : Hyp t f h L δ ρ Δ) (x0 : E) (hΔ : ∀ x, f x0 - f x ≤ Δ)
    (hK : Δ < t.K * (t.α * tau t ρ ^ 2)) :
    ‖gradient f (eval (orc (Fo f) (Fo h)) (method t x0))‖ ≤ t.ε := by
  unfold method
  rw [eval_loop]
  set c := t.α * tau t ρ ^ 2
  have hc : 0 < c := by have := hyp.hα; have := hyp.tau_pos; positivity
  have inv : ∀ k : ℕ, ‖gradient f ((fun y => eval (orc (Fo f) (Fo h)) (epoch t y))^[k] x0)‖ ≤ t.ε ∨
      f ((fun y => eval (orc (Fo f) (Fo h)) (epoch t y))^[k] x0) ≤ f x0 - k * c := by
    intro k
    induction k with
    | zero => right; simp
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        set y := (fun y => eval (orc (Fo f) (Fo h)) (epoch t y))^[k] x0
        rcases ih with hs | hd
        · left
          rw [eval_epoch, ite_eq_left hs]
          exact hs
        · have hy : f y ≤ f x0 := by
            have : 0 ≤ (k : ℝ) * c := by positivity
            linarith
          rcases epoch_progress hyp y (grad_sq_le hyp x0 y hΔ hy) with h1 | h1
          · exact Or.inl h1
          · right; push_cast; linarith
  rcases inv t.K with hs | hd
  · exact hs
  · exfalso
    have := hΔ ((fun y => eval (orc (Fo f) (Fo h)) (epoch t y))^[t.K] x0)
    linarith

end Run

section Budget

lemma calls_bound {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L δ ρ Δ ε : ℝ) (x0 : E)
    (g : Fin 2 → E → ℝ × E) (j : Fin 2) :
    calls g j (method (tuning L δ ρ Δ ε) x0) ≤
      ![(⌈2 ^ 19 * Δ * Real.sqrt (ρ * ε) / ε ^ 2⌉₊ + 1) * ((⌈6 * Real.sqrt (1 + δ / Real.sqrt (ρ * ε)) *
        Real.log (8 + 8 * δ / Real.sqrt (ρ * ε))⌉₊ + 1) *
        (⌈15 * Real.log (400 * (1 + (L + δ) / Real.sqrt (ρ * ε)))⌉₊ + 2) + 6),
      (⌈2 ^ 19 * Δ * Real.sqrt (ρ * ε) / ε ^ 2⌉₊ + 1) * ((⌈6 * Real.sqrt (1 + δ / Real.sqrt (ρ * ε)) *
        Real.log (8 + 8 * δ / Real.sqrt (ρ * ε))⌉₊ + 1) *
        ((⌈15 * Real.log (400 * (1 + (L + δ) / Real.sqrt (ρ * ε)))⌉₊ + 1) *
          (⌈(L / δ + 6) * Real.log (2 ^ 110 * (1 + (L + δ) / Real.sqrt (ρ * ε)) ^ 10 *
            (1 + Δ * Real.sqrt (ρ * ε) / ε ^ 2))⌉₊ + 3) + 1))] j := by
  refine (calls_method g (tuning L δ ρ Δ ε) j x0).trans (le_of_eq ?_)
  fin_cases j <;> rfl

end Budget

section Final

open LongTails.Setups.AuxiliarySimilarityNonconvex

lemma run_result (p : Params) (hp : spec.valid p) (I : spec.Instance (spec.publicInput p))
    (O : Oracle (spec.Query (spec.publicInput p)) (spec.Reply (spec.publicInput p)) spec.numOracles)
    (hO : spec.admissible p I O) (B : Fin 2 → ℕ)
    (hB : ∀ j, calls (orc (Fo I.1) (Fo I.2)) j (method (tuning p.L p.δ p.ρ p.Δ p.ε) p.x0) ≤ B j)
    (seed : Unit) (ξ : (k : ℕ) → O.Seed k) :
    ‖gradient I.1 (execute O (TwoPlan.algorithm p.x0 p.x0
      (method (tuning p.L p.δ p.ρ p.Δ p.ε) p.x0)) B seed ξ)‖ ≤ p.ε := by
  obtain ⟨hL, hδ, hρ, hΔ, hε⟩ := hp
  obtain ⟨hf, hh, hHess, hsim, hLh, hΔf, hO0, hO1⟩ := hO
  have hb : Base p.L p.δ p.ρ p.Δ p.ε := ⟨hL, hδ, hρ, hΔ, hε⟩
  have hyp := hb.hyp hf hh hHess hsim hLh
  have hans : ∀ hist i q s, O.answer hist (i, q) s = orc (Fo I.1) (Fo I.2) i q := by
    intro hist i q s
    fin_cases i
    · simp only [Fin.zero_eta, orc_zero]; exact hO0 hist q s
    · simp only [Fin.mk_one, orc_one]; exact hO1 hist q s
  rw [execute_eq_eval (orc (Fo I.1) (Fo I.2)) p.x0 p.x0 _ O hans B hB ξ]
  exact method_stationary hyp p.x0 hΔf hb.hK

end Final

end LongTails.Proofs.AuxiliaryConvergence
