import LongTails.Setups.HighDimensionalHighProbabilityStationarity
import LongTails.Proofs.HighProbabilityChainFailure
import LongTails.Proofs.HighProbabilityTwoPointFailure
import LongTails.TemplateLowerBound

open MeasureTheory OracleTemplate

namespace LongTails.Proofs.HighProbabilityLowerAssembly

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open LongTails.Setups.HighDimensionalHighProbabilityStationarity

noncomputable def chainParams (q : Params) : LongTails.Setups.HighDimensionalAbcNoiseNonconvex.Params where
  d := q.d
  L := q.L
  A := 0
  B := 0
  C := q.σ ^ 2
  Δ := q.Δ
  ε := q.ε
  x0 := q.x0

lemma chainParams_valid (q : Params) (hv : spec.valid q) :
    LongTails.Setups.HighDimensionalAbcNoiseNonconvex.spec.valid (chainParams q) := by
  obtain ⟨hL, hσ, hε, hδ, hδ1, hreg, hd⟩ := hv
  refine ⟨hL, le_rfl, le_rfl, sq_nonneg _, hε, ?_, ?_⟩
  · change 2 ^ 26 * q.ε ^ 2 ≤ q.L * q.Δ
    nlinarith [sq_nonneg q.ε]
  · change 2 ^ 40 * (1 + q.L * q.Δ * (1 + 0 + 0 * q.Δ / q.ε ^ 2 + q.σ ^ 2 / q.ε ^ 2) / q.ε ^ 2) ^ 4 ≤
      (q.d : ℝ)
    simpa only [add_zero, zero_mul, zero_div] using hd

lemma chain_admissible (q : Params) (f : EuclideanSpace ℝ (Fin q.d) → ℝ)
    (O : Oracle (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d)))
    (h : LongTails.Setups.HighDimensionalAbcNoiseNonconvex.spec.admissible (chainParams q) f O) :
    spec.admissible q f O := by
  obtain ⟨g, p, P, fstar, hiid, hO, hgrad, hlip, hlow, hinf, hgap, hm, hi, hmean, hvi, hvar⟩ := h
  refine ⟨g, p, P, fstar, hiid, hO, hgrad, hlip, hlow, hinf, hgap, hm, hi, hmean, hvi, ?_⟩
  intro x
  refine le_trans (hvar x) (le_of_eq ?_)
  simp [chainParams, LongTails.Setups.HighDimensionalAbcNoiseNonconvex.toGeneral, toGeneral]

lemma budget_split (q : Params) (hv : spec.valid q) (N : ℕ)
    (hN : N ≤ ⌊(q.L * q.Δ * (1 + q.σ ^ 2 / q.ε ^ 2) + q.σ ^ 2 * Real.log (1 / (4 * q.δ))) /
      (2 ^ 54 * q.ε ^ 2)⌋₊)
    (hbig : LongTails.Proofs.AbcLowerParameters.lowerBudget (chainParams q) < N) :
    (N : ℝ) * (8 * q.ε ^ 2) ≤ q.σ ^ 2 * Real.log (1 / (4 * q.δ)) := by
  obtain ⟨hL, hσ, hε, hδ, hδ1, hreg, hd⟩ := hv
  have hε2 : 0 < q.ε ^ 2 := by positivity
  set X := q.L * q.Δ * (1 + q.σ ^ 2 / q.ε ^ 2)
  set Y := q.σ ^ 2 * Real.log (1 / (4 * q.δ))
  have hX : 0 ≤ X := by
    have : 0 ≤ q.L * q.Δ := by nlinarith [sq_nonneg q.ε]
    positivity
  have hlow : LongTails.Proofs.AbcLowerParameters.lowerBudget (chainParams q) =
      ⌊X / (2 ^ 53 * q.ε ^ 2)⌋₊ := by
    unfold LongTails.Proofs.AbcLowerParameters.lowerBudget
    congr 2
    change q.L * q.Δ * (1 + 0 + 0 * q.Δ / q.ε ^ 2 + q.σ ^ 2 / q.ε ^ 2) = X
    simp only [X, add_zero, zero_mul, zero_div]
  rw [hlow] at hbig
  have h1 : X / (2 ^ 53 * q.ε ^ 2) < N := by
    have := Nat.lt_floor_add_one (X / (2 ^ 53 * q.ε ^ 2))
    have h2 : (⌊X / (2 ^ 53 * q.ε ^ 2)⌋₊ : ℝ) + 1 ≤ N := by exact_mod_cast hbig
    linarith
  have hY : (N : ℝ) ≤ (X + Y) / (2 ^ 54 * q.ε ^ 2) := by
    have hpos : 0 ≤ (X + Y) / (2 ^ 54 * q.ε ^ 2) ∨ (X + Y) / (2 ^ 54 * q.ε ^ 2) < 0 :=
      le_or_gt _ _
    rcases hpos with hpos | hneg
    · exact (Nat.cast_le.mpr hN).trans (Nat.floor_le hpos)
    · have h0 : ⌊(X + Y) / (2 ^ 54 * q.ε ^ 2)⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      have : N = 0 := by omega
      subst this
      have : (0 : ℝ) ≤ X / (2 ^ 53 * q.ε ^ 2) := by positivity
      simp at h1
      linarith
  rw [div_lt_iff₀ (by positivity)] at h1
  rw [le_div_iff₀ (by positivity)] at hY
  nlinarith

lemma nonConvergence :
    NonConvergence spec (fun q _ => ⌊(q.L * q.Δ * (1 + q.σ ^ 2 / q.ε ^ 2) +
      q.σ ^ 2 * Real.log (1 / (4 * q.δ))) / (2 ^ 54 * q.ε ^ 2)⌋₊) := by
  intro q hv A _ b hb
  have heq : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  rw [heq]
  have hδ1 : q.δ ≤ 1 / 4 := hv.2.2.2.2.1
  by_cases hsmall : b 0 ≤ LongTails.Proofs.AbcLowerParameters.lowerBudget (chainParams q)
  · have hv' := chainParams_valid q hv
    obtain ⟨π, hπ⟩ := LongTails.Proofs.HighProbabilityChainFailure.exists_hp_failure
      (chainParams q) hv' A (b 0) hsmall
    refine ⟨_, _, chain_admissible q _ _
      (LongTails.Proofs.AbcLowerAssembly.hard_admissible (chainParams q) hv' π), ?_⟩
    intro _ hs
    apply hπ
    refine ⟨hs.1, ?_⟩
    have h2 := hs.2
    change 1 - q.δ ≤ _ at h2
    exact le_trans (by linarith) h2
  · push Not at hsmall
    have hN := budget_split q hv (b 0) (hb 0) hsmall
    have hd : 0 < q.d := by
      have h := hv.2.2.2.2.2.2
      have hLΔ : 0 < q.L * q.Δ := lt_of_lt_of_le (by have := hv.2.2.1; positivity) hv.2.2.2.2.2.1
      have hx : 0 ≤ q.L * q.Δ * (1 + q.σ ^ 2 / q.ε ^ 2) / q.ε ^ 2 :=
        div_nonneg (mul_nonneg hLΔ.le (by positivity)) (sq_nonneg _)
      have h1 : (0 : ℝ) < 1 + q.L * q.Δ * (1 + q.σ ^ 2 / q.ε ^ 2) / q.ε ^ 2 := by linarith
      have hpos : (0 : ℝ) < q.d := lt_of_lt_of_le (by positivity) h
      exact_mod_cast hpos
    obtain ⟨s, hs, hfail⟩ :=
      LongTails.Proofs.HighProbabilityTwoPointFailure.exists_failure q hv A (b 0) hN hd
    exact ⟨_, _, LongTails.Proofs.HighProbabilityTwoPointFailure.hard_admissible q hv hd s hs, hfail⟩

end LongTails.Proofs.HighProbabilityLowerAssembly
