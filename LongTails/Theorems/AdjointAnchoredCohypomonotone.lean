import LongTails.Proofs.Execution
import LongTails.Setups.CohypomonotoneAdjoint
import LongTails.Proofs.AdjointExecution
import Mathlib.Analysis.InnerProductSpace.Adjoint

open scoped RealInnerProductSpace

namespace OracleTemplate.CohypomonotoneAdjoint.AdjointAnchoredCohypomonotone

open LongTails.Setups.CohypomonotoneAdjoint

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈(4 * q.L * q.R / ((1 + q.ρ * q.L) * q.ε) + 2) * (5 + 8 * (2 + 2 * q.ρ * q.L) ^ 2 * Real.log (11 + 10 * q.ρ * q.L)) + 128 * (1 + 2 * q.ρ * q.L) ^ 2 * (2 + 2 * q.ρ * q.L) ^ 2 * q.L₂ * q.R * (4 + Real.log (1 + 4 * q.L * q.R / q.ε)) ^ 2 / q.L⌉₊

theorem result : Convergence LongTails.Setups.CohypomonotoneAdjoint.spec budget := by
  apply convergence_of_call_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p => adjointAnchored p.L p.L₂ p.ρ p.x0, ?_, fun _ _ => trivial⟩
  rintro q ⟨hL, hL₂, hρ, hR, hε⟩
  intro K hK
  rintro F oracle ⟨J, hF, hJ, hder, hjlip, hlip, hco, xs, hxs, hdist⟩
  have hyp : Hyp F J q.L q.L₂ q.ρ := ⟨hder, hjlip, hlip, hco⟩
  have : CompleteSpace q.E := FiniteDimensional.complete ℝ q.E
  let adj : q.E → q.E → q.E := fun x w => ContinuousLinearMap.adjoint (J x) w
  have hadj : ∀ x w y, ⟪adj x w, y⟫ = ⟪w, J x y⟫ := fun x w y =>
    ContinuousLinearMap.adjoint_inner_left (J x) y w
  let N := ⌈4 * q.L * q.R / ((1 + q.ρ * q.L) * q.ε)⌉₊
  have hρL : 0 ≤ q.ρ * q.L := mul_nonneg hρ hL.le
  have hN : 4 * q.L * q.R / ((1 + q.ρ * q.L) * q.ε) ≤ (N : ℝ) := Nat.le_ceil _
  have hN1 : (N : ℝ) < 4 * q.L * q.R / ((1 + q.ρ * q.L) * q.ε) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hcum : cum q.L q.L₂ q.ρ F adj q.x0 (N + 1) ≤ K := by
    have hc := cum_le hyp hL hL₂ hρ hadj hxs hdist N
    have hA : 0 ≤ 5 + 8 * (2 + 2 * q.ρ * q.L) ^ 2 * Real.log (11 + 10 * q.ρ * q.L) := by
      have : 0 ≤ Real.log (11 + 10 * q.ρ * q.L) := Real.log_nonneg (by nlinarith)
      positivity
    have hlg : 0 ≤ Real.log (1 + 4 * q.L * q.R / q.ε) := Real.log_nonneg (by
      have : 0 ≤ 4 * q.L * q.R / q.ε := by positivity
      linarith)
    have hH0 := hsum_nonneg N
    have hH : hsum N ≤ 1 + Real.log (1 + 4 * q.L * q.R / q.ε) := by
      refine (hsum_le_log N).trans ?_
      rcases Nat.eq_zero_or_pos N with h0 | hpos
      · rw [h0, Nat.cast_zero, Real.log_zero]; linarith
      · have hle : (N : ℝ) ≤ 1 + 4 * q.L * q.R / q.ε := by
          have : 4 * q.L * q.R / ((1 + q.ρ * q.L) * q.ε) ≤ 4 * q.L * q.R / q.ε := by
            apply div_le_div_of_nonneg_left (by positivity) hε
            nlinarith
          linarith
        have := Real.log_le_log (by exact_mod_cast hpos) hle
        linarith
    have hX : 1 + (24 + 4 * hsum N) * hsum N ≤ 4 * (4 + Real.log (1 + 4 * q.L * q.R / q.ε)) ^ 2 := by
      nlinarith
    have e : 32 * (2 * q.ρ + 1 / q.L) * q.L₂ * (2 + 2 * q.ρ * q.L) ^ 2 *
        ((2 * q.ρ + 1 / q.L) * q.L * q.R * (1 + (24 + 4 * hsum N) * hsum N)) =
        32 * (1 + 2 * q.ρ * q.L) ^ 2 * (2 + 2 * q.ρ * q.L) ^ 2 * q.L₂ * q.R *
          (1 + (24 + 4 * hsum N) * hsum N) / q.L := by
      field_simp; ring
    have h2 : 32 * (1 + 2 * q.ρ * q.L) ^ 2 * (2 + 2 * q.ρ * q.L) ^ 2 * q.L₂ * q.R *
          (1 + (24 + 4 * hsum N) * hsum N) / q.L ≤
        128 * (1 + 2 * q.ρ * q.L) ^ 2 * (2 + 2 * q.ρ * q.L) ^ 2 * q.L₂ * q.R *
          (4 + Real.log (1 + 4 * q.L * q.R / q.ε)) ^ 2 / q.L := by
      apply div_le_div_of_nonneg_right _ hL.le
      have hp : 0 ≤ 32 * (1 + 2 * q.ρ * q.L) ^ 2 * (2 + 2 * q.ρ * q.L) ^ 2 * q.L₂ * q.R := by
        positivity
      nlinarith [mul_le_mul_of_nonneg_left hX hp]
    have h1 : ((N : ℝ) + 1) * (5 + 8 * (2 + 2 * q.ρ * q.L) ^ 2 * Real.log (11 + 10 * q.ρ * q.L)) ≤
        (4 * q.L * q.R / ((1 + q.ρ * q.L) * q.ε) + 2) *
          (5 + 8 * (2 + 2 * q.ρ * q.L) ^ 2 * Real.log (11 + 10 * q.ρ * q.L)) :=
      mul_le_mul_of_nonneg_right (by linarith) hA
    have hreal : (cum q.L q.L₂ q.ρ F adj q.x0 (N + 1) : ℝ) ≤ (K : ℝ) := by
      refine le_trans ?_ ((Nat.le_ceil _).trans (Nat.cast_le.mpr hK))
      rw [e] at hc
      linarith
    exact_mod_cast hreal
  have hacc : ∀ m, N ≤ m → ‖F (run q.L q.L₂ q.ρ F adj q.x0 m)‖ ≤ q.ε := by
    intro m hm
    have hg := gnorm hyp hL hL₂ hρ hadj q.x0 hxs hdist m
    refine hg.trans ?_
    have hm' : (N : ℝ) ≤ m := by exact_mod_cast hm
    have hpos : 0 < ((m : ℝ) + 1) * (q.ρ + 1 / q.L) := by positivity
    rw [div_le_iff₀ hpos]
    have hNm : 4 * q.L * q.R / ((1 + q.ρ * q.L) * q.ε) ≤ (m : ℝ) + 1 := by linarith
    rw [div_le_iff₀ (by positivity)] at hNm
    have e : ((m : ℝ) + 1) * (q.ρ + 1 / q.L) = ((m : ℝ) + 1) * (1 + q.ρ * q.L) / q.L := by
      field_simp; ring
    rw [e, mul_div_assoc', le_div_iff₀ hL]
    nlinarith
  obtain ⟨m, hm, hout⟩ := output_late (L := q.L) (L₂ := q.L₂) (ρ := q.ρ) (F := F) (adj := adj)
    (x0 := q.x0) N (K) hcum
  have hexec : ∀ seed : Unit × ((k : ℕ) → oracle.Seed k),
      execute oracle (adjointAnchored q.L q.L₂ q.ρ q.x0) (fun _ => (K)) seed.1 seed.2 =
        run q.L q.L₂ q.ρ F adj q.x0 m := by
    rintro ⟨⟨⟩, ξ⟩
    refine (execute_eq_of_answer_eq oracle (Sum.elim F (fun p : q.E × q.E => adj p.1 p.2))
      (by
        rintro k (x | ⟨x, w⟩) seed
        · exact hF k seed x
        · exact ext_inner_right ℝ fun y => (hJ k seed x w y).trans (hadj x w y).symm)
      _ _ _ _).trans ?_
    exact (execute_iterate _ _ _ _).trans hout
  refine Filter.Eventually.of_forall (fun seed => ?_)
  · exact (le_of_eq (congrArg (fun r => ‖F r‖) (hexec seed))).trans (hacc m hm)

end OracleTemplate.CohypomonotoneAdjoint.AdjointAnchoredCohypomonotone
