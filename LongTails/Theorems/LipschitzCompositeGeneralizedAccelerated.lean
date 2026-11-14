import LongTails.Setups.LipschitzCompositeGeneralizedSmooth
import LongTails.Proofs.Execution
import LongTails.Proofs.CompositeSherpaBudget

open Set

namespace OracleTemplate.CompositeSherpa

open LongTails.Setups.LipschitzCompositeGeneralizedSmooth

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈184 * Real.sqrt ((q.L0 + q.L1 * q.M) * q.R ^ 2 / q.ε) + 130000 * (1 + q.L1 * q.R) * Real.log (2 + q.L1 * q.R)⌉₊

set_option maxHeartbeats 1000000 in
theorem result : Convergence LongTails.Setups.LipschitzCompositeGeneralizedSmooth.spec budget := by
  apply convergence_of_call_budget (S := spec) (fun q => budget q 0)
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  rintro q ⟨hL0, hL1, hM, hR, hε⟩ N hN I oracle
    ⟨hgAns, hpAns, hvAns, hc, hgrad, hcont, hsmooth, hψc, hψlip, hprox, xs, hmin, hdist⟩
  have H : Hyp I.f I.ψ I.grad I.prox q.L0 q.L1 q.M xs :=
    ⟨hL0, hL1, hM, hc, hgrad, hcont, hsmooth, hψc, hψlip, hprox, hmin⟩
  set qq := q.L1 * q.R with hqq
  have hqpos : 0 < qq := by positivity
  have hLp : 0 < q.L0 + q.L1 * q.M := by positivity
  have hans : ∀ k query seed, oracle.answer k (0, query) seed =
      answerOf q.toPublic I.grad I.prox I.ψ query := by
    intro k query seed
    cases query with
    | gradient x => exact hgAns k seed x
    | prox a z v => exact hpAns k seed a z v
    | value x => exact hvAns k seed x
  have hexec (seed : (algorithm q.toPublic).Seed × ((k : ℕ) → oracle.Seed k)) :
      execute oracle (algorithm q.toPublic) (fun _ => N) seed.1 seed.2 =
        stateOutput ((T q.toPublic I.grad I.prox I.ψ)^[N] (initState q.x0)) := by
    rw [execute_eq_of_answer_eq oracle _ hans]
    exact execute_algorithm q.toPublic I.grad I.prox I.ψ N
  have hNreal : (budget q 0 : ℝ) ≤ N := by exact_mod_cast hN
  have hceil : 184 * Real.sqrt ((q.L0 + q.L1 * q.M) * q.R ^ 2 / q.ε) +
      130000 * (1 + qq) * Real.log (2 + qq) ≤ (budget q 0 : ℝ) := by
    unfold budget; exact Nat.le_ceil _
  have hsteps := phaseSteps_le hqpos.le
  have hlogpos := RadiusFreeSherpa.log2q_pos hqpos.le
  have hl1 := RadiusFreeSherpa.one_le_log2q hqpos.le
  have hsq : 0 ≤ Real.sqrt ((q.L0 + q.L1 * q.M) * q.R ^ 2 / q.ε) := Real.sqrt_nonneg _
  have hacc : I.f (stateOutput ((T q.toPublic I.grad I.prox I.ψ)^[N] (initState q.x0))) +
      I.ψ (stateOutput ((T q.toPublic I.grad I.prox I.ψ)^[N] (initState q.x0))) -
      (I.f xs + I.ψ xs) ≤ q.ε := by
    rcases run_dichotomy (p := q.toPublic) H hqq hR hdist N with
      ⟨ph, hstate, hinv⟩ | ⟨z, c1, hc1, hz, hc1le, hstate⟩
    · exfalso
      have h1 := hinv.steps_le
      have : (N : ℝ) ≤ 75000 * (1 + qq) * Real.log (2 + qq) := h1.trans hsteps
      nlinarith [mul_nonneg hqpos.le hlogpos.le]
    · rw [hstate, exitState_eq, T_second_iterate, output_second]
      have hh0pos : 0 < 1 / (q.L0 + q.L1 * q.M) := by positivity
      have hΔpos : 0 < 6 * (q.L0 + q.L1 * q.M) * q.R / q.L1 := by positivity
      have hyp2 : CompositeGeneralized.Hyp I.f I.ψ I.grad univ I.prox q.L0 q.L1 :=
        ⟨hL0, hL1.le, hc, hgrad, hcont, hsmooth, convex_univ, hψc,
          fun a ha z v => ⟨mem_univ _, hprox a ha z v⟩⟩
      have b : CompositeParameterFree.Base I.f I.ψ I.grad univ I.prox q.L0 q.L1 q.R q.M
          (6 * (q.L0 + q.L1 * q.M) * q.R / q.L1) xs z (1 / (q.L0 + q.L1 * q.M)) :=
        ⟨hyp2, hR, H.gxs_le, hΔpos, hh0pos, mem_univ _, hmin, mem_univ _, hz.1,
          hz.gap (p := q.toPublic) H⟩
      set n2 := (N - c1) / 3 with hn2
      have hsuff := CompositeParameterFree.trials_sufficient (ε := q.ε) hLp hL1.le hR hΔpos hh0pos
      have hrej := CompositeParameterFree.rej_bound b n2
      have e1 : 1 / Real.sqrt ((q.L0 + q.L1 * q.M) * (1 / (q.L0 + q.L1 * q.M))) = 1 := by
        rw [mul_one_div, div_self hLp.ne', Real.sqrt_one, div_one]
      have e2 : q.L1 * Real.sqrt (6 * (q.L0 + q.L1 * q.M) * q.R / q.L1 / (q.L0 + q.L1 * q.M)) =
          Real.sqrt (6 * qq) := by
        have hd : 6 * (q.L0 + q.L1 * q.M) * q.R / q.L1 / (q.L0 + q.L1 * q.M) = 6 * q.R / q.L1 := by
          field_simp
        rw [hd, show q.L1 * Real.sqrt (6 * q.R / q.L1) =
          Real.sqrt (q.L1 ^ 2) * Real.sqrt (6 * q.R / q.L1) by rw [Real.sqrt_sq hL1.le],
          ← Real.sqrt_mul (by positivity)]
        congr 1; rw [hqq]; field_simp
      have e3 : 1 / (16 * (q.L0 + q.L1 * q.M) * (1 / (q.L0 + q.L1 * q.M))) = 1 / 16 := by
        field_simp
      have e4 : 22 * q.L1 ^ 2 * (6 * (q.L0 + q.L1 * q.M) * q.R / q.L1) / (q.L0 + q.L1 * q.M) =
          132 * qq := by
        rw [hqq]; field_simp; ring
      have e5 : 1 / (q.L0 + q.L1 * q.M) *
          (40 * (q.L0 + q.L1 * q.M) + 400 * q.L1 ^ 2 * (6 * (q.L0 + q.L1 * q.M) * q.R / q.L1)) =
          40 + 2400 * qq := by
        rw [hqq]; field_simp; ring
      have e6 : 1 + 32 * q.L1 * q.R = 1 + 32 * qq := by rw [hqq]; ring
      have e7 : 200 * q.L1 ^ 2 * q.R ^ 2 = 200 * qq ^ 2 := by rw [hqq]; ring
      have e8 : 35 + 1067 * q.L1 * q.R = 35 + 1067 * qq := by rw [hqq]; ring
      have e9 : 12 + 400 * q.L1 * q.R = 12 + 400 * qq := by rw [hqq]; ring
      rw [e1, e2, e3, e4, e5, e6, e7, e8, e9] at hsuff
      have hp2 := phase2_bound_le (A := (q.L0 + q.L1 * q.M) * q.R ^ 2 / q.ε) hqpos.le
      have hn2real : 3 * (n2 : ℝ) ≥ (N : ℝ) - c1 - 2 := by
        have h1 : 3 * n2 + 2 ≥ N - c1 := by omega
        have h2 : (c1 : ℝ) ≤ N := by exact_mod_cast hc1
        have h3 : ((N - c1 : ℕ) : ℝ) = (N : ℝ) - c1 := by push_cast [Nat.cast_sub hc1]; ring
        have h4 : ((3 * n2 + 2 : ℕ) : ℝ) ≥ ((N - c1 : ℕ) : ℝ) := by exact_mod_cast h1
        push_cast at h4
        linarith
      have hformula : 4 + 61 * Real.sqrt ((q.L0 + q.L1 * q.M) * q.R ^ 2 / q.ε) +
          (35 + 1067 * qq) * Real.log (1 + (12 + 400 * qq) * (1 + 1 + Real.sqrt (6 * qq))) +
          4 * Real.log (5 / 2 + 1 / 16 + 132 * qq) +
          2 * Real.log (2 * ((1 + (40 + 2400 * qq)) * (8 * (1 + 32 * qq) ^ 2 + 200 * qq ^ 2))) ≤
          (n2 : ℝ) := by
        nlinarith [mul_nonneg hqpos.le hlogpos.le]
      have hacc2 : 1 + CompositeParameterFree.L0c (q.L0 + q.L1 * q.M)
            (CompositeParameterFree.Amin (q.L0 + q.L1 * q.M) q.L1
              (6 * (q.L0 + q.L1 * q.M) * q.R / q.L1) (1 / (q.L0 + q.L1 * q.M))) +
          4 / 3 * (4 * Real.sqrt 32 * Real.sqrt ((q.L0 + q.L1 * q.M) * q.R ^ 2 / q.ε) +
            (1 + CompositeParameterFree.ρc q.L1 q.R) / CompositeParameterFree.ρc q.L1 q.R *
              Real.log (1 + CompositeParameterFree.δc (q.L0 + q.L1 * q.M) /
                CompositeParameterFree.ρc q.L1 q.R /
                Real.sqrt (CompositeParameterFree.Amin (q.L0 + q.L1 * q.M) q.L1
                  (6 * (q.L0 + q.L1 * q.M) * q.R / q.L1) (1 / (q.L0 + q.L1 * q.M))))) ≤
          (CompositeParameterFree.acc I.grad I.prox z (1 / (q.L0 + q.L1 * q.M)) n2 : ℝ) := by
        linarith
      have hA := CompositeParameterFree.run_accuracy b hε le_rfl n2 hacc2
      have hinv := CompositeParameterFree.run_inv b n2
      obtain ⟨-, -, -, hΦ, -, -, -⟩ := hinv
      set st := CompositeParameterFree.run I.grad I.prox z (1 / (q.L0 + q.L1 * q.M)) n2 with hst
      clear_value st
      have hgap0 : 0 ≤ I.f st.x + I.ψ st.x - (I.f xs + I.ψ xs) := by
        have := hmin (mem_univ st.x)
        simp only [mem_ofPred_eq] at this
        change I.f xs + I.ψ xs ≤ I.f st.x + I.ψ st.x at this
        linarith
      have h1 : st.A * (I.f st.x + I.ψ st.x - (I.f xs + I.ψ xs)) ≤ q.R ^ 2 := by
        have := sq_nonneg ‖st.z - xs‖
        linarith
      have h2 : q.R ^ 2 / q.ε * (I.f st.x + I.ψ st.x - (I.f xs + I.ψ xs)) ≤ q.R ^ 2 :=
        (mul_le_mul_of_nonneg_right hA hgap0).trans h1
      rw [div_mul_eq_mul_div, div_le_iff₀ hε] at h2
      have hR2 : 0 < q.R ^ 2 := by positivity
      exact le_of_mul_le_mul_left h2 hR2
  refine ⟨xs, hmin, Filter.Eventually.of_forall fun seed => ?_⟩
  show objective I (execute oracle (algorithm q.toPublic) (fun _ => N) seed.1 seed.2) -
    objective I xs ≤ q.ε
  rw [hexec seed]
  exact hacc

end OracleTemplate.CompositeSherpa
