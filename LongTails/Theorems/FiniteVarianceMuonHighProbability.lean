import LongTails.Setups.FiniteVarianceSpectralSmooth
import LongTails.Proofs.MuonConvergence
import LongTails.Proofs.MatrixPolarCharacterization
import LongTails.Proofs.Execution

namespace LongTails.Theorems.FiniteVarianceMuonHighProbability

open MeasureTheory OracleTemplate
open LongTails.Setups.FiniteVarianceSpectralSmooth LongTails.Setups.MatrixGeometry
open LongTails.Algorithms.ValidatedMuon LongTails.Proofs

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => if 2 * p.L * p.Δ ≤ p.ε ^ 2 then 0 else ⌈2 ^ 45 * (1 + p.s ^ 2 / p.ε ^ 2) * (1 + p.L * p.Δ / p.ε ^ 2 + Real.sqrt (1 + p.L * p.Δ / p.ε ^ 2) * Real.log (2 ^ 56 * (1 + p.s ^ 2 / p.ε ^ 2) * (1 + p.L * p.Δ / p.ε ^ 2) / p.δ) ^ 2)⌉₊

theorem result : Convergence LongTails.Setups.FiniteVarianceSpectralSmooth.spec budget := by
  classical
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p => finiteVarianceMuon p.L p.Δ p.s p.ε p.δ p.x0, ?_,
    MuonConvergence.finiteVarianceMuon_allowed⟩
  intro p hp f O hadm
  rcases hp with ⟨hL, hΔ, hs, hε, hδ, hδ1⟩
  rcases hadm with ⟨hgrad, hlip, ⟨fmin, hmin, hgap⟩, model, P, hIID, rfl⟩
  let succeeds (A : Algorithm (Space p.m p.n) (Space p.m p.n) (Space p.m p.n)) : Prop :=
    let O : Oracle (Space p.m p.n) (Space p.m p.n) :=
      { Seed := fun _ => model.Ω, law := P, answer := fun _ (_, x) ω => model.sample x ω }
    spec.successful p f
      (fun z : A.Seed × (ℕ → model.Ω) => execute O A (fun _ => budget p 0) z.1 z.2)
      ⟨(A.law : Measure _).prod (P : Measure _), inferInstance⟩
  change succeeds (finiteVarianceMuon p.L p.Δ p.s p.ε p.δ p.x0)
  by_cases hcase : 2 * p.L * p.Δ ≤ p.ε ^ 2
  · have hh := MuonConvergence.initial_success p
      { Seed := fun _ => model.Ω, law := P, answer := fun _ (_, x) ω => model.sample x ω }
      hL hε hgrad hlip hmin hgap hcase
    have hAlg : finiteVarianceMuon p.L p.Δ p.s p.ε p.δ p.x0 = returnInitial p.x0 := by
      simp only [finiteVarianceMuon, ite_eq_left hcase]
    rw [hAlg]
    simpa only [succeeds, budget, ite_eq_left hcase] using hh
  · let e := p.ε / 8
    let γ := p.δ / 4
    let D := p.L * p.Δ / e ^ 2
    let a := max 1 (4096 * p.s ^ 2 / e ^ 2)
    let H := Real.log (1073741824 * a * D / γ)
    let T := ⌈1048576 * a * (D + Real.sqrt D * H ^ 2)⌉₊
    let q := ⌈Real.log (1 / γ) / Real.log 2⌉₊
    let b := max 1 ⌈144 * p.s ^ 2 / e ^ 2⌉₊
    let k := ⌈8 * Real.log ((q : ℝ) / γ)⌉₊
    let N := budget p 0
    have he : 0 < e := by dsimp [e]; positivity
    have hγ : 0 < γ := by dsimp [γ]; positivity
    have hγ1 : γ < 1 := by dsimp [γ]; linarith
    have hparams := MuonTuning.hard_parameter_bounds (s := p.s) hL hΔ hε hδ hδ1 (lt_of_not_ge hcase)
    have hLp : 0 < p.L := hparams.1
    have hΔp : 0 < p.Δ := hparams.2.1
    have hD : 1 ≤ D := hparams.2.2.1
    have ha : 1 ≤ a := hparams.2.2.2.1
    have hH : 1 ≤ H := hparams.2.2.2.2.1
    have hnoise : 4096 * p.s ^ 2 ≤ a * e ^ 2 := hparams.2.2.2.2.2.1
    have hscale : p.L * p.Δ = D * e ^ 2 := hparams.2.2.2.2.2.2.1
    have hexp : Real.exp H = 1073741824 * a * D / γ := hparams.2.2.2.2.2.2.2
    have hTb := MuonTuning.training_count_bounds ha hD hH
    have hqb := MuonTuning.validation_draw_bounds ha hD hH hγ hγ1 hexp
    have hbb := MuonTuning.validation_batch_bounds he ha hnoise
    have hkb := MuonTuning.validation_block_bounds ha hD hH hγ hγ1 hqb.1 hqb.2.1 hexp
    have hT : T - 1 + 1 = T := Nat.sub_add_cancel hTb.1
    have hq : q - 1 + 1 = q := Nat.sub_add_cancel hqb.1
    have hk : k - 1 + 1 = k := Nat.sub_add_cancel hkb.1
    have hcost := MuonTuning.total_cost_bound ha hD hH hqb.2.1 hbb.2.2 hkb.2.1
    let A := 1 + p.s ^ 2 / p.ε ^ 2
    let R := 1 + p.L * p.Δ / p.ε ^ 2
    let J := Real.log (72057594037927936 * A * R / p.δ)
    have hcomp := MuonTuning.public_parameter_comparison (s := p.s) hε hδ (mul_pos hLp hΔp)
    have hpublic := MuonTuning.public_budget_domination (by linarith : 0 ≤ D)
      (by linarith : 0 ≤ H) (show 0 ≤ A by dsimp [A]; positivity) hcomp.1 hcomp.2.1 hcomp.2.2
    have hN : (b * (k - 1 + 1)) * (q - 1 + 1) + (T - 1 + 1) ≤ N := by
      rw [hT, hq, hk]
      have hh : T + q * b * k ≤ N := by
        apply hcost.trans
        simpa only [N, budget, ite_eq_right hcase, A, R, J,
          show (2 : ℝ) ^ 45 = 35184372088832 by norm_num,
          show (2 : ℝ) ^ 56 = 72057594037927936 by norm_num] using hpublic
      have hc : b * k * q + T = T + q * b * k := by ring
      rw [hc]
      exact hh
    have hacc := MuonConvergence.execution_accuracy model P hIID hLp hs hΔp he ha hD hH hγ hγ1
      hscale hnoise hexp hgrad hlip hmin p.x0 hgap
      (T := T - 1) (q := q - 1) (b := b) (k := k - 1) (N := N)
      hT hq rfl (by rw [hq]; exact hk) hN
    have hTr : ((T - 1 : ℕ) : ℝ) + 1 = T := by exact_mod_cast hT
    dsimp only at hacc
    rw [hTr] at hacc
    have heps : 8 * e = p.ε := by dsimp [e]; ring
    let Alg := validatedMuon (1 / a) (p.Δ / (e * T)) (2 * e / 3) (T - 1) b (k - 1) (q - 1) p.x0
    let O : Oracle (Space p.m p.n) (Space p.m p.n) :=
      { Seed := fun _ => model.Ω, law := P, answer := fun _ (_, x) ω => model.sample x ω }
    let output := fun z : Alg.Seed × (ℕ → model.Ω) => execute O Alg (fun _ => N) z.1 z.2
    have hsuccess : spec.successful p f output
        ⟨(Alg.law : Measure _).prod (P : Measure _), inferInstance⟩ := by
      refine ⟨hacc.1, ?_⟩
      change ((Alg.law : Measure Alg.Seed).prod (P : Measure (ℕ → model.Ω)))
        {z | p.ε < nuclearNorm (gradient f (output z))} ≤ ENNReal.ofReal p.δ
      apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
      rw [ENNReal.toReal_ofReal hδ.le]
      change ((Alg.law : Measure _).prod (P : Measure _)).real
        {z | p.ε < nuclearNorm (gradient f (output z))} ≤ p.δ
      rw [← heps]
      exact hacc.2.trans (by dsimp only [γ]; linarith only [hδ])
    have hAlg : finiteVarianceMuon p.L p.Δ p.s p.ε p.δ p.x0 = Alg := by
      simp only [finiteVarianceMuon, ite_eq_right hcase]
      rfl
    rw [hAlg]
    exact hsuccess

end LongTails.Theorems.FiniteVarianceMuonHighProbability
