import LongTails.Setups.TailObliviousMonotoneRootFinding
import LongTails.Proofs.TailObliviousLaw
import LongTails.Proofs.TailObliviousBudget

open MeasureTheory OracleTemplate

namespace LongTails.Theorems.TailObliviousRootFinding

open LongTails.Setups.TailObliviousMonotoneRootFinding
open LongTails.Algorithms.TailObliviousExtragradient
open LongTails.Proofs.TailObliviousProcess LongTails.Proofs.TailObliviousAccuracy
open LongTails.Proofs.TailObliviousExecution LongTails.Proofs.TailObliviousLaw
open LongTails.Proofs.TailObliviousBudget

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈2 ^ 20 * (1 + q.L * q.R / q.ε) * (64 * (q.α / (q.α - 1)) ^ 2 * (1 + Real.log (1 + q.L * q.R / q.ε + q.σ / q.ε))) ^ 2 + 2 ^ (20 / (q.α - 1)) * (q.σ / q.ε) ^ (q.α / (q.α - 1)) * (64 * (q.α / (q.α - 1)) ^ 2 * (1 + Real.log (1 + q.L * q.R / q.ε + q.σ / q.ε))) ^ (2 * q.α / (q.α - 1))⌉₊

theorem result : Convergence LongTails.Setups.TailObliviousMonotoneRootFinding.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  rintro q ⟨hL, hα1, hα2, hσ, hR, hε⟩ F O
    ⟨g, p, P, hIID, rfl, hmono, hlip, ⟨xstar, hstar, hdist⟩, hg⟩
  set X := 2 ^ 20 * (1 + q.L * q.R / q.ε) *
    (64 * (q.α / (q.α - 1)) ^ 2 * (1 + Real.log (1 + q.L * q.R / q.ε + q.σ / q.ε))) ^ 2 +
    2 ^ (20 / (q.α - 1)) * (q.σ / q.ε) ^ (q.α / (q.α - 1)) *
    (64 * (q.α / (q.α - 1)) ^ 2 * (1 + Real.log (1 + q.L * q.R / q.ε + q.σ / q.ε))) ^
      (2 * q.α / (q.α - 1)) with hXdef
  set M := ⌈X⌉₊ with hMdef
  have hα0 : 0 < q.α - 1 := by linarith
  have hβ2 : 2 ≤ q.α / (q.α - 1) := by rw [le_div_iff₀ hα0]; linarith
  have hLR : 0 ≤ q.L * q.R / q.ε := by positivity
  have hσε : 0 ≤ q.σ / q.ε := by positivity
  have hlog : 0 ≤ Real.log (1 + q.L * q.R / q.ε + q.σ / q.ε) := Real.log_nonneg (by linarith)
  have hbig : (1048576 : ℝ) ≤ X := by
    have hZ : 1 ≤ 64 * (q.α / (q.α - 1)) ^ 2 * (1 + Real.log (1 + q.L * q.R / q.ε + q.σ / q.ε)) := by
      nlinarith
    have h1 : (1 : ℝ) ≤ (64 * (q.α / (q.α - 1)) ^ 2 *
        (1 + Real.log (1 + q.L * q.R / q.ε + q.σ / q.ε))) ^ 2 := one_le_pow₀ hZ
    have h2 : 0 ≤ 2 ^ (20 / (q.α - 1)) * (q.σ / q.ε) ^ (q.α / (q.α - 1)) *
        (64 * (q.α / (q.α - 1)) ^ 2 * (1 + Real.log (1 + q.L * q.R / q.ε + q.σ / q.ε))) ^
          (2 * q.α / (q.α - 1)) := by positivity
    rw [hXdef]
    nlinarith
  have hXM : X ≤ (M : ℝ) := Nat.le_ceil X
  have hMX : (M : ℝ) ≤ 2 * X := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ X)
    linarith
  have hM192 : 192 ≤ M := by
    have : (192 : ℝ) ≤ M := by linarith
    exact_mod_cast this
  obtain ⟨K, hlow, hhigh⟩ := exists_epoch M hM192
  have hF : Problem q.toPublic F := ⟨hL, hmono, hlip⟩
  have hbound := budget_accuracy q.toPublic hL q.R q.σ q.α q.ε hR hσ hα1 hα2 hε M K hlow hhigh
    hXM hMX
  let O' : Oracle q.E q.E :=
    { Seed := fun _ => q.Ω
      law := P
      answer := fun _ (_, x) seed => g x seed }
  have hexec (ξ : ℕ → q.Ω) : execute O' (algorithm q.toPublic) (fun _ => M) () ξ =
      epochOutput q.toPublic g K (blocks K (2 * epochOffset K) ξ) := by
    erw [OracleTemplate.StochasticGradient.execute_advance]
    exact best_after g ξ (K + 1) M hlow hhigh
  let z := fun ξ : ℕ → q.Ω => epochOutput q.toPublic g K (blocks K (2 * epochOffset K) ξ)
  have hΦ := epoch_blocks_law (p : Measure q.Ω) (P : Measure (ℕ → q.Ω)) hIID K (epochOffset K)
  have hacc := epoch_accuracy hF p g q.σ q.α q.R hσ hg hα1 hα2 xstar hstar hdist K
  have hzm : Measurable z := hacc.1.comp hΦ.measurable
  have hFc : Continuous F := (LipschitzWith.of_dist_le_mul (K := ⟨q.L, hL.le⟩) (by
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    exact hlip x y)).continuous
  have hfm : Measurable (fun w : q.E => ‖F w‖ ^ q.α) := (hFc.measurable.norm.pow_const q.α)
  have hzi : Integrable (fun ξ => ‖F (z ξ)‖ ^ q.α) (P : Measure (ℕ → q.Ω)) :=
    hΦ.integrable_comp_of_integrable hacc.2.1
  have hzint : (∫ ξ, ‖F (z ξ)‖ ^ q.α ∂(P : Measure (ℕ → q.Ω))) ≤ q.ε ^ q.α := by
    have he := integral_map (μ := (P : Measure (ℕ → q.Ω))) hΦ.measurable.aemeasurable
      ((hfm.comp hacc.1).aestronglyMeasurable)
    rw [hΦ.map_eq] at he
    calc (∫ ξ, ‖F (z ξ)‖ ^ q.α ∂(P : Measure (ℕ → q.Ω)))
        = ∫ ζ, ‖F (epochOutput q.toPublic g K ζ)‖ ^ q.α ∂streamLaw p K := he.symm
      _ ≤ accuracyBound q.toPublic q.R q.σ q.α K := hacc.2.2
      _ ≤ q.ε ^ q.α := hbound
  change Measurable (fun seed : Unit × (ℕ → q.Ω) =>
      execute O' (algorithm q.toPublic) (fun _ => M) seed.1 seed.2) ∧
    Integrable (fun seed : Unit × (ℕ → q.Ω) =>
      ‖F (execute O' (algorithm q.toPublic) (fun _ => M) seed.1 seed.2)‖ ^ q.α)
      ((Measure.dirac ()).prod (P : Measure _)) ∧
    (∫ seed : Unit × (ℕ → q.Ω),
      ‖F (execute O' (algorithm q.toPublic) (fun _ => M) seed.1 seed.2)‖ ^ q.α
      ∂(Measure.dirac ()).prod (P : Measure _)) ≤ q.ε ^ q.α
  have he (seed : Unit × (ℕ → q.Ω)) :
      execute O' (algorithm q.toPublic) (fun _ => M) seed.1 seed.2 = z seed.2 := by
    rcases seed with ⟨⟨⟩, ξ⟩
    exact hexec ξ
  simp_rw [he]
  refine ⟨hzm.comp measurable_snd, ?_, ?_⟩
  · exact (measurePreserving_snd (μ := Measure.dirac ())
      (ν := (P : Measure (ℕ → q.Ω)))).integrable_comp_of_integrable hzi
  · rw [integral_fun_snd (fun ξ => ‖F (z ξ)‖ ^ q.α)]
    simpa using hzint

end LongTails.Theorems.TailObliviousRootFinding
