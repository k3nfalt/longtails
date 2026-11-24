import LongTails.Proofs.HeavyTailNcscTwoPoint
import LongTails.TemplateLowerBound

open MeasureTheory OracleTemplate

namespace LongTails.Proofs.HeavyTailNcscLowerAssembly

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open LongTails.Setups.HighDimensionalHeavyTailedNcsc
open LongTails.Proofs.HeavyTailNcscChain LongTails.Proofs.HeavyTailNcscTwoPoint
open LongTails.Proofs.AbcLowerParameters

noncomputable def chainPart (q : Params) : ℝ :=
  q.L * q.Δ / q.ε ^ 2 * (1 + (Real.sqrt (q.L / q.μ) * (q.σ / q.ε) / 2 ^ 14) ^ (q.p / (q.p - 1)))

noncomputable def pointPart (q : Params) : ℝ :=
  (q.L / q.μ * (q.σ / q.ε) / 2 ^ 5) ^ (q.p / (q.p - 1))

section

variable {q : Params} (hv : spec.valid q)
include hv

lemma A_nonneg : 0 ≤ q.L * q.Δ / q.ε ^ 2 := by
  have hreg : 2 ^ 32 * q.ε ^ 2 ≤ q.L * q.Δ := hv.2.2.2.1
  have : 0 ≤ q.L * q.Δ := le_trans (by positivity) hreg
  positivity

lemma chainPart_nonneg : 0 ≤ chainPart q := by
  unfold chainPart
  have := A_nonneg hv
  have hσ := sigma_nonneg hv
  have hε := eps_pos hv
  have : 0 ≤ (Real.sqrt (q.L / q.μ) * (q.σ / q.ε) / 2 ^ 14) ^ (q.p / (q.p - 1)) :=
    Real.rpow_nonneg (by positivity) _
  positivity

lemma pointPart_nonneg : 0 ≤ pointPart q := by
  unfold pointPart
  have hσ := sigma_nonneg hv
  have hε := eps_pos hv
  have hμ := mu_pos hv
  have hL := L_pos hv
  exact Real.rpow_nonneg (by positivity) _

lemma d_pos : 0 < q.d := by
  have hd := hv.2.2.2.2.2
  have hσ := sigma_nonneg hv
  have hε := eps_pos hv
  have hX : 0 ≤ q.L * q.Δ / q.ε ^ 2 *
      (1 + (Real.sqrt (q.L / q.μ) * (q.σ / q.ε)) ^ (q.p / (q.p - 1))) := by
    have := A_nonneg hv
    have : 0 ≤ (Real.sqrt (q.L / q.μ) * (q.σ / q.ε)) ^ (q.p / (q.p - 1)) :=
      Real.rpow_nonneg (by positivity) _
    positivity
  have h1 : (1 : ℝ) ≤ (1 + q.L * q.Δ / q.ε ^ 2 *
      (1 + (Real.sqrt (q.L / q.μ) * (q.σ / q.ε)) ^ (q.p / (q.p - 1)))) ^ 4 :=
    one_le_pow₀ (by linarith)
  have : (0 : ℝ) < q.d := by nlinarith
  exact_mod_cast this

lemma chain_budget_le (N : ℕ) (hN : N ≤ ⌊chainPart q / 2 ^ 60⌋₊) :
    N ≤ lowerBudget (chainParams q) := by
  refine hN.trans (Nat.floor_le_floor ?_)
  have hε := eps_pos hv
  have hσ := sigma_nonneg hv
  have hA := A_nonneg hv
  have hK := KK_nonneg hv
  have hs : 0 ≤ Real.sqrt (q.L / q.μ) * (q.σ / q.ε) := by positivity
  have hx : (Real.sqrt (q.L / q.μ) * (q.σ / q.ε) / 2 ^ 14) ^ (q.p / (q.p - 1)) ≤ KK q ^ rr q := by
    apply Real.rpow_le_rpow (by positivity) _ (le_trans (by norm_num : (0 : ℝ) ≤ 2) (rr_ge_two hv))
    unfold KK
    apply div_le_div_of_nonneg_left hs (by norm_num) (by norm_num)
  have hKr : 0 ≤ KK q ^ rr q := Real.rpow_nonneg hK _
  change chainPart q / 2 ^ 60 ≤ q.L * (25 * q.Δ / 1152) *
    (1 + 0 + 0 * (25 * q.Δ / 1152) / q.ε ^ 2 + 2 * 1740 ^ 2 * q.ε ^ 2 * KK q ^ rr q / q.ε ^ 2) /
      (2 ^ 53 * q.ε ^ 2)
  have he : q.L * (25 * q.Δ / 1152) *
      (1 + 0 + 0 * (25 * q.Δ / 1152) / q.ε ^ 2 + 2 * 1740 ^ 2 * q.ε ^ 2 * KK q ^ rr q / q.ε ^ 2) /
        (2 ^ 53 * q.ε ^ 2) =
      25 / 1152 * (q.L * q.Δ / q.ε ^ 2) * (1 + 2 * 1740 ^ 2 * KK q ^ rr q) / 2 ^ 53 := by
    field_simp
    ring
  rw [he]
  unfold chainPart
  change q.L * q.Δ / q.ε ^ 2 * (1 + (Real.sqrt (q.L / q.μ) * (q.σ / q.ε) / 2 ^ 14) ^ (q.p / (q.p - 1))) /
      2 ^ 60 ≤ _
  have h1 : 1 + (Real.sqrt (q.L / q.μ) * (q.σ / q.ε) / 2 ^ 14) ^ (q.p / (q.p - 1)) ≤
      1 + 2 * 1740 ^ 2 * KK q ^ rr q := by
    have hx' : (Real.sqrt (q.L / q.μ) * (q.σ / q.ε) / 2 ^ 14) ^ rr q ≤ KK q ^ rr q := hx
    change 1 + (Real.sqrt (q.L / q.μ) * (q.σ / q.ε) / 2 ^ 14) ^ rr q ≤ _
    nlinarith [hx', hKr]
  have h2 := mul_le_mul_of_nonneg_left h1 hA
  have h3 : 0 ≤ q.L * q.Δ / q.ε ^ 2 * (1 + 2 * 1740 ^ 2 * KK q ^ rr q) := by positivity
  rw [div_le_iff₀ (by positivity)]
  nlinarith

lemma two_theta : q.σ / (2 * th q) = 5 / 96 * (q.L / q.μ * (q.σ / q.ε)) := by
  unfold th m1 Yv
  have hμ := mu_pos hv
  have hL := L_pos hv
  have hε := eps_pos hv
  field_simp
  ring

lemma point_budget (N : ℕ) (hN : N ≤ ⌊(chainPart q + pointPart q) / 2 ^ 61⌋₊)
    (hbig : ⌊chainPart q / 2 ^ 60⌋₊ < N) : (N : ℝ) ≤ TT q / 2 := by
  have hX := chainPart_nonneg hv
  have hY := pointPart_nonneg hv
  have h1 : chainPart q / 2 ^ 60 < N := (Nat.floor_lt (by positivity)).mp hbig
  have h2 : (N : ℝ) ≤ (chainPart q + pointPart q) / 2 ^ 61 :=
    (Nat.cast_le.mpr hN).trans (Nat.floor_le (by positivity))
  rw [div_lt_iff₀ (by positivity)] at h1
  rw [le_div_iff₀ (by positivity)] at h2
  have h3 : (N : ℝ) ≤ pointPart q / 2 := by nlinarith
  refine h3.trans ?_
  have hσ := sigma_nonneg hv
  have hε := eps_pos hv
  have hμ := mu_pos hv
  have hL := L_pos hv
  have h4 : pointPart q ≤ TT q := by
    unfold pointPart TT
    rw [two_theta hv]
    apply Real.rpow_le_rpow (by positivity) _ (le_trans (by norm_num : (0 : ℝ) ≤ 2) (rr_ge_two hv))
    have : 0 ≤ q.L / q.μ * (q.σ / q.ε) := by positivity
    nlinarith
  linarith

end

lemma nonConvergence :
    NonConvergence spec (fun q _ => ⌊(chainPart q + pointPart q) / 2 ^ 61⌋₊) := by
  intro q hv A _ b hb
  have heq : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  rw [heq]
  by_cases hsmall : b 0 ≤ ⌊chainPart q / 2 ^ 60⌋₊
  · obtain ⟨π, hπ⟩ := chain_failure hv A (b 0) (chain_budget_le hv _ hsmall)
    exact ⟨liftedF q hv π, liftOracle q hv π, lifted_admissible hv π, hπ⟩
  · push Not at hsmall
    have hd := d_pos hv
    obtain ⟨s, hs, hfail⟩ := tp_failure hv hd A (b 0) (point_budget hv (b 0) (hb 0) hsmall)
    exact ⟨tpF q hd s, tpOracle q hd s, tp_admissible hv hd s hs, hfail⟩

end LongTails.Proofs.HeavyTailNcscLowerAssembly
