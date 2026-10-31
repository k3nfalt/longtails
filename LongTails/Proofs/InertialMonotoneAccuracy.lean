import LongTails.Setups.StochasticLipschitzMonotone
import LongTails.Proofs.InertialMonotoneIteration
import LongTails.Proofs.InertialMonotoneSchedule

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.InertialMonotone

open LongTails.Setups.StochasticLipschitzMonotone

lemma finite_accuracy (q : Params) (hL : 0 < q.L) (hR : 0 ≤ q.R) (hε : 0 < q.ε)
    (F : q.E → q.E) (hm : ∀ a b, 0 ≤ ⟪F a - F b, a - b⟫)
    (hlip : ∀ a b, ‖F a - F b‖ ≤ q.L * ‖a - b‖)
    (p : ProbabilityMeasure q.Ω) (g : q.E → q.Ω → q.E)
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator (p : Measure _) F g q.σ)
    (xs : q.E) (hxs : F xs = 0) (hxs0 : ‖q.x0 - xs‖ ≤ q.R) :
    let N := horizon q.L q.R q.ε
    let μ := regularization q.L N
    let η := stepSize q.L N
    let r := growth N
    let b := batchSize q.σ q.ε N
    let output := fun ξ => (finiteRun g μ η r b (q.x0, q.x0) N ξ).2
    Measurable output ∧
      Integrable (fun ξ => ‖F (output ξ)‖ ^ 2) (Measure.pi fun _ : Fin (calls b N) => (p : Measure _)) ∧
      (∫ ξ, ‖F (output ξ)‖ ^ 2 ∂Measure.pi (fun _ : Fin (calls b N) => (p : Measure _))) ≤ q.ε ^ 2 := by
  intro N μ η r b output
  have hN : 4096 ≤ N := horizon_large hL.le hR hε
  have hN0 : 0 < N := by omega
  have hc : Continuous F := (LipschitzWith.of_dist_le_mul (K := ⟨q.L, hL.le⟩)
    (fun a b => by
      simp only [dist_eq_norm]
      change ‖F a - F b‖ ≤ q.L * ‖a - b‖
      exact hlip a b)).continuous
  have hμ (k : ℕ) (hk : k ≤ N) : 0 < μ k := regularization_pos hL hN0 hk
  have hi := finiteRun_energy_bound hc hm hg hlip μ η r b (q.x0, q.x0) N hμ
    (fun k hk => (growth_bounds hk).1) (fun k hk => (growth_bounds hk).2.2)
    (fun _ _ => rfl) (fun k hk => schedule_cap hL hN hk)
    (fun k _ => batchSize_pos q.σ q.ε N k)
    (fun k hk => regularization_update q.L hk) N le_rfl
  have hout : Measurable output := (finiteRun_measurable hg.measurable μ η r b (q.x0, q.x0) N).snd
  have hf : Measurable (fun ξ => ‖F (output ξ)‖ ^ 2) := (hc.measurable.comp hout).norm.pow_const 2
  have hpt (ξ) : ‖F (output ξ)‖ ^ 2 ≤
      2 * energy F hc hm (μ N) (hμ N le_rfl) (finiteRun g μ η r b (q.x0, q.x0) N ξ) :=
    energy_residual F hc hm (μ N) (hμ N le_rfl) hL.le
      (regularization_terminal_ge hL.le hN) hlip _
  have hfi := (hi.1.const_mul 2).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hpt ξ))
  refine ⟨hout, hfi, ?_⟩
  have hh := integral_mono hfi (hi.1.const_mul 2) hpt
  rw [integral_const_mul] at hh
  have hinit := energy_initial F hc hm (μ 0) (hμ 0 (Nat.zero_le N)) q.x0 xs hxs hxs0
  have hsum : (∑ k ∈ Finset.range N, 14 * (r k) ^ 2 * (q.σ ^ 2 / b k)) =
      14 * ∑ k ∈ Finset.range N, (r k) ^ 2 * (q.σ ^ 2 / b k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hib := hi.2
  rw [hsum] at hib
  have hfinal := schedule_accuracy (σ := q.σ) hL.le hR hε
  change 4 * (μ 0) ^ 2 * q.R ^ 2 +
    28 * (∑ k ∈ Finset.range N, (r k) ^ 2 * (q.σ ^ 2 / b k)) ≤ q.ε ^ 2 at hfinal
  linarith

lemma execution_accuracy (q : Params) (hL : 0 < q.L) (hR : 0 ≤ q.R) (hε : 0 < q.ε)
    (F : q.E → q.E) (hm : ∀ a b, 0 ≤ ⟪F a - F b, a - b⟫)
    (hlip : ∀ a b, ‖F a - F b‖ ≤ q.L * ‖a - b‖)
    (p : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure _) (P : Measure _))
    (g : q.E → q.Ω → q.E)
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator (p : Measure _) F g q.σ)
    (xs : q.E) (hxs : F xs = 0) (hxs0 : ‖q.x0 - xs‖ ≤ q.R)
    (K : ℕ) (hK : calls (batchSize q.σ q.ε (horizon q.L q.R q.ε)) (horizon q.L q.R q.ε) ≤ K) :
    let O : Oracle q.E q.E :=
      { Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
    Measurable (fun ξ => terminalPoint q.L q.R q.σ q.ε q.x0 O K ((), ξ)) ∧
      Integrable (fun ξ => ‖F (terminalPoint q.L q.R q.σ q.ε q.x0 O K ((), ξ))‖ ^ 2) (P : Measure _) ∧
      (∫ ξ, ‖F (terminalPoint q.L q.R q.σ q.ε q.x0 O K ((), ξ))‖ ^ 2 ∂(P : Measure _)) ≤ q.ε ^ 2 := by
  dsimp only
  simp_rw [terminalPoint_eq q.L q.R q.σ q.ε q.x0 g P K hK]
  have ha := finite_accuracy q hL hR hε F hm hlip p g hg xs hxs hxs0
  have hi := iid_run_integral hIID g (regularization q.L (horizon q.L q.R q.ε))
    (stepSize q.L (horizon q.L q.R q.ε)) (growth (horizon q.L q.R q.ε))
    (batchSize q.σ q.ε (horizon q.L q.R q.ε)) (q.x0, q.x0) (horizon q.L q.R q.ε)
    (fun state => ‖F state.2‖ ^ 2) ha.2.1
  refine ⟨?_, hi.1, hi.2.trans_le ha.2.2⟩
  have hout := ha.1.comp (show Measurable (fun ξ : ℕ → q.Ω =>
    fun i : Fin (calls (batchSize q.σ q.ε (horizon q.L q.R q.ε)) (horizon q.L q.R q.ε)) => ξ i) by fun_prop)
  simpa only [runPlan_eval_finiteRun, Nat.zero_add, Function.comp_def] using hout

end OracleTemplate.InertialMonotone
