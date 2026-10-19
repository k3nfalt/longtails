import LongTails.Proofs.CharacteristicGradientBounds
import LongTails.Proofs.ZerothOrderExecution

open MeasureTheory Set

namespace LongTails.Proofs.CharacteristicConvergence

open OracleTemplate OracleTemplate.BiasedStochasticGradient
open OracleTemplate.HeavyTailedMarkovGradient

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma projectedRun_congr_ball {g h : E → Ω → E} {D R : ℝ} (hR : 0 ≤ R) (x0 : E)
    (he : ∀ x, ‖x - x0‖ ≤ R → ∀ ω, g x ω = h x ω)
    (K k : ℕ) (x z : E) (hx : ‖x - x0‖ ≤ R) (hz : ‖z - x0‖ ≤ R) (ξ : Fin K → Ω) :
    projectedRun g D R x0 K k x z ξ = projectedRun h D R x0 K k x z ξ := by
  induction K generalizing k x z with
  | zero => rfl
  | succ K ih =>
    have hq := query_ball hx hz k
    have hn := projectedUpdate_ball (D := D) (z := z) hR hx k
      (h (Gradient.acceleratedQuery (k, x, z)) (ξ 0))
    simp only [projectedRun]
    rw [he _ hq]
    exact ih (k + 1) _ _ hn.1 hn.2 _

variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω]

lemma local_projected_expected_rate {f : E → ℝ} {g : E → Ω → E} {p : Measure Ω}
    [IsProbabilityMeasure p] {L D R b v : ℝ}
    (hL : 0 < L) (hD : 0 < D) (hLD : 2 * L ≤ D) (hR : 0 ≤ R) (hb0 : 0 ≤ b) (hv0 : 0 ≤ v)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hG : Measurable (Function.uncurry g)) (x0 u : E)
    (hGi : ∀ x, ‖x - x0‖ ≤ R → Integrable (g x) p)
    (hb : ∀ x, ‖x - x0‖ ≤ R → ‖gradient f x - ∫ ω, g x ω ∂p‖ ≤ b)
    (hvi : ∀ x, ‖x - x0‖ ≤ R → Integrable (fun ω => ‖gradient f x - g x ω‖ ^ 2) p)
    (hv : ∀ x, ‖x - x0‖ ≤ R → (∫ ω, ‖gradient f x - g x ω‖ ^ 2 ∂p) ≤ v)
    (hm : IsMinOn f univ u) (hu : ‖u - x0‖ ≤ R) (K : ℕ) (hK : 0 < K) :
    Integrable (fun ξ => f (projectedRun g D R x0 K 0 x0 x0 ξ).1 - f u)
      (Measure.pi fun _ : Fin K => p) ∧
    (∫ ξ, f (projectedRun g D R x0 K 0 x0 x0 ξ).1 - f u
      ∂Measure.pi (fun _ : Fin K => p)) ≤
      2 * D * R ^ 2 / ((K : ℝ) * ((K : ℝ) + 1)) + 4 * R * b + 4 * (K : ℝ) * v / D := by
  classical
  let g' := fun x ω => if ‖x - x0‖ ≤ R then g x ω else gradient f x
  have hG' : Measurable (Function.uncurry g') := by
    apply Measurable.ite (measurableSet_le (by fun_prop) measurable_const) hG
    exact (measurable_gradient_of_lipschitz hL.le hlip).comp measurable_fst
  have hGi' (x : E) : Integrable (g' x) p := by
    by_cases hx : ‖x - x0‖ ≤ R
    · simpa [g', hx] using hGi x hx
    · simp [g', hx]
  have hb' (x : E) : ‖gradient f x - ∫ ω, g' x ω ∂p‖ ≤ b := by
    by_cases hx : ‖x - x0‖ ≤ R
    · simpa [g', hx] using hb x hx
    · simpa [g', hx] using hb0
  have hvi' (x : E) : Integrable (fun ω => ‖gradient f x - g' x ω‖ ^ 2) p := by
    by_cases hx : ‖x - x0‖ ≤ R
    · simpa [g', hx] using hvi x hx
    · simp [g', hx]
  have hv' (x : E) : (∫ ω, ‖gradient f x - g' x ω‖ ^ 2 ∂p) ≤ v := by
    by_cases hx : ‖x - x0‖ ≤ R
    · simpa [g', hx] using hv x hx
    · simpa [g', hx] using hv0
  have hr := projected_expected_rate hL hD hLD hR hb0 hv0 hc hg hlip hG' hGi' hb' hvi' hv'
    x0 u hm hu K hK
  have he (ξ : Fin K → Ω) : projectedRun g' D R x0 K 0 x0 x0 ξ =
      projectedRun g D R x0 K 0 x0 x0 ξ :=
    projectedRun_congr_ball hR x0 (fun x hx ω => by simp [g', hx]) K 0 x0 x0
      (by simpa using hR) (by simpa using hR) ξ
  simp_rw [he] at hr
  exact hr

end LongTails.Proofs.CharacteristicConvergence

namespace LongTails.Proofs.CharacteristicConvergence

open OracleTemplate OracleTemplate.BiasedStochasticGradient
open OracleTemplate.HeavyTailedMarkovGradient
open LongTails.Setups.QuantileSymmetricRemainderConvex
open LongTails.Algorithms.CharacteristicGradient
open CharacteristicGradientBounds

lemma output_expected {d K N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {p : Measure Ω} [IsProbabilityMeasure p] {f : Space d → ℝ} {g : Space d → Ω → Space d}
    {L D R t r M : ℝ} (hL : 0 < L) (hD : 0 < D) (hLD : 2 * L ≤ D)
    (hR : 0 ≤ R) (ht : 0 < t) (hr : 0 ≤ r) (hM : 0 ≤ M)
    (htr : t * (2 * L * R + r) ≤ 1 / 4)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hG : Measurable (Function.uncurry g)) (x0 u : Space d)
    (hm : IsMinOn f univ u) (hu : ‖u - x0‖ ≤ R)
    (hnoise : ∀ x i, NoiseCondition ((p : Measure Ω).map (fun ω => (g x ω - gradient f x) i)) r M)
    (hN : 0 < N) :
    Integrable (fun ξ => f (output (K := K) g D R t x0 N ξ) - f u)
      (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin K => p) ∧
    (∫ ξ, f (output (K := K) g D R t x0 N ξ) - f u
      ∂Measure.pi (fun _ : Fin N => Measure.pi fun _ : Fin K => p)) ≤
      2 * D * R ^ 2 / ((N : ℝ) * ((N : ℝ) + 1)) +
        4 * R * (Real.sqrt d * (M * t + (1 / 2 : ℝ) ^ K / t)) +
          4 * (N : ℝ) * (4 * d / t ^ 2) / D := by
  have hb (x : Space d) (hx : ‖x - x0‖ ≤ R) :=
    batch_bounds (K := K) (hG.comp (measurable_const.prodMk measurable_id)) ht hr hM
      (fun i => (show |gradient f x i| ≤ ‖gradient f x‖ by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (gradient f x) i).trans
          (gradient_ball hL hg hlip hm hu hx)) htr (hnoise x)
  apply local_projected_expected_rate hL hD hLD hR (by positivity) (by positivity)
    hc hg hlip (measurable_batch_oracle hG t) x0 u
  · exact fun x hx => (hb x hx).1
  · intro x hx
    rw [norm_sub_rev]
    exact (hb x hx).2.1
  · intro x hx
    simpa only [batchedOracle, Function.comp_apply, Function.uncurry_apply_pair, id_eq, norm_sub_rev (gradient f x)] using (hb x hx).2.2.1
  · intro x hx
    simpa only [batchedOracle, Function.comp_apply, Function.uncurry_apply_pair, id_eq, norm_sub_rev (gradient f x)] using (hb x hx).2.2.2
  · exact hm
  · exact hu
  · exact hN

lemma execute_output {d K : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (hK : 0 < K) (P : ProbabilityMeasure (ℕ → Ω)) (g : Space d → Ω → Space d)
    (D R t : ℝ) (x0 : Space d) (N : ℕ) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      (algorithm hK D R t x0) (fun _ => N * K) () ξ =
        output (K := K) g D R t x0 N (fun n j => ξ (n.val * K + j.val)) := by
  unfold algorithm
  erw [execute_batched]
  have he := OracleTemplate.ZerothOrder.advance_projected (batchedOracle (K := K) g t) D R x0
    (fun n j => ξ (n * K + j.val)) N 0 0 x0 x0
  simpa only [Nat.zero_add, projectedAccelerated, output, batchedOracle] using
    congrArg (fun s => s.2.1) he

end LongTails.Proofs.CharacteristicConvergence

namespace LongTails.Proofs.CharacteristicConvergence

open OracleTemplate OracleTemplate.BiasedStochasticGradient
open LongTails.Setups.QuantileSymmetricRemainderConvex
open LongTails.Algorithms.CharacteristicGradient

lemma stream_expected {d K N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (p : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) (p : Measure _) (P : Measure _))
    (g : Space d → Ω → Space d) (hG : Measurable (Function.uncurry g))
    (D R t : ℝ) (x0 u : Space d) (f : Space d → ℝ) (B : ℝ)
    (ha : Integrable (fun ξ => f (output (K := K) g D R t x0 N ξ) - f u)
      (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin K => (p : Measure _)) ∧
      (∫ ξ, f (output (K := K) g D R t x0 N ξ) - f u
        ∂Measure.pi (fun _ : Fin N => Measure.pi fun _ : Fin K => (p : Measure _))) ≤ B) :
    let result := fun s : Unit × (ℕ → Ω) =>
      output (K := K) g D R t x0 N (fun n j => s.2 (n.val * K + j.val))
    Measurable result ∧ Integrable (fun s => f (result s) - f u)
      ((Measure.dirac () : Measure Unit).prod (P : Measure _)) ∧
      (∫ s, f (result s) - f u ∂((Measure.dirac () : Measure Unit).prod (P : Measure _))) ≤ B := by
  let block := fun ξ : ℕ → Ω => fun n : Fin N => fun j : Fin K => ξ (n.val * K + j.val)
  have hi := OracleTemplate.FiniteVariance.infinite_block_law
    (p : Measure Ω) (P : Measure (ℕ → Ω)) hs.independent hs.marginal K
  have hp := OracleTemplate.StochasticGradient.prefix_measurePreserving
    (Measure.pi fun _ : Fin K => (p : Measure Ω)) N
  have hb : MeasurePreserving block (P : Measure (ℕ → Ω))
      (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin K => (p : Measure Ω)) := hp.comp hi
  have ho : Measurable (output (K := K) g D R t x0 N) :=
    ((measurable_projectedRun (g := batchedOracle (K := K) g t)
      (CharacteristicGradientBounds.measurable_batch_oracle (K := K) hG t)
      D R x0 N 0).comp
        (measurable_const.prodMk measurable_id : Measurable (fun ξ : Fin N → Fin K → Ω => ((x0, x0), ξ)))).fst
  have hdrop : MeasurePreserving (fun s : Unit × (ℕ → Ω) => s.2)
      ((Measure.dirac () : Measure Unit).prod (P : Measure _)) (P : Measure _) :=
    measurePreserving_snd
  have hm := hb.comp hdrop
  exact ⟨ho.comp hm.measurable, hm.integrable_comp_of_integrable ha.1,
    (OracleTemplate.ZerothOrder.integral_comp_preserving hm ha.1).trans_le ha.2⟩

end LongTails.Proofs.CharacteristicConvergence
