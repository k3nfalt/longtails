import LongTails.Proofs.MarkovQuadraticWeightedAverageEnergy
import LongTails.Algorithms.MarkovQuadraticWeightedAverage
import Mathlib.Analysis.Convex.Jensen

open MeasureTheory ProbabilityTheory Function Preorder
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.MarkovQuadraticWeightedAverage

open MarkovQuadratic MarkovProduct LongTails.Setups.MarkovQuadraticInterpolation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma execute_output {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure (ℕ → Ω))
    (g : E → Ω → E) (L α : ℝ) (x0 : E) (K : ℕ) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) z => g x z }
      (algorithm L α x0) (fun _ => K) () ξ = output α x0 (iterate g L⁻¹ x0 ξ) K := by
  let A := algorithm L α x0
  let x := iterate g L⁻¹ x0 ξ
  let state := fun k : ℕ => (k, x k, ∑ j ∈ Finset.range (k - 1), x (j+1))
  have hs (k : ℕ) : A.update (state k) (g (A.query (state k)).2 (ξ k)) = state (k+1) := by
    cases k with
    | zero => simp [A, algorithm, state, x, iterate]
    | succ k => simp [A, algorithm, state, x, iterate, Finset.sum_range_succ]; abel
  have ha (n k : ℕ) : StochasticGradient.advance
      (fun j z => A.update z (g (A.query z).2 (ξ j))) n k (state k) = state (k+n) := by
    induction n generalizing k with
    | zero => rfl
    | succ n ih =>
      change StochasticGradient.advance _ n (k+1) (A.update (state k)
        (g (A.query (state k)).2 (ξ k))) = _
      rw [hs, ih]
      congr 1
      omega
  erw [StochasticGradient.execute_advance]
  change A.output (StochasticGradient.advance _ K 0 (state 0)) = _
  rw [ha, Nat.zero_add]
  rfl

open LongTails.Setups.HeavyTailedMarkovSmoothAndConvex (pathLaw)

variable {q : Params} {m : ℕ} {π : ProbabilityMeasure (Fin m)}
  {κ : Kernel (Fin m) (Fin m)} {H : Fin m → q.E →L[ℝ] q.E}
  {f : q.E → ℝ} {u : q.E}

private lemma convex_gap (h : Model q m π κ H f u) :
    ConvexOn ℝ Set.univ (fun x => f x - f u) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [h.population, finite_integral, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [show a • x + b • y - u = a • (x-u) + b • (y-u) by
    rw [show b = 1-a by linarith]; module]
  let X := x-u
  let Y := y-u
  have hd := mul_nonneg (mul_nonneg ha hb) (h.positive i (X-Y))
  have he : ⟪a • X + b • Y, H i (a • X + b • Y)⟫ ≤
      a * ⟪X,H i X⟫ + b * ⟪Y,H i Y⟫ := by
    simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, map_sub, inner_sub_left, inner_sub_right] at hd ⊢
    rw [show b = 1-a by linarith] at hd ⊢
    linarith only [hd]
  have := mul_le_mul_of_nonneg_left he (show 0 ≤ (π : Measure (Fin m)).real {i} from ENNReal.toReal_nonneg)
  dsimp [X,Y] at this
  linarith only [this]

private lemma jensen (h : Model q m π κ H f u) (hα : 0 < q.α) (x : ℕ → q.E) (n : ℕ) :
    f (output q.α q.x0 x (n+1)) - f u ≤
      (1 + q.α * n)⁻¹ * ((f (x (n+1)) - f u) +
        q.α * ∑ j ∈ Finset.range n, (f (x (j+1)) - f u)) := by
  let d := 1 + q.α * n
  have hd : 0 < d := by dsimp [d]; positivity
  have hw : d⁻¹ + ∑ _j ∈ Finset.range n, d⁻¹ * q.α = 1 := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp [hd.ne']
    dsimp [d]
    ring
  have hj := (convex_gap h).map_add_sum_le (p := fun j => x (j+1)) (q := x (n+1))
    (fun j (_ : j ∈ Finset.range n) => mul_nonneg (inv_nonneg.mpr hd.le) hα.le) hw
    (fun _ _ => Set.mem_univ _) (inv_nonneg.mpr hd.le) (Set.mem_univ _)
  rw [add_comm (d⁻¹ • x (n+1))] at hj
  simpa only [output, average, Nat.add_sub_cancel, smul_add, smul_smul, Finset.smul_sum,
    smul_eq_mul, mul_add, ← mul_assoc, Finset.mul_sum, d] using hj

lemma measurable_output (H : Fin m → q.E →L[ℝ] q.E) (u : q.E) (K : ℕ) :
    Measurable (fun ξ => output q.α q.x0 (point q H u ξ) K) := by
  have hx := fun n => measurable_iterate (fun x i => H i (x-u)) (sample_gradient_measurable H u) q.L⁻¹ q.x0 n
  cases K with
  | zero => exact measurable_const
  | succ n =>
    exact ((Finset.measurable_sum _ (fun j _ => hx (j+1))).const_smul q.α |>.add
      (hx (n+1))).const_smul _

private lemma integrable_prefix (P : Measure (ℕ → Fin m)) [IsFiniteMeasure P]
    (n : ℕ) (v : (ℕ → Fin m) → ℝ)
    (hv : ∀ ξ, v (extendHistory (frestrictLe n ξ)) = v ξ) : Integrable v P := by
  have hh := (finite_integrable (P.map (frestrictLe n))
    (fun b => v (extendHistory b))).comp_aemeasurable (by fun_prop : AEMeasurable (frestrictLe n) P)
  simpa only [Function.comp_def, hv] using hh

lemma integrable_output_gap (P : Measure (ℕ → Fin m)) [IsFiniteMeasure P] (K : ℕ) :
    Integrable (fun ξ => f (output q.α q.x0 (point q H u ξ) K) - f u) P := by
  apply integrable_prefix P K
  intro ξ
  have hx (j : ℕ) (hj : j ≤ K) : point q H u (extendHistory (frestrictLe K ξ)) j =
      point q H u ξ j := by
    apply iterate_congr_samples
    intro k hk
    rw [extendHistory_eq _ (by omega : k ≤ K)]
    rfl
  simp only [output, hx K le_rfl]
  congr 3
  apply Finset.sum_congr rfl
  intro j hj
  exact hx _ (by have := Finset.mem_range.mp hj; omega)

lemma output_risk [IsMarkovKernel κ] (h : Model q m π κ H f u) (μ : ProbabilityMeasure (Fin m))
    (hL : 0 < q.L) (hα : 0 < q.α) (n : ℕ) :
    (∫ ξ, f (output q.α q.x0 (point q H u ξ) (n+1)) - f u
      ∂(pathLaw κ μ : Measure (ℕ → Fin m))) ≤ (q.L * q.R^2 / 2) / (1 + q.α * n) := by
  let P := (pathLaw κ μ : Measure (ℕ → Fin m))
  let G := fun k (ξ : ℕ → Fin m) => f (point q H u ξ k) - f u
  let V := fun k (ξ : ℕ → Fin m) => q.L / 2 * ‖point q H u ξ k - u‖^2
  have hstep : q.L⁻¹ * q.L ≤ 2 := by simp [hL.ne']
  have hiG (k : ℕ) : Integrable (G k) P :=
    h.integrable_iterate_gap hL (inv_nonneg.mpr hL.le) hstep P k
  have hiV (k : ℕ) : Integrable (V k) P := by
    apply integrable_prefix P k
    intro ξ
    simp only [V, point, iterate_prefix]
  have ht (k : ℕ) : q.α * ∑ j ∈ Finset.range k, (∫ ξ, G (j+1) ξ ∂P) +
      (∫ ξ, V (k+1) ξ ∂P) ≤ q.L * q.R^2 / 2 := by
    induction k with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero, zero_add]
      have hb (ξ : ℕ → Fin m) : V 1 ξ ≤ q.L * q.R^2 / 2 := by
        have hr := h.iterate_radius hL (inv_nonneg.mpr hL.le) hstep ξ 1
        dsimp only [V, point]
        nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hr 2) hL.le]
      simpa using integral_mono (hiV 1) (integrable_const _) hb
    | succ k ih =>
      have hs := expected_step h μ hL hα.le k
      change (∫ ξ, q.α * G (k+1) ξ + V (k+2) ξ ∂P) ≤ ∫ ξ, V (k+1) ξ ∂P at hs
      rw [integral_add ((hiG _).const_mul _) (hiV _), integral_const_mul] at hs
      rw [Finset.sum_range_succ, mul_add]
      linarith
  have hfin := integral_mono (hiG (n+1)) (hiV (n+1)) (fun ξ => by
    dsimp only [G,V]
    linarith only [h.objective_upper (point q H u ξ (n+1))])
  have hsum := integrable_finsetSum (Finset.range n) (fun j _ => hiG (j+1))
  have hb := integral_mono (integrable_output_gap P (n+1))
    (((hiG (n+1)).add (hsum.const_mul q.α)).const_mul ((1 + q.α * n)⁻¹))
    (fun ξ => jensen h hα (point q H u ξ) n)
  change (∫ ξ, _ ∂P) ≤ ∫ ξ, (1 + q.α * n)⁻¹ *
    (G (n+1) ξ + q.α * ∑ j ∈ Finset.range n, G (j+1) ξ) ∂P at hb
  rw [integral_const_mul, integral_add (hiG _) (hsum.const_mul _), integral_const_mul,
    integral_finsetSum _ (fun j _ => hiG (j+1))] at hb
  refine hb.trans ?_
  rw [div_eq_inv_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith [ht n]

end OracleTemplate.MarkovQuadraticWeightedAverage
