import LongTails.Proofs.ReshufflingAffineConvergence
import LongTails.Proofs.ReshufflingTuning
import LongTails.Proofs.QuadraticFiniteSumModel

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.QuadraticReshuffling

open QuadraticFiniteSum
open LongTails.Setups.QuadraticFiniteSum

lemma tuned_objective_accuracy (p : Params) (hp : spec.valid p) (f : Instance p)
    (hs : ∀ i, (f.A i).toLinearMap.IsSymmetric) (hA : ∀ i, ‖f.A i‖ ≤ p.L)
    (hcoercive : ∀ y, p.μ * ‖y‖ ^ 2 ≤ (p.n : ℝ)⁻¹ * ∑ i, ⟪y, f.A i y⟫)
    (u : p.E) (hu : (∑ i, (f.A i u + f.b i)) = 0)
    (hR : ‖p.x0 - u‖ ≤ p.R) (hG : ∀ i, ‖f.A i u + f.b i‖ ≤ p.G) :
    (∫ seed : RandomReshuffling.Seeds p.n (epochCount p),
      objective f (RandomReshuffling.epochs (fun i y => f.A i y + f.b i) (stepSize p)
        (List.ofFn (fun k => List.ofFn (seed k))) p.x0) - objective f u
      ∂(PMF.uniformOfFintype (RandomReshuffling.Seeds p.n (epochCount p))).toMeasure) ≤ p.ε := by
  obtain ⟨hL, hμ, hμL, hR0, hG0, hε⟩ := hp
  let η := stepSize p
  let K := epochCount p
  let C : ℝ := Fintype.card (Equiv.Perm (Fin p.n))
  let r := 1 - η * p.n * p.μ / 2
  let b := fun i => f.A i u + f.b i
  let out := fun seed : RandomReshuffling.Seeds p.n K =>
    RandomReshuffling.epochs (fun i y => f.A i y + f.b i) η
      (List.ofFn (fun k => List.ofFn (seed k))) p.x0
  have hn : (0 : ℝ) < p.n := by exact_mod_cast NeZero.pos p.n
  have hη : 0 < η := stepSize_pos p hL hμ hG0 hε
  have hsmall : η * p.n * p.L ≤ 1 / 32 := stepSize_small p hL hμ hG0 hε
  have hμsmall : η * p.n * p.μ ≤ 1 / 32 :=
    (mul_le_mul_of_nonneg_left hμL (show 0 ≤ η * p.n by positivity)).trans hsmall
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hC : 0 < C := by
    dsimp [C]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Equiv.Perm (Fin p.n)))
  have hsum : ∀ y, (p.n : ℝ) * p.μ * ‖y‖ ^ 2 ≤ ⟪y, (∑ i, f.A i) y⟫ := by
    intro y
    have hh := mul_le_mul_of_nonneg_left (hcoercive y) hn.le
    simp only [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul] at hh
    simpa only [sum_apply, inner_sum, mul_assoc] using hh
  have hshift : ∀ seed : RandomReshuffling.Seeds p.n K,
      out seed - u = RandomReshuffling.epochs (fun i y => f.A i y + b i) η
        (List.ofFn (fun k => List.ofFn (seed k))) (p.x0 - u) := by
    intro seed
    have he := RandomReshuffling.epochs_translate (fun i y => f.A i y + f.b i)
      (fun i y => f.A i y + b i) η (List.ofFn (fun k => List.ofFn (seed k))) u (p.x0 - u)
      (by intro i y; simp only [map_add, b, add_assoc])
    simpa only [sub_add_cancel, add_sub_cancel_right, out] using congrArg (fun y => y - u) he
  have hdist := Reshuffling.affine_epochs_energy (NeZero.pos p.n) f.A b hL hμ hμL hη.le
    hs hA hsum hu hG hsmall K (p.x0 - u)
  change (∑ seed : RandomReshuffling.Seeds p.n K,
    ‖RandomReshuffling.epochs (fun i y => f.A i y + b i) η
      (List.ofFn (fun k => List.ofFn (seed k))) (p.x0 - u)‖ ^ 2) ≤ _ at hdist
  simp_rw [← hshift] at hdist
  have hinit : p.L * p.R ^ 2 / 2 * r ^ K ≤ p.ε / 2 :=
    initialization_tuning p hL hμ hμL hG0 hε
  have hbias : 512 * η ^ 2 * p.L ^ 3 * p.G ^ 2 / p.μ ^ 2 ≤ p.ε / 8 := bias_tuning p hL hμ hG0 hε
  have hvar : 4 * η ^ 3 * (p.n : ℝ) ^ 2 * p.L ^ 3 * p.G ^ 2 / p.μ ≤ p.ε / 16 :=
    variance_tuning p hL hμ hG0 hε
  have hraw : (∑ seed : RandomReshuffling.Seeds p.n K, (objective f (out seed) - objective f u)) ≤
      C ^ K * p.ε := by
    calc
      _ ≤ ∑ seed : RandomReshuffling.Seeds p.n K, p.L * ‖out seed - u‖ ^ 2 / 2 :=
        Finset.sum_le_sum (fun seed _ => objective_upper f hs hA hu (out seed))
      _ = p.L / 2 * ∑ seed : RandomReshuffling.Seeds p.n K, ‖out seed - u‖ ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro seed hseed
        ring
      _ ≤ p.L / 2 * (C ^ K * (r ^ K * ‖p.x0 - u‖ ^ 2 +
          1024 * η ^ 2 * p.L ^ 2 * p.G ^ 2 / p.μ ^ 2 +
          8 * η ^ 3 * (p.n : ℝ) ^ 2 * p.L ^ 2 * p.G ^ 2 / p.μ)) :=
        mul_le_mul_of_nonneg_left hdist (by positivity)
      _ ≤ C ^ K * (p.L * p.R ^ 2 / 2 * r ^ K +
          512 * η ^ 2 * p.L ^ 3 * p.G ^ 2 / p.μ ^ 2 +
          4 * η ^ 3 * (p.n : ℝ) ^ 2 * p.L ^ 3 * p.G ^ 2 / p.μ) := by
        have hi := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hR 2)
          (show 0 ≤ p.L / 2 * C ^ K * r ^ K by positivity)
        convert add_le_add_right hi
          (C ^ K * (512 * η ^ 2 * p.L ^ 3 * p.G ^ 2 / p.μ ^ 2 +
            4 * η ^ 3 * (p.n : ℝ) ^ 2 * p.L ^ 3 * p.G ^ 2 / p.μ)) using 1 <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hinit, hbias, hvar, hε]) (pow_nonneg hC.le K)
  have hcard : (Fintype.card (RandomReshuffling.Seeds p.n K) : ℝ) = C ^ K := by
    simp only [RandomReshuffling.Seeds, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, C]
  change (∫ seed : RandomReshuffling.Seeds p.n K, objective f (out seed) - objective f u
    ∂(PMF.uniformOfFintype (RandomReshuffling.Seeds p.n K)).toMeasure) ≤ p.ε
  have hint : (∫ seed : RandomReshuffling.Seeds p.n K, objective f (out seed) - objective f u
      ∂(PMF.uniformOfFintype (RandomReshuffling.Seeds p.n K)).toMeasure) =
      (C ^ K)⁻¹ * ∑ seed : RandomReshuffling.Seeds p.n K, (objective f (out seed) - objective f u) := by
    simp [PMF.integral_eq_sum, PMF.uniformOfFintype_apply, ← Finset.mul_sum, hcard]
  rw [hint]
  calc
    _ ≤ (C ^ K)⁻¹ * (C ^ K * p.ε) := mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hC.ne'), one_mul]

end OracleTemplate.QuadraticReshuffling
