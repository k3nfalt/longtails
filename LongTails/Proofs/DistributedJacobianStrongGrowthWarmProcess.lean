import LongTails.Proofs.DistributedJacobianStrongGrowthMedian
import LongTails.Proofs.LocalNonlinearExtragradientSampling

open MeasureTheory

namespace LongTails.Proofs.DistributedJacobianStrongGrowthWarmProcess

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradient
open LongTails.Algorithms.DistributedLocalExtragradientWarmStart
open LongTails.Algorithms.DistributedQuantization

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma measurable_quantize (d width : ℕ) (spacing : ℝ) :
    Measurable (quantize d width spacing) := by
  apply Measurable.of_eval
  intro j
  have hx : Measurable (fun x : EuclideanSpace ℝ (Fin d) => x j) :=
    (measurable_pi_apply j).comp (WithLp.measurable_ofLp 2 _)
  have hf := Nat.measurable_floor.comp
    ((hx.div_const spacing).add_const (((2 ^ width - 1 : ℕ) : ℝ) / 2))
  let code : ℕ → Fin (2 ^ width) := fun m =>
    ⟨min m (2 ^ width - 1), lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt (by positivity) (by decide))⟩
  exact (measurable_of_countable code).comp hf

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma measurable_warmPoint (p : Params) (s : ℕ)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (i : Fin p.n) :
    Measurable (warmPoint p s g i) := by
  have hread : Measurable (fun samples : ℕ → p.Ω => fun j => samples (p.n * j + i.val)) :=
    Measurable.of_eval fun j => measurable_pi_apply _
  have hw := (LocalNonlinearExtragradientSampling.measurable_warmRun
    (p.μ / (p.ρ * p.L ^ 2)) (g i) p.x0 (hg i) s).comp hread
  convert! (DistributedJacobianStrongGrowthProjection.measurable_projectBall p p.R).comp
    (measurable_const.prodMk hw) using 1

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma measurable_warmCodes (p : Params) (s width : ℕ) (spacing : ℝ)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) :
    Measurable (warmCodes p s width spacing g) := by
  apply Measurable.of_eval
  intro i
  exact (measurable_quantize p.d width spacing).comp ((measurable_warmPoint p s g hg i).sub_const p.x0)

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma measurable_warmCenter (p : Params) (s width : ℕ) (spacing : ℝ)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) :
    Measurable (warmCenter p s width spacing g) := by
  have hf : Measurable (fun codes : Fin p.n → Grid p.d width =>
      projectBall p p.x0 p.R (p.x0 + reconstruct spacing (medianGrid codes))) :=
    measurable_of_countable _
  convert! hf.comp (measurable_warmCodes p s width spacing g hg) using 1

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma warmCenter_prefix (p : Params) (s width : ℕ) (spacing : ℝ)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples other : ℕ → p.Ω)
    (heq : ∀ j < p.n * s, samples j = other j) :
    warmCenter p s width spacing g samples = warmCenter p s width spacing g other := by
  have hp (i : Fin p.n) : warmPoint p s g i samples = warmPoint p s g i other := by
    apply congrArg (projectBall p p.x0 p.R)
    apply LocalNonlinearExtragradientSampling.warmRun_prefix
    intro k hk
    apply heq
    calc
      p.n * k + i.val < p.n * k + p.n := Nat.add_lt_add_left i.isLt _
      _ = p.n * (k + 1) := by ring
      _ ≤ p.n * s := Nat.mul_le_mul_left _ (by omega)
  have hcodes : warmCodes p s width spacing g samples = warmCodes p s width spacing g other := by
    funext i
    exact congrArg (quantize p.d width spacing) (congrArg (fun x => x - p.x0) (hp i))
  exact congrArg (fun codes => projectBall p p.x0 p.R (p.x0 + reconstruct spacing (medianGrid codes))) hcodes

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma warmCenter_factor (p : Params) (s width : ℕ) (spacing : ℝ)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (default : p.Ω) (hR : 0 ≤ p.R) :
    ∃ center : (Fin (p.n * s) → p.Ω) → Point p,
      Measurable center ∧ (∀ z, ‖center z - p.x0‖ ≤ p.R) ∧
        ∀ samples : ℕ → p.Ω, center (fun i => samples i.val) = warmCenter p s width spacing g samples := by
  let extend : (Fin (p.n * s) → p.Ω) → ℕ → p.Ω :=
    fun z j => if hj : j < p.n * s then z ⟨j, hj⟩ else default
  have hm : Measurable extend := by
    apply Measurable.of_eval
    intro j
    by_cases hj : j < p.n * s
    · simpa only [extend, dite_eq_left hj] using
        (measurable_pi_apply (⟨j, hj⟩ : Fin (p.n * s)))
    · simpa only [extend, dite_eq_right hj] using
        (measurable_const : Measurable (fun _ : Fin (p.n * s) → p.Ω => default))
  refine ⟨fun z => warmCenter p s width spacing g (extend z),
    (measurable_warmCenter p s width spacing g hg).comp hm,
    fun z => DistributedJacobianStrongGrowthMedian.warmCenter_global p s width spacing g (extend z) hR, ?_⟩
  intro samples
  apply warmCenter_prefix
  intro j hj
  simp only [extend, dite_eq_left hj]

end LongTails.Proofs.DistributedJacobianStrongGrowthWarmProcess
