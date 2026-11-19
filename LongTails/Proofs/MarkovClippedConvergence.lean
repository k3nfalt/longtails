import LongTails.Proofs.MarkovClippedExpectation
import LongTails.Proofs.MarkovClippedDescent

open OracleTemplate MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.MarkovClippedConvergence

open LongTails.Setups.MarkovSmoothNonconvex LongTails.Algorithms.MarkovClippedSgd
open MarkovClippedExpectation MarkovClippedTuning MarkovClippedExecution MarkovClippedDescent
open LongTails.Setups.HeavyTailedMarkovSmoothAndConvex (pathLaw)
open MixedNoise HeavyTailedMarkovGradient

lemma accuracy (p : Params) (hv : spec.valid p) (f : Space p → ℝ)
    (O : Oracle (Space p) (Space p)) (ha : spec.admissible p f O) :
    spec.successful p f (fun s : (algorithm p).Seed × ((k : ℕ) → O.Seed k) =>
      execute O (algorithm p) (fun _ => (steps p + 1) * period p) s.1 s.2)
      ⟨((algorithm p).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨hf, hl, hgap, Z, mZ, κ, hκ, π, g, rfl, _, hmix, hg, hi, hmean, hmi, hm⟩ := ha
  let P : ProbabilityMeasure (ℕ → Z) := pathLaw κ π
  let K := steps p
  let η := stepSize p
  let C := threshold p
  let m := period p
  let X := fun k (z : ℕ → Z) => iterate p g z k
  let U := fun k z => ‖gradient f (X k z)‖
  let S := fun k (z : ℕ → Z) => score p (gradient f (X k z)) (g (X k z) (z (k * m)))
  obtain ⟨_, hC, hη, _⟩ := constants p hv
  have hε := hv.2.1
  have hx k : Measurable (X k) := point_measurable hg η C m p.x0 k
  have hgr := (AbcSgdRate.gradient_continuous hl).measurable
  have hu k : Measurable (U k) := (hgr.comp (hx k)).norm
  have hui k : Integrable (U k) (P : Measure _) :=
    Integrable.of_bound (hu k).aestronglyMeasurable (gradBound p f k) (.of_forall fun z => by
      simpa only [Real.norm_eq_abs, U, abs_norm] using grad_bound p hv hl g z k)
  have hsi k : Integrable (S k) (P : Measure _) := by
    have hpair := (hgr.comp (hx k)).prodMk (hg.comp ((hx k).prodMk (measurable_pi_apply (k*m))))
    have hsm := (score_measurable p).comp hpair
    change Measurable (S k) at hsm
    apply Integrable.of_bound hsm.aestronglyMeasurable
      (p.L * η / 2 * C ^ 2 + (C + p.ε / 4) * gradBound p f k + p.ε ^ 2 / 8)
    apply Filter.Eventually.of_forall
    intro z
    have hc : 0 ≤ C + p.ε / 4 := add_nonneg hC.le (by positivity)
    have hh := mul_le_mul_of_nonneg_left (grad_bound p hv hl g z k) hc
    exact (score_bound p hv _ _).trans (by linarith only [hh])
  have hs k : (∫ z, S k z ∂(P : Measure _)) ≤ 0 :=
    expected_score p hv κ π hmix hl hg hi hmean hmi hm k
  let F := fun z => ∑ k ∈ Finset.range (K+1), U k z
  let H := fun z => ∑ k ∈ Finset.range (K+1), S k z
  have hF : Integrable F (P : Measure _) := integrable_finsetSum _ fun k _ => hui k
  have hH : Integrable H (P : Measure _) := integrable_finsetSum _ fun k _ => hsi k
  have hH0 : (∫ z, H z ∂(P : Measure _)) ≤ 0 := by
    dsimp only [H]
    rw [integral_finsetSum _ (fun k _ => hsi k)]
    exact Finset.sum_nonpos fun k _ => hs k
  have hpath (z : ℕ → Z) : η * (p.ε / 4) * F z ≤
      (p.Δ + η * (K+1 : ℕ) * p.ε ^ 2 / 8) + η * H z := by
    have h := sum_descent hf hl hη.le C p.ε g m p.x0 z (K+1)
    change f (X (K+1) z) + η * (p.ε / 4) * F z ≤
      f p.x0 + η * H z + η * (K+1 : ℕ) * p.ε ^ 2 / 8 at h
    linarith only [h, hgap (X (K+1) z)]
  have hav := integral_mono (hF.const_mul (η * (p.ε / 4)))
    ((integrable_const _).add (hH.const_mul η)) hpath
  simp only [Pi.add_apply] at hav
  rw [integral_const_mul, integral_add (integrable_const (p.Δ + η * (K+1 : ℕ) * p.ε ^ 2 / 8)) (hH.const_mul η),
    integral_const, probReal_univ, one_smul, integral_const_mul] at hav
  have hsum : (∫ z, F z ∂(P : Measure _)) ≤ (K+1 : ℕ) * p.ε := by
    have hbudget := steps_suffice p hv
    change p.Δ ≤ (K+1 : ℕ) * η * p.ε ^ 2 / 8 at hbudget
    apply le_of_mul_le_mul_left (a := η * (p.ε / 4))
    · nlinarith only [hav, hbudget, mul_nonpos_of_nonneg_of_nonpos hη.le hH0]
    · exact mul_pos hη (div_pos hε (by norm_num))
  let μ : Measure (Fin (K+1)) := (PMF.uniformOfFintype _).toMeasure
  let Q : Measure (Fin (K+1) × (ℕ → Z)) := μ.prod (P : Measure (ℕ → Z))
  let Y := fun z : Fin (K+1) × (ℕ → Z) => U z.1.val z.2
  have hy : Measurable Y := measurable_from_prod_countable_right fun i => hu i.val
  have hyi : Integrable Y Q := by
    refine Integrable.of_bound hy.aestronglyMeasurable (gradBound p f K) (.of_forall fun z => ?_)
    have hle : (z.1.val : ℝ) ≤ K := by exact_mod_cast Nat.le_of_lt_succ z.1.isLt
    have hbd := grad_bound p hv hl g z.2 z.1.val
    have hmono := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hη.le) hC.le) hv.1.le
    change |‖gradient f (X z.1.val z.2)‖| ≤ _
    rw [abs_norm]
    exact hbd.trans (by unfold gradBound; linarith only [hmono])
  have he : (∫ z, Y z ∂Q) ≤ p.ε := by
    rw [integral_prod _ hyi, integral_uniform_finite, Fintype.card_fin]
    rw [← integral_finsetSum _ (fun i _ => hui i.val)]
    change ((K+1 : ℕ) : ℝ)⁻¹ * (∫ z, ∑ i : Fin (K+1), U i.val z ∂(P : Measure _)) ≤ p.ε
    have heq (z : ℕ → Z) : (∑ i : Fin (K+1), U i.val z) = F z :=
      Fin.sum_univ_eq_sum_range (fun k => U k z) (K+1)
    simp_rw [heq]
    rw [inv_mul_le_iff₀ (by positivity)]
    exact hsum
  have hout (s : Fin (K+1) × (ℕ → Z)) := execute_spaced P g η C K m (period_pos_and_mix p hv).1
    p.x0 s.2 s.1
  change spec.successful p f (fun s : Fin (K+1) × (ℕ → Z) =>
    execute { Seed := fun _ => Z, law := P, answer := fun _ (_, x) y => g x y } (spaced m (clipped η C K p.x0)) (fun _ => (K+1)*m) s.1 s.2) _
  simp only [hout]
  exact ⟨measurable_from_prod_countable_right fun i => hx i.val, hyi, he⟩

end LongTails.Proofs.MarkovClippedConvergence
