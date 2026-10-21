import LongTails.Proofs.GeneralCovarianceReverseFisherStep
import LongTails.Proofs.Execution

set_option linter.unusedSectionVars false

open MeasureTheory OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Proofs.GeneralCovarianceReverseFisherConvergence

open LongTails.Setups.GeneralCovarianceReverseFisher
open LongTails.Algorithms.GeneralCovarianceReverseFisherGD
open LongTails.Proofs.GeneralCovarianceReverseFisherDescent
open LongTails.Proofs.GeneralCovarianceReverseFisherRate
open LongTails.Proofs.GeneralCovarianceReverseFisherStep

lemma stepSize_pos (p : Params) (hlo : 0 < p.lower) : 0 < stepSize p := by
  unfold stepSize
  have hn1 : (1 : ℝ) ≤ p.components := by exact_mod_cast p.components.pos
  have := Real.log_nonneg hn1
  have : (0 : ℝ) < p.components := by linarith
  positivity

lemma algorithm_gdFamily (p : Params) (hlo : 0 < p.lower) : gdFamily p (algorithm p) :=
  ⟨id, fun _ => stepSize p, fun _ => stepSize_pos p hlo, fun _ => rfl, fun _ => rfl,
    fun _ _ => rfl, fun _ => rfl⟩

noncomputable def gdMap {p : Params} (M : Model p) (θ : Means p) : Means p :=
  θ - stepSize p • gradient (loss M) θ

lemma execute_eq (p : Params) (M : Model p) (oracle : Oracle (Means p) (Means p))
    (h : ∀ k query seed, oracle.answer k query seed = gradient (loss M) query.2) (K : ℕ)
    (seed : (algorithm p).Seed) (ξ : (k : ℕ) → oracle.Seed k) :
    execute oracle (algorithm p) (fun _ => K) seed ξ =
      (gdMap M)^[K] (WithLp.toLp 2 p.start) := by
  rw [execute_eq_of_answer_eq oracle (gradient (loss M)) (fun k q s => h k (0, q) s),
    execute_iterate]
  rfl

lemma vnorm_nonneg {p : Params} (M : Model p) (Y : Fin p.components → Space p) :
    0 ≤ vnorm M.covarianceRoot Y :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem iterate_accuracy (p : Params) (hp : spec.valid p) (M : Model p)
    (hs : spectralBounds p M) (hst : startBound p M) (K : ℕ)
    (hK : (1 + 8 * Real.log p.components) * (p.upper / p.lower) ^ 2 *
      (2 * Real.log (1 + p.radius ^ 2 / p.lower) +
        4 * p.components * min (p.components : ℝ) p.dimension * p.upper / p.accuracy) + 1 ≤ K)
    (i : Fin p.components) :
    ‖((gdMap M)^[K] (WithLp.toLp 2 p.start)) i - M.target‖ ^ 2 ≤ p.accuracy := by
  rcases hp with ⟨hlo, hlh, hR, hε⟩
  have hhi : 0 < p.upper := lt_of_lt_of_le hlo hlh
  set A := M.covarianceRoot
  set t := M.target
  set n : ℝ := (p.components : ℝ)
  have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr p.components.pos
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  set V : ℕ → ℝ := fun k => vnorm A (fun i => ((gdMap M)^[k] (WithLp.toLp 2 p.start)) i - t)
  set kd : ℕ := min (p.components : ℕ) (Module.finrank ℝ (Space p))
  have hfin : Module.finrank ℝ (Space p) = p.dimension := finrank_euclideanSpace_fin
  have hkd : (kd : ℝ) = min (p.components : ℝ) p.dimension := by
    simp only [kd, hfin, Nat.cast_min]
  have hkd1 : (1 : ℝ) ≤ kd := by
    rw [hkd]
    exact le_min hn1 (by exact_mod_cast p.dimension.pos)
  set N : ℝ := n * kd
  set a : ℝ := p.lower ^ 2 / ((1 + 8 * Real.log n) * p.upper ^ 2)
  have hN : 0 < N := by positivity
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : p.lower ^ 2 ≤ p.upper ^ 2 := pow_le_pow_left₀ hlo.le hlh 2
    nlinarith [sq_nonneg p.upper]
  have h0 : ∀ k, 0 ≤ V k := fun k => vnorm_nonneg M _
  have hrec : ∀ k, V (k + 1) ≤ V k - a * min (V k / 2) (V k ^ 2 / (4 * N)) := by
    intro k
    have := gd_step M hs hlo hlh ((gdMap M)^[k] (WithLp.toLp 2 p.start))
    simp only [V, Function.iterate_succ_apply']
    exact this
  set B : ℝ := 1 + p.radius ^ 2 / p.lower
  have hB : 1 ≤ B := by
    have : 0 ≤ p.radius ^ 2 / p.lower := by positivity
    linarith
  have hl := lower_bound_symm M hs hlo
  have hV0 : V 0 ≤ 2 * N * B := by
    have h1 : V 0 ≤ n * (p.radius ^ 2 / p.lower) := by
      simp only [V, Function.iterate_zero, id, vnorm]
      calc ∑ i, ‖A.symm ((WithLp.toLp 2 p.start : Means p) i - t)‖ ^ 2
          ≤ ∑ _i : Fin p.components, p.radius ^ 2 / p.lower := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            rw [le_div_iff₀ hlo]
            have e1 := hl ((WithLp.toLp 2 p.start : Means p) i - t)
            have e2 : ‖(WithLp.toLp 2 p.start : Means p) i - t‖ ^ 2 ≤ p.radius ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (hst i) 2
            nlinarith
        _ = n * (p.radius ^ 2 / p.lower) := by simp [n]
    have h2 : n * (p.radius ^ 2 / p.lower) ≤ 2 * N * B := by
      have hr : 0 ≤ p.radius ^ 2 / p.lower := by positivity
      have hnk : 0 ≤ n * kd := by positivity
      calc n * (p.radius ^ 2 / p.lower) ≤ n * (p.radius ^ 2 / p.lower) * kd :=
            le_mul_of_one_le_right (by positivity) hkd1
        _ ≤ 2 * N * B := by
            simp only [N, B]
            nlinarith [mul_nonneg hnk hr]
    linarith
  have hε' : 0 < p.accuracy / p.upper := by positivity
  have hKr : 2 / a * Real.log B + 4 * N / (a * (p.accuracy / p.upper)) + 1 ≤ K := by
    refine le_trans (le_of_eq ?_) hK
    simp only [a, N, B, hkd]
    field_simp
    ring
  have hVK := rate ha0 ha1 hN h0 hrec hB hV0 hε' K hKr
  have hi : ‖A.symm (((gdMap M)^[K] (WithLp.toLp 2 p.start)) i - t)‖ ^ 2 ≤ V K :=
    Finset.single_le_sum
      (f := fun j => ‖A.symm (((gdMap M)^[K] (WithLp.toLp 2 p.start)) j - t)‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hu := upper_bound_symm M hs hhi (((gdMap M)^[K] (WithLp.toLp 2 p.start)) i - t)
  have : p.upper * V K ≤ p.accuracy := by
    rw [le_div_iff₀ hhi] at hVK; linarith
  nlinarith

theorem output_success (p : Params) (hp : spec.valid p) (M : Model p)
    (oracle : Oracle (Means p) (Means p)) (ho : spec.admissible p M oracle) (K : ℕ)
    (hK : (1 + 8 * Real.log p.components) * (p.upper / p.lower) ^ 2 *
      (2 * Real.log (1 + p.radius ^ 2 / p.lower) +
        4 * p.components * min (p.components : ℝ) p.dimension * p.upper / p.accuracy) + 1 ≤ K) :
    spec.successful p M
      (fun z : (algorithm p).Seed × ((k : ℕ) → oracle.Seed k) =>
        execute oracle (algorithm p) (fun _ => K) z.1 z.2)
      ⟨((algorithm p).law : Measure _).prod (oracle.law : Measure _), inferInstance⟩ := by
  rcases ho with ⟨hs, hst, horacle⟩
  intro ω i
  show ‖(execute oracle (algorithm p) (fun _ => K) ω.1 ω.2) i - M.target‖ ^ 2 ≤ p.accuracy
  rw [execute_eq p M oracle horacle K ω.1 ω.2]
  exact iterate_accuracy p hp M hs hst K hK i

end LongTails.Proofs.GeneralCovarianceReverseFisherConvergence
