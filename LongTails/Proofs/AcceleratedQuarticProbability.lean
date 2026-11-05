import LongTails.Proofs.AcceleratedQuarticExecution
import LongTails.Proofs.SvrgConvex

set_option synthInstance.maxSize 256

namespace LongTails.Proofs.AcceleratedQuarticProbability

open LongTails.Algorithms.AcceleratedQuarticNewton LongTails.Algorithms.QuarticProximalTrial
open OracleTemplate OracleTemplate.QueryPlan
open scoped BigOperators Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ} [NeZero n]

lemma run_failure (ε R Q L γ : ℝ) (x0 : E)
    (oracle : Fin n × E → LongTails.Algorithms.TaylorCorrectedNewton.Reply E)
    (P : ℕ → Status E → Prop) {δ : ℝ} (hδ : 0 ≤ δ) (N : ℕ)
    (hstep : ∀ j < N, ∀ status, P j status →
      (𝔼 seed : Fin (64 * logarithm Q) → StageSeed n (24 * logarithm Q),
        (if ¬P (j + 1) (eval oracle (round ε R Q L γ x0 seed status)) then (1 : ℝ) else 0)) ≤ δ) :
    ∀ K j, j + K ≤ N → ∀ status, P j status →
      (𝔼 seeds : Fin K → Fin (64 * logarithm Q) → StageSeed n (24 * logarithm Q),
        (if ¬P (j + K) (eval oracle (run ε R Q L γ x0 K seeds status)) then (1 : ℝ) else 0)) ≤ K * δ := by
  intro K
  induction K with
  | zero =>
    intro j _ status hp
    simp only [run, eval, Nat.add_zero, hp, not_true_eq_false, ↓reduceIte, Fintype.expect_const,
      Nat.cast_zero, zero_mul, le_refl]
  | succ K ih =>
    intro j hj status hp
    rw [OracleTemplate.VarianceReducedWeakMinty.expect_fin_succ]
    let next := fun seed => eval oracle (round ε R Q L γ x0 seed status)
    have he (seed : Fin (64 * logarithm Q) → StageSeed n (24 * logarithm Q))
        (seeds : Fin K → Fin (64 * logarithm Q) → StageSeed n (24 * logarithm Q)) :
        eval oracle (run ε R Q L γ x0 (K + 1) (Fin.cons seed seeds) status) =
          eval oracle (run ε R Q L γ x0 K seeds (next seed)) := by
      rw [run, eval_bind]
      rfl
    have hjadd : j + (K + 1) = (j + 1) + K := by omega
    simp only [he, hjadd]
    have hpoint (seed : Fin (64 * logarithm Q) → StageSeed n (24 * logarithm Q)) :
        (𝔼 seeds : Fin K → Fin (64 * logarithm Q) → StageSeed n (24 * logarithm Q),
          (if ¬P ((j + 1) + K) (eval oracle (run ε R Q L γ x0 K seeds (next seed))) then (1 : ℝ) else 0)) ≤
        (if ¬P (j + 1) (next seed) then (1 : ℝ) else 0) + K * δ := by
      by_cases hg : P (j + 1) (next seed)
      · simp only [hg, not_true_eq_false, ↓reduceIte, zero_add]
        exact ih (j + 1) (by omega) (next seed) hg
      · simp only [hg, not_false_eq_true, ↓reduceIte]
        have hb : (𝔼 seeds : Fin K → Fin (64 * logarithm Q) → StageSeed n (24 * logarithm Q),
            (if ¬P ((j + 1) + K) (eval oracle (run ε R Q L γ x0 K seeds (next seed))) then (1 : ℝ) else 0)) ≤ 1 := by
          calc
            _ ≤ (𝔼 _ : Fin K → Fin (64 * logarithm Q) → StageSeed n (24 * logarithm Q), (1 : ℝ)) :=
              Finset.expect_le_expect (s := Finset.univ) (fun _ _ => by split_ifs <;> norm_num)
            _ = 1 := Fintype.expect_const _
        exact hb.trans (by linarith [show (0 : ℝ) ≤ K * δ by positivity])
    have hmean := Finset.expect_le_expect (s := Finset.univ) (fun seed _ => hpoint seed)
    rw [Finset.expect_add_distrib, Fintype.expect_const] at hmean
    have hfirst := hstep j (by omega) status hp
    change (𝔼 seed : Fin (64 * logarithm Q) → StageSeed n (24 * logarithm Q),
      (if ¬P (j + 1) (next seed) then (1 : ℝ) else 0)) ≤ δ at hfirst
    push_cast
    linarith

open LongTails.Proofs.AcceleratedQuarticExecution LongTails.Proofs.QuarticTrialExecution

variable [FiniteDimensional ℝ E]

lemma run_good_probability {f : E → ℝ} (hf : Differentiable ℝ f) (hc : ConvexOn ℝ Set.univ f)
    {ε R Q L γ : ℝ} (hε : 0 < ε) (hR : 0 < R) (hQ : 3 ≤ Q) (hγ : 0 < γ)
    (x0 xstar : E) (hx0 : ‖x0 - xstar‖ ≤ R) (hmin : ∀ x, f xstar ≤ f x)
    (oracle : Fin n × E → LongTails.Algorithms.TaylorCorrectedNewton.Reply E)
    (N : ℕ) (hN : 0 < N) (hNQ : (N : ℝ) ≤ 256 * Q)
    (htrial : ∀ c, ‖c - xstar‖ ≤ R * Q ^ 8 →
      (∀ seed : Fin (64 * logarithm Q) → StageSeed n (24 * logarithm Q),
        eval oracle (trial ε R Q L γ x0 c seed) ≠ .failed →
          ValidAt f ε γ c xstar (eval oracle (trial ε R Q L γ x0 c seed))) ∧
      (𝔼 seed : Fin (64 * logarithm Q) → StageSeed n (24 * logarithm Q),
        (if eval oracle (trial ε R Q L γ x0 c seed) = .failed then (1 : ℝ) else 0)) ≤ 1 / (4 * (N : ℝ))) :
    (𝔼 seeds : Fin N → Fin (64 * logarithm Q) → StageSeed n (24 * logarithm Q),
      (if ¬GoodAt f ε γ x0 xstar N (eval oracle (run ε R Q L γ x0 N seeds .initial)) then (1 : ℝ) else 0)) ≤ 1 / 4 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hstep (j : ℕ) (hj : j < N) (status : Status E) (hg : GoodAt f ε γ x0 xstar j status) :
      (𝔼 seed : Fin (64 * logarithm Q) → StageSeed n (24 * logarithm Q),
        (if ¬GoodAt f ε γ x0 xstar (j + 1) (eval oracle (round ε R Q L γ x0 seed status)) then (1 : ℝ) else 0)) ≤
      1 / (4 * (N : ℝ)) := by
    have hcenter := good_center hc hγ x0 xstar hx0 hmin status hg
    have hscale := mul_le_mul_of_nonneg_right (center_scale hQ hj.le hNQ) hR.le
    have hcenter' : ‖queryCenter E x0 status - xstar‖ ≤ R * Q ^ 8 := by nlinarith only [hcenter, hscale]
    have ht := htrial (queryCenter E x0 status) hcenter'
    have hm := Finset.expect_le_expect (s := Finset.univ) (fun seed _ =>
      round_bad_le hf hc hε.le hγ x0 xstar oracle seed status hg (ht.1 seed))
    exact hm.trans ht.2
  have hh := run_failure ε R Q L γ x0 oracle (GoodAt f ε γ x0 xstar)
    (by positivity : 0 ≤ 1 / (4 * (N : ℝ))) N hstep N 0 (by omega) .initial rfl
  simp only [Nat.zero_add] at hh
  change (𝔼 seeds : Fin N → Fin (64 * logarithm Q) → StageSeed n (24 * logarithm Q),
      (if ¬GoodAt f ε γ x0 xstar N (eval oracle (run ε R Q L γ x0 N seeds .initial)) then (1 : ℝ) else 0)) ≤
    (N : ℝ) * (1 / (4 * (N : ℝ))) at hh
  have he : (N : ℝ) * (1 / (4 * (N : ℝ))) = 1 / 4 := by field_simp
  rwa [he] at hh


omit [FiniteDimensional ℝ E] in
lemma output_failure_bound {Ω : Type*} [Fintype Ω] {f : E → ℝ} (hc : ConvexOn ℝ Set.univ f)
    {ε γ R : ℝ} (hε : 0 < ε) (hγ : 0 < γ) (hR : 0 < R)
    (x0 xstar : E) (hx0 : ‖x0 - xstar‖ ≤ R) (hmin : ∀ x, f xstar ≤ f x)
    {N : ℕ} (hbudget : 64 * (1 + (γ * R ^ 4 / ε) ^ (1 / 5 : ℝ)) ≤ (N : ℝ))
    (Z : Ω → Status E)
    (hbad : (𝔼 ω, (if ¬GoodAt f ε γ x0 xstar N (Z ω) then (1 : ℝ) else 0)) ≤ 1 / 4) :
    (𝔼 ω, (if ¬f (output x0 (Z ω)) - f xstar ≤ ε then (1 : ℝ) else 0)) ≤ 1 / 4 := by
  apply le_trans _ hbad
  apply Finset.expect_le_expect
  intro ω _
  by_cases hg : GoodAt f ε γ x0 xstar N (Z ω)
  · have hh := good_output_accuracy hc hε hγ hR x0 xstar hx0 hmin hbudget (Z ω) hg
    simp only [hg, hh, not_true_eq_false, ↓reduceIte, le_refl]
  · simp only [hg, not_false_eq_true, ↓reduceIte]
    split_ifs <;> norm_num

lemma uniform_success {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (P : Ω → Prop) [DecidablePred P]
    (hbad : (𝔼 ω, (if ¬P ω then (1 : ℝ) else 0)) ≤ 1 / 4) :
    (2 / 3 : ENNReal) ≤ (PMF.uniformOfFintype Ω).toMeasure {ω | P ω} := by
  classical
  have hsum : (𝔼 ω, (if P ω then (1 : ℝ) else 0)) + (𝔼 ω, (if ¬P ω then (1 : ℝ) else 0)) = 1 := by
    rw [← Finset.expect_add_distrib]
    calc
      _ = (𝔼 _ : Ω, (1 : ℝ)) := Finset.expect_congr rfl (fun ω _ => by by_cases h : P ω <;> simp [h])
      _ = 1 := Fintype.expect_const _
  have hgood : (2 / 3 : ℝ) ≤ (𝔼 ω, (if P ω then (1 : ℝ) else 0)) := by linarith
  have hset : MeasurableSet {ω | P ω} := (Set.toFinite _).measurableSet
  have he : ((PMF.uniformOfFintype Ω).toMeasure {ω | P ω}).toReal = (𝔼 ω, (if P ω then (1 : ℝ) else 0)) := by
    change (PMF.uniformOfFintype Ω).toMeasure.real {ω | P ω} = _
    rw [← MeasureTheory.integral_indicator_one hset, OracleTemplate.FiniteSum.uniform_integral]
    apply Finset.expect_congr rfl
    intro ω _
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
  have hh := ENNReal.ofReal_le_of_le_toReal (hgood.trans_eq he.symm)
  simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3), ENNReal.ofReal_ofNat] using hh


end LongTails.Proofs.AcceleratedQuarticProbability
