import LongTails.Proofs.MixedNoiseSelectors
import Mathlib.Data.Fin.Rev
import LongTails.Proofs.AdaptiveIID
import LongTails.Proofs.AdaptiveHistoryTracking
import LongTails.Algorithms.HeterogeneousAdam
import LongTails.Proofs.Execution
import LongTails.Proofs.AdaptiveHistoryAlgebra
import LongTails.Proofs.HeavyTailedPLStep
import Mathlib.MeasureTheory.Function.L2Space

open LongTails.Proofs.AdaptiveHistoryTracking
namespace LongTails.Proofs.HeterogeneousAdamExecution

open MeasureTheory
open OracleTemplate LongTails.Algorithms.HeterogeneousAdam
open LongTails.Proofs.AdaptiveHistoryAlgebra

lemma run_clock (cfg : Config) (x₀ : Point b h) (seed : Fin (cfg.lastIndex + 1))
    (g : ℕ → Point b h → Point b h) (n : ℕ) : (run cfg x₀ seed g n).clock = n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [run, update] using congrArg Nat.succ ih

lemma run_target (cfg : Config) (x₀ : Point b h) (seed : Fin (cfg.lastIndex + 1))
    (g : ℕ → Point b h → Point b h) (n : ℕ) : (run cfg x₀ seed g n).target = seed.val := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

lemma run_core_independent (cfg : Config) (x₀ : Point b h)
    (seed seed' : Fin (cfg.lastIndex + 1)) (g : ℕ → Point b h → Point b h) (n : ℕ) :
    (run cfg x₀ seed g n).point = (run cfg x₀ seed' g n).point ∧
    (run cfg x₀ seed g n).momentum = (run cfg x₀ seed' g n).momentum ∧
    (run cfg x₀ seed g n).accumulator = (run cfg x₀ seed' g n).accumulator := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    rcases ih with ⟨hp, hm, hv⟩
    simp only [run, update, nextPoint, nextMomentum, nextAccumulator, run_clock, hp, hm, hv]
    simp

lemma run_point (cfg : Config) (x₀ : Point b h) (seed : Fin (cfg.lastIndex + 1))
    (g : ℕ → Point b h → Point b h) (n : ℕ) :
    (run cfg x₀ seed g n).point = trajectory cfg x₀ g n :=
  (run_core_independent cfg x₀ seed 0 g n).1

lemma indexed_iterate (cfg : Config) (x₀ : Point b h) (seed : Fin (cfg.lastIndex + 1))
    (g : ℕ → Point b h → Point b h) (n : ℕ) :
    ((fun sc : State b h × ℕ => (update cfg sc.1 (g sc.2 sc.1.point), sc.2 + 1))^[n]
      (initial cfg x₀ seed, 0)) = (run cfg x₀ seed g n, n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

lemma execute_run (cfg : Config) (x₀ : Point b h)
    (O : Oracle (Point b h) (Point b h)) (seed : Fin (cfg.lastIndex + 1))
    (ξ : (k : ℕ) → O.Seed k) (n : ℕ) :
    execute O (method cfg x₀) (fun _ => n) seed ξ =
      output (run cfg x₀ seed (fun k x => O.answer k (0, x) (ξ k)) n) := by
  erw [execute_indexed]
  change output (((fun sc : State b h × ℕ =>
    (update cfg sc.1 (O.answer sc.2 (0, sc.1.point) (ξ sc.2)), sc.2 + 1))^[n]
      (initial cfg x₀ seed, 0)).1) = _
  exact congrArg (fun sc : State b h × ℕ => output sc.1)
    (indexed_iterate cfg x₀ seed (fun k x => O.answer k (0, x) (ξ k)) n)

lemma run_selected (cfg : Config) (x₀ : Point b h) (seed : Fin (cfg.lastIndex + 1))
    (g : ℕ → Point b h → Point b h) (n : ℕ) :
    seed.val ≤ n → (run cfg x₀ seed g n).selected = trajectory cfg x₀ g seed.val := by
  induction n with
  | zero =>
    intro hn
    have hz : seed.val = 0 := by omega
    simp [run, initial, trajectory, hz]
  | succ n ih =>
    intro hn
    by_cases he : n + 1 = seed.val
    · have hp := run_point cfg x₀ seed g (n + 1)
      change nextPoint cfg (run cfg x₀ seed g n) (g n (run cfg x₀ seed g n).point) = _ at hp
      simpa only [run, update, run_clock, run_target, he, ite_true] using hp
    · have hsn : seed.val ≤ n := by omega
      simpa only [run, update, run_clock, run_target, ite_eq_right he] using ih hsn

lemma execute_output (cfg : Config) (x₀ : Point b h)
    (O : Oracle (Point b h) (Point b h)) (seed : Fin (cfg.lastIndex + 1))
    (ξ : (k : ℕ) → O.Seed k) :
    execute O (method cfg x₀) (fun _ => cfg.lastIndex + 1) seed ξ =
      trajectory cfg x₀ (fun k x => O.answer k (0, x) (ξ k)) seed.val := by
  erw [execute_run]
  exact run_selected cfg x₀ seed _ _ (by omega)


lemma run_congr_prefix (cfg : Config) (x₀ : Point b h) (seed : Fin (cfg.lastIndex + 1))
    {g g' : ℕ → Point b h → Point b h} (n : ℕ)
    (heq : ∀ k, k < n → g k = g' k) : run cfg x₀ seed g n = run cfg x₀ seed g' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run, run, ih (fun k hk => heq k (by omega)), heq n (by omega)]

lemma trajectory_congr_prefix (cfg : Config) (x₀ : Point b h)
    {g g' : ℕ → Point b h → Point b h} (n : ℕ)
    (heq : ∀ k, k < n → g k = g' k) : trajectory cfg x₀ g n = trajectory cfg x₀ g' n :=
  congrArg State.point (run_congr_prefix cfg x₀ 0 n heq)

lemma trajectory_sample_congr_prefix {Ω : Type*} (cfg : Config) (x₀ : Point b h)
    (oracle : Point b h → Ω → Point b h) {ξ ξ' : ℕ → Ω} (n : ℕ)
    (heq : ∀ k, k < n → ξ k = ξ' k) :
    trajectory cfg x₀ (fun k x => oracle x (ξ k)) n =
      trajectory cfg x₀ (fun k x => oracle x (ξ' k)) n := by
  apply trajectory_congr_prefix
  intro k hk
  rw [heq k hk]


lemma run_core_measurable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (cfg : Config) (x₀ : Point b h) (seed : Fin (cfg.lastIndex + 1))
    {oracle : Point b h → Ω → Point b h} {ξ : ℕ → Ξ → Ω}
    (ho : Measurable (Function.uncurry oracle)) (hξ : ∀ k, Measurable (ξ k)) (n : ℕ) :
    Measurable (fun ω => (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) n).point) ∧
    Measurable (fun ω => (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) n).momentum) ∧
    Measurable (fun ω => (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) n).accumulator) := by
  induction n with
  | zero => exact ⟨measurable_const, measurable_const, measurable_const⟩
  | succ n ih =>
    let s := fun ω => run cfg x₀ seed (fun k x => oracle x (ξ k ω)) n
    let g := fun ω => oracle (s ω).point (ξ n ω)
    have hg : Measurable g := ho.comp (ih.1.prodMk (hξ n))
    have hp (i : Fin b ⊕ Fin h) : Measurable (fun ω => (s ω).point i) := by
      exact (measurable_pi_apply i).comp ((WithLp.measurable_ofLp 2 _).comp ih.1)
    have hm (i : Fin b ⊕ Fin h) : Measurable (fun ω => (s ω).momentum i) := by
      exact (measurable_pi_apply i).comp ((WithLp.measurable_ofLp 2 _).comp ih.2.1)
    have hv (i : Fin b ⊕ Fin h) : Measurable (fun ω => (s ω).accumulator i) := by
      exact (measurable_pi_apply i).comp ((WithLp.measurable_ofLp 2 _).comp ih.2.2)
    have hgi (i : Fin b ⊕ Fin h) : Measurable (fun ω => g ω i) := by
      exact (measurable_pi_apply i).comp ((WithLp.measurable_ofLp 2 _).comp hg)
    have hnm : Measurable (fun ω => nextMomentum cfg (s ω) (g ω)) := by
      apply (WithLp.measurable_toLp 2 _).comp
      apply Measurable.of_eval
      intro i
      cases i with
      | inl j => exact (measurable_const.mul (hm _)).add (measurable_const.mul (hgi _))
      | inr j => exact hgi _
    have hnv : Measurable (fun ω => nextAccumulator cfg (s ω) (g ω)) := by
      apply (WithLp.measurable_toLp 2 _).comp
      apply Measurable.of_eval
      intro i
      cases i with
      | inl j => exact (measurable_const.mul (hv _)).add (measurable_const.mul ((hgi _).pow_const 2))
      | inr j => exact (hv _).add ((hgi _).pow_const 2)
    refine ⟨?_, hnm, hnv⟩
    change Measurable (fun ω => nextPoint cfg (s ω) (g ω))
    apply (WithLp.measurable_toLp 2 _).comp
    apply Measurable.of_eval
    intro i
    have hmi : Measurable (fun ω => nextMomentum cfg (s ω) (g ω) i) :=
      (measurable_pi_apply i).comp ((WithLp.measurable_ofLp 2 _).comp hnm)
    have hvi : Measurable (fun ω => nextAccumulator cfg (s ω) (g ω) i) :=
      (measurable_pi_apply i).comp ((WithLp.measurable_ofLp 2 _).comp hnv)
    have hc (ω) : (s ω).clock = n := run_clock cfg x₀ seed _ n
    simp only [hc]
    cases i with
    | inl j => exact (hp _).sub ((measurable_const.mul (hmi.div measurable_const)).div
        (measurable_const.add ((hvi.div measurable_const).sqrt)))
    | inr j => exact (hp _).sub ((measurable_const.mul (hgi _)).div hvi.sqrt)

lemma trajectory_measurable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (cfg : Config) (x₀ : Point b h)
    {oracle : Point b h → Ω → Point b h} {ξ : ℕ → Ξ → Ω}
    (ho : Measurable (Function.uncurry oracle)) (hξ : ∀ k, Measurable (ξ k)) (n : ℕ) :
    Measurable (fun ω => trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) n) :=
  (run_core_measurable cfg x₀ 0 ho hξ n).1


lemma run_body_moment_bound (cfg : Config) (hα : cfg.α = 9 / 10) (hβ : cfg.β = 999 / 1000)
    (x₀ : Point b h) (seed : Fin (cfg.lastIndex + 1))
    (g : ℕ → Point b h → Point b h) (n : ℕ) (j : Fin b) :
    0 ≤ (run cfg x₀ seed g n).accumulator (.inl j) ∧
      (run cfg x₀ seed g n).momentum (.inl j) ^ 2 ≤
        64 * (run cfg x₀ seed g n).accumulator (.inl j) := by
  induction n with
  | zero => simp [run, initial]
  | succ n ih =>
    have hh := default_momentum_invariant (g := g n (run cfg x₀ seed g n).point (.inl j)) ih.1 ih.2
    constructor
    · simp only [run, update, nextAccumulator, PiLp.toLp_apply, hβ]
      nlinarith [sq_nonneg (g n (run cfg x₀ seed g n).point (.inl j)), ih.1]
    · simpa only [run, update, nextAccumulator, nextMomentum, PiLp.toLp_apply, hα, hβ] using hh

lemma run_head_accumulator_lower (cfg : Config) (x₀ : Point b h)
    (seed : Fin (cfg.lastIndex + 1)) (g : ℕ → Point b h → Point b h) (n : ℕ) (j : Fin h) :
    cfg.r₀ ^ 2 ≤ (run cfg x₀ seed g n).accumulator (.inr j) := by
  induction n with
  | zero => simp [run, initial]
  | succ n ih =>
    simp only [run, update, nextAccumulator, PiLp.toLp_apply]
    nlinarith [sq_nonneg (g n (run cfg x₀ seed g n).point (.inr j))]


lemma default_bias_parameters (n : ℕ) :
    (1 / 10 : ℝ) ≤ 1 - (9 / 10 : ℝ) ^ (n + 1) ∧
      0 < 1 - (999 / 1000 : ℝ) ^ (n + 1) ∧
      1 - (999 / 1000 : ℝ) ^ (n + 1) ≤ 1 := by
  have ha := pow_le_pow_of_le_one (a := (9 / 10 : ℝ)) (by norm_num) (by norm_num)
    (show 1 ≤ n + 1 by omega)
  have hb := pow_lt_one₀ (a := (999 / 1000 : ℝ)) (by norm_num) (by norm_num)
    (show n + 1 ≠ 0 by omega)
  simp only [pow_one] at ha
  exact ⟨by linarith, by linarith, by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 999 / 1000) (n + 1)]⟩

lemma run_body_increment (cfg : Config) (hα : cfg.α = 9 / 10) (hβ : cfg.β = 999 / 1000)
    (hδ : 0 < cfg.δ) (x₀ : Point b h) (seed : Fin (cfg.lastIndex + 1))
    (g : ℕ → Point b h → Point b h) (n : ℕ) (j : Fin b) :
    |(run cfg x₀ seed g (n + 1)).point (.inl j) - (run cfg x₀ seed g n).point (.inl j)| ≤
      80 * |cfg.bodyStep n| := by
  have hv := run_body_moment_bound cfg hα hβ x₀ seed g (n + 1) j
  have ht := default_bias_parameters n
  have hd := bias_corrected_direction_bound hv.1 hv.2 ht.1 ht.2.1 ht.2.2 hδ
  let s := run cfg x₀ seed g n
  let G := g n s.point
  let m := nextMomentum cfg s G (.inl j)
  let v := nextAccumulator cfg s G (.inl j)
  change |(m / (1 - (9 / 10 : ℝ) ^ (n + 1))) /
    (cfg.δ + Real.sqrt (v / (1 - (999 / 1000 : ℝ) ^ (n + 1))))| ≤ 80 at hd
  have hc : s.clock = n := run_clock cfg x₀ seed g n
  change |nextPoint cfg s G (.inl j) - s.point (.inl j)| ≤ _
  simp only [nextPoint, PiLp.toLp_apply, hc, hα, hβ]
  change |(s.point (.inl j) - cfg.bodyStep n * (m / (1 - (9 / 10 : ℝ) ^ (n + 1))) /
    (cfg.δ + Real.sqrt (v / (1 - (999 / 1000 : ℝ) ^ (n + 1))))) - s.point (.inl j)| ≤ _
  rw [sub_sub_cancel_left, abs_neg, mul_div_assoc, abs_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hd (abs_nonneg (cfg.bodyStep n))

lemma run_head_increment (cfg : Config) (x₀ : Point b h) (seed : Fin (cfg.lastIndex + 1))
    (g : ℕ → Point b h → Point b h) (n : ℕ) (j : Fin h) :
    |(run cfg x₀ seed g (n + 1)).point (.inr j) - (run cfg x₀ seed g n).point (.inr j)| ≤
      |cfg.headStep n| := by
  have hv : 0 ≤ (run cfg x₀ seed g n).accumulator (.inr j) :=
    (sq_nonneg cfg.r₀).trans (run_head_accumulator_lower cfg x₀ seed g n j)
  have hd := adagrad_direction_bound (g := g n (run cfg x₀ seed g n).point (.inr j)) hv
  simp only [run, update, nextPoint, nextAccumulator, PiLp.toLp_apply, run_clock]
  rw [sub_sub_cancel_left, abs_neg, mul_div_assoc, abs_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hd (abs_nonneg (cfg.headStep n))

lemma point_norm_sq_le {b h : ℕ} (v : Point b h) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hb : ∀ j, |v (.inl j)| ≤ A) (hh : ∀ j, |v (.inr j)| ≤ B) :
    ‖v‖ ^ 2 ≤ b * A ^ 2 + h * B ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type]
  have hbs : (∑ j : Fin b, v (.inl j) ^ 2) ≤ ∑ _j : Fin b, A ^ 2 := by
    apply Finset.sum_le_sum
    intro j _
    nlinarith [hb j, abs_nonneg (v (.inl j)), sq_abs (v (.inl j))]
  have hhs : (∑ j : Fin h, v (.inr j) ^ 2) ≤ ∑ _j : Fin h, B ^ 2 := by
    apply Finset.sum_le_sum
    intro j _
    nlinarith [hh j, abs_nonneg (v (.inr j)), sq_abs (v (.inr j))]
  simpa using add_le_add hbs hhs

lemma run_increment_sq (cfg : Config) (hα : cfg.α = 9 / 10) (hβ : cfg.β = 999 / 1000)
    (hδ : 0 < cfg.δ) (x₀ : Point b h) (seed : Fin (cfg.lastIndex + 1))
    (g : ℕ → Point b h → Point b h) (n : ℕ) :
    ‖(run cfg x₀ seed g (n + 1)).point - (run cfg x₀ seed g n).point‖ ^ 2 ≤
      6400 * b * (cfg.bodyStep n) ^ 2 + h * (cfg.headStep n) ^ 2 := by
  have hh := point_norm_sq_le
    ((run cfg x₀ seed g (n + 1)).point - (run cfg x₀ seed g n).point)
    (A := 80 * |cfg.bodyStep n|) (B := |cfg.headStep n|) (by positivity) (by positivity)
    (run_body_increment cfg hα hβ hδ x₀ seed g n) (run_head_increment cfg x₀ seed g n)
  convert hh using 1
  simp only [mul_pow, sq_abs]
  ring


lemma run_increment_norm (cfg : Config) (hα : cfg.α = 9 / 10) (hβ : cfg.β = 999 / 1000)
    (hδ : 0 < cfg.δ) (x₀ : Point b h) (seed : Fin (cfg.lastIndex + 1))
    (g : ℕ → Point b h → Point b h) (n : ℕ) :
    ‖(run cfg x₀ seed g (n + 1)).point - (run cfg x₀ seed g n).point‖ ≤
      Real.sqrt (6400 * b * (cfg.bodyStep n) ^ 2 + h * (cfg.headStep n) ^ 2) := by
  have hh := run_increment_sq cfg hα hβ hδ x₀ seed g n
  have ht := Real.sq_sqrt (show 0 ≤ 6400 * b * (cfg.bodyStep n) ^ 2 + h * (cfg.headStep n) ^ 2 by positivity)
  nlinarith [norm_nonneg ((run cfg x₀ seed g (n + 1)).point - (run cfg x₀ seed g n).point),
    Real.sqrt_nonneg (6400 * b * (cfg.bodyStep n) ^ 2 + h * (cfg.headStep n) ^ 2)]

lemma run_displacement_sum (cfg : Config) (hα : cfg.α = 9 / 10) (hβ : cfg.β = 999 / 1000)
    (hδ : 0 < cfg.δ) (x₀ : Point b h) (seed : Fin (cfg.lastIndex + 1))
    (g : ℕ → Point b h → Point b h) (n : ℕ) :
    ‖(run cfg x₀ seed g n).point - x₀‖ ≤
      ∑ k ∈ Finset.range n, Real.sqrt (6400 * b * (cfg.bodyStep k) ^ 2 + h * (cfg.headStep k) ^ 2) := by
  have hh := dist_le_range_sum_of_dist_le (f := fun k => (run cfg x₀ seed g k).point) n
    (d := fun k => Real.sqrt (6400 * b * (cfg.bodyStep k) ^ 2 + h * (cfg.headStep k) ^ 2))
    (fun {k} _ => by simpa only [dist_eq_norm, norm_sub_rev] using
      run_increment_norm cfg hα hβ hδ x₀ seed g k)
  simpa only [run, initial, dist_eq_norm, norm_sub_rev] using hh

lemma initial_gradient_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {L Δ : ℝ} {x₀ : E} (hL : 0 < L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hgap : ∀ x, f x₀ - f x ≤ Δ) : ‖gradient f x₀‖ ≤ Real.sqrt (2 * L * Δ) := by
  have hΔ : 0 ≤ Δ := by simpa using hgap x₀
  have hh := OracleTemplate.HeavyTailedPL.gradient_sq_le hL hg hlip
    (m := f x₀ - Δ) (fun x => by linarith [hgap x]) x₀
  have hs := Real.sq_sqrt (show 0 ≤ 2 * L * Δ by positivity)
  nlinarith [norm_nonneg (gradient f x₀), Real.sqrt_nonneg (2 * L * Δ)]

lemma run_gradient_bound (cfg : Config) (hα : cfg.α = 9 / 10) (hβ : cfg.β = 999 / 1000)
    (hδ : 0 < cfg.δ) (x₀ : Point b h) (seed : Fin (cfg.lastIndex + 1))
    (g : ℕ → Point b h → Point b h) {f : Point b h → ℝ} {L Δ : ℝ} (hL : 0 < L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hgap : ∀ x, f x₀ - f x ≤ Δ) (n : ℕ) :
    ‖gradient f (run cfg x₀ seed g n).point‖ ≤ Real.sqrt (2 * L * Δ) +
      L * ∑ k ∈ Finset.range n, Real.sqrt (6400 * b * (cfg.bodyStep k) ^ 2 + h * (cfg.headStep k) ^ 2) := by
  let x := (run cfg x₀ seed g n).point
  calc
    ‖gradient f x‖ ≤ ‖gradient f x - gradient f x₀‖ + ‖gradient f x₀‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ L * ‖x - x₀‖ + Real.sqrt (2 * L * Δ) :=
      add_le_add (hlip x x₀) (initial_gradient_norm hL hg hlip hgap)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (run_displacement_sum cfg hα hβ hδ x₀ seed g n) hL.le
      dsimp [x]
      linarith


def paddedSamples {Ω : Type*} {n : ℕ} (a : Ω) (z : Fin n → Ω) (k : ℕ) : Ω :=
  if hk : k < n then z ⟨k, hk⟩ else a

lemma paddedSamples_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (a : Ω) (k : ℕ) :
    Measurable (fun z : Fin n → Ω => paddedSamples a z k) := by
  by_cases hk : k < n
  · simpa only [paddedSamples, dite_eq_left hk] using measurable_pi_apply (⟨k, hk⟩ : Fin n)
  · simpa only [paddedSamples, dite_eq_right hk] using (measurable_const (a := a))

lemma trajectory_insertNth_independent {Ω : Type*} {n : ℕ} (cfg : Config) (x₀ : Point b h)
    (oracle : Point b h → Ω → Point b h) (i : Fin (n + 1)) (z : Fin n → Ω)
    (a u v : Ω) (t : ℕ) (ht : t ≤ (i : ℕ)) :
    trajectory cfg x₀ (fun k x => oracle x (paddedSamples a (i.insertNth u z) k)) t =
      trajectory cfg x₀ (fun k x => oracle x (paddedSamples a (i.insertNth v z) k)) t := by
  apply trajectory_sample_congr_prefix
  intro k hk
  have hkn : k < n + 1 := by omega
  have hki : (⟨k, hkn⟩ : Fin (n + 1)) < i := by exact_mod_cast Nat.lt_of_lt_of_le hk ht
  simp only [paddedSamples, dite_eq_left hkn]
  rw [Fin.insertNth_apply_below hki, Fin.insertNth_apply_below hki]

lemma trajectory_deleted_representation {Ω : Type*} {n : ℕ} (cfg : Config) (x₀ : Point b h)
    (oracle : Point b h → Ω → Point b h) (i : Fin (n + 1)) (z : Fin (n + 1) → Ω)
    (a : Ω) (t : ℕ) (ht : t ≤ (i : ℕ)) :
    trajectory cfg x₀ (fun k x => oracle x (paddedSamples a z k)) t =
      trajectory cfg x₀ (fun k x => oracle x
        (paddedSamples a (i.insertNth a (fun j => z (i.succAbove j))) k)) t := by
  have he : i.insertNth (z i) (fun j => z (i.succAbove j)) = z :=
    Fin.insertNth_eq_iff.mpr ⟨rfl, rfl⟩
  have hh := trajectory_insertNth_independent cfg x₀ oracle i
    (fun j => z (i.succAbove j)) a (z i) a t ht
  simpa only [he] using hh

lemma trajectory_displacement_memLp {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (cfg : Config) (hα : cfg.α = 9 / 10) (hβ : cfg.β = 999 / 1000) (hδ : 0 < cfg.δ)
    (x₀ : Point b h) {oracle : Point b h → Ω → Point b h}
    (ho : Measurable (Function.uncurry oracle)) {ξ : ℕ → Ξ → Ω}
    (hξ : ∀ k, Measurable (ξ k)) (t s : ℕ) (P : Measure Ξ) [IsFiniteMeasure P] :
    MemLp (fun z => ‖trajectory cfg x₀ (fun k x => oracle x (ξ k z)) t -
      trajectory cfg x₀ (fun k x => oracle x (ξ k z)) s‖) 2 P := by
  have hmt := trajectory_measurable cfg x₀ ho hξ t
  have hms := trajectory_measurable cfg x₀ ho hξ s
  let B := fun l => ∑ k ∈ Finset.range l,
    Real.sqrt (6400 * b * (cfg.bodyStep k) ^ 2 + h * (cfg.headStep k) ^ 2)
  apply MemLp.of_bound ((hmt.sub hms).norm.aestronglyMeasurable) (B t + B s)
  filter_upwards [] with z
  simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have ht := run_displacement_sum cfg hα hβ hδ x₀ 0 (fun k x => oracle x (ξ k z)) t
  have hs := run_displacement_sum cfg hα hβ hδ x₀ 0 (fun k x => oracle x (ξ k z)) s
  have htri := norm_sub_le
    (trajectory cfg x₀ (fun k x => oracle x (ξ k z)) t - x₀)
    (trajectory cfg x₀ (fun k x => oracle x (ξ k z)) s - x₀)
  rw [sub_sub_sub_cancel_right] at htri
  exact htri.trans (add_le_add ht hs)

lemma complementary_displacement_memLp {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (cfg : Config) (hα : cfg.α = 9 / 10) (hβ : cfg.β = 999 / 1000) (hδ : 0 < cfg.δ)
    (x₀ : Point b h) {oracle : Point b h → Ω → Point b h}
    (ho : Measurable (Function.uncurry oracle)) (i : Fin (n + 1)) (a : Ω) (t s : ℕ)
    (P : Measure (Fin n → Ω)) [IsFiniteMeasure P] :
    MemLp (fun z : Fin n → Ω =>
      ‖trajectory cfg x₀ (fun k x => oracle x (paddedSamples a (i.insertNth a z) k)) t -
        trajectory cfg x₀ (fun k x => oracle x (paddedSamples a (i.insertNth a z) k)) s‖) 2 P := by
  let ξ : ℕ → (Fin n → Ω) → Ω := fun k z => paddedSamples a (i.insertNth a z) k
  have hins : Measurable (fun z : Fin n → Ω => (i.insertNth a z : Fin (n + 1) → Ω)) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) i).symm.measurable.comp
      (measurable_const.prodMk measurable_id)
  have hξ (k) : Measurable (ξ k) := (paddedSamples_measurable a k).comp hins
  exact trajectory_displacement_memLp cfg hα hβ hδ x₀ ho hξ t s P


lemma iid_prefix_window_law {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P) (m n : ℕ) :
    MeasurePreserving (fun ω => ((fun i : Fin m => ξ i ω), (fun i : Fin n => ξ (m+i) ω)))
      P ((Measure.pi fun _ : Fin m => p).prod (Measure.pi fun _ : Fin n => p)) := by
  have hp := (MeasurePreserving.id (Measure.pi fun _ : Fin m => p)).prod
    (OracleTemplate.StochasticGeneralized.prefix_preserving p n)
  exact hp.comp (h.prefix_tail_law m)

lemma iid_prefix_inverse_root_moment {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    {m n : ℕ} {G : (Fin m → Ω) → ℝ} {noise : (Fin m → Ω) → Ω → ℝ}
    (hG : Measurable G) (hm : Measurable (Function.uncurry noise))
    (hsym : ∀ x, (p.map (noise x)).map (fun z : ℝ => -z) = p.map (noise x))
    {β : ℝ} (hβ : 1 / 2 < β) (hβ1 : β < 1) (b : Fin n → ℝ)
    (hb : ∀ k : Fin n, (1 - β) * β ^ ((k : ℕ) + 1) ≤ b k) :
    let r := {w : (Fin m → Ω) × (Fin n → Ω) | ∃ k, 0 ≤ G w.1 * noise w.1 (w.2 k)}.indicator
      (fun w => |G w.1| / Real.sqrt (∑ k, b k * (G w.1 + noise w.1 (w.2 k)) ^ 2))
    let F := fun ω => ((fun i : Fin m => ξ i ω), (fun i : Fin n => ξ (m+i) ω))
    MemLp (r ∘ F) 2 P ∧ (∫ ω, r (F ω) ^ 2 ∂P) ≤
      8 / ((1 - β) * (1 - 1 / (2 * β))) := by
  dsimp only
  have hh := LongTails.Proofs.AdaptiveHistoryTracking.prefix_truncated_inverse_root_moment
    (P := Measure.pi fun _ : Fin m => p) hG hm hsym hβ hβ1 b hb
  have hp := iid_prefix_window_law h m n
  refine ⟨hh.1.comp_measurePreserving hp, ?_⟩
  rw [← hp.map_eq] at hh
  have he := integral_map hp.measurable.aemeasurable
    (hh.1.aestronglyMeasurable.pow 2)
  exact he.symm.trans_le hh.2



lemma iid_prefix_reverse_window_law {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P) (m n : ℕ) :
    MeasurePreserving (fun ω => ((fun i : Fin m => ξ i ω), (fun i : Fin n => ξ (m+i.rev) ω)))
      P ((Measure.pi fun _ : Fin m => p).prod (Measure.pi fun _ : Fin n => p)) := by
  have hr := measurePreserving_piCongrLeft (fun _ : Fin n => p) (Fin.revPerm : Fin n ≃ Fin n)
  have hp := (MeasurePreserving.id (Measure.pi fun _ : Fin m => p)).prod hr
  convert hp.comp (iid_prefix_window_law h m n) using 1
  funext ω
  apply Prod.ext
  · rfl
  · funext i
    simp [Prod.map, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply_eq_cast, Fin.revPerm]



def prefixReverseSamples {Ω : Type*} {m n : ℕ} (a : Ω)
    (pre : Fin m → Ω) (z : Fin n → Ω) (k : ℕ) : Ω :=
  if hk : k < m then pre ⟨k,hk⟩ else paddedSamples a (fun j => z j.rev) (k-m)

lemma prefixReverseSamples_measurable {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (a : Ω) (k : ℕ) :
    Measurable (fun w : (Fin m → Ω) × (Fin n → Ω) => prefixReverseSamples a w.1 w.2 k) := by
  by_cases hk : k < m
  · simpa only [prefixReverseSamples, dite_eq_left hk, Function.comp_def] using
      (measurable_pi_apply (⟨k,hk⟩ : Fin m)).comp measurable_fst
  · simp only [prefixReverseSamples, dite_eq_right hk]
    have hh : Measurable (fun w : (Fin m → Ω) × (Fin n → Ω) => fun j : Fin n => w.2 j.rev) :=
      Measurable.of_eval fun j => (measurable_pi_apply j.rev).comp measurable_snd
    simpa only [Function.comp_def] using (paddedSamples_measurable a (k-m)).comp hh

lemma trajectory_reverse_insertNth_independent {Ω : Type*} {m n : ℕ}
    (cfg : Config) (x₀ : Point b h) (oracle : Point b h → Ω → Point b h)
    (pre : Fin m → Ω) (i : Fin (n+1)) (z : Fin n → Ω)
    (a u v : Ω) (t : ℕ) (ht : t ≤ m + (i.rev : ℕ)) :
    trajectory cfg x₀ (fun k x => oracle x (prefixReverseSamples a pre (i.insertNth u z) k)) t =
      trajectory cfg x₀ (fun k x => oracle x (prefixReverseSamples a pre (i.insertNth v z) k)) t := by
  apply trajectory_sample_congr_prefix
  intro k hk
  by_cases hkm : k < m
  · simp only [prefixReverseSamples, dite_eq_left hkm]
  · have hkn : k-m < n+1 := by have hi := i.rev.isLt; omega
    have hki : i < (⟨k-m,hkn⟩ : Fin (n+1)).rev := by
      change (i : ℕ) < ((⟨k-m,hkn⟩ : Fin (n+1)).rev : ℕ)
      simp only [Fin.val_rev]
      have hi : (i.rev : ℕ) = n+1-((i : ℕ)+1) := Fin.val_rev i
      omega
    simp only [prefixReverseSamples, dite_eq_right hkm, paddedSamples, dite_eq_left hkn]
    rw [Fin.insertNth_apply_above hki, Fin.insertNth_apply_above hki]

lemma trajectory_reverse_deleted_representation {Ω : Type*} {m n : ℕ}
    (cfg : Config) (x₀ : Point b h) (oracle : Point b h → Ω → Point b h)
    (pre : Fin m → Ω) (i : Fin (n+1)) (z : Fin (n+1) → Ω)
    (a : Ω) (t : ℕ) (ht : t ≤ m + (i.rev : ℕ)) :
    trajectory cfg x₀ (fun k x => oracle x (prefixReverseSamples a pre z k)) t =
      trajectory cfg x₀ (fun k x => oracle x
        (prefixReverseSamples a pre (i.insertNth a (fun j => z (i.succAbove j))) k)) t := by
  have he : i.insertNth (z i) (fun j => z (i.succAbove j)) = z :=
    Fin.insertNth_eq_iff.mpr ⟨rfl,rfl⟩
  have hh := trajectory_reverse_insertNth_independent cfg x₀ oracle pre i
    (fun j => z (i.succAbove j)) a (z i) a t ht
  simpa only [he] using hh

lemma prefixReverseSamples_reconstruct {Ω : Type*} (a : Ω) (ξ : ℕ → Ω) (m n k : ℕ)
    (hk : k < m+n) :
    prefixReverseSamples a (fun i : Fin m => ξ i)
      (fun i : Fin n => ξ (m+i.rev)) k = ξ k := by
  by_cases hkm : k < m
  · simp only [prefixReverseSamples, dite_eq_left hkm]
  · have hkn : k-m < n := by omega
    simp only [prefixReverseSamples, dite_eq_right hkm, paddedSamples, dite_eq_left hkn,
      Fin.rev_rev]
    congr 1
    omega

lemma trajectory_prefix_reverse_representation {Ω : Type*} (cfg : Config) (x₀ : Point b h)
    (oracle : Point b h → Ω → Point b h) (a : Ω) (ξ : ℕ → Ω) (m n t : ℕ)
    (ht : t ≤ m+n) :
    trajectory cfg x₀ (fun k x => oracle x (ξ k)) t =
      trajectory cfg x₀ (fun k x => oracle x
        (prefixReverseSamples a (fun i : Fin m => ξ i) (fun i : Fin n => ξ (m+i.rev)) k)) t := by
  apply trajectory_sample_congr_prefix
  intro k hk
  exact (prefixReverseSamples_reconstruct a ξ m n k (by omega)).symm

lemma reverse_complementary_displacement_memLp {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (cfg : Config) (hα : cfg.α = 9 / 10) (hβ : cfg.β = 999 / 1000) (hδ : 0 < cfg.δ)
    (x₀ : Point b h) {oracle : Point b h → Ω → Point b h}
    (ho : Measurable (Function.uncurry oracle)) (i : Fin (n+1)) (a : Ω) (t s : ℕ)
    (P : Measure ((Fin m → Ω) × (Fin n → Ω))) [IsFiniteMeasure P] :
    MemLp (fun w => ‖trajectory cfg x₀ (fun k x => oracle x
      (prefixReverseSamples a w.1 (i.insertNth a w.2) k)) t -
      trajectory cfg x₀ (fun k x => oracle x
      (prefixReverseSamples a w.1 (i.insertNth a w.2) k)) s‖) 2 P := by
  have hins : Measurable (fun w : (Fin m → Ω) × (Fin n → Ω) =>
      (w.1, (i.insertNth a w.2 : Fin (n+1) → Ω))) :=
    measurable_fst.prodMk ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Ω) i).symm.measurable.comp
      (measurable_const.prodMk measurable_snd))
  exact trajectory_displacement_memLp cfg hα hβ hδ x₀ ho
    (fun k => (prefixReverseSamples_measurable a k).comp hins) t s P


open LongTails.Proofs.AdaptiveHistoryAlgebra LongTails.Algorithms.HeterogeneousAdam

lemma run_momentum_history (cfg : Config) (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1))
    (g : ℕ → Point b h → Point b h) (s n : ℕ) (j : Fin b) :
    (run cfg x₀ seed g (s+n)).momentum (.inl j) =
      cfg.α^n * (run cfg x₀ seed g s).momentum (.inl j) +
      ∑ i : Fin n, cfg.α^(i : ℕ) * ((1-cfg.α) *
        g (s+(i.rev : ℕ)) (run cfg x₀ seed g (s+(i.rev : ℕ))).point (.inl j)) := by
  refine affine_history_expansion
    (fun t => (run cfg x₀ seed g t).momentum (.inl j))
    (fun t => (1-cfg.α) * g t (run cfg x₀ seed g t).point (.inl j)) cfg.α ?_ s n
  intro t
  simp only [run, update, nextMomentum, PiLp.toLp_apply]

lemma run_accumulator_history (cfg : Config) (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1))
    (g : ℕ → Point b h → Point b h) (s n : ℕ) (j : Fin b) :
    (run cfg x₀ seed g (s+n)).accumulator (.inl j) =
      cfg.β^n * (run cfg x₀ seed g s).accumulator (.inl j) +
      ∑ i : Fin n, cfg.β^(i : ℕ) * ((1-cfg.β) *
        (g (s+(i.rev : ℕ)) (run cfg x₀ seed g (s+(i.rev : ℕ))).point (.inl j))^2) := by
  refine affine_history_expansion
    (fun t => (run cfg x₀ seed g t).accumulator (.inl j))
    (fun t => (1-cfg.β) * (g t (run cfg x₀ seed g t).point (.inl j))^2) cfg.β ?_ s n
  intro t
  simp only [run, update, nextAccumulator, PiLp.toLp_apply]



lemma path_window_displacement_sq {E : Type*} [NormedAddCommGroup E]
    (x : ℕ → E) (s k : ℕ) :
    ‖x (s+k) - x s‖^2 ≤ (k : ℝ) * ∑ j ∈ Finset.range k, ‖x (s+j+1) - x (s+j)‖^2 := by
  have hh := dist_le_range_sum_of_dist_le (f := fun j => x (s+j)) k
    (d := fun j => ‖x (s+j+1) - x (s+j)‖)
    (fun {j} _ => by simp [dist_eq_norm, norm_sub_rev, Nat.add_assoc])
  simp only [Nat.add_zero, dist_eq_norm] at hh
  rw [norm_sub_rev (x s) (x (s+k))] at hh
  have hs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range k)
    (fun _ => (1 : ℝ)) (fun j => ‖x (s+j+1) - x (s+j)‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hs
  exact (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun j _ => norm_nonneg _)).mpr hh |>.trans hs

lemma shifted_energy_sum_le (e : ℕ → ℝ) (he : ∀ j, 0 ≤ e j) (N k j : ℕ) (hj : j ≤ k) :
    (∑ t ∈ Finset.range N, e (t+j)) ≤ ∑ r ∈ Finset.range (N+k), e r := by
  apply Finset.sum_le_sum_of_injOn (fun t => t+j)
  · intro t _ u _ h
    exact Nat.add_right_cancel h
  · intro t ht
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ht
    simp only [Finset.mem_range] at hr ⊢
    omega
  · intro t _
    exact le_rfl
  · intro t _ _
    exact he t

lemma path_windows_energy {E : Type*} [NormedAddCommGroup E]
    (x : ℕ → E) (N k : ℕ) :
    (∑ t ∈ Finset.range N, ‖x (t+k) - x t‖^2) ≤
      (k : ℝ)^2 * ∑ r ∈ Finset.range (N+k), ‖x (r+1) - x r‖^2 := by
  calc
    _ ≤ ∑ t ∈ Finset.range N, (k : ℝ) * ∑ j ∈ Finset.range k, ‖x (t+j+1)-x (t+j)‖^2 :=
      Finset.sum_le_sum fun t _ => path_window_displacement_sq x t k
    _ = (k : ℝ) * ∑ j ∈ Finset.range k, ∑ t ∈ Finset.range N, ‖x (t+j+1)-x (t+j)‖^2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (k : ℝ) * ∑ _j ∈ Finset.range k, ∑ r ∈ Finset.range (N+k), ‖x (r+1)-x r‖^2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro j hj
      exact shifted_energy_sum_le (fun r => ‖x (r+1)-x r‖^2) (fun _ => sq_nonneg _) N k j
        (Nat.le_of_lt (Finset.mem_range.mp hj))
    _ = _ := by simp [pow_two, mul_assoc]



lemma body_reply_difference {Ω : Type*} {b h : ℕ}
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h}
    {L K : ℝ} (hgrad : ∀ x y, ‖grad x-grad y‖ ≤ L*‖x-y‖)
    (ω : Ω) (hnoise : ∀ x y (i : Fin b),
      |(oracle x ω-grad x) (.inl i)-(oracle y ω-grad y) (.inl i)| ≤ K*‖x-y‖)
    (x y : Point b h) (i : Fin b) :
    |oracle x ω (.inl i)-oracle y ω (.inl i)| ≤ (L+K)*‖x-y‖ := by
  have hcoord : |grad x (.inl i)-grad y (.inl i)| ≤ L*‖x-y‖ := by
    have hh := (PiLp.norm_apply_le (grad x-grad y) (.inl i)).trans (hgrad x y)
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using hh
  have hn := hnoise x y i
  change |(oracle x ω (.inl i)-grad x (.inl i))-
    (oracle y ω (.inl i)-grad y (.inl i))| ≤ K*‖x-y‖ at hn
  have ht := abs_add_le
    (grad x (.inl i)-grad y (.inl i))
    ((oracle x ω (.inl i)-grad x (.inl i))-(oracle y ω (.inl i)-grad y (.inl i)))
  have he : (grad x (.inl i)-grad y (.inl i))+
      ((oracle x ω (.inl i)-grad x (.inl i))-(oracle y ω (.inl i)-grad y (.inl i))) =
      oracle x ω (.inl i)-oracle y ω (.inl i) := by ring
  rw [he] at ht
  nlinarith

lemma joint_body_noise_measurable {Ω : Type*} [MeasurableSpace Ω] {b h : ℕ}
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h}
    (ho : Measurable (Function.uncurry oracle)) (hg : Measurable grad) (i : Fin b) :
    Measurable (fun w : Point b h × Ω => (oracle w.1 w.2-grad w.1) (.inl i)) := by
  have hc : Measurable (fun x : Point b h => x (.inl i)) := by fun_prop
  exact hc.comp (ho.sub (hg.comp measurable_fst))



lemma default_bias_multiplier_bounds (n : ℕ) :
    (3/100 : ℝ) ≤ Real.sqrt (1-(999/1000 : ℝ)^(n+1))/(1-(9/10 : ℝ)^(n+1)) ∧
      Real.sqrt (1-(999/1000 : ℝ)^(n+1))/(1-(9/10 : ℝ)^(n+1)) ≤ 10 := by
  have hp := default_bias_parameters n
  have ha0 : 0 < 1-(9/10 : ℝ)^(n+1) := by linarith [hp.1]
  have ha1 : 1-(9/10 : ℝ)^(n+1) ≤ 1 := by
    linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 9/10) (n+1)]
  have hb := pow_le_pow_of_le_one (a := (999/1000 : ℝ)) (by norm_num) (by norm_num)
    (show 1 ≤ n+1 by omega)
  simp only [pow_one] at hb
  have hr : (3/100 : ℝ) ≤ Real.sqrt (1-(999/1000 : ℝ)^(n+1)) := by
    apply (Real.le_sqrt (by norm_num) hp.2.1.le).mpr
    nlinarith
  have hr1 : Real.sqrt (1-(999/1000 : ℝ)^(n+1)) ≤ 1 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by nlinarith [hp.2.2])
  constructor
  · apply (le_div_iff₀ ha0).mpr
    nlinarith
  · apply (div_le_iff₀ ha0).mpr
    nlinarith [hp.1]



lemma run_head_movement_log {b h : ℕ} (cfg : Config) (hr : 0 < cfg.r₀)
    (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1)) (g : ℕ → Point b h → Point b h)
    {η : ℝ} (hη : ∀ n, cfg.headStep n = η) (T : ℕ) (j : Fin h) :
    (∑ n ∈ Finset.range T,
      ((run cfg x₀ seed g (n+1)).point (.inr j)-(run cfg x₀ seed g n).point (.inr j))^2) ≤
      η^2*(Real.log ((run cfg x₀ seed g T).accumulator (.inr j))-Real.log (cfg.r₀^2)) := by
  let v := fun n => (run cfg x₀ seed g n).accumulator (.inr j)
  have hv (n) : 0 < v n := (sq_pos_of_pos hr).trans_le (run_head_accumulator_lower cfg x₀ seed g n j)
  have he (n) : ((run cfg x₀ seed g (n+1)).point (.inr j)-(run cfg x₀ seed g n).point (.inr j))^2 =
      η^2*((v (n+1)-v n)/v (n+1)) := by
    have hrec : v (n+1) = v n + (g n (run cfg x₀ seed g n).point (.inr j))^2 := rfl
    have hp : 0 ≤ v n+(g n (run cfg x₀ seed g n).point (.inr j))^2 :=
      add_nonneg (hv n).le (sq_nonneg _)
    simp only [run,update,nextPoint,nextAccumulator,PiLp.toLp_apply,run_clock,hη]
    rw [sub_sub_cancel_left,neg_sq,div_pow,mul_pow,Real.sq_sqrt hp,hrec]
    dsimp only [v]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left (accumulator_log_sum v hv T) (sq_nonneg η)
  simpa only [v,run,initial,PiLp.toLp_apply] using hh



lemma body_coordinate_absolute_moment {Ω : Type*} [MeasurableSpace Ω] {p : Measure Ω}
    [IsProbabilityMeasure p] {b h : ℕ} {G : Ω → Point b h} {q : Point b h} {σ : ℝ}
    (hGi : Integrable G p)
    (hB : (∫ ω,∑ i : Fin b, |(G ω-q) (.inl i)| ∂p) ≤ σ) (j : Fin b) :
    Integrable (fun ω => G ω (.inl j)) p ∧
      (∫ ω,|G ω (.inl j)| ∂p) ≤ |q (.inl j)|+σ := by
  have hi (i : Fin b) : Integrable (fun ω => G ω (.inl i)) p :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin b ⊕ Fin h => ℝ) (.inl i)).integrable_comp hGi
  have hn (i : Fin b) : Integrable (fun ω => |(G ω-q) (.inl i)|) p :=
    ((hi i).sub (integrable_const (q (.inl i)))).abs
  have hs : Integrable (fun ω => ∑ i : Fin b, |(G ω-q) (.inl i)|) p :=
    integrable_finsetSum _ (fun i _ => hn i)
  have hnb : (∫ ω, |(G ω-q) (.inl j)| ∂p) ≤ σ :=
    (integral_mono (hn j) hs (fun ω => Finset.single_le_sum
      (f := fun i : Fin b => |(G ω-q) (.inl i)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j))).trans hB
  refine ⟨hi j,?_⟩
  calc
    _ ≤ ∫ ω, |q (.inl j)|+|(G ω-q) (.inl j)| ∂p := by
      apply integral_mono (hi j).abs ((integrable_const _).add (hn j))
      intro ω
      have hh := abs_add_le (q (.inl j)) ((G ω-q) (.inl j))
      have he : q (.inl j)+(G ω-q) (.inl j) = G ω (.inl j) := by
        simp only [PiLp.sub_apply]
        ring
      rw [he] at hh
      exact hh
    _ = |q (.inl j)|+(∫ ω,|(G ω-q) (.inl j)| ∂p) := by
      rw [integral_add (integrable_const _) (hn j),integral_const]
      simp only [probReal_univ,smul_eq_mul,one_mul]
    _ ≤ _ := add_le_add_right hnb _

lemma prefix_body_coordinate_absolute_moment {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] {P : Measure X} {p : Measure Ω}
    [IsProbabilityMeasure P] [IsProbabilityMeasure p] {b h : ℕ}
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h}
    {x : X → Point b h} {B σ : ℝ}
    (ho : Measurable (Function.uncurry oracle)) (hx : Measurable x)
    (hi : ∀ z, Integrable (oracle z) p)
    (hσ : ∀ z, (∫ ω,∑ i : Fin b, |(oracle z ω-grad z) (.inl i)| ∂p) ≤ σ)
    (j : Fin b) (hB : ∀ a, |grad (x a) (.inl j)| ≤ B) :
    Integrable (fun w : X × Ω => oracle (x w.1) w.2 (.inl j)) (P.prod p) ∧
      (∫ w : X × Ω,|oracle (x w.1) w.2 (.inl j)| ∂P.prod p) ≤ B+σ := by
  apply LongTails.Proofs.AdaptiveHistoryTracking.prefix_absolute_moment
  · have hp : Measurable (fun v : Point b h => v (.inl j)) := by fun_prop
    exact hp.comp (ho.comp ((hx.comp measurable_fst).prodMk measurable_snd))
  · intro a
    exact (body_coordinate_absolute_moment (hi (x a)) (hσ (x a)) j).1
  · intro a
    exact (body_coordinate_absolute_moment (hi (x a)) (hσ (x a)) j).2.trans
      (add_le_add_left (hB a) σ)


lemma iid_prefix_sample_law {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P) (n : ℕ) :
    MeasurePreserving (fun ω => ((fun i : Fin n => ξ i ω),ξ n ω))
      P ((Measure.pi fun _ : Fin n => p).prod p) := by
  have hh := ((MeasurePreserving.id (Measure.pi fun _ : Fin n => p)).prod
    (measurePreserving_eval (fun _ : Fin 1 => p) 0)).comp (iid_prefix_window_law h n 1)
  simpa only [Function.comp_def,Prod.map_apply,id_eq,Function.eval,Fin.val_zero,Nat.add_zero] using hh

lemma trajectory_prefix_representation {Ω : Type*} (cfg : Config) {b h : ℕ} (x₀ : Point b h)
    (oracle : Point b h → Ω → Point b h) (a : Ω) (ξ : ℕ → Ω) (n : ℕ) :
    trajectory cfg x₀ (fun k x => oracle x (ξ k)) n =
      trajectory cfg x₀ (fun k x => oracle x (paddedSamples a (fun i : Fin n => ξ i) k)) n := by
  apply trajectory_sample_congr_prefix
  intro k hk
  simp only [paddedSamples,dite_eq_left hk]

lemma iid_body_reply_first_moment {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (x₀ : Point b h) (a : Ω)
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h}
    (ho : Measurable (Function.uncurry oracle)) (hi : ∀ z, Integrable (oracle z) p)
    {σ B : ℝ} (hσ : ∀ z, (∫ ω,∑ i : Fin b, |(oracle z ω-grad z) (.inl i)| ∂p) ≤ σ)
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P) (n : ℕ) (j : Fin b)
    (hB : ∀ z : ℕ → Ω, |grad (trajectory cfg x₀ (fun k x => oracle x (z k)) n) (.inl j)| ≤ B) :
    Integrable (fun ω => oracle (trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) n) (ξ n ω) (.inl j)) P ∧
      (∫ ω,|oracle (trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) n) (ξ n ω) (.inl j)| ∂P) ≤ B+σ := by
  let x := fun z : Fin n → Ω => trajectory cfg x₀ (fun k x => oracle x (paddedSamples a z k)) n
  have hx : Measurable x := trajectory_measurable cfg x₀ ho (paddedSamples_measurable a) n
  have hh := prefix_body_coordinate_absolute_moment (P := Measure.pi (fun _ : Fin n => p))
    ho hx hi hσ j (fun z => hB (paddedSamples a z))
  let F := fun w : (Fin n → Ω) × Ω => oracle (x w.1) w.2 (.inl j)
  have hp := iid_prefix_sample_law hs n
  have he (ω : Ξ) : F ((fun i : Fin n => ξ i ω),ξ n ω) =
      oracle (trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) n) (ξ n ω) (.inl j) := by
    dsimp [F,x]
    rw [← trajectory_prefix_representation cfg x₀ oracle a (fun k => ξ k ω) n]
  have hFi : Integrable F ((Measure.pi fun _ : Fin n => p).prod p) := hh.1
  refine ⟨?_,?_⟩
  · have hc := hp.integrable_comp_of_integrable hFi
    simpa only [Function.comp_def,he] using hc
  · have hm := integral_map hp.measurable.aemeasurable
      (f := fun w => |F w|) (hp.map_eq.symm ▸ hFi.abs.aestronglyMeasurable)
    simp only [hp.map_eq,he] at hm
    exact hm.symm.le.trans hh.2


lemma iid_body_accumulator_root_moment {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (hβ : cfg.β = 999/1000) (x₀ : Point b h)
    (seed : Fin (cfg.lastIndex+1)) (a : Ω)
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h}
    (ho : Measurable (Function.uncurry oracle)) (hi : ∀ z, Integrable (oracle z) p)
    {σ B : ℝ} (hν : 0 ≤ B+σ)
    (hσ : ∀ z, (∫ ω,∑ i : Fin b, |(oracle z ω-grad z) (.inl i)| ∂p) ≤ σ)
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P) (n : ℕ) (j : Fin b)
    (hB : ∀ t<n, ∀ z : ℕ → Ω,
      |grad (trajectory cfg x₀ (fun k x => oracle x (z k)) t) (.inl j)| ≤ B) :
    Integrable (fun ω => Real.sqrt ((run cfg x₀ seed (fun k x => oracle x (ξ k ω)) n).accumulator (.inl j))) P ∧
      (∫ ω,Real.sqrt ((run cfg x₀ seed (fun k x => oracle x (ξ k ω)) n).accumulator (.inl j)) ∂P) ≤ 64*(B+σ) := by
  let w := fun i : Fin n => (1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ)
  let X := fun i : Fin n => fun ω =>
    oracle (trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) i.rev) (ξ i.rev ω) (.inl j)
  have hX (i : Fin n) : Measurable (X i) := by
    have hc : Measurable (fun v : Point b h => v (.inl j)) := by fun_prop
    exact hc.comp (ho.comp ((trajectory_measurable cfg x₀ ho hs.measurable i.rev).prodMk (hs.measurable i.rev)))
  have hm (i : Fin n) := iid_body_reply_first_moment cfg x₀ a ho hi hσ hs i.rev j (hB i.rev i.rev.isLt)
  have hh := LongTails.Proofs.AdaptiveHistoryFinite.weightedRoot_moment w X (fun _ => B+σ)
    (fun i => by dsimp [w]; positivity) hX (fun i => (hm i).1) (fun i => (hm i).2)
  have he (ω : Ξ) : (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) n).accumulator (.inl j) =
      ∑ i : Fin n,w i*(X i ω)^2 := by
    have hhist := run_accumulator_history cfg x₀ seed (fun k x => oracle x (ξ k ω)) 0 n j
    simp only [run,initial,PiLp.toLp_apply,mul_zero,zero_add,hβ,run_point] at hhist
    rw [hhist]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [w,X]
    ring
  simp_rw [he]
  refine ⟨hh.1,hh.2.trans ?_⟩
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right
    ((LongTails.Proofs.AdaptiveHistoryFinite.geometric_root_sum_le n (by norm_num : (0 : ℝ)≤999/1000)
      (by norm_num : (999/1000 : ℝ)<1)).trans
        LongTails.Proofs.AdaptiveHistoryFinite.default_geometric_root_constant) hν



lemma body_sum_absolute_moment {Ω : Type*} [MeasurableSpace Ω] {p : Measure Ω}
    [IsProbabilityMeasure p] {b h : ℕ} {G : Ω → Point b h} {q : Point b h} {σ : ℝ}
    (hGi : Integrable G p)
    (hB : (∫ ω,∑ i : Fin b, |(G ω-q) (.inl i)| ∂p) ≤ σ) :
    Integrable (fun ω => ∑ j : Fin b, |G ω (.inl j)|) p ∧
      (∫ ω,∑ j : Fin b,|G ω (.inl j)| ∂p) ≤ (∑ j : Fin b,|q (.inl j)|)+σ := by
  have hi (i : Fin b) := (body_coordinate_absolute_moment hGi hB i).1
  have hn (i : Fin b) : Integrable (fun ω => |(G ω-q) (.inl i)|) p :=
    ((hi i).sub (integrable_const (q (.inl i)))).abs
  have hni := integrable_finsetSum Finset.univ (fun i _ => hn i)
  have hsi := integrable_finsetSum Finset.univ (fun i _ => (hi i).abs)
  have hp (ω) : (∑ j : Fin b,|G ω (.inl j)|) ≤
      (∑ j : Fin b,|q (.inl j)|)+(∑ j : Fin b,|(G ω-q) (.inl j)|) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    have hh := abs_add_le (q (.inl j)) ((G ω-q) (.inl j))
    have he : q (.inl j)+(G ω-q) (.inl j)=G ω (.inl j) := by
      simp only [PiLp.sub_apply]
      ring
    rw [he] at hh
    exact hh
  refine ⟨hsi,?_⟩
  have hh := integral_mono hsi ((integrable_const _).add hni) hp
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const (∑ j : Fin b,|q (.inl j)|)) hni,integral_const] at hh
  simp only [probReal_univ,smul_eq_mul,one_mul] at hh
  exact hh.trans (add_le_add_right hB _)

lemma prefix_body_sum_absolute_moment {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] {P : Measure X} {p : Measure Ω}
    [IsProbabilityMeasure P] [IsProbabilityMeasure p] {b h : ℕ}
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h}
    {x : X → Point b h} {B σ : ℝ}
    (ho : Measurable (Function.uncurry oracle)) (hx : Measurable x)
    (hi : ∀ z, Integrable (oracle z) p)
    (hσ : ∀ z, (∫ ω,∑ i : Fin b, |(oracle z ω-grad z) (.inl i)| ∂p) ≤ σ)
    (hB : ∀ a (j : Fin b), |grad (x a) (.inl j)| ≤ B) :
    Integrable (fun w : X × Ω => ∑ j : Fin b,|oracle (x w.1) w.2 (.inl j)|) (P.prod p) ∧
      (∫ w : X × Ω,∑ j : Fin b,|oracle (x w.1) w.2 (.inl j)| ∂P.prod p) ≤ b*B+σ := by
  have hsum (a : X) : (∑ j : Fin b, |grad (x a) (.inl j)|) ≤ b*B := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => hB a j)
  have hm : Measurable (fun w : X × Ω => ∑ j : Fin b,|oracle (x w.1) w.2 (.inl j)|) := by
    have hc : Measurable (fun v : Point b h => ∑ j : Fin b,|v (.inl j)|) := by fun_prop
    exact hc.comp (ho.comp ((hx.comp measurable_fst).prodMk measurable_snd))
  have ha (z : Point b h) : abs (∑ j : Fin b, |z (.inl j)|) = ∑ j : Fin b,|z (.inl j)| :=
    abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hh := LongTails.Proofs.AdaptiveHistoryTracking.prefix_absolute_moment (P := P) hm
    (fun a => (body_sum_absolute_moment (hi (x a)) (hσ (x a))).1)
    (fun a => by
      simp only [ha]
      exact (body_sum_absolute_moment (hi (x a)) (hσ (x a))).2.trans (add_le_add_left (hsum a) σ))
  simpa only [ha] using hh

lemma iid_body_reply_sum_first_moment {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (x₀ : Point b h) (a : Ω)
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h}
    (ho : Measurable (Function.uncurry oracle)) (hi : ∀ z, Integrable (oracle z) p)
    {σ B : ℝ} (hσ : ∀ z, (∫ ω,∑ i : Fin b, |(oracle z ω-grad z) (.inl i)| ∂p) ≤ σ)
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P) (n : ℕ)
    (hB : ∀ (z : ℕ → Ω) (j : Fin b),
      |grad (trajectory cfg x₀ (fun k x => oracle x (z k)) n) (.inl j)| ≤ B) :
    Integrable (fun ω => ∑ j : Fin b,
      |oracle (trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) n) (ξ n ω) (.inl j)|) P ∧
      (∫ ω,∑ j : Fin b,
        |oracle (trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) n) (ξ n ω) (.inl j)| ∂P) ≤ b*B+σ := by
  let x := fun z : Fin n → Ω => trajectory cfg x₀ (fun k x => oracle x (paddedSamples a z k)) n
  have hx : Measurable x := trajectory_measurable cfg x₀ ho (paddedSamples_measurable a) n
  have hh := prefix_body_sum_absolute_moment (P := Measure.pi (fun _ : Fin n => p))
    ho hx hi hσ (fun z => hB (paddedSamples a z))
  let F := fun w : (Fin n → Ω) × Ω => ∑ j : Fin b,|oracle (x w.1) w.2 (.inl j)|
  have hp := iid_prefix_sample_law hs n
  have he (ω : Ξ) : F ((fun i : Fin n => ξ i ω),ξ n ω) =
      ∑ j : Fin b,|oracle (trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) n) (ξ n ω) (.inl j)| := by
    dsimp [F,x]
    rw [← trajectory_prefix_representation cfg x₀ oracle a (fun k => ξ k ω) n]
  have hFi : Integrable F ((Measure.pi fun _ : Fin n => p).prod p) := hh.1
  refine ⟨?_,?_⟩
  · have hc := hp.integrable_comp_of_integrable hFi
    simpa only [Function.comp_def,he] using hc
  · have hm := integral_map hp.measurable.aemeasurable
      (f := F) (hp.map_eq.symm ▸ hFi.aestronglyMeasurable)
    simp only [hp.map_eq,he] at hm
    exact hm.symm.le.trans hh.2


lemma iid_body_accumulator_sum_root_moment {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (hβ : cfg.β = 999/1000) (x₀ : Point b h)
    (seed : Fin (cfg.lastIndex+1)) (a : Ω)
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h}
    (ho : Measurable (Function.uncurry oracle)) (hi : ∀ z, Integrable (oracle z) p)
    {σ B : ℝ} (hν : 0 ≤ b*B+σ)
    (hσ : ∀ z, (∫ ω,∑ i : Fin b, |(oracle z ω-grad z) (.inl i)| ∂p) ≤ σ)
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P) (n : ℕ)
    (hB : ∀ t<n, ∀ (z : ℕ → Ω) (j : Fin b),
      |grad (trajectory cfg x₀ (fun k x => oracle x (z k)) t) (.inl j)| ≤ B) :
    Integrable (fun ω => ∑ j : Fin b,
      Real.sqrt ((run cfg x₀ seed (fun k x => oracle x (ξ k ω)) n).accumulator (.inl j))) P ∧
      (∫ ω,∑ j : Fin b,
        Real.sqrt ((run cfg x₀ seed (fun k x => oracle x (ξ k ω)) n).accumulator (.inl j)) ∂P) ≤ 64*(b*B+σ) := by
  let w := fun i : Fin n => (1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ)
  let X := fun (j : Fin b) (i : Fin n) => fun ω =>
    oracle (trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) i.rev) (ξ i.rev ω) (.inl j)
  have hX (j : Fin b) (i : Fin n) : Measurable (X j i) := by
    have hc : Measurable (fun v : Point b h => v (.inl j)) := by fun_prop
    exact hc.comp (ho.comp ((trajectory_measurable cfg x₀ ho hs.measurable i.rev).prodMk (hs.measurable i.rev)))
  have hm (j : Fin b) (i : Fin n) := iid_body_reply_first_moment cfg x₀ a ho hi hσ hs i.rev j
    (fun z => hB i.rev i.rev.isLt z j)
  have hsum (i : Fin n) := iid_body_reply_sum_first_moment cfg x₀ a ho hi hσ hs i.rev (hB i.rev i.rev.isLt)
  have hh := LongTails.Proofs.AdaptiveHistoryFinite.sum_weightedRoot_moment w X (fun _ => b*B+σ)
    (fun i => by dsimp [w]; positivity) hX (fun j i => (hm j i).1) (fun i => (hsum i).2)
  have he (ω : Ξ) (j : Fin b) :
      (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) n).accumulator (.inl j) =
        ∑ i : Fin n,w i*(X j i ω)^2 := by
    have hhist := run_accumulator_history cfg x₀ seed (fun k x => oracle x (ξ k ω)) 0 n j
    simp only [run,initial,PiLp.toLp_apply,mul_zero,zero_add,hβ,run_point] at hhist
    rw [hhist]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [w,X]
    ring
  simp_rw [he]
  refine ⟨hh.1,hh.2.trans ?_⟩
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right
    ((LongTails.Proofs.AdaptiveHistoryFinite.geometric_root_sum_le n (by norm_num : (0 : ℝ)≤999/1000)
      (by norm_num : (999/1000 : ℝ)<1)).trans
        LongTails.Proofs.AdaptiveHistoryFinite.default_geometric_root_constant) hν



lemma run_full_history_caps {b h : ℕ} (cfg : Config)
    (hα : cfg.α=9/10) (hβ : cfg.β=999/1000) (x₀ : Point b h)
    (seed : Fin (cfg.lastIndex+1)) (g : ℕ → Point b h → Point b h)
    (s n : ℕ) (j : Fin b) {δ : ℝ} (hδ : 0 < δ) (w : Fin n → ℝ) :
    let a := fun i : Fin n => (1-(9/10 : ℝ))*(9/10 : ℝ)^(i : ℕ)
    let b := fun i : Fin n => (1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ)
    let z := fun i : Fin n => g (s+i.rev) (run cfg x₀ seed g (s+i.rev)).point (.inl j)
    let M := (9/10 : ℝ)^n*(run cfg x₀ seed g s).momentum (.inl j)
    let V := (999/1000 : ℝ)^n*(run cfg x₀ seed g s).accumulator (.inl j)
    let H := (M+∑ i,a i*w i)/(δ+Real.sqrt (V+∑ i,b i*(w i)^2))
    |(run cfg x₀ seed g (s+n)).momentum (.inl j)/
      (δ+Real.sqrt ((run cfg x₀ seed g (s+n)).accumulator (.inl j)))-H| ≤
        16*min 1 (Real.sqrt (∑ i,b i*(z i-w i)^2)/(δ+Real.sqrt (∑ i,b i*(w i)^2))) ∧
    |H-(∑ i,a i*w i)/(δ+Real.sqrt (∑ i,b i*(w i)^2))| ≤
      16*min 1 (Real.sqrt V/(δ+Real.sqrt (∑ i,b i*(w i)^2))) := by
  dsimp only
  let a := fun i : Fin n => (1-(9/10 : ℝ))*(9/10 : ℝ)^(i : ℕ)
  let b := fun i : Fin n => (1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ)
  let z := fun i : Fin n => g (s+i.rev) (run cfg x₀ seed g (s+i.rev)).point (.inl j)
  have hMf : (run cfg x₀ seed g (s+n)).momentum (.inl j) =
      (9/10 : ℝ)^n*(run cfg x₀ seed g s).momentum (.inl j)+∑ i,a i*z i := by
    rw [run_momentum_history,hα]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    dsimp [a,z]
    ring
  have hVf : (run cfg x₀ seed g (s+n)).accumulator (.inl j) =
      (999/1000 : ℝ)^n*(run cfg x₀ seed g s).accumulator (.inl j)+∑ i,b i*(z i)^2 := by
    rw [run_accumulator_history,hβ]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    dsimp [b,z]
    ring
  have hi := run_body_moment_bound cfg hα hβ x₀ seed g s j
  have hh := LongTails.Proofs.AdaptiveHistoryTracking.default_full_history_caps hi.1 hi.2 hδ z w
  rw [hMf,hVf]
  simpa only [zero_add] using hh



lemma body_coordinate_noise_integrals {Ω : Type*} [MeasurableSpace Ω] {p : Measure Ω}
    [IsProbabilityMeasure p] {b h : ℕ}
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h} {σ : ℝ}
    (ho : Measurable (Function.uncurry oracle)) (hg : Measurable grad)
    (hi : ∀ x,Integrable (oracle x) p)
    (hσ : ∀ x,(∫ ω,∑ j : Fin b,|(oracle x ω-grad x) (.inl j)| ∂p) ≤ σ) :
    (∀ j : Fin b,Measurable (fun x => ∫ ω,|(oracle x ω-grad x) (.inl j)| ∂p)) ∧
      ∀ x,(∑ j : Fin b,∫ ω,|(oracle x ω-grad x) (.inl j)| ∂p) ≤ σ := by
  constructor
  · intro j
    have hm := joint_body_noise_measurable ho hg j
    have ha : Measurable (fun w : Point b h × Ω => |(oracle w.1 w.2-grad w.1) (.inl j)|) := by fun_prop
    exact ha.stronglyMeasurable.integral_prod_right'.measurable
  · intro x
    have hni (j : Fin b) : Integrable (fun ω => |(oracle x ω-grad x) (.inl j)|) p := by
      have hc := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin b ⊕ Fin h => ℝ) (.inl j)).integrable_comp
        ((hi x).sub (integrable_const (grad x)))
      exact hc.abs
    rw [← integral_finsetSum _ (fun j _ => hni j)]
    exact hσ x



lemma default_effective_stabilizer {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    0 < δ*Real.sqrt (1-(999/1000 : ℝ)^(n+1)) ∧
      δ*Real.sqrt (1-(999/1000 : ℝ)^(n+1)) ≤ δ := by
  have hp := default_bias_parameters n
  have hs : Real.sqrt (1-(999/1000 : ℝ)^(n+1)) ≤ 1 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by simpa using hp.2.2)
  exact ⟨mul_pos hδ (Real.sqrt_pos.mpr hp.2.1),by nlinarith⟩

lemma run_body_update_identity {b h : ℕ} (cfg : Config)
    (hα : cfg.α=9/10) (hβ : cfg.β=999/1000) (hδ : 0 < cfg.δ)
    (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1))
    (g : ℕ → Point b h → Point b h) (n : ℕ) (j : Fin b) :
    (run cfg x₀ seed g (n+1)).point (.inl j)-(run cfg x₀ seed g n).point (.inl j) =
      -cfg.bodyStep n*(Real.sqrt (1-(999/1000 : ℝ)^(n+1))/(1-(9/10 : ℝ)^(n+1)))*
        ((run cfg x₀ seed g (n+1)).momentum (.inl j)/
          (cfg.δ*Real.sqrt (1-(999/1000 : ℝ)^(n+1))+
            Real.sqrt ((run cfg x₀ seed g (n+1)).accumulator (.inl j)))) := by
  let m := (run cfg x₀ seed g (n+1)).momentum (.inl j)
  let v := (run cfg x₀ seed g (n+1)).accumulator (.inl j)
  have hp := default_bias_parameters n
  have ha : 0 < 1-(9/10 : ℝ)^(n+1) := by linarith [hp.1]
  have hv := (run_body_moment_bound cfg hα hβ x₀ seed g (n+1) j).1
  have hb := bias_corrected_direction_identity (m := m) ha hp.2.1 hδ hv
  have he : (run cfg x₀ seed g (n+1)).point (.inl j)-(run cfg x₀ seed g n).point (.inl j) =
      -cfg.bodyStep n*((m/(1-(9/10 : ℝ)^(n+1)))/(cfg.δ+Real.sqrt (v/(1-(999/1000 : ℝ)^(n+1))))) := by
    simp only [run,update,nextPoint,nextMomentum,nextAccumulator,PiLp.toLp_apply,run_clock,hα,hβ,m,v]
    ring
  rw [he,hb]
  ring



lemma prefix_deleted_window_law {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    {P : Measure X} {p : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure p]
    {n : ℕ} (i : Fin (n+1)) :
    MeasurePreserving (fun w : X × (Fin (n+1) → Ω) => (w.1,fun j => w.2 (i.succAbove j)))
      (P.prod (Measure.pi (fun _ : Fin (n+1) => p)))
      (P.prod (Measure.pi (fun _ : Fin n => p))) := by
  have hp := (measurePreserving_snd (μ := p) (ν := Measure.pi (fun _ : Fin n => p))).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => p) i)
  exact (MeasurePreserving.id P).prod hp

lemma iid_prefix_reverse_deleted_law {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (m n : ℕ) (i : Fin (n+1)) :
    MeasurePreserving (fun ω => ((fun j : Fin m => ξ j ω),fun j : Fin n => ξ (m+(i.succAbove j).rev) ω))
      P ((Measure.pi fun _ : Fin m => p).prod (Measure.pi fun _ : Fin n => p)) := by
  exact (prefix_deleted_window_law (P := Measure.pi (fun _ : Fin m => p)) i).comp
    (iid_prefix_reverse_window_law h m (n+1))

lemma integral_prefix_deleted_window {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    {P : Measure X} {p : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure p]
    {n : ℕ} (i : Fin (n+1)) {f : X × (Fin n → Ω) → ℝ}
    (hf : AEStronglyMeasurable f (P.prod (Measure.pi (fun _ : Fin n => p)))) :
    (∫ w : X × (Fin (n+1) → Ω),f (w.1,fun j => w.2 (i.succAbove j))
      ∂P.prod (Measure.pi (fun _ : Fin (n+1) => p))) =
        ∫ w,f w ∂P.prod (Measure.pi (fun _ : Fin n => p)) := by
  have hp := prefix_deleted_window_law (P := P) (p := p) i
  have hh := integral_map hp.measurable.aemeasurable (f := f) (hp.map_eq.symm ▸ hf)
  simpa only [hp.map_eq] using hh.symm



lemma iid_reverse_deleted_displacement_moment {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h m n : ℕ}
    (cfg : Config) (hα : cfg.α=9/10) (hβ : cfg.β=999/1000) (hδ : 0 < cfg.δ)
    (x₀ : Point b h) {oracle : Point b h → Ω → Point b h}
    (ho : Measurable (Function.uncurry oracle))
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (i : Fin (n+1)) (a : Ω) (t s : ℕ)
    (ht : t ≤ m+(i.rev : ℕ)) (hs' : s ≤ m+(i.rev : ℕ)) :
    (∫ w : (Fin m → Ω) × (Fin n → Ω),
      ‖trajectory cfg x₀ (fun k x => oracle x (prefixReverseSamples a w.1 (i.insertNth a w.2) k)) t-
        trajectory cfg x₀ (fun k x => oracle x (prefixReverseSamples a w.1 (i.insertNth a w.2) k)) s‖^2
      ∂(Measure.pi (fun _ : Fin m => p)).prod (Measure.pi (fun _ : Fin n => p))) =
    ∫ ω,‖trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) t-
      trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) s‖^2 ∂P := by
  let F := fun w : (Fin m → Ω) × (Fin n → Ω) =>
    ‖trajectory cfg x₀ (fun k x => oracle x (prefixReverseSamples a w.1 (i.insertNth a w.2) k)) t-
      trajectory cfg x₀ (fun k x => oracle x (prefixReverseSamples a w.1 (i.insertNth a w.2) k)) s‖^2
  have hFi : Integrable F ((Measure.pi (fun _ : Fin m => p)).prod (Measure.pi (fun _ : Fin n => p))) :=
    (reverse_complementary_displacement_memLp cfg hα hβ hδ x₀ ho i a t s _).integrable_sq
  have hp := iid_prefix_reverse_deleted_law hs m n i
  have he (ω : Ξ) (u : ℕ) (hu : u ≤ m+(i.rev : ℕ)) :
      trajectory cfg x₀ (fun k x => oracle x
        (prefixReverseSamples a (fun j : Fin m => ξ j ω)
          (i.insertNth a (fun j : Fin n => ξ (m+(i.succAbove j).rev) ω)) k)) u =
      trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) u := by
    have hrep := trajectory_reverse_deleted_representation cfg x₀ oracle
      (fun j : Fin m => ξ j ω) i (fun j : Fin (n+1) => ξ (m+j.rev) ω) a u hu
    rw [← hrep]
    exact (trajectory_prefix_reverse_representation cfg x₀ oracle a (fun k => ξ k ω) m (n+1) u
      (by have hi := i.rev.isLt; omega)).symm
  have hm := integral_map hp.measurable.aemeasurable (f := F) (hp.map_eq.symm ▸ hFi.aestronglyMeasurable)
  simp only [hp.map_eq,F] at hm
  simpa only [he _ t ht,he _ s hs'] using hm



lemma trajectory_prefixReverse_before {Ω : Type*} {b h m n : ℕ}
    (cfg : Config) (x₀ : Point b h) (oracle : Point b h → Ω → Point b h)
    (a : Ω) (pre : Fin m → Ω) (z : Fin n → Ω) (s : ℕ) (hs : s ≤ m) :
    trajectory cfg x₀ (fun k x => oracle x (prefixReverseSamples a pre z k)) s =
      trajectory cfg x₀ (fun k x => oracle x (paddedSamples a pre k)) s := by
  apply trajectory_sample_congr_prefix
  intro k hk
  have hkm : k < m := lt_of_lt_of_le hk hs
  simp only [prefixReverseSamples,paddedSamples,dite_eq_left hkm]

lemma reverse_window_reply_difference {Ω : Type*} [MeasurableSpace Ω]
    {p : Measure Ω} [IsProbabilityMeasure p] {b h m n : ℕ}
    (cfg : Config) (x₀ : Point b h) (a : Ω)
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h}
    {L : ℝ} {K : Ω → ℝ}
    (hgrad : ∀ x y,‖grad x-grad y‖ ≤ L*‖x-y‖)
    (hnoise : ∀ᵐ ω ∂p,∀ x y (j : Fin b),
      |(oracle x ω-grad x) (.inl j)-(oracle y ω-grad y) (.inl j)| ≤ K ω*‖x-y‖)
    (s : ℕ) (hs : s ≤ m) (j : Fin b) :
    ∀ᵐ w : (Fin m → Ω) × (Fin (n+1) → Ω)
      ∂(Measure.pi (fun _ : Fin m => p)).prod (Measure.pi (fun _ : Fin (n+1) => p)),∀ i : Fin (n+1),
      |oracle (trajectory cfg x₀ (fun k x => oracle x (prefixReverseSamples a w.1 w.2 k)) (m+i.rev)) (w.2 i) (.inl j)-
        oracle (trajectory cfg x₀ (fun k x => oracle x (paddedSamples a w.1 k)) s) (w.2 i) (.inl j)| ≤
      (L+K (w.2 i))*‖trajectory cfg x₀ (fun k x => oracle x
          (prefixReverseSamples a w.1 (i.insertNth a (fun l => w.2 (i.succAbove l))) k)) (m+i.rev)-
        trajectory cfg x₀ (fun k x => oracle x
          (prefixReverseSamples a w.1 (i.insertNth a (fun l => w.2 (i.succAbove l))) k)) s‖ := by
  apply ae_all_iff.mpr
  intro i
  have hp := (measurePreserving_eval (fun _ : Fin (n+1) => p) i).comp
    (measurePreserving_snd (μ := Measure.pi (fun _ : Fin m => p))
      (ν := Measure.pi (fun _ : Fin (n+1) => p)))
  have hn := hp.quasiMeasurePreserving.ae hnoise
  filter_upwards [hn] with w hw
  have hh := body_reply_difference hgrad (w.2 i) hw
    (trajectory cfg x₀ (fun k x => oracle x (prefixReverseSamples a w.1 w.2 k)) (m+i.rev))
    (trajectory cfg x₀ (fun k x => oracle x (paddedSamples a w.1 k)) s) j
  refine hh.trans_eq ?_
  congr 1
  rw [← trajectory_prefixReverse_before cfg x₀ oracle a w.1 w.2 s hs,
    trajectory_reverse_deleted_representation cfg x₀ oracle w.1 i w.2 a (m+i.rev) le_rfl,
    trajectory_reverse_deleted_representation cfg x₀ oracle w.1 i w.2 a s (by omega)]



lemma run_prefixReverse_before {Ω : Type*} {b h m n : ℕ}
    (cfg : Config) (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1))
    (oracle : Point b h → Ω → Point b h) (a : Ω)
    (pre : Fin m → Ω) (z : Fin n → Ω) (s : ℕ) (hs : s ≤ m) :
    run cfg x₀ seed (fun k x => oracle x (prefixReverseSamples a pre z k)) s =
      run cfg x₀ seed (fun k x => oracle x (paddedSamples a pre k)) s := by
  apply run_congr_prefix
  intro k hk
  have hkm : k < m := lt_of_lt_of_le hk hs
  simp only [prefixReverseSamples,paddedSamples,dite_eq_left hkm]

lemma run_prefix_reverse_representation {Ω : Type*} {b h : ℕ}
    (cfg : Config) (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1))
    (oracle : Point b h → Ω → Point b h) (a : Ω) (ξ : ℕ → Ω) (m n t : ℕ)
    (ht : t ≤ m+n) :
    run cfg x₀ seed (fun k x => oracle x (ξ k)) t =
      run cfg x₀ seed (fun k x => oracle x
        (prefixReverseSamples a (fun i : Fin m => ξ i) (fun i : Fin n => ξ (m+i.rev)) k)) t := by
  apply run_congr_prefix
  intro k hk
  funext x
  rw [prefixReverseSamples_reconstruct a ξ m n k (by omega)]

lemma run_reverse_window_history {Ω : Type*} {b h m n : ℕ}
    (cfg : Config) (hα : cfg.α=9/10) (hβ : cfg.β=999/1000)
    (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1))
    (oracle : Point b h → Ω → Point b h) (a : Ω)
    (pre : Fin m → Ω) (z : Fin n → Ω) (j : Fin b) :
    let g := fun k x => oracle x (prefixReverseSamples a pre z k)
    let old := run cfg x₀ seed (fun k x => oracle x (paddedSamples a pre k)) m
    let Z := fun i : Fin n => oracle (trajectory cfg x₀ g (m+i.rev)) (z i) (.inl j)
    (run cfg x₀ seed g (m+n)).momentum (.inl j) =
      (9/10 : ℝ)^n*old.momentum (.inl j)+∑ i : Fin n,(1-(9/10 : ℝ))*(9/10 : ℝ)^(i : ℕ)*Z i ∧
    (run cfg x₀ seed g (m+n)).accumulator (.inl j) =
      (999/1000 : ℝ)^n*old.accumulator (.inl j)+∑ i : Fin n,(1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ)*(Z i)^2 := by
  dsimp only
  let g := fun k x => oracle x (prefixReverseSamples a pre z k)
  have hz (i : Fin n) : prefixReverseSamples a pre z (m+i.rev)=z i := by
    have hnm : ¬m+(i.rev : ℕ)<m := by omega
    simp only [prefixReverseSamples,dite_eq_right hnm,Nat.add_sub_cancel_left,paddedSamples,
      dite_eq_left i.rev.isLt]
    change z i.rev.rev=z i
    rw [Fin.rev_rev]
  have hm := run_momentum_history cfg x₀ seed g m n j
  have hv := run_accumulator_history cfg x₀ seed g m n j
  dsimp [g] at hm hv
  simp only [hα,hβ,run_point,run_prefixReverse_before cfg x₀ seed oracle a pre z m le_rfl] at hm hv
  constructor
  · convert hm using 1
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [show n-((i : ℕ)+1)=(i.rev : ℕ) from rfl,hz i]
    ring
  · convert hv using 1
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [show n-((i : ℕ)+1)=(i.rev : ℕ) from rfl,hz i]
    ring

lemma iid_prefix_run_integral {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1))
    (oracle : Point b h → Ω → Point b h) (a : Ω)
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (n : ℕ) (F : State b h → ℝ)
    (hF : AEStronglyMeasurable (fun pre : Fin n → Ω =>
      F (run cfg x₀ seed (fun k x => oracle x (paddedSamples a pre k)) n))
      (Measure.pi (fun _ : Fin n => p))) :
    (Integrable (fun pre : Fin n → Ω => F (run cfg x₀ seed (fun k x => oracle x (paddedSamples a pre k)) n))
      (Measure.pi (fun _ : Fin n => p)) ↔
      Integrable (fun ω => F (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) n)) P) ∧
    (∫ pre : Fin n → Ω,F (run cfg x₀ seed (fun k x => oracle x (paddedSamples a pre k)) n)
      ∂Measure.pi (fun _ : Fin n => p)) =
      ∫ ω,F (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) n) ∂P := by
  have hp := (measurePreserving_fst (μ := Measure.pi (fun _ : Fin n => p)) (ν := p)).comp
    (iid_prefix_sample_law hs n)
  have he (ω : Ξ) : run cfg x₀ seed (fun k x => oracle x (paddedSamples a (fun i : Fin n => ξ i ω) k)) n =
      run cfg x₀ seed (fun k x => oracle x (ξ k ω)) n := by
    apply run_congr_prefix
    intro k hk
    simp only [paddedSamples,dite_eq_left hk]
  constructor
  · have hi := hp.integrable_comp hF
    simpa only [Function.comp_def,he] using hi.symm
  · have hi := integral_map hp.measurable.aemeasurable
      (f := fun pre : Fin n → Ω => F (run cfg x₀ seed (fun k x => oracle x (paddedSamples a pre k)) n))
      (hp.map_eq.symm ▸ hF)
    have hmap : P.map (fun ω => fun i : Fin n => ξ i ω)=Measure.pi (fun _ : Fin n => p) := hp.map_eq
    simp only [Function.comp_def] at hi
    simpa only [hmap,he] using hi


lemma run_body_normalized_bound {b h : ℕ} (cfg : Config)
    (hα : cfg.α=9/10) (hβ : cfg.β=999/1000) (x₀ : Point b h)
    (seed : Fin (cfg.lastIndex+1)) (g : ℕ → Point b h → Point b h)
    (n : ℕ) (j : Fin b) {δ : ℝ} (hδ : 0 < δ) :
    |(run cfg x₀ seed g n).momentum (.inl j)/
      (δ+Real.sqrt ((run cfg x₀ seed g n).accumulator (.inl j)))| ≤ 8 := by
  have hi := run_body_moment_bound cfg hα hβ x₀ seed g n j
  exact normalized_value_bound (Real.sqrt_nonneg _) hδ (by norm_num)
    (momentum_sqrt_bound hi.1 hi.2)


lemma body_gradient_direction_integrable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ξ} [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (hα : cfg.α=9/10) (hβ : cfg.β=999/1000)
    (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1))
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h} {ξ : ℕ → Ξ → Ω}
    (ho : Measurable (Function.uncurry oracle)) (hg : Measurable grad) (hξ : ∀ k,Measurable (ξ k))
    (u t : ℕ) (j : Fin b) {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
    (hGB : ∀ z : ℕ → Ω,|grad (trajectory cfg x₀ (fun k x => oracle x (z k)) u) (.inl j)| ≤ B) :
    Integrable (fun ω => grad (trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) u) (.inl j)*
      ((run cfg x₀ seed (fun k x => oracle x (ξ k ω)) t).momentum (.inl j)/
        (δ+Real.sqrt ((run cfg x₀ seed (fun k x => oracle x (ξ k ω)) t).accumulator (.inl j))))) P := by
  let F := fun ω => (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) t).momentum (.inl j)/
    (δ+Real.sqrt ((run cfg x₀ seed (fun k x => oracle x (ξ k ω)) t).accumulator (.inl j)))
  let G := fun ω => grad (trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) u) (.inl j)
  have hc : Measurable (fun v : Point b h => v (.inl j)) := by fun_prop
  have hr := run_core_measurable cfg x₀ seed ho hξ t
  have hF : Measurable F := (hc.comp hr.2.1).div (measurable_const.add (hc.comp hr.2.2).sqrt)
  have hG : Measurable G := hc.comp (hg.comp (trajectory_measurable cfg x₀ ho hξ u))
  have hFb (ω) : |F ω| ≤ 8 := by
    have hh := run_body_moment_bound cfg hα hβ x₀ seed (fun k x => oracle x (ξ k ω)) t j
    exact normalized_value_bound (Real.sqrt_nonneg _) hδ (by norm_num) (momentum_sqrt_bound hh.1 hh.2)
  have hb (ω) : ‖G ω*F ω‖ ≤ B*8 := by
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul (hGB (fun k => ξ k ω)) (hFb ω) (abs_nonneg _) hB
  exact (show MemLp (fun ω => G ω*F ω) 1 P from MemLp.of_bound
    (hG.mul hF).aestronglyMeasurable (B*8) (Filter.Eventually.of_forall hb)).integrable (by norm_num)


lemma run_head_update_identity {b h : ℕ} (cfg : Config) (x₀ : Point b h)
    (seed : Fin (cfg.lastIndex+1)) (g : ℕ → Point b h → Point b h) (n : ℕ) (j : Fin h) :
    (run cfg x₀ seed g (n+1)).point (.inr j)-(run cfg x₀ seed g n).point (.inr j) =
      -cfg.headStep n*g n (run cfg x₀ seed g n).point (.inr j)/
        Real.sqrt ((run cfg x₀ seed g n).accumulator (.inr j)+(g n (run cfg x₀ seed g n).point (.inr j))^2) := by
  simp only [run,update,nextPoint,nextAccumulator,PiLp.toLp_apply,run_clock]
  ring


lemma iid_run_sample_integral {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1))
    (oracle : Point b h → Ω → Point b h) (a : Ω)
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (n : ℕ) (F : State b h → Ω → ℝ)
    (hF : AEStronglyMeasurable (fun w : (Fin n → Ω) × Ω =>
      F (run cfg x₀ seed (fun k x => oracle x (paddedSamples a w.1 k)) n) w.2)
      ((Measure.pi (fun _ : Fin n => p)).prod p)) :
    (Integrable (fun w : (Fin n → Ω) × Ω => F (run cfg x₀ seed (fun k x => oracle x (paddedSamples a w.1 k)) n) w.2)
      ((Measure.pi (fun _ : Fin n => p)).prod p) ↔
      Integrable (fun ω => F (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) n) (ξ n ω)) P) ∧
    (∫ w : (Fin n → Ω) × Ω,F (run cfg x₀ seed (fun k x => oracle x (paddedSamples a w.1 k)) n) w.2
      ∂(Measure.pi (fun _ : Fin n => p)).prod p) =
      ∫ ω,F (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) n) (ξ n ω) ∂P := by
  have hp := iid_prefix_sample_law hs n
  have he (ω : Ξ) : run cfg x₀ seed (fun k x => oracle x (paddedSamples a (fun i : Fin n => ξ i ω) k)) n =
      run cfg x₀ seed (fun k x => oracle x (ξ k ω)) n := by
    apply run_congr_prefix
    intro k hk
    simp only [paddedSamples,dite_eq_left hk]
  constructor
  · have hi := hp.integrable_comp hF
    simpa only [Function.comp_def,he] using hi.symm
  · have hi := integral_map hp.measurable.aemeasurable
      (f := fun w : (Fin n → Ω) × Ω => F (run cfg x₀ seed (fun k x => oracle x (paddedSamples a w.1 k)) n) w.2)
      (hp.map_eq.symm ▸ hF)
    simpa only [hp.map_eq,he] using hi


lemma run_gradient_increment_integrable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ξ} [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (hα : cfg.α=9/10) (hβ : cfg.β=999/1000) (hδ : 0 < cfg.δ)
    (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1))
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h}
    {ξ : ℕ → Ξ → Ω} {B : ℝ} (hB : 0 ≤ B)
    (ho : Measurable (Function.uncurry oracle)) (hg : Measurable grad)
    (hξ : ∀ k,Measurable (ξ k)) (n : ℕ) (j : Fin b ⊕ Fin h)
    (hGB : ∀ z : ℕ → Ω,|grad (trajectory cfg x₀ (fun k x => oracle x (z k)) n) j| ≤ B) :
    Integrable (fun ω =>
      grad (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) n).point j *
      ((run cfg x₀ seed (fun k x => oracle x (ξ k ω)) (n+1)).point-
        (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) n).point) j) P := by
  let x := fun ω k => (run cfg x₀ seed (fun t x => oracle x (ξ t ω)) k).point
  have hx (k) : Measurable (fun ω => x ω k) := (run_core_measurable cfg x₀ seed ho hξ k).1
  have hj : Measurable (fun z : Point b h => z j) := by fun_prop
  have hm : Measurable (fun ω => grad (x ω n) j*(x ω (n+1)-x ω n) j) :=
    (hj.comp (hg.comp (hx n))).mul (hj.comp ((hx (n+1)).sub (hx n)))
  let C := Real.sqrt (6400*b*(cfg.bodyStep n)^2+h*(cfg.headStep n)^2)
  have hb (ω) : ‖grad (x ω n) j*(x ω (n+1)-x ω n) j‖ ≤ B*C := by
    have h1 : |grad (x ω n) j| ≤ B := by
      simpa only [x,run_point] using hGB (fun k => ξ k ω)
    have h2 : ‖(x ω (n+1)-x ω n) j‖ ≤ C := (PiLp.norm_apply_le _ j).trans
      (run_increment_norm cfg hα hβ hδ x₀ seed (fun k x => oracle x (ξ k ω)) n)
    rw [norm_mul,Real.norm_eq_abs]
    exact mul_le_mul h1 h2 (norm_nonneg _) hB
  exact (show MemLp (fun ω => grad (x ω n) j*(x ω (n+1)-x ω n) j) 1 P from
    MemLp.of_bound hm.aestronglyMeasurable (B*C) (Filter.Eventually.of_forall hb)).integrable (by norm_num)


lemma preceding_path_energy_le {E : Type*} [NormedAddCommGroup E] (x : ℕ → E) (T : ℕ) :
    (∑ t ∈ Finset.range T,‖x t-x (t-1)‖^2) ≤
      ∑ t ∈ Finset.range T,‖x (t+1)-x t‖^2 := by
  have he (N) : (∑ t ∈ Finset.range (N+1),‖x t-x (t-1)‖^2)=
      ∑ t ∈ Finset.range N,‖x (t+1)-x t‖^2 := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ,ih,Finset.sum_range_succ]
      simp
  cases T with
  | zero => simp
  | succ T =>
    rw [he,Finset.sum_range_succ]
    exact le_add_of_nonneg_right (sq_nonneg _)


lemma expected_preceding_path_energy_le {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {P : Measure Ω} (x : Ω → ℕ → E) (T : ℕ)
    (hm : ∀ t,Integrable (fun ω => ‖x ω (t+1)-x ω t‖^2) P) :
    (∑ t ∈ Finset.range T,∫ ω,‖x ω t-x ω (t-1)‖^2 ∂P) ≤
      ∑ t ∈ Finset.range T,∫ ω,‖x ω (t+1)-x ω t‖^2 ∂P := by
  have hp (t) : Integrable (fun ω => ‖x ω t-x ω (t-1)‖^2) P := by
    cases t with
    | zero => simp
    | succ t => simpa only [Nat.add_sub_cancel] using hm t
  have hh := integral_mono (integrable_finsetSum _ (fun t _ => hp t))
    (integrable_finsetSum _ (fun t _ => hm t)) (fun ω => preceding_path_energy_le (x ω) T)
  rw [integral_finsetSum _ (fun t _ => hp t),integral_finsetSum _ (fun t _ => hm t)] at hh
  exact hh



lemma run_gradient_bound_constant_steps {b h : ℕ} (cfg : Config)
    (hα : cfg.α=9/10) (hβ : cfg.β=999/1000) (hδ : 0 < cfg.δ)
    (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1)) (g : ℕ → Point b h → Point b h)
    {f : Point b h → ℝ} {L Δ ηb ηh : ℝ} (hL : 0 < L)
    (hg : ∀ x,HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y,‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (hgap : ∀ x,f x₀-f x ≤ Δ)
    (hb : ∀ t,cfg.bodyStep t=ηb) (hh : ∀ t,cfg.headStep t=ηh)
    (n k : ℕ) (hnk : n ≤ k) :
    ‖gradient f (run cfg x₀ seed g n).point‖ ≤
      Real.sqrt (2*L*Δ)+L*k*Real.sqrt (6400*b*ηb^2+h*ηh^2) := by
  have he := run_gradient_bound cfg hα hβ hδ x₀ seed g hL hg hlip hgap n
  simp only [hb,hh,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at he
  have hnk' : (n : ℝ) ≤ k := by exact_mod_cast hnk
  nlinarith [mul_le_mul_of_nonneg_right hnk' (Real.sqrt_nonneg (6400*b*ηb^2+h*ηh^2))]



lemma integrable_scaled_coordinate_roots {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} {v : ι → Ω → ℝ} {c B : ℝ} (hc : 0 ≤ c)
    (hm : ∀ i,Measurable (v i))
    (hi : Integrable (fun ω => ∑ i,Real.sqrt (v i ω)) P)
    (hB : (∫ ω,∑ i,Real.sqrt (v i ω) ∂P) ≤ B) :
    (∀ i,Integrable (fun ω => Real.sqrt (c*v i ω)) P) ∧
      (∑ i,∫ ω,Real.sqrt (c*v i ω) ∂P) ≤ Real.sqrt c*B := by
  have hvi (i) : Integrable (fun ω => Real.sqrt (v i ω)) P := by
    apply hi.mono' (hm i).sqrt.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Finset.single_le_sum (f := fun j => Real.sqrt (v j ω)) (fun j _ => Real.sqrt_nonneg _) (Finset.mem_univ i)
  have hci (i) : Integrable (fun ω => Real.sqrt (c*v i ω)) P := by
    simpa only [Real.sqrt_mul hc] using (hvi i).const_mul (Real.sqrt c)
  refine ⟨hci,?_⟩
  simp_rw [Real.sqrt_mul hc,integral_const_mul]
  rw [← Finset.mul_sum,← integral_finsetSum _ (fun i _ => hvi i)]
  exact mul_le_mul_of_nonneg_left hB (Real.sqrt_nonneg _)



lemma run_tuned_gradient_envelopes {b h : ℕ} (cfg : Config)
    (hα : cfg.α=9/10) (hβ : cfg.β=999/1000) (hδ : 0 < cfg.δ)
    (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1)) (g : ℕ → Point b h → Point b h)
    {f : Point b h → ℝ} {L Δ : ℝ} (hL : 0 < L) (hΔ : 0 < Δ) (hd : 0 < b+h)
    (hg : ∀ x,HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y,‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (hgap : ∀ x,f x₀-f x ≤ Δ) (T : ℕ) (hT : 1 ≤ T)
    (hb : ∀ t,cfg.bodyStep t=Real.sqrt (Δ/(L*((b : ℝ)+h)))/Real.sqrt T)
    (hh : ∀ t,cfg.headStep t=Real.sqrt (Δ/(L*((b : ℝ)+h)))) :
    (∀ n,n ≤ T → ‖gradient f (run cfg x₀ seed g n).point‖ ≤ 83*Real.sqrt (L*Δ)*T) ∧
    (∀ n k,n ≤ k → ‖gradient f (run cfg x₀ seed g n).point‖ ≤ (2+80*k)*Real.sqrt (L*Δ)) := by
  let a := Real.sqrt (Δ/(L*((b : ℝ)+h)))
  let q := Real.sqrt (Δ/L)
  let η := a/Real.sqrt T
  let C := Real.sqrt (6400*(b : ℝ)*η^2+h*a^2)
  have hd' : (0 : ℝ) < (b : ℝ)+h := by exact_mod_cast hd
  rcases hybrid_tuning_identities hL hΔ hd' hT with ⟨ha,hη,hηa,hscale,hstep,hroot,hinit⟩
  have hC : C ≤ 80*q := constant_block_step_bound (Nat.cast_nonneg b) (Nat.cast_nonneg h)
    ha.le hη.le hηa (Real.sqrt_nonneg _) hscale
  have hpre (n k : ℕ) (hn : n ≤ k) := run_gradient_bound_constant_steps cfg hα hβ hδ x₀ seed g
    hL hg hlip hgap hb hh n k hn
  have hgrowth (n k : ℕ) (hn : n ≤ k) : ‖gradient f (run cfg x₀ seed g n).point‖ ≤ 2*L*q+L*k*C := by
    have he := hpre n k hn
    change ‖gradient f (run cfg x₀ seed g n).point‖ ≤ Real.sqrt (2*L*Δ)+L*k*C at he
    linarith
  constructor
  · intro n hn
    have he := preliminary_gradient_envelope hL.le (Real.sqrt_nonneg (Δ/L)) hT hn hC (hgrowth n n le_rfl)
    have heq : 82*L*q*(T : ℝ)=82*Real.sqrt (L*Δ)*T := by rw [← hroot]; ring
    rw [heq] at he
    nlinarith [Real.sqrt_nonneg (L*Δ),Nat.cast_nonneg (α := ℝ) T]
  · intro n k hn
    have he := hgrowth n k hn
    have hc := mul_le_mul_of_nonneg_left hC (show 0 ≤ L*k by positivity)
    have heq : (2+80*(k : ℝ))*Real.sqrt (L*Δ)=2*L*q+80*L*k*q := by rw [← hroot]; ring
    rw [heq]
    nlinarith [he,hc]



lemma run_head_accumulator_monotone {b h : ℕ} (cfg : Config) (x₀ : Point b h)
    (seed : Fin (cfg.lastIndex+1)) (g : ℕ → Point b h → Point b h) (j : Fin h) :
    Monotone (fun t => (run cfg x₀ seed g t).accumulator (.inr j)) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [run,update,nextAccumulator,PiLp.toLp_apply]
  nlinarith [sq_nonneg (g n (run cfg x₀ seed g n).point (.inr j))]



lemma uniform_trajectory_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {b h : ℕ}
    (x : ℕ → Ω → Point b h) {grad : Point b h → Point b h} (n : ℕ)
    (hx : ∀ t,Measurable (x t)) (hg : Measurable grad)
    (hi : ∀ t,t<n+1 → Integrable (fun ω => ‖grad (x t ω)‖) P) :
    let Q := (PMF.uniformOfFintype (Fin (n+1))).toMeasure.prod P
    let out := fun z : Fin (n+1) × Ω => x z.1 z.2
    Measurable out ∧ Integrable (fun z => ‖grad (out z)‖) Q ∧
      (∫ z,‖grad (out z)‖ ∂Q)=
        (∑ t ∈ Finset.range (n+1),∫ ω,‖grad (x t ω)‖ ∂P)/(n+1) := by
  let Q := (PMF.uniformOfFintype (Fin (n+1))).toMeasure.prod P
  let out := fun z : Fin (n+1) × Ω => x z.1 z.2
  have hm : Measurable out := measurable_from_prod_countable_right fun j => hx j
  have hgm : Measurable (fun z => ‖grad (out z)‖) := (hg.comp hm).norm
  have hgi : Integrable (fun z => ‖grad (out z)‖) Q := by
    rw [integrable_prod_iff hgm.aestronglyMeasurable]
    exact ⟨Filter.Eventually.of_forall (fun j => hi j j.isLt),Integrable.of_finite⟩
  refine ⟨hm,hgi,?_⟩
  rw [integral_prod _ hgi,OracleTemplate.MixedNoise.integral_uniform_finite,Fintype.card_fin]
  change ((n+1 : ℕ) : ℝ)⁻¹*(∑ j : Fin (n+1),∫ ω,‖grad (x j ω)‖ ∂P)=_
  rw [Fin.sum_univ_eq_sum_range (fun t => ∫ ω,‖grad (x t ω)‖ ∂P) (n+1)]
  push_cast
  ring




lemma execute_uniform_gradient_integral {Ω : Type} [MeasurableSpace Ω] {b h : ℕ}
    (cfg : Config) (x₀ : Point b h) (P : ProbabilityMeasure (ℕ → Ω))
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h}
    (ho : Measurable (Function.uncurry oracle)) (hg : Measurable grad)
    (hi : ∀ t,t<cfg.lastIndex+1 → Integrable
      (fun (ω : ℕ → Ω) => ‖grad (trajectory cfg x₀ (fun r x => oracle x (ω r)) t)‖) (P : Measure _)) :
    let O : Oracle (Point b h) (Point b h) :=
      { Seed := fun _ => Ω, law := P, answer := fun _ (_,x) ω => oracle x ω }
    let Q := (PMF.uniformOfFintype (Fin (cfg.lastIndex+1))).toMeasure.prod (P : Measure _)
    let out := fun z : Fin (cfg.lastIndex+1) × (ℕ → Ω) =>
      execute O (method cfg x₀) (fun _ => cfg.lastIndex+1) z.1 z.2
    Measurable out ∧ Integrable (fun z => ‖grad (out z)‖) Q ∧
      (∫ z,‖grad (out z)‖ ∂Q)=
        (∑ t ∈ Finset.range (cfg.lastIndex+1),∫ (ω : ℕ → Ω),
          ‖grad (trajectory cfg x₀ (fun r x => oracle x (ω r)) t)‖ ∂(P : Measure _))/(cfg.lastIndex+1) := by
  let O : Oracle (Point b h) (Point b h) :=
    { Seed := fun _ => Ω, law := P, answer := fun _ (_,x) ω => oracle x ω }
  let x := fun t (ω : ℕ → Ω) => trajectory cfg x₀ (fun r x => oracle x (ω r)) t
  let out := fun z : Fin (cfg.lastIndex+1) × (ℕ → Ω) =>
    execute O (method cfg x₀) (fun _ => cfg.lastIndex+1) z.1 z.2
  have hx (t) : Measurable (x t) := trajectory_measurable cfg x₀ ho
    (fun r => measurable_pi_apply r) t
  have he : out=(fun z : Fin (cfg.lastIndex+1) × (ℕ → Ω) => x z.1 z.2) := by
    funext z
    exact execute_output cfg x₀ O z.1 z.2
  have hu := uniform_trajectory_integral x cfg.lastIndex hx hg hi
  change Measurable out ∧ Integrable (fun z => ‖grad (out z)‖)
      ((PMF.uniformOfFintype (Fin (cfg.lastIndex+1))).toMeasure.prod (P : Measure _)) ∧
    (∫ z,‖grad (out z)‖ ∂((PMF.uniformOfFintype (Fin (cfg.lastIndex+1))).toMeasure.prod (P : Measure _)))=
      (∑ t ∈ Finset.range (cfg.lastIndex+1),∫ ω,‖grad (x t ω)‖ ∂(P : Measure _))/(cfg.lastIndex+1)
  rw [he]
  exact hu


end LongTails.Proofs.HeterogeneousAdamExecution
