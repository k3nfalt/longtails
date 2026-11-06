import LongTails.Proofs.ConstrainedSaddleExecution
import LongTails.Proofs.PLMinimaxBudget

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ConstrainedSaddleBudget

open LongTails.Setups.ConstrainedMinimaxSecondOrder
open LongTails.Algorithms.ConstrainedSaddleCubic
open LongTails.Algorithms.AuxiliaryPlan
open ConstrainedSaddleInner ConstrainedSaddleTracking ConstrainedSaddleOuter
open ConstrainedMinimaxEnvelope ConstrainedSaddleExecution

lemma small_step_length {R ε r : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (hs : r ^ 2 ≤ ε / (4 * R)) : r ≤ Real.sqrt ε / (2 * Real.sqrt R) := by
  have hstep := (le_div_iff₀ (by positivity : 0 < 4 * R)).mp hs
  apply (le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt R)).mpr
  have he : (r * (2 * Real.sqrt R)) ^ 2 = r ^ 2 * (4 * R) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hR.le]
    ring
  nlinarith [Real.sq_sqrt hε.le, Real.sqrt_nonneg ε]

lemma terminal_cost {j h ε G t r m n : ℝ} (hj : 0 ≤ j) (hh : 0 < h) (hε : 0 < ε)
    (hG : 0 ≤ G) (hn : 1 ≤ n) (hm : m ≤ 1 + r / h) (hr : r ≤ t) :
    1 + j * m ≤ (1 + j) * n + (j / h) * (48 * G / ε + t) := by
  have ha := mul_le_mul_of_nonneg_left hm hj
  have hb := mul_le_mul_of_nonneg_left hr (div_nonneg hj hh.le)
  have hc := mul_le_mul_of_nonneg_left hn (by linarith : 0 ≤ 1 + j)
  have hd : 0 ≤ j / h * (48 * G / ε) := by positivity
  have he : j * (1 + r / h) = j + j / h * r := by ring
  rw [he] at ha
  nlinarith

lemma amortized_cost {j h ε G d t r m n C : ℝ} (hj : 0 ≤ j) (hh : 0 < h) (hε : 0 < ε)
    (hm : m ≤ 1 + r / h) (hr : ε * r / 48 ≤ d)
    (hC : C ≤ (1 + j) * n + (j / h) * (48 * (G - d) / ε + t)) :
    1 + j * m + C ≤ (1 + j) * (n + 1) + (j / h) * (48 * G / ε + t) := by
  have hp : r ≤ 48 * d / ε := by apply (le_div_iff₀ hε).mpr; linarith
  have ha := mul_le_mul_of_nonneg_left hm hj
  have hb := mul_le_mul_of_nonneg_left hp (div_nonneg hj hh.le)
  have he : j * (1 + r / h) = j + j / h * r := by ring
  rw [he] at ha
  have hid : (1 + j) * (n + 1) + j / h * (48 * G / ε + t) =
      1 + j + j / h * (48 * d / ε) + ((1 + j) * n + j / h * (48 * (G - d) / ε + t)) := by ring
  rw [hid]
  linarith

lemma run_outer_cost {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (n : ℕ) (z : p.E) (state : Space p × Space p) (G : ℝ)
    (hw : TrackingInvariant f z state) (hG : 0 ≤ G)
    (hgap : ∀ u, envelope f z - envelope f u ≤ G)
    (hn : G < n * (p.ε * Real.sqrt p.ε / (96 * Real.sqrt (modelScale p)))) :
    (AuxiliaryPlan.TwoPlan.length (fun _ => jet f) (runOuter n z state) : ℝ) ≤
      (1 + 2 * refinementSteps p) * n + (2 * refinementSteps p / segmentLength p) *
        (48 * G / p.ε + Real.sqrt p.ε / (2 * Real.sqrt (modelScale p))) := by
  have hε := hv.2.2.2.2.2.1
  have hh := segment_length_positive hv
  have hj : (0 : ℝ) ≤ 2 * refinementSteps p := by positivity
  induction n generalizing z state G with
  | zero => simp only [Nat.cast_zero, zero_mul] at hn; linarith
  | succ n ih =>
    let z' := OracleTemplate.QueryPlan.eval (jet f) (outerPlan z state)
    let next := OracleTemplate.QueryPlan.eval (jet f)
      (trackPlan z z' (segmentCount z z') 0 (segmentCount z z') state)
    have hnext : TrackingInvariant f z' next := tracking_complete H hv z z' state hw
    have hm := segment_count_bound hv z z'
    rw [runOuter, length_bind, length_liftPlan, eval_liftPlan,
      length_bind, length_liftPlan, eval_liftPlan]
    change (((1 + (2 * refinementSteps p * segmentCount z z' +
      AuxiliaryPlan.TwoPlan.length (fun _ => jet f)
        (if ‖z' - z‖ ^ 2 ≤ p.ε / (4 * modelScale p) then .done next.1.fst else runOuter n z' next))) : ℕ) : ℝ) ≤ _
    by_cases hs : ‖z' - z‖ ^ 2 ≤ p.ε / (4 * modelScale p)
    · rw [ite_eq_left hs, AuxiliaryPlan.TwoPlan.length]
      push_cast
      have hr := small_step_length (model_scale_positive hv) hε hs
      have hc := terminal_cost hj hh hε hG (show (1 : ℝ) ≤ (n : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) n]) hm hr
      simpa only [add_zero, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat] using hc
    · rw [ite_eq_right hs]
      push_cast
      have hlarge : p.ε / (4 * modelScale p) ≤ ‖z' - z‖ ^ 2 := (lt_of_not_ge hs).le
      have hd := outer_large_step_decrease H hv z state hw hlarge
      change p.ε * Real.sqrt p.ε / (96 * Real.sqrt (modelScale p)) ≤ envelope f z - envelope f z' at hd
      have hi := ih z' next (G - (envelope f z - envelope f z')) hnext
        (by linarith [hgap z']) (fun u => by linarith [hgap u])
        (by push_cast at hn; nlinarith)
      have hp := outer_large_step_path H hv z state hw hlarge
      change p.ε * ‖z' - z‖ / 48 ≤ envelope f z - envelope f z' at hp
      have hc := amortized_cost hj hh hε hm hp hi
      simpa only [add_assoc] using hc

lemma full_plan_cost {p : Params} {f : Space p → ℝ} (H : Assumptions p f)
    (hv : spec.valid p) :
    (AuxiliaryPlan.TwoPlan.length (fun _ => jet f) (fullPlan p) : ℝ) ≤
      2 * startupSteps p + 2 * refinementSteps p + (1 + 2 * refinementSteps p) * outerSteps p +
        (2 * refinementSteps p / segmentLength p) *
          (48 * p.Δ / p.ε + Real.sqrt p.ε / (2 * Real.sqrt (modelScale p))) := by
  rw [fullPlan, length_bind, length_liftPlan, eval_liftPlan,
    length_bind, length_liftPlan, eval_liftPlan]
  have hh := run_outer_cost H.toRegularity hv (outerSteps p) p.x0 _ p.Δ
    (startup_invariant H hv) hv.2.2.2.1 (envelope_initial_gap H hv) (outer_steps_sufficient hv)
  push_cast
  linarith

lemma sqrt_condition_bound {p : Params} (hv : spec.valid p) :
    Real.sqrt (4 + p.L / p.μ) ≤ (5 / 2) * Real.sqrt (p.L / p.μ) := by
  have hk : 1 ≤ p.L / p.μ := (le_div_iff₀ hv.1).mpr (by simpa using hv.2.1)
  have hk0 : 0 ≤ p.L / p.μ := by linarith
  have ha := Real.sq_sqrt (show 0 ≤ 4 + p.L / p.μ by linarith)
  have hb := Real.sq_sqrt hk0
  have hc : ((5 / 2) * Real.sqrt (p.L / p.μ)) ^ 2 = (25 / 4) * (p.L / p.μ) := by
    rw [mul_pow, hb]
    norm_num
  nlinarith [Real.sqrt_nonneg (p.L / p.μ)]

lemma model_scale_bound {p : Params} (hv : spec.valid p) :
    Real.sqrt (modelScale p) ≤ 4 * Real.sqrt p.ρ * (p.L / p.μ) ^ (3 / 4 : ℝ) := by
  have hk : 1 ≤ p.L / p.μ := (le_div_iff₀ hv.1).mpr (by simpa using hv.2.1)
  have hk0 : 0 < p.L / p.μ := by linarith
  have ha : 0 < 4 + p.L / p.μ := by linarith
  have hs := sqrt_condition_bound hv
  have hb : (4 + p.L / p.μ) * Real.sqrt (4 + p.L / p.μ) ≤
      16 * ((p.L / p.μ) * Real.sqrt (p.L / p.μ)) := by
    have hh := mul_le_mul (show 4 + p.L / p.μ ≤ 5 * (p.L / p.μ) by linarith) hs
      (Real.sqrt_nonneg _) (by positivity : 0 ≤ 5 * (p.L / p.μ))
    nlinarith [mul_nonneg hk0.le (Real.sqrt_nonneg (p.L / p.μ))]
  have hh := Real.sqrt_le_sqrt hb
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)] at hh
  rw [show Real.sqrt (16 : ℝ) = 4 by norm_num] at hh
  rw [OracleTemplate.PLMinimax.sqrt_three_quarters hk0] at hh
  unfold modelScale
  rw [pow_succ, Real.sq_sqrt ha.le, Real.sqrt_mul hv.2.2.1.le]
  have hm := mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg p.ρ)
  nlinarith

lemma outer_steps_bound {p : Params} (hv : spec.valid p) :
    outerSteps p ≤ 1 + ⌈384 * p.Δ * Real.sqrt p.ρ * (p.L / p.μ) ^ (3 / 4 : ℝ) /
      (p.ε * Real.sqrt p.ε)⌉₊ := by
  have hΔ := hv.2.2.2.1
  have hε := hv.2.2.2.2.2.1
  unfold outerSteps
  apply Nat.add_le_add_left
  apply Nat.ceil_le_ceil
  have hh := mul_le_mul_of_nonneg_left (model_scale_bound hv)
    (by positivity : 0 ≤ 96 * p.Δ / (p.ε * Real.sqrt p.ε))
  convert hh using 1 <;> ring

lemma tracking_path_bound {p : Params} (hv : spec.valid p) :
    (48 * p.Δ / p.ε) / segmentLength p ≤
      2048 * p.ρ * Real.sqrt (p.L / p.μ) * p.Δ / (p.μ * p.ε) := by
  have hμ := hv.1
  have hρ := hv.2.2.1
  have hΔ := hv.2.2.2.1
  have hε := hv.2.2.2.2.2.1
  have hs := sqrt_condition_bound hv
  have hh : 768 * Real.sqrt (4 + p.L / p.μ) ≤ 2048 * Real.sqrt (p.L / p.μ) := by
    nlinarith [Real.sqrt_nonneg (p.L / p.μ)]
  have hm := mul_le_mul_of_nonneg_right hh
    (by positivity : 0 ≤ p.ρ * p.Δ / (p.μ * p.ε))
  unfold segmentLength
  convert hm using 1
  all_goals field_simp
  all_goals ring

lemma tracking_terminal_bound {p : Params} (hv : spec.valid p) :
    (Real.sqrt p.ε / (2 * Real.sqrt (modelScale p))) / segmentLength p ≤
      8 * Real.sqrt (p.ρ * p.ε) / p.μ := by
  have hμ := hv.1
  have hρ := hv.2.2.1
  have hε := hv.2.2.2.2.2.1
  have hR := model_scale_positive hv
  have hk : 1 ≤ p.L / p.μ := (le_div_iff₀ hμ).mpr (by simpa using hv.2.1)
  let a := Real.sqrt (4 + p.L / p.μ)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha : 1 ≤ a := by
    have hh := Real.sq_sqrt (show 0 ≤ 4 + p.L / p.μ by linarith)
    change a ^ 2 = 4 + p.L / p.μ at hh
    nlinarith
  have hlow : p.ρ * a ^ 2 ≤ modelScale p := by
    change p.ρ * a ^ 2 ≤ p.ρ * a ^ 3
    have hh := mul_nonneg (show 0 ≤ a - 1 by linarith) (sq_nonneg a)
    have hm := mul_le_mul_of_nonneg_left (show a ^ 2 ≤ a ^ 3 by nlinarith) hρ.le
    exact hm
  have hroot : Real.sqrt p.ρ * a ≤ Real.sqrt (modelScale p) := by
    have he : (Real.sqrt p.ρ * a) ^ 2 = p.ρ * a ^ 2 := by rw [mul_pow, Real.sq_sqrt hρ.le]
    nlinarith [Real.sq_sqrt hR.le, Real.sqrt_nonneg (modelScale p)]
  have hratio : p.ρ * a / Real.sqrt (modelScale p) ≤ Real.sqrt p.ρ := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hR)).mpr
    have hh := mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg p.ρ)
    have he : Real.sqrt p.ρ * (Real.sqrt p.ρ * a) = p.ρ * a := by
      rw [← mul_assoc, Real.mul_self_sqrt hρ.le]
    rw [he] at hh
    exact hh
  have hh := mul_le_mul_of_nonneg_left hratio
    (by positivity : 0 ≤ 8 * Real.sqrt p.ε / p.μ)
  rw [Real.sqrt_mul hρ.le]
  unfold segmentLength
  change Real.sqrt p.ε / (2 * Real.sqrt (modelScale p)) / (p.μ / (16 * p.ρ * a)) ≤ _
  convert hh using 1
  all_goals field_simp
  all_goals ring

lemma tracking_allowance_bound {p : Params} (hv : spec.valid p) :
    (48 * p.Δ / p.ε + Real.sqrt p.ε / (2 * Real.sqrt (modelScale p))) / segmentLength p ≤
      2048 * p.ρ * Real.sqrt (p.L / p.μ) * p.Δ / (p.μ * p.ε) +
        8 * Real.sqrt (p.ρ * p.ε) / p.μ := by
  rw [add_div]
  exact add_le_add (tracking_path_bound hv) (tracking_terminal_bound hv)

lemma explicit_plan_cost {p : Params} {f : Space p → ℝ} (H : Assumptions p f)
    (hv : spec.valid p) :
    AuxiliaryPlan.TwoPlan.length (fun _ => jet f) (fullPlan p) ≤
      4 * (1 + ⌈16 * p.L / p.μ * Real.log (1 + 32 * p.ρ * p.B / p.μ ^ 2)⌉₊ +
        (2 + ⌈384 * p.Δ * Real.sqrt p.ρ * (p.L / p.μ) ^ (3 / 4 : ℝ) / (p.ε * Real.sqrt p.ε)⌉₊ +
          ⌈2048 * p.ρ * Real.sqrt (p.L / p.μ) * p.Δ / (p.μ * p.ε) + 8 * Real.sqrt (p.ρ * p.ε) / p.μ⌉₊) *
          (2 + ⌈2 * Real.log (33 + 512 * p.L * p.μ / (p.ρ * p.ε))⌉₊)) := by
  let E := startupSteps p
  let J := refinementSteps p
  let T := 1 + ⌈384 * p.Δ * Real.sqrt p.ρ * (p.L / p.μ) ^ (3 / 4 : ℝ) / (p.ε * Real.sqrt p.ε)⌉₊
  let N := ⌈2048 * p.ρ * Real.sqrt (p.L / p.μ) * p.Δ / (p.μ * p.ε) + 8 * Real.sqrt (p.ρ * p.ε) / p.μ⌉₊
  have ht := tracking_allowance_bound hv
  have hc : (48 * p.Δ / p.ε + Real.sqrt p.ε / (2 * Real.sqrt (modelScale p))) / segmentLength p ≤ (N : ℝ) :=
    ht.trans (Nat.le_ceil _)
  have hm := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ (2 : ℝ) * J)
  have hh := full_plan_cost H hv
  have he : (2 * refinementSteps p / segmentLength p) *
      (48 * p.Δ / p.ε + Real.sqrt p.ε / (2 * Real.sqrt (modelScale p))) =
      (2 : ℝ) * J * ((48 * p.Δ / p.ε + Real.sqrt p.ε / (2 * Real.sqrt (modelScale p))) / segmentLength p) := by
    dsimp [J]
    ring
  rw [he] at hh
  have hreal : (AuxiliaryPlan.TwoPlan.length (fun _ => jet f) (fullPlan p) : ℝ) ≤
      (2 * E + 2 * J + (1 + 2 * J) * outerSteps p + 2 * J * N : ℕ) := by
    push_cast
    change _ ≤ 2 * startupSteps p + 2 * refinementSteps p +
      (1 + 2 * refinementSteps p) * outerSteps p + (2 : ℝ) * J * N
    linarith
  have hnat : AuxiliaryPlan.TwoPlan.length (fun _ => jet f) (fullPlan p) ≤
      2 * E + 2 * J + (1 + 2 * J) * outerSteps p + 2 * J * N := by exact_mod_cast hreal
  have hT : outerSteps p ≤ T := outer_steps_bound hv
  have hbound : AuxiliaryPlan.TwoPlan.length (fun _ => jet f) (fullPlan p) ≤
      4 * (1 + E + (1 + T + N) * (1 + J)) := by
    have hm := Nat.mul_le_mul_left (1 + 2 * J) hT
    nlinarith
  convert hbound using 1
  dsimp [E, J, T, N, startupSteps, refinementSteps]
  ring

end LongTails.Proofs.ConstrainedSaddleBudget
