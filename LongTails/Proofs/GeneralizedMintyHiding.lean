import LongTails.Proofs.GeneralizedMintyScales
import LongTails.Proofs.MintyChainHiding

open Classical MeasureTheory
open scoped BigOperators

namespace LongTails.Proofs.GeneralizedMintyHiding

open LongTails.Setups.GeneralizedLipschitzMinty
open MintyChainGeometry MintyChainHiding GeneralizedMintyChain GeneralizedMintyScales
open SmoothConvexFiniteHiding FiniteSumNondualLowerHiding FiniteSumNondualLowerBound
open FiniteSumNondualLowerAveraging

variable {p : Params} (s : Scales p)

abbrev V (p : Params) := EuclideanSpace ℝ (Fin p.d)

noncomputable def hard (π : Fin (2 * s.m + 1) ↪ Fin p.d) :=
  amplified s.κ s.r s.B s.M p.L1 π

lemma plateau (h1 : 0 ≤ p.L1) (π : Fin (2 * s.m + 1) ↪ Fin p.d) (u : V p)
    (hs : ∀ j : Fin (2 * s.m + 1), s.m ≤ j.val → |ball s.B u (π j)| ≤ s.r / 4) :
    hard s π u = s.M • field s.κ s.r s.B π u := by
  have h := s.saturation.trans
    (mul_le_mul_of_nonneg_left (deficit_large _ _ π u hs) (by positivity))
  simp only [hard, amplified, exponent, min_eq_left h, Real.exp_log (lt_of_lt_of_le zero_lt_one s.cap)]

variable {S : Type*} (N : ℕ) (q out : S → V p) (upd : S → V p → S) (start : S)

private def probe (v : ℕ × S) := if v.1 < N then q v.2 else out v.2

private noncomputable def advance (v : ℕ × S) (a : V p) := (v.1 + 1, upd v.2 (s.M • a))

noncomputable def loss (π : Fin (2 * s.m + 1) ↪ Fin p.d) :=
  ‖hard s π (out ((fun v => upd v (hard s π (q v)))^[N] start))‖

lemma average (hp : 0 ≤ p.L1) (he : 0 < p.ε) (hN : N ≤ s.m) :
    3 * p.ε * Fintype.card (CoordinateWords p.d (2 * s.m)) ≤
      2 * ∑ w : CoordinateWords p.d (2 * s.m), loss s N q out upd start (coordinateEmbedding w) := by
  let Q := probe N q out
  let U := advance s upd
  let bad := fun w : CoordinateWords p.d (2 * s.m) =>
    coordinateBad s.κ s.r s.B Q Q U (0, start) (coordinateEmbedding w)
  have hs := bad_sum_bound s.κ s.r s.B s.D s.radius.le s.spacing s.width.le s.space
    Q Q U (0, start)
  let nb : ℝ := ∑ w, if bad w then (1 : ℝ) else 0
  have hnb : 4 * nb ≤ Fintype.card (CoordinateWords p.d (2 * s.m)) := by
    apply le_of_mul_le_mul_left (a := s.D) _ s.width
    change s.D * nb ≤ _ at hs
    nlinarith [mul_le_mul_of_nonneg_right s.count
      (Nat.cast_nonneg (Fintype.card (CoordinateWords p.d (2 * s.m))) (α := ℝ))]
  have hpoint (w : CoordinateWords p.d (2 * s.m)) :
      2 * p.ε * (1 - if bad w then (1 : ℝ) else 0) ≤ loss s N q out upd start (coordinateEmbedding w) := by
    by_cases hw : bad w
    · simp [hw, loss]
    simp only [hw, ↓reduceIte, sub_zero, mul_one]
    let π := coordinateEmbedding w
    let sim := simulatedState s.κ s.r s.B π Q U (0, start)
    have count (t : ℕ) : (sim t).1 = t := by
      induction t with
      | zero => rfl
      | succ t ih => change (sim t).1 + 1 = _; rw [ih]
    have small (t : ℕ) (ht : t ≤ N) (j : Fin (2 * s.m + 1)) (hj : t ≤ j.val) :
        |ball s.B (Q (sim t)) (π j)| ≤ s.r / 4 := by
      have htt : t < 2 * s.m + 1 := by omega
      have h := good_observation_small s.κ s.r s.B s.radius.le Q Q U (0, start) π hw
        ⟨t, htt⟩ j hj
      simpa only [observation, ite_self] using h
    have link (t : ℕ) (ht : t ≤ N) : (sim t).2 =
        (fun v => upd v (hard s π (q v)))^[t] start := by
      induction t with
      | zero => rfl
      | succ t ih =>
        have ht' : t < N := by omega
        have hq : Q (sim t) = q (sim t).2 := by simp [Q, probe, count, ht']
        have htrue := plateau s hp π (Q (sim t)) (fun j hj => small t ht'.le j (by omega))
        rw [field_eq_partial _ _ _ s.spacing π t _ (small t ht'.le)] at htrue
        change upd (sim t).2 (s.M • partialField s.κ s.r s.B π t (Q (sim t))) = _
        rw [← htrue, hq, ih ht'.le, Function.iterate_succ_apply']
    have hq : Q (sim N) = out (sim N).2 := by simp [Q, probe, count]
    have hsmall (j : Fin (2 * s.m + 1)) (hj : s.m ≤ j.val) :=
      small N le_rfl j (le_trans hN hj)
    have hbar := field_lower s.κ s.r s.B s.slope s.spacing s.radius π s.far (Q (sim N))
      ⟨Fin.last _, (le_abs_self _).trans ((hsmall (Fin.last _) (by simp only [Fin.val_last]; omega)).trans
        (by linarith [s.spacing]))⟩
    have hnorm : s.κ * s.r / 4 ≤ ‖field s.κ s.r s.B π (Q (sim N))‖ := by
      apply le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _)
      nlinarith [sq_nonneg (s.κ * s.r)]
    change 2 * p.ε ≤ ‖hard s π (out ((fun v => upd v (hard s π (q v)))^[N] start))‖
    rw [← link N le_rfl, ← hq, plateau s hp π _ hsmall, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ((by linarith [s.cap]) : 0 ≤ s.M)]
    nlinarith [s.barrier, mul_nonneg (by linarith [s.cap] : 0 ≤ s.M) (sub_nonneg.mpr hnorm)]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun w _ => hpoint w)
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hsum
  change 2 * p.ε * (Fintype.card (CoordinateWords p.d (2 * s.m)) - nb) ≤ _ at hsum
  nlinarith [mul_nonneg he.le (sub_nonneg.mpr hnb)]

lemma failure {Ω : Type*} [MeasurableSpace Ω] (init : Ω → S) (P : ProbabilityMeasure Ω)
    (hp : 0 ≤ p.L1) (he : 0 < p.ε) (hN : N ≤ s.m) :
    ∃ π : Fin (2 * s.m + 1) ↪ Fin p.d,
      let g := fun ω => loss s N q out upd (init ω) π
      ¬ (Integrable g (P : Measure Ω) ∧ (∫ ω, g ω ∂(P : Measure Ω)) ≤ p.ε) := by
  by_contra! h
  let g := fun (w : CoordinateWords p.d (2 * s.m)) ω =>
    loss s N q out upd (init ω) (coordinateEmbedding w)
  have hi (w) : Integrable (g w) (P : Measure Ω) := (h (coordinateEmbedding w)).1
  have hu (w) : (∫ ω, g w ω ∂(P : Measure Ω)) ≤ p.ε := (h (coordinateEmbedding w)).2
  have hsum := integrable_finsetSum Finset.univ (fun w _ => hi w)
  have hb := integral_mono (integrable_const (3 * p.ε * Fintype.card (CoordinateWords p.d (2 * s.m))))
    (hsum.const_mul 2) (fun ω => average s N q out upd (init ω) hp he hN)
  simp only [integral_const, probReal_univ, one_smul, integral_const_mul,
    integral_finsetSum Finset.univ (fun w _ => hi w)] at hb
  have htot := Finset.sum_le_sum (s := Finset.univ) (fun w _ => hu w)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at htot
  have hd : 2 * s.m + 1 ≤ p.d := by
    exact_mod_cast (show ((2 * s.m + 1 : ℕ) : ℝ) ≤ p.d by linarith [s.space, s.width])
  have hc : (0 : ℝ) < Fintype.card (CoordinateWords p.d (2 * s.m)) := by
    exact_mod_cast coordinateWords_card_pos p.d (2 * s.m) hd
  nlinarith [mul_pos he hc]

end LongTails.Proofs.GeneralizedMintyHiding
