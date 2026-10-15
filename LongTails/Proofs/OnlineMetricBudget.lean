import LongTails.Proofs.OnlineMetricFinal

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.OnlineMetricAccelerated

open LongTails.Setups.DiagonalSmoothStronglyConvex

variable {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {w : Fin d → ℝ} {μ fstar : ℝ}
  {xstar x0 : EuclideanSpace ℝ (Fin d)}

lemma halving_target {Δ ε : ℝ} (hΔ : 0 ≤ Δ) (hε : 0 < ε) {e : ℕ}
    (he : ⌈Real.logb 2 (Δ / ε)⌉₊ ≤ e) : Δ / 2 ^ e ≤ ε := by
  rcases eq_or_lt_of_le hΔ with h0 | hpos
  · rw [← h0]; simp; exact hε.le
  have hq : 0 < Δ / ε := div_pos hpos hε
  have h1 : Real.logb 2 (Δ / ε) ≤ e := (Nat.le_ceil _).trans (by exact_mod_cast he)
  have h2 : Δ / ε ≤ (2 : ℝ) ^ e := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) hq] at h1
    exact_mod_cast h1
  rw [div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ hε] at h2
  linarith

lemma accuracy [NeZero d] (H : Hyp f w μ fstar xstar) (hd : 1 ≤ (d : ℝ)) {Δ ε : ℝ}
    (hgap : f x0 - fstar ≤ Δ) (hε : 0 < ε) (N : ℕ)
    (hN : d + 1 + ⌈Real.logb 2 (Δ / ε)⌉₊ * ⌈24 * Real.sqrt (1 / μ) + Real.logb 2 d + 2⌉₊ +
      (d * ⌈Real.logb 2 (1 / μ)⌉₊ + 1) *
        ⌈110 * d ^ 2 * (1 + Real.log (2 * d)) ^ 2 * Real.sqrt (1 / μ)⌉₊ ≤ N) :
    f ((macroStep fstar x0 f)^[N] (initialCore x0)).xs - fstar ≤ ε := by
  set J := ⌈Real.logb 2 (Δ / ε)⌉₊
  set X := 24 * Real.sqrt (1 / μ) + Real.logb 2 d + 2
  set K := d * ⌈Real.logb 2 (1 / μ)⌉₊
  set Y := 110 * d ^ 2 * (1 + Real.log (2 * d)) ^ 2 * Real.sqrt (1 / μ)
  have hsplit : N = (N - d) + d := by omega
  rw [hsplit, Function.iterate_add_apply, iterate_init le_rfl]
  set n := N - d
  have I := inv_iterate (x0 := x0) H hd (inv_init (fstar := fstar) H hd) n
  have hb0 : ∀ i, secantBox f x0 i ≤ 1 / (μ * w i) := fun i => (secant_mem H i).2
  set s := (macroStep fstar x0 f)^[n] (initState f x0 d)
  have hgap0 : 0 ≤ f x0 - fstar := by linarith [H.ge_fstar x0]
  by_cases hJ : s.ep < J
  · exfalso
    have hc := count_bound H hd hb0 I hJ
    have hn : 1 + J * ⌈X⌉₊ + (K + 1) * ⌈Y⌉₊ ≤ n := by omega
    have hn' : (1 : ℝ) + J * ⌈X⌉₊ + ((K : ℝ) + 1) * ⌈Y⌉₊ ≤ n := by exact_mod_cast hn
    have h1 : (J : ℝ) * X ≤ J * ⌈X⌉₊ :=
      mul_le_mul_of_nonneg_left (Nat.le_ceil X) (Nat.cast_nonneg _)
    have h2 : ((K : ℝ) + 1) * Y ≤ (K + 1) * ⌈Y⌉₊ :=
      mul_le_mul_of_nonneg_left (Nat.le_ceil Y) (by positivity)
    have hc2 : (n : ℝ) ≤ J * X + ((K : ℝ) + 1) * Y := by
      have e : ((d * ⌈Real.logb 2 (1 / μ)⌉₊ : ℕ) : ℝ) = (K : ℝ) := rfl
      rw [e] at hc; exact hc
    linarith
  · push Not at hJ
    have hf := I.fs
    have hh := I.halving
    rw [← hf]
    have hΔ : 0 ≤ Δ := le_trans hgap0 hgap
    calc s.fs - fstar ≤ (f x0 - fstar) / 2 ^ s.ep := hh
      _ ≤ Δ / 2 ^ s.ep := div_le_div_of_nonneg_right hgap (by positivity)
      _ ≤ ε := halving_target hΔ hε hJ

lemma two_queries (p : Public) (f : EuclideanSpace ℝ (Fin p.d) → ℝ) (s : Core p.d) :
    let T := fun state => (algorithm p).update state
      ((fun x => (f x, gradient f x)) (((algorithm p).query state).2))
    T (T (.ready s)) = .ready (macroStep p.fstar p.x0 f s) := rfl

lemma execute_algorithm (p : Public) (f : EuclideanSpace ℝ (Fin p.d) → ℝ) (N : ℕ) :
    execute { answer := fun _ query _ => (fun x => (f x, gradient f x)) query.2 } (algorithm p)
      (fun _ => (2 * N)) = ((macroStep p.fstar p.x0 f)^[N] (initialCore p.x0)).xs := by
  let T := fun state => (algorithm p).update state
    ((fun x => (f x, gradient f x)) (((algorithm p).query state).2))
  have hi : ∀ n, T^[2 * n] ((algorithm p).initial ()) =
      .ready ((macroStep p.fstar p.x0 f)^[n] (initialCore p.x0)) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [show 2 * (n + 1) = 2 + 2 * n by omega, Function.iterate_add_apply, ih]
      exact (two_queries p f _).trans
        (congrArg State.ready (Function.iterate_succ_apply' _ n _).symm)
  have h := execute_iterate (fun x : EuclideanSpace ℝ (Fin p.d) => (f x, gradient f x))
    (algorithm p) (2 * N) ()
  refine h.trans ?_
  change (algorithm p).output (T^[2 * N] ((algorithm p).initial ())) = _
  rw [hi]
  rfl

end OracleTemplate.OnlineMetricAccelerated
