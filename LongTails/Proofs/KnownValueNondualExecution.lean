import LongTails.Proofs.KnownValueNondualControl

open Set

namespace LongTails.Proofs.KnownValueNondualExecution

open LongTails.Setups.KnownValueNondualGeneralizedConvex
open LongTails.Algorithms.KnownValueNondual
open KnownValueNondualControl

noncomputable def step (p : Public) (f : Point p → ℝ) (g : Point p → Point p)
    (s : State p) : State p := update p s (f (query p s), g (query p s))

noncomputable def lineOutput (p : Public) (f : Point p → ℝ) (g : Point p → Point p)
    (c : Control p) := LongTails.Algorithms.NondualLineSearch.output (selector p c.body) c.incumbent
      ((NondualLineSearch.step f g (4 * p.R) (p.ε / 2) (selector p c.body) c.incumbent)^[lineCalls p] .first)

noncomputable def advance (p : Public) (f : Point p → ℝ) (g : Point p → Point p)
    (c : Control p) : Control p :=
  if c.finished then c else finishLine p c (lineOutput p f g c)

lemma midpointCount_suffices (p : Public) :
    128 * (1 + p.L0 * (4 * p.R) ^ 2 / (p.ε / 2) + p.L1 * (4 * p.R)) ^ 2 ≤
      (2 : ℝ) ^ midpointCount p := by
  have he : 1 + p.L0 * (4 * p.R) ^ 2 / (p.ε / 2) + p.L1 * (4 * p.R) =
      1 + 32 * p.L0 * p.R ^ 2 / p.ε + 4 * p.L1 * p.R := by ring
  rw [he]
  refine (Nat.le_ceil _).trans ?_
  have h := (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2)
    ⌈128 * (1 + 32 * p.L0 * p.R ^ 2 / p.ε + 4 * p.L1 * p.R) ^ 2⌉₊).le
  exact_mod_cast (by simpa [midpointCount, Nat.add_comm] using h)

lemma execute_iterates (p : Public) (O : OracleTemplate.Oracle (Point p)
    (LongTails.Algorithms.NondualLineSearch.Reply (Point p)))
    (f : Point p → ℝ) (g : Point p → Point p)
    (hO : ∀ history x seed, O.answer history (0, x) seed = (f x, g x))
    (K : ℕ) (ξ : (k : ℕ) → O.Seed k) :
    OracleTemplate.execute O (algorithm p) (fun _ => K) () ξ =
      ((step p f g)^[K] ⟨initialControl p, .first, 0⟩).control.incumbent := by
  exact (OracleTemplate.execute_eq_of_answer_eq O (fun x => (f x, g x)) hO
    (algorithm p) K () ξ).trans
    (OracleTemplate.execute_iterate (fun x => (f x, g x)) (algorithm p) K ())

lemma step_finished (p : Public) (f : Point p → ℝ) (g : Point p → Point p)
    (s : State p) (hs : s.control.finished = true) : step p f g s = s := by
  simp [step, update, hs]

lemma within_block (p : Public) (f : Point p → ℝ) (g : Point p → Point p)
    (c : Control p) (hc : c.finished = false) (k : ℕ) (hk : k < lineCalls p) :
    (step p f g)^[k] ⟨c, .first, 0⟩ =
      ⟨c, (NondualLineSearch.step f g (4 * p.R) (p.ε / 2)
        (selector p c.body) c.incumbent)^[k] .first, k⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih (by omega), Function.iterate_succ_apply']
    simp [step, update, query, hc, NondualLineSearch.step, show k + 1 ≠ lineCalls p by omega]

lemma whole_block (p : Public) (f : Point p → ℝ) (g : Point p → Point p)
    (c : Control p) :
    (step p f g)^[lineCalls p] ⟨c, .first, 0⟩ = ⟨advance p f g c, .first, 0⟩ := by
  cases hc : c.finished with
  | true =>
    have hs : step p f g ⟨c, .first, 0⟩ = ⟨c, .first, 0⟩ := step_finished p f g _ hc
    rw [Function.iterate_fixed hs]
    simp [advance, hc]
  | false =>
    have hcalls : lineCalls p = (midpointCount p + 1) + 1 := by simp [lineCalls, Nat.add_assoc]
    rw [hcalls, Function.iterate_succ_apply',
      within_block p f g c hc _ (by rw [hcalls]; omega)]
    have hline : (NondualLineSearch.step f g (4 * p.R) (p.ε / 2)
        (selector p c.body) c.incumbent)^[lineCalls p] .first =
        NondualLineSearch.step f g (4 * p.R) (p.ε / 2) (selector p c.body) c.incumbent
          ((NondualLineSearch.step f g (4 * p.R) (p.ε / 2)
            (selector p c.body) c.incumbent)^[midpointCount p + 1] .first) := by
      rw [hcalls, Function.iterate_succ_apply']
    simp [step, update, query, hc, ← hcalls, advance, lineOutput, hline,
      NondualLineSearch.step]

lemma blocks (p : Public) (f : Point p → ℝ) (g : Point p → Point p)
    (c : Control p) (n : ℕ) :
    (step p f g)^[n * lineCalls p] ⟨c, .first, 0⟩ =
      ⟨(advance p f g)^[n] c, .first, 0⟩ := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, Function.iterate_add_apply, whole_block, ih,
      Function.iterate_succ_apply]

lemma lineOutput_guarantee (p : Public) {f : Point p → ℝ} {g : Point p → Point p}
    (hd : 0 < p.d) (hconv : ConvexOn ℝ univ f)
    (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hL0 : 0 < p.L0) (hL1 : 0 < p.L1) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (p.L0 + p.L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (xstar : Point p) (hprior : ‖p.x0 - xstar‖ ≤ p.R)
    (c : Control p) (hc : Invariant p f xstar c) :
    NondualLineSearch.Guarantee f g p.L0 p.L1 (4 * p.R) (p.ε / 2)
      (selector p c.body) c.incumbent (lineOutput p f g c) := by
  have hz := KnownValueNondualGeometry.selector_distance p hd xstar hprior
    ⟨_, hc.minimizer_mem⟩ hc.compact hc.convex hc.subset
  exact NondualLineSearch.valid_output hconv hgrad hg hL0 hL1 (by positivity) (by positivity) hgs
    (KnownValueNondualGeometry.segment_length p xstar _ _ hz hc.radius)
    (NondualLineSearch.valid_iterate hconv hgrad _ _ _ _ (midpointCount p))
    (midpointCount_suffices p)

lemma advance_invariant (p : Public) {f : Point p → ℝ} {g : Point p → Point p}
    (hd : 0 < p.d) (hconv : ConvexOn ℝ univ f)
    (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hL0 : 0 < p.L0) (hL1 : 0 < p.L1) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (p.L0 + p.L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (xstar : Point p) (hmin : IsMinOn f univ xstar) (hval : f xstar = p.fstar)
    (hprior : ‖p.x0 - xstar‖ ≤ p.R) (c : Control p) (hc : Invariant p f xstar c) :
    Invariant p f xstar (advance p f g c) := by
  unfold advance
  split_ifs
  · exact hc
  · exact finishLine_invariant p hd hconv hgrad hg hL0 hL1 hR hε hgs xstar hmin hval hprior c hc _
      (lineOutput_guarantee p hd hconv hgrad hg hL0 hL1 hR hε hgs xstar hprior c hc)

lemma iterate_invariant (p : Public) {f : Point p → ℝ} {g : Point p → Point p}
    (hd : 0 < p.d) (hconv : ConvexOn ℝ univ f)
    (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hL0 : 0 < p.L0) (hL1 : 0 < p.L1) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (p.L0 + p.L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (xstar : Point p) (hmin : IsMinOn f univ xstar) (hval : f xstar = p.fstar)
    (hprior : ∑ i, |p.x0 i - xstar i| ≤ p.R) (n : ℕ) :
    Invariant p f xstar ((advance p f g)^[n] (initialControl p)) := by
  induction n with
  | zero => exact initial_invariant p hgrad hg hL0 hL1 hR hgs xstar hmin hprior
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact advance_invariant p hd hconv hgrad hg hL0 hL1 hR hε hgs xstar hmin hval
      (KnownValueNondualGeometry.initialBody_norm p hprior) _ ih

lemma execute_after_finished_block (p : Public) (O : OracleTemplate.Oracle (Point p)
    (LongTails.Algorithms.NondualLineSearch.Reply (Point p)))
    (f : Point p → ℝ) (g : Point p → Point p)
    (hO : ∀ history x seed, O.answer history (0, x) seed = (f x, g x))
    (n K : ℕ) (hK : n * lineCalls p ≤ K)
    (hfinished : ((advance p f g)^[n] (initialControl p)).finished = true)
    (ξ : (k : ℕ) → O.Seed k) :
    OracleTemplate.execute O (algorithm p) (fun _ => K) () ξ =
      ((advance p f g)^[n] (initialControl p)).incumbent := by
  rw [execute_iterates p O f g hO]
  have he : K = (K - n * lineCalls p) + n * lineCalls p := by omega
  rw [he, Function.iterate_add_apply, blocks]
  rw [Function.iterate_fixed (step_finished p f g _ hfinished)]

end LongTails.Proofs.KnownValueNondualExecution
