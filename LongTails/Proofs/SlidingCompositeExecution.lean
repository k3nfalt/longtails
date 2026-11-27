import LongTails.Algorithms.SlidingStochasticComposite
import LongTails.Proofs.Execution
import LongTails.Proofs.SgdExecution

open MeasureTheory

namespace LongTails.Proofs.SlidingCompositeExecution

open OracleTemplate OracleTemplate.SlidingStochasticComposite OracleTemplate.StochasticGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Type}

lemma advance_succ' {S : Type*} (step : ℕ → S → S) (k call : ℕ) (s : S) :
    advance step (k + 1) call s = step (call + k) (advance step k call s) := by
  induction k generalizing call s with
  | zero => simp [advance]
  | succ k ih =>
      rw [advance, ih, advance]
      congr 1
      omega

lemma advance_add {S : Type*} (step : ℕ → S → S) (a b call : ℕ) (s : S) :
    advance step (a + b) call s = advance step b (call + a) (advance step a call s) := by
  induction a generalizing call s with
  | zero => simp [advance]
  | succ a ih =>
      rw [show a + 1 + b = (a + b) + 1 by omega, advance, ih, advance]
      congr 1
      omega

variable (ℓ D : ℝ) (N K : ℕ) (x0 : E) (gf : E → E) (g : E → Ω → E) (ξ : ℕ → Ω)

noncomputable def answer (k : ℕ) (q : Fin 2 × E) : E :=
  if q.1 = 0 then gf q.2 else g q.2 (ξ k)

noncomputable def step (k : ℕ) (s : State E) : State E :=
  (method ℓ D N K x0).update s (answer gf g ξ k ((method ℓ D N K x0).query s))

lemma divmod_of (q r : ℕ) (h : r < N + 1) :
    (q * (N + 1) + r) / (N + 1) = q ∧ (q * (N + 1) + r) % (N + 1) = r := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.succ_pos N), Nat.div_eq_of_lt h, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h]

lemma step_boundary (k : ℕ) (s : State E) (h : s.t % (N + 1) = 0) :
    step ℓ D N K x0 gf g ξ k s =
      ⟨s.t + 1, s.c, gf s.c, 0, s.c, s.c, s.index,
        if s.t / (N + 1) = s.index then s.c else s.out⟩ := by
  simp [step, method, answer, h]

lemma step_inner (k : ℕ) (s : State E) (h : ¬ s.t % (N + 1) = 0) :
    step ℓ D N K x0 gf g ξ k s =
      let y := Gradient.acceleratedQuery (s.k, s.x, s.z)
      let G := s.v + g y (ξ k) + ℓ • (y - s.c)
      ⟨s.t + 1, if s.t % (N + 1) = N then y - (1 / D) • G else s.c, s.v, s.k + 1,
        y - (1 / D) • G, s.z - (((s.k : ℝ) + 1) / (2 * D)) • G, s.index, s.out⟩ := by
  simp [step, method, answer, h, div_div]

lemma run_snoc {Ω' : Type*} (g' : E → Ω' → E) (m k : ℕ) (x z : E) (η : Fin (m + 1) → Ω') :
    acceleratedRun g' D (m + 1) k x z η =
      let p := acceleratedRun g' D m k x z (fun i => η i.castSucc)
      let y := Gradient.acceleratedQuery (k + m, p.1, p.2)
      (y - (1 / D) • g' y (η (Fin.last m)),
        p.2 - ((((k + m : ℕ) : ℝ) + 1) / (2 * D)) • g' y (η (Fin.last m))) := by
  induction m generalizing k x z with
  | zero => simp [acceleratedRun]
  | succ m ih =>
      rw [acceleratedRun, ih]
      simp only [acceleratedRun, Fin.castSucc_zero, Fin.succ_last, Fin.succ_castSucc]
      congr 2 <;> push_cast <;> ring_nf

lemma inner_phase (m : ℕ) (s : State E) (call q r : ℕ) (hcall : s.t = call) (hr1 : 1 ≤ r)
    (hrN : r + m ≤ N) (ht : s.t = q * (N + 1) + r) :
    advance (step ℓ D N K x0 gf g ξ) m call s =
      ⟨s.t + m, s.c, s.v, s.k + m,
        (acceleratedRun (fun y ω => s.v + g y ω + ℓ • (y - s.c)) D m s.k s.x s.z
          (fun i => ξ (s.t + i))).1,
        (acceleratedRun (fun y ω => s.v + g y ω + ℓ • (y - s.c)) D m s.k s.x s.z
          (fun i => ξ (s.t + i))).2,
        s.index, s.out⟩ := by
  induction m generalizing s r call with
  | zero => cases s; simp [advance, acceleratedRun]
  | succ m ih =>
      subst hcall
      have hmod : s.t % (N + 1) = r := by rw [ht]; exact (divmod_of N q r (by omega)).2
      have hne : ¬ s.t % (N + 1) = 0 := by omega
      have hlast : ¬ s.t % (N + 1) = N := by omega
      rw [advance, step_inner ℓ D N K x0 gf g ξ s.t s hne]
      simp only [hlast, ite_false]
      rw [ih _ (s.t + 1) (r + 1) rfl (by omega) (by omega) (by simp only; omega)]
      have hξ : (fun i : Fin m => ξ (s.t + 1 + (i : ℕ))) = (fun i : Fin m => ξ (s.t + (i.succ : ℕ))) := by
        funext i
        congr 1
        simp only [Fin.val_succ]
        omega
      simp only [acceleratedRun]
      refine State.ext ?_ rfl rfl ?_ ?_ ?_ rfl rfl
      · simp only; omega
      · simp only; omega
      · simp only [Fin.val_zero, add_zero]
        rw [hξ]
      · simp only [Fin.val_zero, add_zero]
        rw [hξ]

lemma stage_run (s : State E) (q : ℕ) (hN : 1 ≤ N) (ht : s.t = q * (N + 1)) :
    advance (step ℓ D N K x0 gf g ξ) (N + 1) s.t s =
      ⟨(q + 1) * (N + 1), innerRun ℓ D N g s.c (gf s.c) (fun j => ξ (q * (N + 1) + 1 + j)),
        gf s.c, N,
        innerRun ℓ D N g s.c (gf s.c) (fun j => ξ (q * (N + 1) + 1 + j)),
        (acceleratedRun (fun y ω => gf s.c + g y ω + ℓ • (y - s.c)) D N 0 s.c s.c
          (fun i => ξ (q * (N + 1) + 1 + i))).2,
        s.index, if q = s.index then s.c else s.out⟩ := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hmod : s.t % (n + 1 + 1) = 0 := by rw [ht]; simp
  have hdiv : s.t / (n + 1 + 1) = q := by rw [ht]; simp
  let gg : E → Ω → E := fun y ω => gf s.c + g y ω + ℓ • (y - s.c)
  let η : Fin (n + 1) → Ω := fun j => ξ (q * (n + 1 + 1) + 1 + j)
  let s1 : State E := ⟨s.t + 1, s.c, gf s.c, 0, s.c, s.c, s.index,
    if q = s.index then s.c else s.out⟩
  let pr := acceleratedRun gg D n 0 s.c s.c (fun i => η i.castSucc)
  let s2 : State E := ⟨s.t + 1 + n, s.c, gf s.c, 0 + n, pr.1, pr.2, s.index,
    if q = s.index then s.c else s.out⟩
  have h1 : advance (step ℓ D (n + 1) K x0 gf g ξ) 1 s.t s = s1 := by
    simp only [advance]
    rw [step_boundary ℓ D (n + 1) K x0 gf g ξ s.t s hmod, hdiv]
  have ht1 : s1.t = q * (n + 1 + 1) + 1 := by
    show s.t + 1 = _
    rw [ht]
  have h2 : advance (step ℓ D (n + 1) K x0 gf g ξ) n (s.t + 1) s1 = s2 := by
    have key := inner_phase ℓ D (n + 1) K x0 gf g ξ n s1 (s.t + 1) q 1 rfl le_rfl (by omega) ht1
    refine key.trans ?_
    have hsamp : (fun i : Fin n => ξ (s1.t + i)) = fun i => η i.castSucc := by
      funext i
      show ξ (s.t + 1 + i) = ξ (q * (n + 1 + 1) + 1 + i)
      rw [ht]
    simp only [s2, pr, gg, hsamp]
    rfl
  have hmod2 : (s.t + (1 + n)) % (n + 1 + 1) = n + 1 := by
    rw [ht, show q * (n + 1 + 1) + (1 + n) = q * (n + 1 + 1) + (n + 1) by omega]
    exact (divmod_of (n + 1) q (n + 1) (by omega)).2
  have hmod3 : s2.t % (n + 1 + 1) = n + 1 := by
    show (s.t + 1 + n) % (n + 1 + 1) = n + 1
    rw [show s.t + 1 + n = s.t + (1 + n) by omega]
    exact hmod2
  have hne : ¬ s2.t % (n + 1 + 1) = 0 := by omega
  have hlast : (η (Fin.last n)) = ξ (s.t + (1 + n)) := by
    show ξ (q * (n + 1 + 1) + 1 + n) = ξ (s.t + (1 + n))
    rw [ht]
    congr 1
    omega
  calc advance (step ℓ D (n + 1) K x0 gf g ξ) (n + 1 + 1) s.t s
      = step ℓ D (n + 1) K x0 gf g ξ (s.t + (1 + n))
          (advance (step ℓ D (n + 1) K x0 gf g ξ) n (s.t + 1)
            (advance (step ℓ D (n + 1) K x0 gf g ξ) 1 s.t s)) := by
        rw [show n + 1 + 1 = (1 + n) + 1 by omega, advance_succ', advance_add]
    _ = step ℓ D (n + 1) K x0 gf g ξ (s.t + (1 + n)) s2 := by rw [h1, h2]
    _ = _ := by
        rw [step_inner ℓ D (n + 1) K x0 gf g ξ _ s2 hne]
        simp only [hmod3, ite_true]
        have hr := run_snoc D gg n 0 s.c s.c η
        simp only [innerRun]
        change _ = (⟨(q + 1) * (n + 1 + 1), (acceleratedRun gg D (n + 1) 0 s.c s.c η).1, gf s.c,
          n + 1, (acceleratedRun gg D (n + 1) 0 s.c s.c η).1,
          (acceleratedRun gg D (n + 1) 0 s.c s.c η).2, s.index,
          if q = s.index then s.c else s.out⟩ : State E)
        rw [hr]
        simp only [s2, pr, gg, hlast, zero_add]
        refine State.ext ?_ rfl rfl rfl rfl rfl rfl rfl
        show s.t + 1 + n + 1 = (q + 1) * (n + 1 + 1)
        rw [ht]
        ring

lemma step_t (k : ℕ) (s : State E) : (step ℓ D N K x0 gf g ξ k s).t = s.t + 1 := by
  unfold step
  simp only [method]
  split_ifs <;> rfl

lemma step_index (k : ℕ) (s : State E) : (step ℓ D N K x0 gf g ξ k s).index = s.index := by
  unfold step
  simp only [method]
  split_ifs <;> rfl

lemma advance_t (k call : ℕ) (s : State E) :
    (advance (step ℓ D N K x0 gf g ξ) k call s).t = s.t + k := by
  induction k generalizing call s with
  | zero => rfl
  | succ k ih => rw [advance, ih, step_t]; omega

lemma advance_index (k call : ℕ) (s : State E) :
    (advance (step ℓ D N K x0 gf g ξ) k call s).index = s.index := by
  induction k generalizing call s with
  | zero => rfl
  | succ k ih => rw [advance, ih, step_index]

noncomputable def blocks (k : ℕ) (j : Fin N) : Ω := ξ (k * (N + 1) + 1 + j)

def init (κ : Fin (K + 1)) : State E := ⟨0, x0, 0, 0, x0, x0, κ.val, x0⟩

noncomputable def stateAt (κ : Fin (K + 1)) (k : ℕ) : State E :=
  advance (step ℓ D N K x0 gf g ξ) k 0 (init K x0 κ)

lemma stateAt_t (κ : Fin (K + 1)) (k : ℕ) : (stateAt ℓ D N K x0 gf g ξ κ k).t = k := by
  have := advance_t ℓ D N K x0 gf g ξ k 0 (init K x0 κ)
  simpa [stateAt, init] using this

lemma stateAt_index (κ : Fin (K + 1)) (k : ℕ) :
    (stateAt ℓ D N K x0 gf g ξ κ k).index = κ.val := by
  have := advance_index ℓ D N K x0 gf g ξ k 0 (init K x0 κ)
  simpa [stateAt, init] using this

lemma query_fst (s : State E) :
    ((method ℓ D N K x0).query s).1 = if s.t % (N + 1) = 0 then 0 else 1 := by
  simp only [method]
  split_ifs <;> rfl

lemma full_run (hN : 1 ≤ N) (κ : Fin (K + 1)) (q : ℕ) :
    (stateAt ℓ D N K x0 gf g ξ κ (q * (N + 1))).c = centers ℓ D N gf g x0 (blocks N ξ) q ∧
      (stateAt ℓ D N K x0 gf g ξ κ (q * (N + 1))).out =
        if κ.val < q then centers ℓ D N gf g x0 (blocks N ξ) κ.val else x0 := by
  induction q with
  | zero => simp [stateAt, init, advance, centers]
  | succ q ih =>
      obtain ⟨h3, h4⟩ := ih
      set s0 := stateAt ℓ D N K x0 gf g ξ κ (q * (N + 1)) with hs0
      have h1 : s0.t = q * (N + 1) := stateAt_t ℓ D N K x0 gf g ξ κ _
      have h2 : s0.index = κ.val := stateAt_index ℓ D N K x0 gf g ξ κ _
      have e : stateAt ℓ D N K x0 gf g ξ κ ((q + 1) * (N + 1)) =
          advance (step ℓ D N K x0 gf g ξ) (N + 1) (q * (N + 1)) s0 := by
        have := advance_add (step ℓ D N K x0 gf g ξ) (q * (N + 1)) (N + 1) 0 (init K x0 κ)
        rw [zero_add] at this
        rw [show (q + 1) * (N + 1) = q * (N + 1) + (N + 1) by ring]
        exact this
      have key := stage_run ℓ D N K x0 gf g ξ s0 q hN h1
      rw [h1] at key
      rw [e, key]
      refine ⟨?_, ?_⟩
      · show innerRun ℓ D N g s0.c (gf s0.c) (fun j => ξ (q * (N + 1) + 1 + j)) =
          centers ℓ D N gf g x0 (blocks N ξ) (q + 1)
        rw [h3]
        rfl
      · show (if q = s0.index then s0.c else s0.out) = _
        rw [h2, h3, h4]
        by_cases hq : q = κ.val
        · subst hq
          simp
        · have hlt : (κ.val < q + 1) ↔ κ.val < q := by omega
          simp only [hq, ite_false]
          by_cases hk : κ.val < q
          · simp only [hk, hlt.mpr hk, ite_true]
          · have hk2 : ¬ κ.val < q + 1 := fun h => hk (hlt.mp h)
            simp only [hk, hk2, ite_false]

noncomputable def remF (q r : ℕ) : Fin 2 → ℕ :=
  fun i => if i = 0 then (K + 1) - (q + min r 1) else (K + 1) * N - (q * N + (r - 1))

noncomputable def remaining (κ : Fin (K + 1)) : ℕ → Fin 2 → ℕ
  | 0 => fun i => if i = 0 then K + 1 else (K + 1) * N
  | k + 1 =>
      Function.update (remaining κ k)
        ((method ℓ D N K x0).query (stateAt ℓ D N K x0 gf g ξ κ k)).1
        (remaining κ k ((method ℓ D N K x0).query (stateAt ℓ D N K x0 gf g ξ κ k)).1 - 1)

lemma remaining_eq (κ : Fin (K + 1)) (k : ℕ) :
    remaining ℓ D N K x0 gf g ξ κ k = remF N K (k / (N + 1)) (k % (N + 1)) := by
  induction k with
  | zero => funext i; fin_cases i <;> simp [remaining, remF]
  | succ k ih =>
      rw [remaining, query_fst, stateAt_t, ih]
      have hk := Nat.div_add_mod k (N + 1)
      have hr : k % (N + 1) < N + 1 := Nat.mod_lt _ (Nat.succ_pos N)
      have hk' : k = k / (N + 1) * (N + 1) + k % (N + 1) := by rw [Nat.mul_comm]; omega
      generalize hq : k / (N + 1) = q at *
      generalize hrr : k % (N + 1) = r at *
      subst hk'
      funext i
      by_cases hrN : r < N
      · obtain ⟨hd, hm⟩ := divmod_of N q (r + 1) (by omega)
        rw [show q * (N + 1) + r + 1 = q * (N + 1) + (r + 1) by omega, hd, hm]
        by_cases hr0 : r = 0
        · subst hr0
          fin_cases i <;> simp [remF, Function.update]
          omega
        · fin_cases i <;> simp [remF, Function.update, hr0] <;> omega
      · have hrN' : r = N := by omega
        subst hrN'
        obtain ⟨hd, hm⟩ := divmod_of r (q + 1) 0 (by omega)
        rw [show q * (r + 1) + r + 1 = (q + 1) * (r + 1) + 0 by ring, hd, hm]
        by_cases hr0 : r = 0
        · subst hr0
          fin_cases i <;> simp [remF, Function.update]
          omega
        · have hq1 : (q + 1) * r = q * r + r := by ring
          fin_cases i <;> simp [remF, Function.update, hr0, hq1] <;> omega

lemma out_stable (hN : 1 ≤ N) (κ : Fin (K + 1)) (j : ℕ) :
    (stateAt ℓ D N K x0 gf g ξ κ ((K + 1) * (N + 1) + j)).out =
      centers ℓ D N gf g x0 (blocks N ξ) κ.val := by
  induction j with
  | zero =>
      have h4 := (full_run ℓ D N K x0 gf g ξ hN κ (K + 1)).2
      rw [add_zero, h4]
      simp only [κ.isLt, ite_true]
  | succ j ih =>
      have e : stateAt ℓ D N K x0 gf g ξ κ ((K + 1) * (N + 1) + (j + 1)) =
          step ℓ D N K x0 gf g ξ (0 + ((K + 1) * (N + 1) + j))
            (stateAt ℓ D N K x0 gf g ξ κ ((K + 1) * (N + 1) + j)) := by
        rw [← Nat.add_assoc]
        exact advance_succ' (step ℓ D N K x0 gf g ξ) _ 0 (init K x0 κ)
      rw [e]
      set s := stateAt ℓ D N K x0 gf g ξ κ ((K + 1) * (N + 1) + j)
      have ht : s.t = (K + 1) * (N + 1) + j := stateAt_t ℓ D N K x0 gf g ξ κ _
      have hi : s.index = κ.val := stateAt_index ℓ D N K x0 gf g ξ κ _
      by_cases h0 : s.t % (N + 1) = 0
      · rw [step_boundary ℓ D N K x0 gf g ξ _ s h0]
        have hdiv : ¬ s.t / (N + 1) = s.index := by
          rw [ht, hi]
          have : K + 1 ≤ ((K + 1) * (N + 1) + j) / (N + 1) := by
            rw [Nat.le_div_iff_mul_le (Nat.succ_pos N)]; nlinarith
          have := κ.isLt
          omega
        show (if s.t / (N + 1) = s.index then s.c else s.out) = _
        simp only [hdiv, ite_false]
        exact ih
      · rw [step_inner ℓ D N K x0 gf g ξ _ s h0]
        exact ih

lemma execute_eq [MeasurableSpace Ω] (hN : 1 ≤ N) (law : ProbabilityMeasure (ℕ → Ω))
    (κ : Fin (K + 1)) :
    execute ({ Seed := fun _ => Ω
               law := law
               answer := fun _ q ω => if q.1 = 0 then gf q.2 else g q.2 ω } :
          Oracle E E 2) (method ℓ D N K x0)
      (fun i => if i = 0 then K + 1 else (K + 1) * N) κ ξ =
      centers ℓ D N gf g x0 (blocks N ξ) κ.val := by
  refine execute_eq_of_safe_prefix
    (O := ({ Seed := fun _ => Ω
             law := law
             answer := fun _ q ω => if q.1 = 0 then gf q.2 else g q.2 ω } : Oracle E E 2))
    (A := method ℓ D N K x0)
    (budget := fun i => if i = 0 then K + 1 else (K + 1) * N) (seed := κ) (ξ := ξ)
    (state := fun k => stateAt ℓ D N K x0 gf g ξ κ k)
    (remaining := remaining ℓ D N K x0 gf g ξ κ) (T := (K + 1) * (N + 1))
    (output := centers ℓ D N gf g x0 (blocks N ξ) κ.val) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro history
    show advance (step ℓ D N K x0 gf g ξ) (history.length + 1) 0 (init K x0 κ) = _
    rw [advance_succ', zero_add]
    rfl
  · rfl
  · intro k
    rfl
  · intro k hk
    rw [remaining_eq, query_fst, stateAt_t]
    have hq : k / (N + 1) ≤ K := by
      apply Nat.le_of_lt_succ
      rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos N)]
      exact hk
    have hr : k % (N + 1) < N + 1 := Nat.mod_lt _ (Nat.succ_pos N)
    by_cases h0 : k % (N + 1) = 0
    · simp only [h0, ite_true, remF]
      omega
    · simp only [h0, ite_false, remF]
      have h1 : ¬ (1 : Fin 2) = 0 := by decide
      simp only [h1, ite_false]
      have hq2 : k / (N + 1) * N ≤ K * N := Nat.mul_le_mul_right _ hq
      have he : (K + 1) * N = K * N + N := by ring
      omega
  · intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    exact out_stable ℓ D N K x0 gf g ξ hN κ j
  · simp only [Fin.sum_univ_two]
    have h1 : ¬ (1 : Fin 2) = 0 := by decide
    simp only [h1, ite_false, ite_true]
    nlinarith

end LongTails.Proofs.SlidingCompositeExecution
