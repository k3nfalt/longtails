import LongTails.Proofs.TailObliviousProcess
import LongTails.Proofs.SgdExecution

namespace LongTails.Proofs.TailObliviousExecution

open OracleTemplate OracleTemplate.StochasticGradient
open OracleTemplate.ContinuizedSimilarQuasar (iterateSamples)
open LongTails.Setups.TailObliviousMonotoneRootFinding
open LongTails.Algorithms.TailObliviousExtragradient
open TailObliviousProcess

variable {d : Public} {Ω : Type*}

lemma advance_add {S : Type*} (step : ℕ → S → S) (n m call : ℕ) (s : S) :
    advance step (n + m) call s = advance step m (call + n) (advance step n call s) := by
  induction n generalizing call s with
  | zero => simp [advance]
  | succ n ih =>
    rw [Nat.succ_add, advance, ih]
    simp only [advance, Nat.add_left_comm, Nat.add_comm]

noncomputable def machine (g : d.E → Ω → d.E) (ξ : ℕ → Ω) (i : ℕ) (s : State d) : State d :=
  update d s (g (if s.half then s.extra else s.point) (ξ i))

def epochOffset : ℕ → ℕ
  | 0 => 0
  | k + 1 => epochOffset k + (k + 1) * innerSteps k

noncomputable def epochStart (d : Public) (k : ℕ) (B : d.E) : State d :=
  ⟨k, 0, 0, false, strength d k 0 • d.x0, d.x0, d.x0, B⟩

lemma iterateSamples_succ {S : Type*} (f : S → (Fin 2 → Ω) → S) (n : ℕ) (x : S)
    (ζ : Fin (n + 1) → Fin 2 → Ω) :
    iterateSamples f (n + 1) x ζ = iterateSamples f n (f x (ζ 0)) (fun i => ζ i.succ) := rfl

lemma two_calls (g : d.E → Ω → d.E) (ξ : ℕ → Ω) (c e j t : ℕ) (b x w B : d.E)
    (ht : t + 1 < innerSteps e) :
    advance (machine g ξ) 2 c ⟨e, j, t, false, b, x, w, B⟩ =
      let z := egStep d g e j b x (fun h => ξ (c + h))
      ⟨e, j, t + 1, false, b, z, z, B⟩ := by
  simp [advance, machine, update, ht, egStep]

lemma stage_finish (g : d.E → Ω → d.E) (ξ : ℕ → Ω) (e j : ℕ) (b x w B : d.E) (c t m : ℕ)
    (hm : 0 < m) (htm : t + m = innerSteps e) :
    advance (machine g ξ) (2 * m) c ⟨e, j, t, false, b, x, w, B⟩ =
      let z := iterateSamples (fun y ω => egStep d g e j b y ω) m x
        (fun i h => ξ (c + 2 * i + h))
      if j < e then ⟨e, j + 1, 0, false, b + strength d e j • z, z, z, B⟩
      else ⟨e + 1, 0, 0, false, strength d (e + 1) 0 • d.x0, d.x0, d.x0, z⟩ := by
  induction m generalizing t c x w with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      have hn : ¬ t + 1 < innerSteps e := by omega
      by_cases hj : j < e
      · simp [advance, machine, update, hn, hj, iterateSamples, egStep]
      · simp [advance, machine, update, hn, hj, iterateSamples, egStep]
    | succ m =>
      have ht : t + 1 < innerSteps e := by omega
      rw [show 2 * (m + 1 + 1) = 2 + 2 * (m + 1) by ring, advance_add, two_calls g ξ c e j t b x w B ht]
      rw [ih _ _ (c + 2) (t + 1) (by omega) (by omega)]
      have hz : iterateSamples (fun y ω => egStep d g e j b y ω) (m + 1 + 1) x
          (fun i h => ξ (c + 2 * ↑i + ↑h)) =
          iterateSamples (fun y ω => egStep d g e j b y ω) (m + 1)
            (egStep d g e j b x (fun h => ξ (c + ↑h))) (fun i h => ξ (c + 2 + 2 * ↑i + ↑h)) := by
        have h0 : (fun h : Fin 2 => ξ (c + 2 * ↑(0 : Fin (m + 1 + 1)) + ↑h)) =
            fun h : Fin 2 => ξ (c + ↑h) := by
          funext h; simp
        have h1 : (fun (i : Fin (m + 1)) (h : Fin 2) => ξ (c + 2 * ↑i.succ + ↑h)) =
            fun (i : Fin (m + 1)) (h : Fin 2) => ξ (c + 2 + 2 * ↑i + ↑h) := by
          funext i h
          simp only [Fin.val_succ]
          ring_nf
        rw [iterateSamples_succ, h0, h1]
      dsimp only
      rw [hz]


def blocks (k c : ℕ) (ξ : ℕ → Ω) : ℕ → Fin (innerSteps k) → Fin 2 → Ω :=
  fun j i h => ξ (c + 2 * (j * innerSteps k + i) + h)

lemma advance_stages (g : d.E → Ω → d.E) (ξ : ℕ → Ω) (k c : ℕ) (B : d.E) (n : ℕ)
    (hn : n ≤ k + 1) :
    advance (machine g ξ) (2 * (n * innerSteps k)) c (epochStart d k B) =
      if n ≤ k then
        ⟨k, n, 0, false, (epochState d g k n (blocks k c ξ)).2.1,
          (epochState d g k n (blocks k c ξ)).2.2, (epochState d g k n (blocks k c ξ)).2.2, B⟩
      else epochStart d (k + 1) (epochState d g k n (blocks k c ξ)).2.2 := by
  induction n with
  | zero =>
    simp [advance, epochStart, epochState, iterateSamples]
  | succ n ih =>
    have hnk : n ≤ k := by omega
    have hi := ih (by omega)
    simp only [hnk, ↓reduceIte] at hi
    rw [show 2 * ((n + 1) * innerSteps k) = 2 * (n * innerSteps k) + 2 * innerSteps k by ring,
      advance_add, hi]
    have hN : 0 < innerSteps k := by unfold innerSteps; positivity
    rw [stage_finish g ξ k n _ _ _ B _ 0 (innerSteps k) hN (by omega)]
    have hstate := epochState_succ g k n (blocks k c ξ)
    have hsamp : (fun (i : Fin (innerSteps k)) (h : Fin 2) =>
        ξ (c + 2 * (n * innerSteps k) + 2 * ↑i + ↑h)) = blocks k c ξ n := by
      funext i h
      simp only [blocks]
      congr 1
      ring
    rw [hsamp]
    have hst := epochState_stage g k n (blocks k c ξ)
    by_cases hlt : n < k
    · have hle : n + 1 ≤ k := hlt
      simp only [hlt, ite_true, hle]
      rw [hstate]
      simp only [epochAdvance, stageRun, hst]
    · have hnot : ¬ (n + 1 ≤ k) := by omega
      simp only [hlt, ite_false, hnot]
      rw [hstate]
      simp only [epochAdvance, stageRun, hst, epochStart]

lemma advance_epoch (g : d.E → Ω → d.E) (ξ : ℕ → Ω) (k c : ℕ) (B : d.E) :
    advance (machine g ξ) (2 * ((k + 1) * innerSteps k)) c (epochStart d k B) =
      epochStart d (k + 1) (epochOutput d g k (blocks k c ξ)) := by
  rw [advance_stages g ξ k c B (k + 1) le_rfl]
  simp only [show ¬(k + 1 ≤ k) by omega, ↓reduceIte]
  rfl

noncomputable def bestBefore (g : d.E → Ω → d.E) (ξ : ℕ → Ω) : ℕ → d.E
  | 0 => d.x0
  | k + 1 => epochOutput d g k (blocks k (2 * epochOffset k) ξ)

lemma advance_doubling (g : d.E → Ω → d.E) (ξ : ℕ → Ω) (k : ℕ) :
    advance (machine g ξ) (2 * epochOffset k) 0 (initial d) =
      epochStart d k (bestBefore g ξ k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * epochOffset (k + 1) = 2 * epochOffset k + 2 * ((k + 1) * innerSteps k) by
      simp only [epochOffset]; ring, advance_add, ih, Nat.zero_add, advance_epoch]
    rfl

def remaining (k : ℕ) (s : State d) : ℕ :=
  2 * ((k - s.stage) * innerSteps k + (innerSteps k - s.step)) - (if s.half then 1 else 0)

lemma best_stable (g : d.E → Ω → d.E) (ξ : ℕ → Ω) (k : ℕ) (m : ℕ) :
    ∀ (s : State d) (c : ℕ), s.epoch = k → s.stage ≤ k → s.step < innerSteps k →
      m < remaining k s → (advance (machine g ξ) m c s).best = s.best := by
  induction m with
  | zero => intro s c _ _ _ _; rfl
  | succ m ih =>
    intro s c he hs ht hm
    rw [advance]
    obtain ⟨e, j, t, half, b, x, w, B⟩ := s
    simp only at he hs ht
    subst he
    simp only [remaining] at hm
    cases half with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.sub_zero] at hm
      have hmach : machine g ξ c ⟨e, j, t, false, b, x, w, B⟩ =
          ⟨e, j, t, true, b, x, x - stepSize d e j • (g x (ξ c) + strength d e j • x - b), B⟩ := by
        simp [machine, update]
      rw [hmach]
      exact ih _ (c + 1) rfl hs ht (by simp only [remaining, ↓reduceIte]; omega)
    | true =>
      simp only [↓reduceIte] at hm
      set x' := x - stepSize d e j • (g w (ξ c) + strength d e j • w - b) with hx'
      by_cases hstep : t + 1 < innerSteps e
      · have hmach : machine g ξ c ⟨e, j, t, true, b, x, w, B⟩ =
            ⟨e, j, t + 1, false, b, x', x', B⟩ := by
          simp [machine, update, hstep, hx']
        rw [hmach]
        exact ih _ (c + 1) rfl hs hstep
          (by simp only [remaining, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero]; omega)
      · by_cases hj : j < e
        · have hmach : machine g ξ c ⟨e, j, t, true, b, x, w, B⟩ =
              ⟨e, j + 1, 0, false, b + strength d e j • x', x', x', B⟩ := by
            simp [machine, update, hstep, hj, hx']
          rw [hmach]
          have hN : 0 < innerSteps e := by unfold innerSteps; positivity
          have hsplit : e - j = (e - (j + 1)) + 1 := by omega
          exact ih _ (c + 1) rfl hj hN (by
            simp only [remaining, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero]
            rw [hsplit, Nat.add_mul, one_mul] at hm
            omega)
        · exfalso
          have hje : e - j = 0 := by omega
          rw [hje, zero_mul, zero_add] at hm
          omega

lemma best_after (g : d.E → Ω → d.E) (ξ : ℕ → Ω) (k M : ℕ)
    (hlow : 2 * epochOffset k ≤ M) (hhigh : M < 2 * epochOffset (k + 1)) :
    (advance (machine g ξ) M 0 (initial d)).best = bestBefore g ξ k := by
  rw [show M = 2 * epochOffset k + (M - 2 * epochOffset k) by omega, advance_add,
    advance_doubling]
  have hN : 0 < innerSteps k := by unfold innerSteps; positivity
  apply best_stable g ξ k _ _ _ rfl (Nat.zero_le _) hN
  simp only [epochOffset] at hhigh
  simp only [remaining, epochStart, Nat.sub_zero, Bool.false_eq_true, ↓reduceIte]
  have : (k + 1) * innerSteps k = k * innerSteps k + innerSteps k := by ring
  omega

end LongTails.Proofs.TailObliviousExecution
