import LongTails.Proofs.BallAnchoredSearchRun
import LongTails.Proofs.Execution

open scoped RealInnerProductSpace

namespace LongTails.Proofs.BallAnchoredExecution

open OracleTemplate
open LongTails.Setups.HessianStableSkewMonotone
open LongTails.Algorithms.BallAnchoredNewton
open LongTails.Proofs.BallAnchoredInner
open LongTails.Proofs.BallAnchoredSearch
open LongTails.Proofs.BallAnchoredTrial
open LongTails.Proofs.BallAnchoredOuter
open LongTails.Proofs.BallAnchoredRun
open LongTails.Proofs.BallAnchoredSearchRun
open LongTails.Proofs.LazyAnchoredLyapunov

noncomputable section

variable {p : Public} {F : p.E → p.E} {S : p.E →L[ℝ] p.E}

def logRatio (p : Public) (Λ : ℝ) : ℝ := Real.log (1 + 48 * Λ * rho p * stepMax p / (7 * radius p))

def outerBound (p : Public) (Λ : ℝ) : ℕ :=
  ⌊(logRatio p Λ ^ 2 * (p.D ^ 2 / (2 * decrement p))) ^ ((1 : ℝ) / 3)⌋₊ + 1

def roundBound (p : Public) (Λ : ℝ) : ℕ :=
  (haltBound p Λ + bisBound p Λ + 3) * tickMax p Λ (outerBound p Λ)

def totalBound (p : Public) (Λ : ℝ) : ℕ := (outerBound p Λ + 1) * roundBound p Λ

variable (hreg : Regular p F S) {xs : p.E} {Λ : ℝ} (hR : Region p F xs Λ)

structure Progress (k : ℕ) (A : ℝ) (z g : p.E) : Prop where
  inv : Inv p F xs Λ k A z g
  lt : A < stepMax p
  start : k = 0 → A = 0
  growth : ∀ n, k = n + 1 → ∃ A1 Q, Growth n A A1 Q ∧
    potential p.x0 A z g ≤ -(decrement p * Q) ∧ 7 * radius p ≤ 48 * Λ * rho p * A1

include hreg hR in
lemma progress_initial : Progress (xs := xs) (Λ := Λ) (F := F) 0 0 p.x0 0 :=
  ⟨inv_initial hreg hR, stepMax_pos hreg, fun _ => rfl, fun n h => absurd h (by omega)⟩

include hreg hR in
lemma progress_bound {k : ℕ} {A : ℝ} {z g : p.E}
    (hP : Progress (xs := xs) (Λ := Λ) (F := F) k A z g) : k ≤ outerBound p Λ := by
  rcases Nat.eq_zero_or_pos k with h0 | hk
  · rw [h0]; unfold outerBound; omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk.ne'
  obtain ⟨A1, Q, hG, hpot, hbig⟩ := hP.growth n rfl
  have hr := radius_pos hreg
  have hD := hreg.D_pos
  have hdec : 0 < decrement p := by unfold decrement; positivity
  have hA1 := hG.A1_pos
  have hA : 0 < A := lt_of_lt_of_le hA1 hG.A1_le
  have hb := growth_bound hG hP.lt.le
  have hg : g = F z := by
    rcases hP.inv.grad with h | h
    · exact absurd h hA.ne'
    · exact h
  have hmono : 0 ≤ ⟪g, z - xs⟫ := by
    have := monotone_F hreg z xs
    rwa [hR.zero, sub_zero, ← hg] at this
  have hlow := potential_lower p.x0 xs z g A p.D hA.le hR.x0_dist hmono
  have hQ : Q ≤ p.D ^ 2 / (2 * decrement p) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hratio_pos : 0 < stepMax p / A1 := div_pos (stepMax_pos hreg) hA1
  have hratio1 : 1 ≤ stepMax p / A1 := by
    rw [le_div_iff₀ hA1, one_mul]; exact hG.A1_le.trans hP.lt.le
  have hlog0 : 0 ≤ Real.log (stepMax p / A1) := Real.log_nonneg hratio1
  have hratio : stepMax p / A1 ≤ 48 * Λ * rho p * stepMax p / (7 * radius p) := by
    rw [div_le_div_iff₀ hA1 (by positivity)]
    have := stepMax_pos hreg
    nlinarith [mul_le_mul_of_nonneg_left hbig this.le]
  have hlog : Real.log (stepMax p / A1) ≤ logRatio p Λ :=
    Real.log_le_log hratio_pos (by linarith)
  have hlog2 : Real.log (stepMax p / A1) ^ 2 ≤ logRatio p Λ ^ 2 :=
    pow_le_pow_left₀ hlog0 hlog 2
  have hX : (n : ℝ) ^ 3 ≤ logRatio p Λ ^ 2 * (p.D ^ 2 / (2 * decrement p)) := by
    calc (n : ℝ) ^ 3 ≤ Real.log (stepMax p / A1) ^ 2 * Q := hb
      _ ≤ logRatio p Λ ^ 2 * (p.D ^ 2 / (2 * decrement p)) :=
        mul_le_mul hlog2 hQ hG.Q_nonneg (sq_nonneg _)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hroot : (n : ℝ) ≤ (logRatio p Λ ^ 2 * (p.D ^ 2 / (2 * decrement p))) ^ ((1 : ℝ) / 3) := by
    have h1 := Real.rpow_le_rpow (by positivity) hX (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have h2 : ((n : ℝ) ^ 3) ^ ((1 : ℝ) / 3) = n := by
      rw [show ((1 : ℝ) / 3) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.pow_rpow_inv_natCast hn0 (by norm_num)
    rwa [h2] at h1
  have := Nat.le_floor hroot
  unfold outerBound
  omega

include hreg hR in
lemma progress_step {k : ℕ} {A : ℝ} {z g : p.E}
    (hP : Progress (xs := xs) (Λ := Λ) (F := F) k A z g) (hk : k ≤ outerBound p Λ) :
    ∃ n ≤ roundBound p Λ, ∃ σ : State p, (trueStep F)^[n] (outerStart k A z g) = σ ∧
      ((∃ A' z' g', σ = outerStart (k + 1) A' z' g' ∧
          Progress (xs := xs) (Λ := Λ) (F := F) (k + 1) A' z' g') ∨
        (σ.phase = .finished ∧ ‖F σ.z‖ ≤ p.ε)) := by
  obtain ⟨n, hn, a, hacc, he⟩ := outer_search hreg hR hP.inv hk hP.lt
  refine ⟨n, hn, _, he, ?_⟩
  have hA := hP.inv.ok.A_nonneg
  have ha := hacc.pos
  have hφ := hacc.res ha
  by_cases hfin : stepMax p ≤ A + a
  · right
    have hσ : outerStart (k + 1) (A + a) (finalPoint F k A z g a) (F (finalPoint F k A z g a)) =
        ⟨.finished, k + 1, A + a, finalPoint F k A z g a, F (finalPoint F k A z g a), 0, false,
          0, 0, 0, 0, 0, p.x0, 0, 0⟩ := by
      unfold outerStart; rw [ite_eq_left hfin]
    rw [hσ]
    refine ⟨rfl, ?_⟩
    show ‖F (finalPoint F k A z g a)‖ ≤ p.ε
    rcases hacc.kind with hk' | hd
    · subst hk'
      exact terminal_accuracy hreg hR hP.inv ha hφ
    · have hI' := accept_inv hreg hR hP.inv ha hφ hd
      exact finished_accuracy hreg hR hI' hfin (by linarith)
  · left
    have hlt : A + a < stepMax p := lt_of_not_ge hfin
    have hd : radius p / 3 ≤ ‖finalPoint F k A z g a - cOf p A z g a‖ := by
      rcases hacc.kind with hk' | hd
      · exfalso; rw [hk'] at hlt; linarith
      · exact hd
    have hbig : 7 * radius p ≤ 48 * Λ * rho p * a := by
      rcases hacc.big with hk' | hb
      · exfalso; rw [hk'] at hlt; linarith
      · exact hb
    have hI' := accept_inv hreg hR hP.inv ha hφ hd
    have hpot := accept_potential hreg hP.inv ha hφ hd
    refine ⟨_, _, _, rfl, hI', hlt, fun h => absurd h (by omega), fun m hm => ?_⟩
    have hm' : m = k := by omega
    subst hm'
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · have hA0 := hP.start h0
      subst hA0
      subst h0
      refine ⟨a, 0, ?_, ?_, hbig⟩
      · rw [zero_add]; exact growth_zero ha
      · have := hI'.pot; simp only [mul_zero, neg_zero]; exact this
    · obtain ⟨n', hn'⟩ := Nat.exists_eq_add_one_of_ne_zero hpos.ne'
      obtain ⟨A1, Q, hG, hp0, hb1⟩ := hP.growth n' hn'
      refine ⟨A1, Q + ((A + a) / a) ^ 2, ?_, ?_, hb1⟩
      · rw [hn']; exact growth_step hG ha
      · have : decrement p * (Q + ((A + a) / a) ^ 2) =
            decrement p * Q + ((A + a) / a) ^ 2 * decrement p := by ring
        rw [this]; linarith

include hreg hR in
lemma progress_run (d : ℕ) : ∀ k A z g, Progress (xs := xs) (Λ := Λ) (F := F) k A z g →
    outerBound p Λ + 1 ≤ k + d →
      ∃ n ≤ d * roundBound p Λ, ∃ σ : State p, (trueStep F)^[n] (outerStart k A z g) = σ ∧
        σ.phase = .finished ∧ ‖F σ.z‖ ≤ p.ε := by
  induction d with
  | zero =>
    intro k A z g hP hk
    have := progress_bound hreg hR hP
    omega
  | succ d ih =>
    intro k A z g hP hk
    have hkb := progress_bound hreg hR hP
    obtain ⟨n, hn, σ, he, hcase⟩ := progress_step hreg hR hP hkb
    rcases hcase with ⟨A', z', g', rfl, hP'⟩ | ⟨hfin, hacc⟩
    · obtain ⟨n', hn', σ', he', hfin', hacc'⟩ := ih (k + 1) A' z' g' hP' (by omega)
      refine ⟨n' + n, ?_, σ', ?_, hfin', hacc'⟩
      · rw [add_mul, one_mul]; omega
      · rw [Function.iterate_add_apply, he, he']
    · refine ⟨n, ?_, σ, he, hfin, hacc⟩
      calc n ≤ roundBound p Λ := hn
        _ = 1 * roundBound p Λ := (one_mul _).symm
        _ ≤ (d + 1) * roundBound p Λ := Nat.mul_le_mul_right _ (by omega)

include hreg hR in
lemma run_finishes : ∃ n ≤ totalBound p Λ, ∃ σ : State p,
    (trueStep F)^[n] (initial (p := p)) = σ ∧ σ.phase = .finished ∧ ‖F σ.z‖ ≤ p.ε := by
  have := progress_run hreg hR (outerBound p Λ + 1) 0 0 p.x0 0 (progress_initial hreg hR)
    (by omega)
  exact this

lemma iterate_fixed (s : State p) (hs : s.phase = .finished) (m : ℕ) :
    (trueStep F)^[m] s = s := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, step_finished F s hs]

def channelCount (F : p.E → p.E) (ch : Fin 2) (t : ℕ) : ℕ :=
  ((Finset.range t).filter (fun u => (query ((trueStep F)^[u] (initial (p := p)))).1 = ch)).card

lemma channelCount_succ (F : p.E → p.E) (ch : Fin 2) (t : ℕ) :
    channelCount F ch (t + 1) = channelCount F ch t +
      (if (query ((trueStep F)^[t] (initial (p := p)))).1 = ch then 1 else 0) := by
  classical
  unfold channelCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

lemma channelCount_le (F : p.E → p.E) (ch : Fin 2) (t : ℕ) : channelCount F ch t ≤ t := by
  unfold channelCount
  exact (Finset.card_filter_le _ _).trans (by simp)

lemma execution_output (P : Params) (F : P.pub.E → P.pub.E)
    (O : Oracle P.pub.E (P.pub.E ⊕ (P.pub.E →L[ℝ] P.pub.E)) 2)
    (hF : ∀ k x seed, O.answer k (0, x) seed = Sum.inl (F x))
    (hJ : ∀ k x seed, O.answer k (1, x) seed = Sum.inr (fderiv ℝ F x))
    (budget : Fin 2 → ℕ) (T : ℕ) (hT : ∀ ch, T ≤ budget ch) (σ : State P.pub)
    (hσ : (trueStep F)^[T] (initial (p := P.pub)) = σ) (hfin : σ.phase = .finished)
    (seed : (algorithm (p := P.pub)).Seed) (ξ : (k : ℕ) → O.Seed k) :
    execute O (algorithm (p := P.pub)) budget seed ξ = σ.z := by
  have hans : ∀ hist q (sd : O.Seed hist.length), O.answer hist q sd = reply F q := by
    intro hist q sd
    obtain ⟨i, x⟩ := q
    fin_cases i
    · simp only [reply, Fin.isValue, Fin.zero_eta, ↓reduceIte]
      exact hF hist x sd
    · simp only [reply, Fin.isValue, Fin.mk_one, one_ne_zero, ↓reduceIte]
      exact hJ hist x sd
  let state : ℕ → State P.pub := fun t => (trueStep F)^[t] (initial (p := P.pub))
  let remaining : ℕ → Fin 2 → ℕ := fun t ch => budget ch - channelCount F ch t
  apply execute_eq_of_safe_prefix O (algorithm (p := P.pub)) budget seed ξ state remaining T σ.z
  · rfl
  · intro hist
    change (trueStep F)^[hist.length + 1] initial =
      update ((trueStep F)^[hist.length] initial)
        (O.answer hist (query ((trueStep F)^[hist.length] initial)) (ξ hist.length))
    rw [hans, Function.iterate_succ_apply']
    rfl
  · funext ch; simp [remaining, channelCount]
  · intro t
    change (fun ch => budget ch - channelCount F ch (t + 1)) =
      Function.update (fun ch => budget ch - channelCount F ch t)
        (query ((trueStep F)^[t] (initial (p := P.pub)))).1
        (budget (query ((trueStep F)^[t] (initial (p := P.pub)))).1 -
          channelCount F (query ((trueStep F)^[t] (initial (p := P.pub)))).1 t - 1)
    funext ch
    rw [channelCount_succ]
    by_cases hc : (query ((trueStep F)^[t] (initial (p := P.pub)))).1 = ch
    · subst hc
      simp only [ite_true, Function.update_self]
      omega
    · have hc' : ch ≠ (query ((trueStep F)^[t] (initial (p := P.pub)))).1 :=
        fun e => hc e.symm
      simp only [hc, ite_false, add_zero, Function.update_of_ne hc']
  · intro t ht
    change 0 < budget (query ((trueStep F)^[t] (initial (p := P.pub)))).1 -
      channelCount F (query ((trueStep F)^[t] (initial (p := P.pub)))).1 t
    have h1 := channelCount_le F (query ((trueStep F)^[t] (initial (p := P.pub)))).1 t
    have h2 := hT (query ((trueStep F)^[t] (initial (p := P.pub)))).1
    omega
  · intro t ht
    change ((trueStep F)^[t] (initial (p := P.pub))).z = σ.z
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [add_comm, Function.iterate_add_apply, hσ, iterate_fixed σ hfin]
  · have := hT 0
    simp only [Fin.sum_univ_two]
    omega

end

end LongTails.Proofs.BallAnchoredExecution
