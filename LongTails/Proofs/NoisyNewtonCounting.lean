import LongTails.Proofs.NoisyNewtonDescent

namespace LongTails.Proofs.NoisyNewtonCounting

open LongTails.Setups.StochasticLocalHessianConvex
open LongTails.Algorithms.NoisyDampedNewton
open LongTails.Proofs.NoisyNewtonProcess
open OracleTemplate.GeneralizedAccelerated (Iterate coupling)
open OracleTemplate.StochasticGeneralized (blockTrace blockTrace_succ blockAdvance)

lemma ghostTrace_prefix_live (p : Params) (f : Point p.d → ℝ) (u : Point p.d)
    (grad : Point p.d → Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (s : Ghost p)
    (ξ : ℕ → p.Ω) (n m : ℕ) (hm : m ≤ n)
    (hlive : ¬ stopped p (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ n).1) :
    ¬ stopped p (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ m).1 := by
  induction n with
  | zero => simpa only [Nat.eq_zero_of_le_zero hm] using hlive
  | succ n ih =>
    by_cases hmn : m = n + 1
    · simpa only [hmn] using hlive
    · have hprev : ¬ stopped p (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ n).1 := by
        intro hs
        rw [blockTrace_succ] at hlive
        exact hlive (ghostNext_sticky p f u grad g H _ _ _ hs)
      exact ih (by omega) hprev

def PhaseStep (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d)
    (s s' : State (Point p.d)) : Prop :=
  ∃ ξ : Fin (phaseCost p s) → p.Ω, s' = phaseNext p g H (phaseCost p s) s ξ

lemma ghostTrace_phaseStep (p : Params) (f : Point p.d → ℝ) (u : Point p.d)
    (grad : Point p.d → Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (s : Ghost p)
    (ξ : ℕ → p.Ω) (n : ℕ)
    (hlive : ¬ stopped p (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ n).1) :
    PhaseStep p g H
      (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ n).1.1
      (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ (n + 1)).1.1 := by
  rw [blockTrace_succ]
  dsimp only [blockAdvance]
  rw [ghostNext_state p f u grad g H _ _ _ hlive]
  have hc : ghostCost p (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ n).1 =
      phaseCost p (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ n).1.1 := by
    simp only [ghostCost, ite_eq_right hlive]
  rw [hc]
  exact ⟨_, rfl⟩

lemma phaseStep_done (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (it : Iterate (Point p.d))
    (s : State (Point p.d)) (h : PhaseStep p g H (.done it) s) : s = .done it := by
  obtain ⟨ξ, h⟩ := h
  exact h

lemma phaseStep_cycle (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (it : Iterate (Point p.d))
    (s₁ s₂ s₃ : State (Point p.d))
    (h₀ : PhaseStep p g H (.model it 0 (fun _ => 0)) s₁)
    (h₁ : PhaseStep p g H s₁ s₂) (h₂ : PhaseStep p g H s₂ s₃) :
    ∃ (v w : Point p.d) (t : Trial (Point p.d)),
      s₁ = .hessian it v ∧
      t = prepare p.M₀ p.M₁ p.ρ p.δ (tolerance p) it (H (coupling it)) v ∧
      t.previous = it ∧ s₂ = .correction t 0 (fun _ => 0) ∧
      s₃ = resume p (finish (curvatureFloor p) t w) := by
  obtain ⟨ξ₀, rfl⟩ := h₀
  obtain ⟨ξ₁, rfl⟩ := h₁
  obtain ⟨ξ₂, rfl⟩ := h₂
  exact ⟨_, _, _, rfl, rfl, rfl, rfl, rfl⟩

lemma phasePath_done (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (S : ℕ → State (Point p.d))
    (n m : ℕ) (hstep : ∀ i < n, PhaseStep p g H (S i) (S (i + 1)))
    (hm : m ≤ n) (it : Iterate (Point p.d)) (hd : S m = .done it) : S n = .done it := by
  induction n with
  | zero => simpa only [Nat.eq_zero_of_le_zero hm] using hd
  | succ n ih =>
    by_cases hmn : m = n + 1
    · simpa only [hmn] using hd
    · have hn := ih (fun i hi => hstep i (by omega)) (by omega)
      have hh := hstep n (by omega)
      rw [hn] at hh
      exact phaseStep_done p g H it _ hh

lemma resume_of_not_done (p : Params) (it : Iterate (Point p.d))
    (h : resume p it ≠ .done it) : resume p it = .model it 0 (fun _ => 0) := by
  classical
  by_cases hh : target p / 2 ≤ it.A
  · simp only [resume, ite_eq_left hh, ne_eq, not_true_eq_false] at h
  · simp only [resume, ite_eq_right hh]

lemma phasePath_model_cycles (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (S : ℕ → State (Point p.d))
    (N : ℕ) (hstep : ∀ i < 3 * N, PhaseStep p g H (S i) (S (i + 1)))
    (it₀ : Iterate (Point p.d)) (h₀ : S 0 = .model it₀ 0 (fun _ => 0))
    (hn : ∀ it, S (3 * N) ≠ .done it) (i : ℕ) (hi : i ≤ N) :
    ∃ it, S (3 * i) = .model it 0 (fun _ => 0) := by
  induction i with
  | zero => exact ⟨it₀, h₀⟩
  | succ i ih =>
    obtain ⟨it, hit⟩ := ih (by omega)
    have h₁ := hstep (3 * i) (by omega)
    rw [hit] at h₁
    have h₂ := hstep (3 * i + 1) (by omega)
    have h₃ := hstep (3 * i + 2) (by omega)
    obtain ⟨v, w, t, _, _, _, _, hout⟩ :=
      phaseStep_cycle p g H it _ _ _ h₁ h₂ h₃
    have hnot : resume p (finish (curvatureFloor p) t w) ≠
        .done (finish (curvatureFloor p) t w) := by
      intro hd
      apply hn (finish (curvatureFloor p) t w)
      exact phasePath_done p g H S (3 * N) (3 * i + 3) hstep (by omega) _ (hout.trans hd)
    refine ⟨finish (curvatureFloor p) t w, ?_⟩
    rw [show 3 * (i + 1) = 3 * i + 3 by omega]
    exact hout.trans (resume_of_not_done p _ hnot)

def stateTrial {E : Type*} [Zero E] (s : State E) : Trial E :=
  match s with
  | .correction t _ _ => t
  | _ => ⟨baseIterate s, 1, 0⟩

def cycleIterate {E : Type*} (S : ℕ → State E) (i : ℕ) : Iterate E := baseIterate (S (3 * i))

def cycleTrial {E : Type*} [Zero E] (S : ℕ → State E) (i : ℕ) : Trial E :=
  stateTrial (S (3 * i + 2))

lemma phasePath_cycle_data (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (S : ℕ → State (Point p.d))
    (N : ℕ) (hstep : ∀ i < 3 * N, PhaseStep p g H (S i) (S (i + 1)))
    (it₀ : Iterate (Point p.d)) (h₀ : S 0 = .model it₀ 0 (fun _ => 0))
    (hn : ∀ it, S (3 * N) ≠ .done it) (i : ℕ) (hi : i < N) :
    ∃ v w,
      cycleTrial S i = prepare p.M₀ p.M₁ p.ρ p.δ (tolerance p)
        (cycleIterate S i) (H (coupling (cycleIterate S i))) v ∧
      (cycleTrial S i).previous = cycleIterate S i ∧
      S (3 * i + 2) = .correction (cycleTrial S i) 0 (fun _ => 0) ∧
      cycleIterate S (i + 1) = finish (curvatureFloor p) (cycleTrial S i) w := by
  obtain ⟨it, hit⟩ := phasePath_model_cycles p g H S N hstep it₀ h₀ hn i hi.le
  have h₁ := hstep (3 * i) (by omega)
  rw [hit] at h₁
  have h₂ := hstep (3 * i + 1) (by omega)
  have h₃ := hstep (3 * i + 2) (by omega)
  obtain ⟨v, w, t, _, ht, hprev, hcorr, hout⟩ := phaseStep_cycle p g H it _ _ _ h₁ h₂ h₃
  have hi₀ : cycleIterate S i = it := by simp only [cycleIterate, hit, baseIterate]
  have ht₀ : cycleTrial S i = t := by simp only [cycleTrial, hcorr, stateTrial]
  refine ⟨v, w, ?_, ?_, ?_, ?_⟩
  · simpa only [hi₀, ht₀] using ht
  · simpa only [hi₀, ht₀] using hprev
  · simpa only [ht₀] using hcorr
  · rw [ht₀]
    unfold cycleIterate
    rw [show 3 * (i + 1) = 3 * i + 3 by omega, hout, baseIterate_resume]

noncomputable def cycleLevel {E : Type*} [Zero E] (S : ℕ → State E) : ℕ → ℕ
  | 0 => 0
  | i + 1 => if (cycleTrial S i).curvature = (cycleTrial S i).previous.guess
      then cycleLevel S i - 1 else cycleLevel S i + 1

lemma phasePath_dyadic_guess (p : Params) (hp : spec.valid p)
    (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (S : ℕ → State (Point p.d))
    (N : ℕ) (hstep : ∀ i < 3 * N, PhaseStep p g H (S i) (S (i + 1)))
    (it₀ : Iterate (Point p.d)) (h₀ : S 0 = .model it₀ 0 (fun _ => 0))
    (hguess : it₀.guess = curvatureFloor p) (hn : ∀ it, S (3 * N) ≠ .done it)
    (i : ℕ) (hi : i ≤ N) :
    (cycleIterate S i).guess = curvatureFloor p * 2 ^ cycleLevel S i := by
  have hf : 0 ≤ curvatureFloor p := by
    have hW := LongTails.Proofs.NoisyNewtonTuning.target_pos p hp
    unfold curvatureFloor
    positivity
  induction i with
  | zero => simpa only [cycleIterate, Nat.mul_zero, h₀, baseIterate, cycleLevel, pow_zero, mul_one] using hguess
  | succ i ih =>
    obtain ⟨v, w, _, hprev, _, hnext⟩ := phasePath_cycle_data p g H S N hstep it₀ h₀ hn i (by omega)
    have hlevel : (cycleTrial S i).previous.guess = curvatureFloor p * 2 ^ cycleLevel S i := by
      rw [hprev]
      exact ih (by omega)
    rw [hnext]
    exact LongTails.Proofs.NoisyMsAccounting.finish_dyadic_level
      (cycleTrial S i) (curvatureFloor p) hf (cycleLevel S i) hlevel w

noncomputable def cycleRejected {E : Type*} [Zero E] (S : ℕ → State E) (i : ℕ) : Bool :=
  decide ((cycleTrial S i).curvature ≠ (cycleTrial S i).previous.guess)

lemma cycleLevel_succ {E : Type*} [Zero E] (S : ℕ → State E) (i : ℕ) :
    cycleLevel S (i + 1) = if cycleRejected S i then cycleLevel S i + 1 else cycleLevel S i - 1 := by
  classical
  by_cases h : (cycleTrial S i).curvature = (cycleTrial S i).previous.guess
  · simp [cycleLevel, cycleRejected, h]
  · simp [cycleLevel, cycleRejected, h]

lemma correction_sum_le (D : ℕ → ℝ) (N : ℕ) (hD : ∀ i < 3 * N, 0 ≤ D i) :
    ∑ i ∈ Finset.range N, D (3 * i + 2) ≤ ∑ i ∈ Finset.range (3 * N), D i := by
  classical
  calc
    _ = ∑ j ∈ (Finset.range N).image (fun i => 3 * i + 2), D j := by
      rw [Finset.sum_image]
      intro i hi j hj hij
      dsimp only at hij
      omega
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      simp only [Finset.mem_range] at hi ⊢
      omega) (fun j hj _ => hD j (Finset.mem_range.mp hj))

lemma initial_model (p : Params) (hp : spec.valid p) (hΔ : ¬ p.Δ ≤ p.ε) :
    (initialGhost p).1 = .model (initialIterate p) 0 (fun _ => 0) := by
  have hW := LongTails.Proofs.NoisyNewtonTuning.target_pos p hp
  have hA := (LongTails.Proofs.NoisyNewtonTuning.initial_properties p hp).2.1
  have hcap : ¬ target p / 2 ≤ (initialIterate p).A := by linarith
  change (if p.Δ ≤ p.ε then .done (initialIterate p) else resume p (initialIterate p)) = _
  simp only [ite_eq_right hΔ, resume, ite_eq_right hcap]

lemma ghostTrace_phasePath (p : Params) (f : Point p.d → ℝ) (u : Point p.d)
    (grad : Point p.d → Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (s : Ghost p)
    (ξ : ℕ → p.Ω) (n : ℕ)
    (hlive : ¬ stopped p (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ n).1) :
    ∀ i < n, PhaseStep p g H
      (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ i).1.1
      (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ (i + 1)).1.1 := by
  intro i hi
  exact ghostTrace_phaseStep p f u grad g H s ξ i
    (ghostTrace_prefix_live p f u grad g H s ξ n i hi.le hlive)

lemma initialTrace_model_cycles (p : Params) (hp : spec.valid p) (hΔ : ¬ p.Δ ≤ p.ε)
    (f : Point p.d → ℝ) (u : Point p.d) (grad : Point p.d → Point p.d)
    (g : Point p.d → p.Ω → Point p.d) (H : Point p.d → Point p.d →L[ℝ] Point p.d)
    (ξ : ℕ → p.Ω) (N : ℕ)
    (hlive : ¬ stopped p
      (blockTrace (ghostCost p) (ghostNext p f u grad g H) (initialGhost p) ξ (3 * N)).1)
    (hn : ∀ it, (blockTrace (ghostCost p) (ghostNext p f u grad g H)
      (initialGhost p) ξ (3 * N)).1.1 ≠ .done it) (i : ℕ) (hi : i ≤ N) :
    ∃ it, (blockTrace (ghostCost p) (ghostNext p f u grad g H)
      (initialGhost p) ξ (3 * i)).1.1 = .model it 0 (fun _ => 0) := by
  exact phasePath_model_cycles p g H _ N
    (ghostTrace_phasePath p f u grad g H (initialGhost p) ξ (3 * N) hlive)
    (initialIterate p) (initial_model p hp hΔ) hn i hi

noncomputable def trialDissipation {E : Type*} [NormedAddCommGroup E]
    (t : Trial E) : ℝ :=
  actualWeight t ^ 2 * (t.curvature * ‖t.displacement‖) ^ 2

lemma trialDissipation_nonneg {E : Type*} [NormedAddCommGroup E]
    (t : Trial E) : 0 ≤ trialDissipation t := by
  unfold trialDissipation
  positivity

lemma trialDissipation_identity {E : Type*} [NormedAddCommGroup E]
    (t : Trial E) (hA : 0 ≤ t.previous.A)
    (hη : 0 < t.previous.guess) (hτ : 0 < t.curvature) :
    trialDissipation t = t.previous.guess *
      (t.previous.A + OracleTemplate.GeneralizedAccelerated.tentativeWeight t.previous) *
      ‖t.displacement‖ ^ 2 := by
  have hroot := OracleTemplate.GeneralizedAccelerated.tentativeWeight_equation t.previous hA hη
  have he : actualWeight t * t.curvature =
      t.previous.guess * OracleTemplate.GeneralizedAccelerated.tentativeWeight t.previous := by
    unfold actualWeight
    field_simp
  calc
    _ = (actualWeight t * t.curvature) ^ 2 * ‖t.displacement‖ ^ 2 := by unfold trialDissipation; ring
    _ = t.previous.guess ^ 2 *
        OracleTemplate.GeneralizedAccelerated.tentativeWeight t.previous ^ 2 * ‖t.displacement‖ ^ 2 := by
      rw [he]
      ring
    _ = _ := by rw [← hroot]; ring

lemma prepared_high_charge (p : Params) (hp : spec.valid p) (it : Iterate (Point p.d))
    (H : Point p.d →L[ℝ] Point p.d) (v : Point p.d) (Q : ℝ)
    (hH : ∀ w, 0 ≤ inner ℝ (shifted H p.δ w) w)
    (hA : 0 < it.A) (hcap : it.A ≤ target p) (hη : 0 < it.guess)
    (hhigh : Q ^ 2 ≤ it.guess * it.A)
    (hcut : 16 * p.δ * target p ≤ tolerance p * Q ^ 2)
    (hrej : (prepare p.M₀ p.M₁ p.ρ p.δ (tolerance p) it H v).curvature ≠ it.guess) :
    let t := prepare p.M₀ p.M₁ p.ρ p.δ (tolerance p) it H v
    Q ^ 2 * p.ρ ^ 2 ≤ 4 * trialDissipation t ∨
      Q ^ 2 * tolerance p ≤ 16 * p.M₁ * trialDissipation t ∨
      tolerance p ^ 2 * Q ^ 6 ≤ 256 * p.M₀ ^ 2 * target p ^ 2 * trialDissipation t := by
  let t := prepare p.M₀ p.M₁ p.ρ p.δ (tolerance p) it H v
  change Q ^ 2 * p.ρ ^ 2 ≤ 4 * trialDissipation t ∨
    Q ^ 2 * tolerance p ≤ 16 * p.M₁ * trialDissipation t ∨
    tolerance p ^ 2 * Q ^ 6 ≤ 256 * p.M₀ ^ 2 * target p ^ 2 * trialDissipation t
  have ht : 2 * it.guess ≤ t.curvature :=
    LongTails.Proofs.NoisyNewtonModel.backtrack_curvature_rejected _ _ _ _ _ _ _ _ hη.le hrej
  have ht0 : 0 < t.curvature := by linarith
  have hprev : t.previous = it := rfl
  have hD := trialDissipation_identity t (hprev.symm ▸ hA.le) (hprev.symm ▸ hη) ht0
  rw [hprev] at hD
  have hprop := OracleTemplate.GeneralizedAccelerated.tentativeWeight_pos it hη
  have hd : Q ^ 2 * ‖t.displacement‖ ^ 2 ≤ trialDissipation t := by
    have hh := mul_le_mul_of_nonneg_right hhigh (sq_nonneg ‖t.displacement‖)
    have hh' := mul_nonneg (mul_nonneg hη.le hprop.le) (sq_nonneg ‖t.displacement‖)
    nlinarith only [hh, hh', hD]
  have hτ : 2 * Q ^ 2 ≤ t.curvature * it.A := by
    have hh := mul_le_mul_of_nonneg_right ht hA.le
    linarith
  have hδ := hp.2.2.2.1
  have hc : 8 * (2 * p.δ) * it.A ≤ tolerance p * Q ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hcap (show 0 ≤ 16 * p.δ by positivity)
    nlinarith only [hh, hcut]
  have hi : 0 < backtrackIndex p.M₀ p.M₁ p.ρ (2 * p.δ) (tolerance p) it.guess (shifted H p.δ) v := by
    by_contra hh
    have hz : backtrackIndex p.M₀ p.M₁ p.ρ (2 * p.δ) (tolerance p) it.guess (shifted H p.δ) v = 0 := by omega
    apply hrej
    simp only [prepare, backtrackCurvature, hz, pow_zero, mul_one]
  have hα := (LongTails.Proofs.NoisyNewtonTuning.tolerance_bounds p hp).1
  have hm := LongTails.Proofs.NoisyNewtonModel.backtrack_movement (shifted H p.δ) hH v
    p.M₀ p.M₁ p.ρ (2 * p.δ) (tolerance p) it.guess hp.1 hp.2.1 hp.2.2.1 hα hη hi
  exact LongTails.Proofs.NoisyMsAccounting.moving_movement_charge it.A (target p) Q
    (tolerance p) (2 * p.δ) p.M₀ p.M₁ p.ρ t.curvature ‖t.displacement‖ (trialDissipation t)
    hA hcap hα.le hp.2.1 hp.2.2.1.le hd hτ hc hm

lemma trial_full_increment {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t : Trial E) (floor Q : ℝ) (w : E) (hA : 0 < t.previous.A)
    (hη : 0 < t.previous.guess) (hQ : 0 ≤ Q) (hfull : t.curvature = t.previous.guess)
    (hsmall : t.previous.guess * t.previous.A ≤ 2 * Q ^ 2) :
    1 ≤ (2 * Q + 1) * (((finish floor t w).A - t.previous.A) / (finish floor t w).A) := by
  have ha : actualWeight t = OracleTemplate.GeneralizedAccelerated.tentativeWeight t.previous := by
    simp only [actualWeight, hfull, div_self hη.ne', one_mul]
  have hh := LongTails.Proofs.NoisyMsAccounting.low_full_relative_increment
    t.previous.A t.previous.guess (OracleTemplate.GeneralizedAccelerated.tentativeWeight t.previous)
    Q hA (OracleTemplate.GeneralizedAccelerated.tentativeWeight_pos t.previous hη) hQ
    (OracleTemplate.GeneralizedAccelerated.tentativeWeight_equation t.previous hA.le hη) hsmall
  change 1 ≤ (2 * Q + 1) * ((t.previous.A + actualWeight t - t.previous.A) /
    (t.previous.A + actualWeight t))
  simpa only [ha, add_sub_cancel_left] using hh

lemma ghostCycle_dissipation_sum (p : Params) (T : ℕ → Ghost p) (N : ℕ)
    (hlive : ∀ i < 3 * N, ¬ stopped p (T i))
    (hcorr : ∀ i < N, (T (3 * i + 2)).1 =
      .correction (cycleTrial (fun j => (T j).1) i) 0 (fun _ => 0)) :
    ∑ i ∈ Finset.range N, trialDissipation (cycleTrial (fun j => (T j).1) i) ≤
      ∑ j ∈ Finset.range (3 * N), LongTails.Proofs.NoisyNewtonDescent.ghostDissipation p (T j) := by
  calc
    _ = ∑ i ∈ Finset.range N,
        LongTails.Proofs.NoisyNewtonDescent.ghostDissipation p (T (3 * i + 2)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      simp only [LongTails.Proofs.NoisyNewtonDescent.ghostDissipation,
        ite_eq_right (hlive (3 * i + 2) (by omega)), hcorr i hi', trialDissipation]
    _ ≤ _ := correction_sum_le _ N
      (fun i _ => LongTails.Proofs.NoisyNewtonDescent.ghostDissipation_nonneg p (T i))

open LongTails.Proofs.NoisyNewtonTuning
open LongTails.Proofs.NoisyMsAccounting

lemma phasePath_count_lt_horizon (p : Params) (hp : spec.valid p)
    (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (S : ℕ → State (Point p.d))
    (N : ℕ) (hstep : ∀ i < 3 * N, PhaseStep p g H (S i) (S (i + 1)))
    (h₀ : S 0 = .model (initialIterate p) 0 (fun _ => 0))
    (hn : ∀ it, S (3 * N) ≠ .done it)
    (hbounds : ∀ i ≤ 3 * N, StateBounds p (S i))
    (hH : ∀ x w, 0 ≤ inner ℝ (shifted (H x) p.δ w) w)
    (hsum : ∑ i ∈ Finset.range N, trialDissipation (cycleTrial S i) ≤ 24 * p.R ^ 2) :
    (N : ℝ) < (horizon p : ℝ) := by
  let Q := countScale p
  let A := fun i => (cycleIterate S i).A
  let D := fun i => trialDissipation (cycleTrial S i)
  let threshold := fun i => dyadicThreshold (curvatureFloor p) (Q ^ 2 / A i)
  have hQ : 0 < Q := countScale_pos p hp
  have hα := (tolerance_bounds p hp).1
  have hW := target_pos p hp
  have hf : 0 < curvatureFloor p := by unfold curvatureFloor; positivity
  have hQ1 : 1 ≤ Q := by
    have hs := (shape_bounds p hp).1
    have hl := confidence_lower p hp
    dsimp [Q, countScale]
    nlinarith only [hs, hl, mul_nonneg (by linarith : 0 ≤ shape p - 1)
      (by linarith : 0 ≤ confidence p - 100)]
  have hb : ∀ i ≤ N, IterateBounds p (cycleIterate S i) := by
    intro i hi
    exact (hbounds (3 * i) (by omega)).1
  have hη : ∀ i ≤ N, 0 < (cycleIterate S i).guess :=
    fun i hi => hf.trans_le (hb i hi).2.2
  have hcycle := phasePath_cycle_data p g H S N hstep (initialIterate p) h₀ hn
  have hactive : ∀ i < N, A i < target p / 2 ∧
      (cycleTrial S i).previous.guess ≤ (cycleTrial S i).curvature := by
    intro i hi
    obtain ⟨v, w, _, hprev, hcorr, _⟩ := hcycle i hi
    have hh := hbounds (3 * i + 2) (by omega)
    rw [hcorr] at hh
    exact ⟨by simpa only [StateBounds, hprev] using hh.2.1, hh.2.2⟩
  have hmono : ∀ i < N, A i ≤ A (i + 1) := by
    intro i hi
    obtain ⟨v, w, _, hprev, _, hnext⟩ := hcycle i hi
    have hηt : 0 < (cycleTrial S i).previous.guess := by rw [hprev]; exact hη i hi.le
    have ha := (actualWeight_bounds (cycleTrial S i) hηt (hactive i hi).2).1
    change (cycleIterate S i).A ≤ (cycleIterate S (i + 1)).A
    rw [hnext]
    change (cycleIterate S i).A ≤ (cycleTrial S i).previous.A + actualWeight (cycleTrial S i)
    rw [hprev]
    linarith
  have hlevel : ∀ i ≤ N, (cycleIterate S i).guess = curvatureFloor p * 2 ^ cycleLevel S i :=
    phasePath_dyadic_guess p hp g H S N hstep (initialIterate p) h₀ rfl hn
  have hfloor : ∀ i < N, curvatureFloor p ≤ Q ^ 2 / A i := by
    intro i hi
    apply (le_div_iff₀ (hb i hi.le).1).mpr
    have hh := mul_le_mul_of_nonneg_left (hactive i hi).1.le hf.le
    have he : curvatureFloor p * (target p / 2) = 1 := by unfold curvatureFloor; field_simp
    rw [he] at hh
    nlinarith only [hh, hQ1, sq_nonneg (Q - 1)]
  have hcuts := countScale_rejection_cutoffs p hp
  have hcount := moving_prefix_count A D (cycleLevel S) threshold (cycleRejected S) N
    Q (tolerance p) p.ρ p.M₀ p.M₁ (target p) (24 * p.R ^ 2) (2 * Q + 1)
    hQ hα hp.2.2.1 hp.2.1 (by positivity) rfl
    (fun i hi => dyadic_threshold_mono _ _ _ hf
      (div_le_div_of_nonneg_left (sq_nonneg Q) (hb i (Finset.mem_range.mp hi).le).1
        (hmono i (Finset.mem_range.mp hi))))
    (fun i _ => cycleLevel_succ S i)
    (fun i hi => (hb i (Finset.mem_range.mp hi).le).1)
    (fun i hi => hmono i (Finset.mem_range.mp hi))
    (fun i _ => trialDissipation_nonneg _) hsum hcuts.1 hcuts.2.1 hcuts.2.2
  have hhigh : ∀ i ∈ Finset.range N, cycleRejected S i = true → threshold i ≤ cycleLevel S i →
      Q ^ 2 * p.ρ ^ 2 ≤ 4 * D i ∨ Q ^ 2 * tolerance p ≤ 16 * p.M₁ * D i ∨
        tolerance p ^ 2 * Q ^ 6 ≤ 256 * p.M₀ ^ 2 * target p ^ 2 * D i := by
    intro i hi hr ht
    have hi' := Finset.mem_range.mp hi
    obtain ⟨v, w, htprep, hprev, _, _⟩ := hcycle i hi'
    have hrej : (cycleTrial S i).curvature ≠ (cycleIterate S i).guess := by
      have hh : (cycleTrial S i).curvature ≠ (cycleTrial S i).previous.guess := by
        simpa only [cycleRejected, decide_eq_true_eq] using hr
      simpa only [hprev] using hh
    have hηQ : Q ^ 2 ≤ (cycleIterate S i).guess * A i := by
      have hh := dyadic_threshold_high (curvatureFloor p) (Q ^ 2 / A i)
        (cycleIterate S i).guess (cycleLevel S i) hf (hlevel i hi'.le) ht
      exact (div_le_iff₀ (hb i hi'.le).1).mp hh
    have hh := prepared_high_charge p hp (cycleIterate S i) (H (coupling (cycleIterate S i))) v Q
      (hH _) (hb i hi'.le).1 (by linarith [(hactive i hi').1]) (hη i hi'.le) hηQ
      (countScale_delta_cutoff p hp) (htprep ▸ hrej)
    simpa only [← htprep] using hh
  have hlow : ∀ i ∈ Finset.range N, cycleRejected S i = false → cycleLevel S i ≤ threshold i →
      1 ≤ (2 * Q + 1) * ((A (i + 1) - A i) / A (i + 1)) := by
    intro i hi hr ht
    have hi' := Finset.mem_range.mp hi
    obtain ⟨v, w, _, hprev, _, hnext⟩ := hcycle i hi'
    have hfull : (cycleTrial S i).curvature = (cycleTrial S i).previous.guess := by
      simpa only [cycleRejected, decide_eq_false_iff_not, not_not] using hr
    have hsmall : (cycleIterate S i).guess * A i ≤ 2 * Q ^ 2 := by
      have hh := dyadic_threshold_low (curvatureFloor p) (Q ^ 2 / A i)
        (cycleIterate S i).guess (cycleLevel S i) hf (hfloor i hi') (hlevel i hi'.le) ht
      have hm := mul_le_mul_of_nonneg_right hh (hb i hi'.le).1.le
      have he : 2 * (Q ^ 2 / A i) * A i = 2 * Q ^ 2 := by
        have hAi : A i ≠ 0 := (hb i hi'.le).1.ne'
        field_simp [hAi]
      rwa [he] at hm
    have hh := trial_full_increment (cycleTrial S i) (curvatureFloor p) Q w
      (hprev.symm ▸ (hb i hi'.le).1) (hprev.symm ▸ hη i hi'.le) hQ.le hfull
      (hprev.symm ▸ hsmall)
    simpa only [← hnext, hprev] using hh
  have hncount := hcount hhigh hlow
  have hA₀ : A 0 = (initialIterate p).A := by simp only [A, cycleIterate, Nat.mul_zero, h₀, baseIterate]
  have hl := iterate_log_ratio p hp (A N) (hb N le_rfl).1 (hb N le_rfl).2.1
  have ht := initial_threshold_bound p hp
  have ht₀ : (threshold 0 : ℝ) ≤ 10 * confidence p := by simpa only [threshold, hA₀] using ht
  rw [hA₀] at hncount
  have hlog := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2 * (2 * Q + 1) by positivity)
  have hhor := horizon_dominates_count p hp
  change 6 * Q + 2 * (2 * Q + 1) * confidence p + 20 * confidence p < _ at hhor
  linarith

lemma initialTrace_done (p : Params) (hp : spec.valid p)
    (f : Point p.d → ℝ) (u : Point p.d) (grad : Point p.d → Point p.d)
    (g : Point p.d → p.Ω → Point p.d) (H : Point p.d → Point p.d →L[ℝ] Point p.d)
    (hH : ∀ x w, 0 ≤ inner ℝ (shifted (H x) p.δ w) w) (ξ : ℕ → p.Ω)
    (hlive : ¬ stopped p (blockTrace (ghostCost p) (ghostNext p f u grad g H)
      (initialGhost p) ξ (3 * horizon p)).1)
    (hsum : ∑ i ∈ Finset.range (3 * horizon p),
      LongTails.Proofs.NoisyNewtonDescent.ghostDissipation p
        (blockTrace (ghostCost p) (ghostNext p f u grad g H) (initialGhost p) ξ i).1 ≤ 24 * p.R ^ 2) :
    ∃ it, (blockTrace (ghostCost p) (ghostNext p f u grad g H)
      (initialGhost p) ξ (3 * horizon p)).1.1 = .done it := by
  classical
  let T := blockTrace (ghostCost p) (ghostNext p f u grad g H) (initialGhost p) ξ
  let S := fun i => (T i).1.1
  have hstep : ∀ i < 3 * horizon p, PhaseStep p g H (S i) (S (i + 1)) :=
    ghostTrace_phasePath p f u grad g H (initialGhost p) ξ (3 * horizon p) hlive
  by_cases hΔ : p.Δ ≤ p.ε
  · have hi : S 0 = .done (initialIterate p) := by
      change (if p.Δ ≤ p.ε then .done (initialIterate p) else resume p (initialIterate p)) = _
      exact ite_eq_left hΔ
    exact ⟨initialIterate p, phasePath_done p g H S (3 * horizon p) 0 hstep (by omega) _ hi⟩
  · by_contra hn
    have hn' : ∀ it, S (3 * horizon p) ≠ .done it := by simpa only [not_exists] using hn
    have h₀ : S 0 = .model (initialIterate p) 0 (fun _ => 0) := initial_model p hp hΔ
    have hb : ∀ i ≤ 3 * horizon p, StateBounds p (S i) := fun i _ =>
      ghostTrace_bounds p hp f u grad g H (initialGhost p) ξ i (initial_bounds p hp)
    have hc : ∀ i < horizon p, (T (3 * i + 2)).1.1 =
        .correction (cycleTrial S i) 0 (fun _ => 0) := by
      intro i hi
      obtain ⟨v, w, _, _, hcorr, _⟩ := phasePath_cycle_data p g H S (horizon p)
        hstep (initialIterate p) h₀ hn' i hi
      exact hcorr
    have hd := ghostCycle_dissipation_sum p (fun i => (T i).1) (horizon p)
      (fun i hi => ghostTrace_prefix_live p f u grad g H (initialGhost p) ξ
        (3 * horizon p) i hi.le hlive) hc
    have hds : ∑ i ∈ Finset.range (horizon p), trialDissipation (cycleTrial S i) ≤ 24 * p.R ^ 2 :=
      hd.trans hsum
    have hh := phasePath_count_lt_horizon p hp g H S (horizon p) hstep h₀ hn' hb hH hds
    exact (lt_irrefl _ hh)

lemma cycle_proposal_sum (p : Params) (hp : spec.valid p)
    (it : ℕ → Iterate (Point p.d)) (t : ℕ → Trial (Point p.d)) (w : ℕ → Point p.d) (n : ℕ)
    (hb : ∀ i ≤ n, IterateBounds p (it i))
    (hprev : ∀ i < n, (t i).previous = it i)
    (hnext : ∀ i < n, it (i + 1) = finish (curvatureFloor p) (t i) (w i))
    (hτ : ∀ i < n, (t i).previous.guess ≤ (t i).curvature) :
    ∑ i ∈ Finset.range n, OracleTemplate.GeneralizedAccelerated.tentativeWeight (it i) ≤
      4 * OracleTemplate.GeneralizedAccelerated.tentativeWeight (it 0) + 13 * ((it n).A - (it 0).A) := by
  have hW := target_pos p hp
  have hf : 0 < curvatureFloor p := by unfold curvatureFloor; positivity
  have hη : ∀ i ≤ n, 0 < (it i).guess := fun i hi => hf.trans_le (hb i hi).2.2
  have hηt : ∀ i < n, 0 < (t i).previous.guess := by
    intro i hi
    rw [hprev i hi]
    exact hη i hi.le
  have ha : ∀ i < n, 0 ≤ actualWeight (t i) :=
    fun i hi => (actualWeight_bounds (t i) (hηt i hi) (hτ i hi)).1.le
  have hledger : ∀ k ≤ n, (∑ i ∈ Finset.range k, actualWeight (t i)) = (it k).A - (it 0).A := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih (by omega), hnext k (by omega)]
      change (it k).A - (it 0).A + actualWeight (t k) =
        (t k).previous.A + actualWeight (t k) - (it 0).A
      rw [hprev k (by omega)]
      ring
  have hh := total_proposals (fun i => OracleTemplate.GeneralizedAccelerated.tentativeWeight (it i))
    (fun i => actualWeight (t i)) n
    (fun i hi => (OracleTemplate.GeneralizedAccelerated.tentativeWeight_pos (it i) (hη i hi)).le)
    ha (by
      intro i hi
      have h := finish_weight_cases (t i) (hprev i hi ▸ (hb i hi.le).1.le)
        (hηt i hi) (hτ i hi) (curvatureFloor p) (w i)
      simpa only [← hnext i hi, hprev i hi] using h)
  rwa [hledger n le_rfl] at hh

lemma phasePath_cycle_boundary (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (S : ℕ → State (Point p.d))
    (N : ℕ) (hstep : ∀ i < 3 * N, PhaseStep p g H (S i) (S (i + 1)))
    (h₀ : (∃ it, S 0 = .model it 0 (fun _ => 0)) ∨ ∃ it, S 0 = .done it)
    (i : ℕ) (hi : i ≤ N) :
    (∃ it, S (3 * i) = .model it 0 (fun _ => 0)) ∨ ∃ it, S (3 * i) = .done it := by
  induction i with
  | zero => exact h₀
  | succ i ih =>
    rcases ih (by omega) with ⟨it, hit⟩ | ⟨it, hit⟩
    · have h₁ := hstep (3 * i) (by omega)
      rw [hit] at h₁
      obtain ⟨v, w, t, _, _, _, _, hout⟩ := phaseStep_cycle p g H it _ _ _ h₁
        (hstep (3 * i + 1) (by omega)) (hstep (3 * i + 2) (by omega))
      rw [show 3 * (i + 1) = 3 * i + 3 by omega, hout]
      unfold resume
      split_ifs
      · exact Or.inr ⟨_, rfl⟩
      · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨it, phasePath_done p g H S (3 * (i + 1)) (3 * i)
        (fun j hj => hstep j (by omega)) (by omega) it hit⟩

end LongTails.Proofs.NoisyNewtonCounting
