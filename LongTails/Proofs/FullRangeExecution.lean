import LongTails.Algorithms.FullRangeProgram
import LongTails.Proofs.FullRangeOperator
import LongTails.Proofs.SgdExecution
import LongTails.Setups.StochasticCohypomonotoneInclusion
import LongTails.Proofs.FullRangeLaw
import LongTails.Proofs.FullRangeCertificate

namespace LongTails.Proofs.FullRangeExecution

open LongTails.Algorithms.FullRangeMlmc LongTails.Algorithms.FullRangeProgram
open LongTails.Proofs.FullRangeInner LongTails.Proofs.FullRangeOperator
open OracleTemplate.LocalHiddenConvex (ballProj)

section Prog

variable {Q R O O' : Type}

lemma eval_bind (resp : ℕ → Q → R) (p : Prog Q R O) (f : O → Prog Q R O') (c : ℕ) :
    Prog.eval resp (p.bind f) c =
      Prog.eval resp (f (Prog.eval resp p c).1) (Prog.eval resp p c).2 := by
  induction p generalizing c with
  | done o => rfl
  | ask q k ih =>
      simp only [Prog.bind, Prog.eval]
      exact ih _ _

lemma eval_le (resp : ℕ → Q → R) (p : Prog Q R O) (c : ℕ) : c ≤ (Prog.eval resp p c).2 := by
  induction p generalizing c with
  | done o => exact le_rfl
  | ask q k ih =>
      simp only [Prog.eval]
      exact (Nat.le_succ c).trans (ih _ _)

end Prog

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def resp (g : E → Ω → E) (J : ℝ → E → E) (ξ : ℕ → Ω) (c : ℕ) (q : Q E) : E :=
  LongTails.Setups.StochasticCohypomonotoneInclusion.reply g J q (ξ c)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma stateAdvance (x0 : E) (r : ℕ → Q E → E) (p : Prog (Q E) E (E × E)) (c m : ℕ) :
    OracleTemplate.StochasticGradient.advance
        (fun k st => stateUpdate st (r k (stateQuery x0 st).2))
        ((Prog.eval r p c).2 - c + m) c p = .done (Prog.eval r p c).1 := by
  induction p generalizing c with
  | done o =>
      simp only [Prog.eval, Nat.sub_self, zero_add]
      induction m generalizing c with
      | zero => rfl
      | succ m ihm => exact ihm (c + 1)
  | ask q k ih =>
      have hle := eval_le r (k (r c q)) (c + 1)
      have hev : Prog.eval r (.ask q k) c = Prog.eval r (k (r c q)) (c + 1) := rfl
      rw [hev]
      have e : (Prog.eval r (k (r c q)) (c + 1)).2 - c + m =
          ((Prog.eval r (k (r c q)) (c + 1)).2 - (c + 1) + m) + 1 := by omega
      rw [e]
      exact ih (r c q) (c + 1)

lemma stepProg_eval (g : E → Ω → E) (J : ℝ → E → E) (ξ : ℕ → Ω) (η γ : ℝ) (x z : E) (c : ℕ) :
    Prog.eval (resp g J ξ) (stepProg η γ x z) c = (innerStep J η γ x z (g z (ξ c)), c + 2) := rfl

lemma pathProg_eval (g : E → Ω → E) (J : ℝ → E → E) (ξ : ℕ → Ω) (η γ0 : ℝ) (n0 : ℕ) (x : E)
    (c k : ℕ) :
    (Prog.eval (resp g J ξ) (pathProg η γ0 n0 x k) c).2 = c + 2 * k ∧
    ∀ j ≤ k, (Prog.eval (resp g J ξ) (pathProg η γ0 n0 x k) c).1 j =
      innerPath J g η γ0 n0 x j (fun i => ξ (c + 2 * i)) := by
  induction k with
  | zero =>
      refine ⟨rfl, fun j hj => ?_⟩
      have : j = 0 := by omega
      subst this
      simp [pathProg, Prog.eval, innerPath, OracleTemplate.ContinuizedSimilarQuasar.iterateSamples]
  | succ k ih =>
      set e := Prog.eval (resp g J ξ) (pathProg η γ0 n0 x k) c with he
      have hk : e.1 k = innerPath J g η γ0 n0 x k (fun i => ξ (c + 2 * i)) := ih.2 k le_rfl
      have hval : Prog.eval (resp g J ξ) (pathProg η γ0 n0 x (k + 1)) c =
          (Function.update e.1 (k + 1)
            (innerStep J η (stepAt γ0 n0 k) x (e.1 k) (g (e.1 k) (ξ e.2))), e.2 + 2) := by
        rw [pathProg, eval_bind, ← he, eval_bind, stepProg_eval]
        rfl
      rw [hval]
      refine ⟨by
          change e.2 + 2 = _
          rw [ih.1]
          ring, fun j hj => ?_⟩
      change Function.update e.1 (k + 1)
        (innerStep J η (stepAt γ0 n0 k) x (e.1 k) (g (e.1 k) (ξ e.2))) j = _
      by_cases hjk : j = k + 1
      · subst hjk
        rw [Function.update_self, innerPath_succ, hk, ih.1]
      · rw [Function.update_of_ne hjk]
        exact ih.2 j (by omega)

lemma levelTime_le (n0 l : ℕ) (_hl : l ≠ 0) : levelTime n0 (l - 1) ≤ levelTime n0 l := by
  unfold levelTime
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))

lemma n0_le_levelTime (n0 l : ℕ) : n0 ≤ levelTime n0 l := by
  unfold levelTime
  exact Nat.le_mul_of_pos_right _ (by positivity)

lemma callProg_eval {S : Type} (g : E → Ω → E) (J : ℝ → E → E) (ξ : ℕ → Ω) (c : Cfg E S) (x : E)
    (l : ℕ) (off : ℕ) :
    Prog.eval (resp g J ξ) (callProg c x l) off =
      ((1 - c.a) • ballProj c.x0 c.r x +
        c.a • estimator J g c.η c.γ0 c.n0 c.top (ballProj c.x0 c.r x) l
          (fun i => ξ (off + 2 * i)), off + levelCost c.n0 l) := by
  set y := ballProj c.x0 c.r x with hy
  have hp := pathProg_eval g J ξ c.η c.γ0 c.n0 y off (levelTime c.n0 l)
  have hval : Prog.eval (resp g J ξ) (callProg c x l) off =
      ((1 - c.a) • y + c.a • histEstimate c.n0 c.top l
        (Prog.eval (resp g J ξ) (pathProg c.η c.γ0 c.n0 y (levelTime c.n0 l)) off).1,
        (Prog.eval (resp g J ξ) (pathProg c.η c.γ0 c.n0 y (levelTime c.n0 l)) off).2) := by
    unfold callProg
    rw [eval_bind]
    rfl
  rw [hval, hp.1]
  have hE : histEstimate c.n0 c.top l
      (Prog.eval (resp g J ξ) (pathProg c.η c.γ0 c.n0 y (levelTime c.n0 l)) off).1 =
      estimator J g c.η c.γ0 c.n0 c.top y l (fun i => ξ (off + 2 * i)) := by
    unfold histEstimate estimator
    by_cases hl : l = 0
    · rw [ite_eq_left hl, ite_eq_left hl]
      exact hp.2 _ (n0_le_levelTime _ _)
    · rw [ite_eq_right hl, ite_eq_right hl, hp.2 _ (n0_le_levelTime _ _), hp.2 _ le_rfl,
        hp.2 _ (levelTime_le _ _ hl)]
  rw [hE]
  rfl

noncomputable def callAdv {S : Type} (J : ℝ → E → E) (g : E → Ω → E) (c : Cfg E S) (s : S) (l : ℕ)
    (ζ : ℕ → Ω) : S :=
  c.update s ((1 - c.a) • ballProj c.x0 c.r (c.point s) +
    c.a • estimator J g c.η c.γ0 c.n0 c.top (ballProj c.x0 c.r (c.point s)) l ζ)

lemma loop_eval {S : Type} (g : E → Ω → E) (J : ℝ → E → E) (ξ : ℕ → Ω) (c : Cfg E S)
    (ls : List ℕ) (s : S) (off : ℕ) :
    Prog.eval (resp g J ξ) (loopProg c ls s) off =
      (LongTails.Proofs.FullRangeLaw.run (callAdv J g c) (levelTime c.n0) ls s
          (fun i => ξ (off + 2 * i)),
        off + 2 * LongTails.Proofs.FullRangeLaw.costOf (levelTime c.n0) ls) := by
  induction ls generalizing s off with
  | nil => simp [loopProg, Prog.eval, LongTails.Proofs.FullRangeLaw.run,
      LongTails.Proofs.FullRangeLaw.costOf]
  | cons l t ih =>
      rw [loopProg, eval_bind, callProg_eval, ih]
      simp only [LongTails.Proofs.FullRangeLaw.run, LongTails.Proofs.FullRangeLaw.costOf, levelCost]
      refine Prod.ext ?_ ?_
      · simp only
        congr 1
        funext i
        simp only [LongTails.Proofs.FullRangeLaw.shift]
        congr 1
        ring
      · simp only
        ring

omit [InnerProductSpace ℝ E] in
lemma batch_eval (g : E → Ω → E) (J : ℝ → E → E) (ξ : ℕ → Ω) (z : E) (m : ℕ) (acc : E) (off : ℕ) :
    Prog.eval (resp g J ξ) (batchProg z m acc) off =
      (acc + ∑ i : Fin m, g z (ξ (off + 2 * i)), off + 2 * m) := by
  induction m generalizing acc off with
  | zero => simp [batchProg, Prog.eval]
  | succ m ih =>
      change Prog.eval (resp g J ξ) (batchProg z m (acc + g z (ξ off))) (off + 1 + 1) = _
      rw [ih, Fin.sum_univ_succ]
      refine Prod.ext ?_ ?_
      · simp only [Fin.val_zero, mul_zero, add_zero, Fin.val_succ]
        rw [add_assoc]
        congr 2
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 2
        ring
      · simp only
        ring

lemma cert_eval {S : Type} (g : E → Ω → E) (J : ℝ → E → E) (ξ : ℕ → Ω) (c : Cfg E S) (y : E)
    (off : ℕ) (_hB : 0 < c.B) :
    let ζ : ℕ → Ω := fun i => ξ (off + 2 * i)
    let zhat := innerPath J g c.η c.γ0 c.n0 y (levelTime c.n0 c.top) ζ
    let p := y - c.η • LongTails.Proofs.FullRangeCertificate.certFhat g zhat
      (levelTime c.n0 c.top) c.B ζ
    Prog.eval (resp g J ξ) (certProg c y) off =
      ((J c.η p, c.η⁻¹ • (p - J c.η p)), off + 2 * levelTime c.n0 c.top + 2 * c.B + 1) := by
  intro ζ zhat p
  have hp := pathProg_eval g J ξ c.η c.γ0 c.n0 y off (levelTime c.n0 c.top)
  unfold certProg
  rw [eval_bind, eval_bind, hp.1, batch_eval]
  have hz : (Prog.eval (resp g J ξ) (pathProg c.η c.γ0 c.n0 y (levelTime c.n0 c.top)) off).1
      (levelTime c.n0 c.top) = zhat := hp.2 _ le_rfl
  rw [hz]
  have hF : (c.B : ℝ)⁻¹ • ((0 : E) + ∑ i : Fin c.B, g zhat (ξ (off + 2 * levelTime c.n0 c.top + 2 * i))) =
      LongTails.Proofs.FullRangeCertificate.certFhat g zhat (levelTime c.n0 c.top) c.B ζ := by
    simp only [LongTails.Proofs.FullRangeCertificate.certFhat, zero_add, one_div, ζ]
    congr 2
    funext i
    congr 2
    ring
  simp only [Prog.eval, resp, LongTails.Setups.StochasticCohypomonotoneInclusion.reply, Sum.elim_inr]
  rw [hF]

end LongTails.Proofs.FullRangeExecution
