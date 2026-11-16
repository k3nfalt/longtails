import LongTails.Algorithms.ManyConstraintVR

open scoped BigOperators

namespace LongTails.Proofs.ManyConstraintPlanEval

open LongTails.Algorithms.ManyConstraintPlan LongTails.Algorithms.ManyConstraintPlan.Plan2
  LongTails.Algorithms.ManyConstraintVR LongTails.Proofs.ManyConstraintRun
  LongTails.Proofs.ManyConstraintPenalty LongTails.Proofs.ManyConstraintFinite
  LongTails.Proofs.ManyConstraintNoise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Ξ : Type*} {m : ℕ}

def ans (grad : Ξ → E → E) (P : Fin m → E → E) (ξ : ℕ → Ξ) : ℕ → Fin 2 → Q E m → E :=
  fun n i q => if i = 0 then grad (ξ n) q.1 else
    match q.2 with
    | some j => P j q.1
    | none => q.1

variable (grad : Ξ → E → E) (P : Fin m → E → E) (ξ : ℕ → Ξ)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma evalS_gradsK {U : Type*} {a c : ℕ} (x : E) :
    ∀ (b : ℕ) (K : (Fin b → E) → Plan2 (Q E m) E U a c) (n : ℕ),
      evalS (ans grad P ξ) n (gradsK x b K) =
        evalS (ans grad P ξ) (n + b) (K (fun i => grad (ξ (n + i)) x)) := by
  intro b
  induction b with
  | zero => intro K n; simp only [gradsK, add_zero]; congr 2; funext i; exact Fin.elim0 i
  | succ b ih =>
    intro K n
    simp only [gradsK, evalS]
    rw [ih]
    simp only [ans]
    rw [show n + 1 + b = n + (b + 1) by omega]
    congr 2
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp
    · simp only [Fin.cons_succ, Fin.val_succ]; congr 2; omega

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma evalS_projsK {U : Type*} {a c : ℕ} (x : E) :
    ∀ (n' : ℕ) (idx : Fin n' → Fin m) (K : (Fin n' → E) → Plan2 (Q E m) E U a c) (n : ℕ),
      evalS (ans grad P ξ) n (projsK x n' idx K) =
        evalS (ans grad P ξ) (n + n') (K (fun i => P (idx i) x)) := by
  intro n'
  induction n' with
  | zero => intro idx K n; simp only [projsK, add_zero]; congr 2; funext i; exact Fin.elim0 i
  | succ n' ih =>
    intro idx K n
    simp only [projsK, evalS]
    rw [ih]
    rw [show n + 1 + n' = n + (n' + 1) by omega]
    congr 2
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [ans]
    · simp

lemma stepFrom_eq (k : Knobs E) (s hs : E) (yz : E × E) (j : Fin m) (ω : Fin k.b → Ξ) :
    stepFrom k s hs yz (fun i => grad (ω i) (ManyConstraintCoupling.mix k.τ s yz.1 yz.2))
      (P j (ManyConstraintCoupling.mix k.τ s yz.1 yz.2)) (P j s) =
      step grad P k s hs yz j ω := by
  simp only [stepFrom, step, batch, penGrad, smul_sub]

lemma evalS_stepK {U : Type*} {a c : ℕ} (k : Knobs E) (s hs : E) (yz : E × E) (j : Fin m)
    (K : E × E → Plan2 (Q E m) E U a c) (n : ℕ) :
    evalS (ans grad P ξ) n (stepK k s hs yz j K) =
      evalS (ans grad P ξ) (n + (k.b + 2)) (K (step grad P k s hs yz j (fun i => ξ (n + i)))) := by
  unfold stepK
  rw [evalS_gradsK, evalS_cast, evalS_projsK, evalS_cast, evalS_projsK]
  rw [show n + k.b + 1 + 1 = n + (k.b + 2) by omega]
  congr 2

lemma evalS_innerK {U : Type*} {a c : ℕ} (k : Knobs E) (s hs : E) :
    ∀ (n' : ℕ) (yz : E × E) (js : Fin n' → Fin m) (K : (E × E) × E → Plan2 (Q E m) E U a c)
      (n : ℕ),
      evalS (ans grad P ξ) n (innerK k s hs n' yz js K) =
        evalS (ans grad P ξ) (n + n' * (k.b + 2))
          (K (innerRun grad P k s hs n' yz js (fun t => ξ (n + t)))) := by
  intro n'
  induction n' with
  | zero => intro yz js K n; simp only [innerK, evalS_cast, zero_mul, add_zero]; rfl
  | succ n' ih =>
    intro yz js K n
    simp only [innerK, evalS_cast]
    rw [evalS_stepK, ih]
    rw [show n + (k.b + 2) + n' * (k.b + 2) = n + (n' + 1) * (k.b + 2) by ring]
    congr 2
    simp only [innerRun]
    congr 3
    · funext t; congr 1; ring
    · congr 2; funext t; congr 1; ring

lemma evalS_epochK {U : Type*} {a c : ℕ} (k : Knobs E) (st : St E) (js : Fin k.M → Fin m)
    (K : St E → Plan2 (Q E m) E U a c) (n : ℕ) :
    evalS (ans grad P ξ) n (epochK k st js K) =
      evalS (ans grad P ξ) (n + epochLen m k) (K (epoch grad P k st js (fun t => ξ (n + t)))) := by
  unfold epochK
  rw [evalS_projsK, evalS_innerK]
  rw [show n + m + k.M * (k.b + 2) = n + epochLen m k by unfold epochLen; ring]
  congr 2
  have hs : (m : ℝ)⁻¹ • ∑ i, k.β • (st.s - P (id i) st.s) = hgrad k.β P st.s := by
    simp [hgrad, penGrad]
  simp only [epoch, hs]
  congr 3 <;> (congr 1; funext t; congr 1; ring)

lemma evalS_runK {U : Type*} {a c : ℕ} (k : Knobs E) :
    ∀ (S : ℕ) (st : St E) (jss : Fin S → Fin k.M → Fin m) (K : St E → Plan2 (Q E m) E U a c)
      (n : ℕ),
      evalS (ans grad P ξ) n (runK k S st jss K) =
        evalS (ans grad P ξ) (n + S * epochLen m k)
          (K (run grad P k S st jss (fun t => ξ (n + t)))) := by
  intro S
  induction S with
  | zero => intro st jss K n; simp only [runK, evalS_cast, zero_mul, add_zero]; rfl
  | succ S ih =>
    intro st jss K n
    simp only [runK, evalS_cast]
    rw [evalS_epochK, ih]
    rw [show n + epochLen m k + S * epochLen m k = n + (S + 1) * epochLen m k by ring]
    congr 2
    simp only [run]
    congr 2
    funext t; congr 1; ring

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma evalS_cleanupK {U : Type*} {a c : ℕ} :
    ∀ (Q' : ℕ) (p : E) (js : Fin Q' → Fin m) (K : E → Plan2 (Q E m) E U a c) (n : ℕ),
      evalS (ans grad P ξ) n (cleanupK Q' p js K) =
        evalS (ans grad P ξ) (n + Q') (K (cleanup P Q' p js)) := by
  intro Q'
  induction Q' with
  | zero => intro p js K n; rfl
  | succ Q' ih =>
    intro p js K n
    simp only [cleanupK, evalS]
    rw [ih]
    rw [show n + 1 + Q' = n + (Q' + 1) by omega]
    rfl

lemma evalS_fullPlan (k : Knobs E) (S Q' : ℕ)
    (seed : (Fin S → Fin k.M → Fin m) × (Fin Q' → Fin m)) :
    evalS (ans grad P ξ) 0 (fullPlan k S Q' seed) =
      cleanup P Q' (run grad P k S ⟨k.x0, k.x0, k.x0⟩ seed.1 ξ).s seed.2 := by
  unfold fullPlan
  rw [evalS_cast, evalS_runK, evalS_cast, evalS_cleanupK]
  simp only [zero_add]
  rfl

end LongTails.Proofs.ManyConstraintPlanEval
