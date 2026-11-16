import LongTails.Algorithms.ManyConstraintPlan
import LongTails.Proofs.ManyConstraintRun

open scoped BigOperators

namespace LongTails.Algorithms.ManyConstraintVR

open LongTails.Algorithms.ManyConstraintPlan LongTails.Algorithms.ManyConstraintPlan.Plan2
  LongTails.Proofs.ManyConstraintRun LongTails.Proofs.ManyConstraintPenalty
  LongTails.Proofs.ManyConstraintBall LongTails.Proofs.ManyConstraintCoupling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : ℕ}

abbrev Q (E : Type*) (m : ℕ) := E × Option (Fin m)

def castPlan {U : Type*} {a c a' c' : ℕ} (h1 : a = a') (h2 : c = c')
    (p : Plan2 (Q E m) E U a c) : Plan2 (Q E m) E U a' c' := h1 ▸ h2 ▸ p

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma evalS_cast {U : Type*} (ans : ℕ → Fin 2 → Q E m → E) {a c a' c' : ℕ} (h1 : a = a')
    (h2 : c = c') (p : Plan2 (Q E m) E U a c) (n : ℕ) :
    evalS ans n (castPlan h1 h2 p) = evalS ans n p := by
  subst h1; subst h2; rfl

def gradsK {U : Type*} {a c : ℕ} (x : E) :
    (b : ℕ) → ((Fin b → E) → Plan2 (Q E m) E U a c) → Plan2 (Q E m) E U (a + b) c
  | 0, k => k (fun i => Fin.elim0 i)
  | b + 1, k => askG (x, none) fun g => gradsK x b (fun gs => k (Fin.cons g gs))

def projsK {U : Type*} {a c : ℕ} (x : E) :
    (n : ℕ) → (Fin n → Fin m) → ((Fin n → E) → Plan2 (Q E m) E U a c) →
      Plan2 (Q E m) E U a (c + n)
  | 0, _, k => k (fun i => Fin.elim0 i)
  | n + 1, idx, k => askP (x, some (idx 0)) fun r =>
      projsK x n (fun i => idx i.succ) (fun rs => k (Fin.cons r rs))

noncomputable def stepFrom (k : Knobs E) (s hs : E) (yz : E × E) (gs : Fin k.b → E)
    (px ps : E) : E × E :=
  let x := mix k.τ s yz.1 yz.2
  let v := (1 / (k.b : ℝ)) • ∑ i, gs i + (k.β • (x - px) - k.β • (s - ps) + hs)
  (proxBall k.μ k.x0 k.ρ (1 / (3 * k.Lt)) x v, proxBall k.μ k.x0 k.ρ k.α yz.2 v)

noncomputable def stepK {U : Type*} {a c : ℕ} (k : Knobs E) (s hs : E) (yz : E × E) (j : Fin m)
    (K : E × E → Plan2 (Q E m) E U a c) : Plan2 (Q E m) E U (a + k.b) (c + 2) :=
  gradsK (mix k.τ s yz.1 yz.2) k.b fun gs =>
    castPlan rfl (by omega) (projsK (mix k.τ s yz.1 yz.2) 1 (fun _ => j) fun px =>
      castPlan rfl rfl (projsK s 1 (fun _ => j) fun ps =>
        K (stepFrom k s hs yz gs (px 0) (ps 0))))

noncomputable def innerK {U : Type*} {a c : ℕ} (k : Knobs E) (s hs : E) :
    (n : ℕ) → (E × E) → (Fin n → Fin m) → ((E × E) × E → Plan2 (Q E m) E U a c) →
      Plan2 (Q E m) E U (a + n * k.b) (c + n * 2)
  | 0, yz, _, K => castPlan (by ring) (by ring) (K (yz, 0))
  | n + 1, yz, js, K => castPlan (by ring) (by ring) (stepK k s hs yz (js 0) fun next =>
      innerK k s hs n next (fun i => js i.succ) fun res => K (res.1, next.1 + k.θ • res.2))

noncomputable def epochK {U : Type*} {a c : ℕ} (k : Knobs E) (st : St E) (js : Fin k.M → Fin m)
    (K : St E → Plan2 (Q E m) E U a c) : Plan2 (Q E m) E U (a + k.M * k.b) (c + k.M * 2 + m) :=
  projsK st.s m id fun ps =>
    innerK k st.s ((m : ℝ)⁻¹ • ∑ i, k.β • (st.s - ps i)) k.M (st.y, st.z) js fun res =>
      K ⟨(weightSum k.θ k.M)⁻¹ • res.2, res.1.1, res.1.2⟩

noncomputable def runK {U : Type*} {a c : ℕ} (k : Knobs E) :
    (S : ℕ) → St E → (Fin S → Fin k.M → Fin m) → (St E → Plan2 (Q E m) E U a c) →
      Plan2 (Q E m) E U (a + S * (k.M * k.b)) (c + S * (k.M * 2 + m))
  | 0, st, _, K => castPlan (by ring) (by ring) (K st)
  | S + 1, st, jss, K => castPlan (by ring) (by ring) (epochK k st (jss 0) fun st' =>
      runK k S st' (fun i => jss i.succ) K)

def cleanupK {U : Type*} {a c : ℕ} :
    (Q' : ℕ) → E → (Fin Q' → Fin m) → (E → Plan2 (Q E m) E U a c) → Plan2 (Q E m) E U a (c + Q')
  | 0, p, _, K => K p
  | Q' + 1, p, js, K => askP (p, some (js 0)) fun r => cleanupK Q' r (fun i => js i.succ) K

noncomputable def fullPlan (k : Knobs E) (S Q' : ℕ)
    (seed : (Fin S → Fin k.M → Fin m) × (Fin Q' → Fin m)) :
    Plan2 (Q E m) E E (S * (k.M * k.b)) (Q' + S * (k.M * 2 + m)) :=
  castPlan (by ring) (by ring) (runK (a := 0) (c := Q') k S ⟨k.x0, k.x0, k.x0⟩ seed.1 fun st =>
    castPlan rfl (by ring) (cleanupK (a := 0) (c := 0) Q' st.s seed.2 fun p => done p))

end LongTails.Algorithms.ManyConstraintVR
