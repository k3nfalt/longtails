import LongTails.Template
import LongTails.Proofs.Execution
import Mathlib.Tactic

namespace LongTails.Algorithms.ManyConstraintPlan

inductive Plan2 (Q R U : Type*) : ℕ → ℕ → Type _
  | done (u : U) : Plan2 Q R U 0 0
  | askG {a c : ℕ} (q : Q) (next : R → Plan2 Q R U a c) : Plan2 Q R U (a + 1) c
  | askP {a c : ℕ} (q : Q) (next : R → Plan2 Q R U a c) : Plan2 Q R U a (c + 1)

namespace Plan2

variable {Q R U V : Type*}

def evalS (ans : ℕ → Fin 2 → Q → R) : {a c : ℕ} → ℕ → Plan2 Q R U a c → U
  | _, _, _, done u => u
  | _, _, n, askG q next => evalS ans (n + 1) (next (ans n 0 q))
  | _, _, n, askP q next => evalS ans (n + 1) (next (ans n 1 q))

def bind {a' c' : ℕ} : {a c : ℕ} → Plan2 Q R U a c → (U → Plan2 Q R V a' c') →
    Plan2 Q R V (a' + a) (c' + c)
  | _, _, done u, f => f u
  | _, _, askG q next, f => askG q (fun r => bind (next r) f)
  | _, _, askP q next, f => askP q (fun r => bind (next r) f)

def map (g : U → V) : {a c : ℕ} → Plan2 Q R U a c → Plan2 Q R V a c
  | _, _, done u => done (g u)
  | _, _, askG q next => askG q (fun r => map g (next r))
  | _, _, askP q next => askP q (fun r => map g (next r))

lemma evalS_bind (ans : ℕ → Fin 2 → Q → R) {a c a' c' : ℕ} (p : Plan2 Q R U a c)
    (f : U → Plan2 Q R V a' c') (n : ℕ) :
    evalS ans n (bind p f) = evalS ans (n + (a + c)) (f (evalS ans n p)) := by
  induction p generalizing n with
  | done u => rfl
  | askG q next ih =>
    simp only [bind, evalS]
    rw [ih]; congr 1; omega
  | askP q next ih =>
    simp only [bind, evalS]
    rw [ih]; congr 1; omega

lemma evalS_map (ans : ℕ → Fin 2 → Q → R) (g : U → V) {a c : ℕ} (p : Plan2 Q R U a c) (n : ℕ) :
    evalS ans n (map g p) = g (evalS ans n p) := by
  induction p generalizing n with
  | done u => rfl
  | askG q next ih => exact ih _ _
  | askP q next ih => exact ih _ _

abbrev PState (Q R U : Type*) := Σ ac : ℕ × ℕ, Plan2 Q R U ac.1 ac.2

def queryP (fallback : Q) : {a c : ℕ} → Plan2 Q R U a c → Fin 2 × Q
  | _, _, done _ => (0, fallback)
  | _, _, askG q _ => (0, q)
  | _, _, askP q _ => (1, q)

def updateP : {a c : ℕ} → Plan2 Q R U a c → R → PState Q R U
  | _, _, done u, _ => ⟨(0, 0), done u⟩
  | a + 1, c, askG _ next, r => ⟨(a, c), next r⟩
  | a, c + 1, askP _ next, r => ⟨(a, c), next r⟩

def outputP (fallback : U) : {a c : ℕ} → Plan2 Q R U a c → U
  | _, _, done u => u
  | _, _, askG _ _ => fallback
  | _, _, askP _ _ => fallback

def query (fallback : Q) (s : PState Q R U) : Fin 2 × Q := queryP fallback s.2

def update (s : PState Q R U) (r : R) : PState Q R U := updateP s.2 r

def output (fallback : U) (s : PState Q R U) : U := outputP fallback s.2

noncomputable def algorithm {S : Type} [MeasurableSpace S]
    (law : MeasureTheory.ProbabilityMeasure S) (q0 : Q) (u0 : U) (a c : ℕ)
    (plan : S → Plan2 Q R U a c) : OracleTemplate.Algorithm Q R U 2 where
  Seed := S
  law := law
  State := PState Q R U
  initial seed := ⟨(a, c), plan seed⟩
  query := query q0
  update := update
  output := output u0

def stateFrom (q0 : Q) (ans : ℕ → Fin 2 → Q → R) : ℕ → PState Q R U → ℕ → PState Q R U
  | _, s, 0 => s
  | n, s, k + 1 => stateFrom q0 ans (n + 1)
      (update s (ans n (query q0 s).1 (query q0 s).2)) k

lemma stateFrom_succ (q0 : Q) (ans : ℕ → Fin 2 → Q → R) :
    ∀ (k n : ℕ) (s : PState Q R U), stateFrom q0 ans n s (k + 1) =
      update (stateFrom q0 ans n s k) (ans (n + k) (query q0 (stateFrom q0 ans n s k)).1
        (query q0 (stateFrom q0 ans n s k)).2) := by
  intro k
  induction k with
  | zero => intro n s; rfl
  | succ k ih =>
    intro n s
    rw [stateFrom, ih (n + 1)]
    simp only [stateFrom]
    congr 2; simp only [Nat.add_assoc, Nat.add_comm 1 k]

lemma stateFrom_done (q0 : Q) (ans : ℕ → Fin 2 → Q → R) (u : U) :
    ∀ (k n : ℕ), stateFrom q0 ans n (⟨(0, 0), done u⟩ : PState Q R U) k = ⟨(0, 0), done u⟩ := by
  intro k
  induction k with
  | zero => intro n; rfl
  | succ k ih => intro n; simp only [stateFrom]; exact ih _

lemma stateFrom_finish (q0 : Q) (ans : ℕ → Fin 2 → Q → R) {a c : ℕ} (p : Plan2 Q R U a c) :
    ∀ n, stateFrom q0 ans n (⟨(a, c), p⟩ : PState Q R U) (a + c) =
      ⟨(0, 0), done (evalS ans n p)⟩ := by
  induction p with
  | done u => intro n; rfl
  | @askG a c q next ih =>
    intro n
    rw [show a + 1 + c = (a + c) + 1 by omega]
    simp only [stateFrom]
    exact ih _ _
  | @askP a c q next ih =>
    intro n
    rw [show a + (c + 1) = (a + c) + 1 by omega]
    simp only [stateFrom]
    exact ih _ _

lemma stateFrom_counts (q0 : Q) (ans : ℕ → Fin 2 → Q → R) {a c : ℕ} (p : Plan2 Q R U a c) :
    ∀ (n k : ℕ), k ≤ a + c →
      (stateFrom q0 ans n (⟨(a, c), p⟩ : PState Q R U) k).1.1 +
        (stateFrom q0 ans n (⟨(a, c), p⟩ : PState Q R U) k).1.2 + k = a + c ∧
      (stateFrom q0 ans n (⟨(a, c), p⟩ : PState Q R U) k).1.1 ≤ a ∧
      (stateFrom q0 ans n (⟨(a, c), p⟩ : PState Q R U) k).1.2 ≤ c := by
  induction p with
  | done u => intro n k hk; simp at hk; subst hk; simp [stateFrom]
  | @askG a c q next ih =>
    intro n k hk
    cases k with
    | zero => simp [stateFrom]
    | succ k =>
      simp only [stateFrom, update, updateP]
      obtain ⟨h1, h2, h3⟩ := ih _ (n + 1) k (by omega)
      exact ⟨by omega, by omega, h3⟩
  | @askP a c q next ih =>
    intro n k hk
    cases k with
    | zero => simp [stateFrom]
    | succ k =>
      simp only [stateFrom, update, updateP]
      obtain ⟨h1, h2, h3⟩ := ih _ (n + 1) k (by omega)
      exact ⟨by omega, h2, by omega⟩

lemma step_counts (q0 : Q) {s : PState Q R U} (hs : 0 < s.1.1 + s.1.2) (r : R) :
    ((query q0 s).1 = 0 ∧ 0 < s.1.1 ∧ (update s r).1 = (s.1.1 - 1, s.1.2)) ∨
    ((query q0 s).1 = 1 ∧ 0 < s.1.2 ∧ (update s r).1 = (s.1.1, s.1.2 - 1)) := by
  obtain ⟨⟨a, c⟩, p⟩ := s
  cases p with
  | done u => simp at hs
  | askG q next => left; simp [query, queryP, update, updateP]
  | askP q next => right; simp [query, queryP, update, updateP]

lemma stateFrom_add (q0 : Q) (ans : ℕ → Fin 2 → Q → R) :
    ∀ (k j n : ℕ) (s : PState Q R U),
      stateFrom q0 ans n s (k + j) = stateFrom q0 ans (n + k) (stateFrom q0 ans n s k) j := by
  intro k
  induction k with
  | zero => intro j n s; simp [stateFrom]
  | succ k ih =>
    intro j n s
    rw [show k + 1 + j = (k + j) + 1 by omega]
    simp only [stateFrom]
    rw [ih j (n + 1)]
    congr 1; omega

lemma execute_plan {S : Type} [MeasurableSpace S] (law : MeasureTheory.ProbabilityMeasure S)
    (q0 : Q) (u0 : U) (a c : ℕ) (plan : S → Plan2 Q R U a c)
    (O : OracleTemplate.Oracle Q R 2) (budget : Fin 2 → ℕ) (hb0 : a ≤ budget 0)
    (hb1 : c ≤ budget 1) (seed : S) (ξ : (k : ℕ) → O.Seed k)
    (response : ℕ → Fin 2 × Q → R)
    (h : ∀ history query, O.answer history query (ξ history.length) =
      response history.length query) :
    OracleTemplate.execute O (algorithm law q0 u0 a c plan) budget seed ξ =
      evalS (fun n i q => response n (i, q)) 0 (plan seed) := by
  set ans : ℕ → Fin 2 → Q → R := fun n i q => response n (i, q)
  set s0 : PState Q R U := ⟨(a, c), plan seed⟩
  set state : ℕ → PState Q R U := fun k => stateFrom q0 ans 0 s0 k
  let rem : ℕ → Fin 2 → ℕ := fun k => Nat.rec budget (fun k r => Function.update r
    (query q0 (state k)).1 (r (query q0 (state k)).1 - 1)) k
  have hcount : ∀ k, k ≤ a + c → (state k).1.1 + (state k).1.2 + k = a + c ∧
      (state k).1.1 ≤ a ∧ (state k).1.2 ≤ c := stateFrom_counts q0 ans (plan seed) 0
  have hinv : ∀ k, k ≤ a + c → rem k 0 = budget 0 - (a - (state k).1.1) ∧
      rem k 1 = budget 1 - (c - (state k).1.2) := by
    intro k
    induction k with
    | zero => intro _; simp [rem, state, s0, stateFrom]
    | succ k ih =>
      intro hk
      obtain ⟨i0, i1⟩ := ih (by omega)
      obtain ⟨hs, ha, hc⟩ := hcount k (by omega)
      have hpos : 0 < (state k).1.1 + (state k).1.2 := by omega
      have hnext : state (k + 1) = update (state k) (ans k (query q0 (state k)).1
          (query q0 (state k)).2) := by
        simp only [state]; rw [stateFrom_succ]; simp
      rcases step_counts q0 hpos (ans k (query q0 (state k)).1 (query q0 (state k)).2) with
        ⟨hq, hp, hu⟩ | ⟨hq, hp, hu⟩
      · have : rem (k + 1) = Function.update (rem k) 0 (rem k 0 - 1) := by
          simp only [rem]; rw [hq]
        rw [this, hnext, hu]
        simp only [Function.update_self, ne_eq, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one,
          not_false_eq_true, Function.update_of_ne]
        constructor <;> omega
      · have : rem (k + 1) = Function.update (rem k) 1 (rem k 1 - 1) := by
          simp only [rem]; rw [hq]
        rw [this, hnext, hu]
        simp only [Function.update_self, ne_eq, zero_ne_one, not_false_eq_true,
          Function.update_of_ne]
        constructor <;> omega
  apply OracleTemplate.execute_eq_of_safe_prefix O (algorithm law q0 u0 a c plan) budget seed ξ
    state rem (a + c) (evalS ans 0 (plan seed))
  · rfl
  · intro history
    change stateFrom q0 ans 0 s0 (history.length + 1) = _
    rw [stateFrom_succ, h]
    simp only [zero_add, ans]
    rfl
  · rfl
  · intro k; rfl
  · intro k hk
    obtain ⟨i0, i1⟩ := hinv k hk.le
    obtain ⟨hs, ha, hc⟩ := hcount k hk.le
    have hpos : 0 < (state k).1.1 + (state k).1.2 := by omega
    change 0 < rem k (query q0 (state k)).1
    rcases step_counts q0 hpos (ans k 0 q0) with ⟨hq, hp, _⟩ | ⟨hq, hp, _⟩
    · rw [hq, i0]; omega
    · rw [hq, i1]; omega
  · intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    change output u0 (stateFrom q0 ans 0 s0 (a + c + j)) = _
    rw [stateFrom_add, stateFrom_finish, stateFrom_done]
    rfl
  · simp only [Fin.sum_univ_two]; omega

end Plan2

end LongTails.Algorithms.ManyConstraintPlan
