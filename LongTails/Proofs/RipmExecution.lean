import Mathlib.Tactic
import LongTails.Setups.RipmGeneral
import LongTails.Algorithms.RipmOutput
import Mathlib.Data.List.Count

open private OracleTemplate._run from LongTails.Template

open LongTails.Setups.RipmGeneral
open LongTails.Algorithms.RipmOutput

namespace LongTails.Proofs.RipmExecution

noncomputable section

lemma execute_correspondence (p : Core.Public) (I : Core.Problem p.d p.m)
    (O : OracleTemplate.Oracle (ℝ × Core.Vec p.d) (Core.Vec p.d) 2)
    (decodeI : (k : ℕ) → O.Seed k → I.Sample)
    (decodeJ : (k : ℕ) → O.Seed k → Fin p.m)
    (hO : Core.OracleExact I O decodeI decodeJ) (heta : 0 < p.eta) (hm : 0 < p.m)
    (T : ℕ) (seed : (method p).Seed) (omega : (k : ℕ) → O.Seed k) :
    OracleTemplate.execute O (method p) (fun _ => T + 1) seed omega =
      lastIterate I p.eta p.x0
        (fun t path => decodeI (2 * t) (path (2 * t)))
        (fun t path => decodeJ (2 * t + 1) (path (2 * t + 1))) T omega := by
  let A := method p
  let H := List ((Fin 2 × (ℝ × Core.Vec p.d)) × Core.Vec p.d)
  let answer : H → (Fin 2 × (ℝ × Core.Vec p.d)) → Core.Vec p.d :=
    fun history query => O.answer history query (omega history.length)
  have hstep (n : ℕ) (history : H) (remaining : Fin 2 → ℕ) (s : A.State) :
      OracleTemplate._run answer A (n + 1) history remaining s =
        if remaining (A.query s).1 = 0 then (A.output s, history)
        else OracleTemplate._run answer A n
          (history ++ [(A.query s, answer history (A.query s))])
          (Function.update remaining (A.query s).1 (remaining (A.query s).1 - 1))
          (A.update s (answer history (A.query s))) := rfl
  have hpair (n : ℕ) (history : H) (y : Core.Vec p.d) :
      let g := answer history (0, (0, y))
      let history1 := history ++ [((0, (0, y)), g)]
      let work := y - p.eta • g
      let reply := answer history1 (1, (p.eta * p.m, work))
      OracleTemplate._run answer A (2 * (n + 1)) history (fun _ => n + 1)
          (⟨y, y, false⟩ : Core.State p.d) =
        OracleTemplate._run answer A (2 * n)
          (history1 ++ [((1, (p.eta * p.m, work)), reply)]) (fun _ => n)
          (⟨reply, reply, false⟩ : Core.State p.d) := by
    let g := answer history (0, (0, y))
    let history1 := history ++ [((0, (0, y)), g)]
    let work := y - p.eta • g
    let reply := answer history1 (1, (p.eta * p.m, work))
    change OracleTemplate._run answer A (2 * (n + 1)) history (fun _ => n + 1)
        (⟨y, y, false⟩ : Core.State p.d) =
      OracleTemplate._run answer A (2 * n)
        (history1 ++ [((1, (p.eta * p.m, work)), reply)]) (fun _ => n)
        (⟨reply, reply, false⟩ : Core.State p.d)
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
    erw [hstep]
    change (if n + 1 = 0 then (y, history)
      else OracleTemplate._run answer A (2 * n + 1) history1
        (Function.update (fun _ : Fin 2 => n + 1) 0 n)
        (⟨y, work, true⟩ : Core.State p.d)) = _
    rw [ite_eq_right (show n + 1 ≠ 0 by omega)]
    erw [hstep]
    change (if n + 1 = 0 then (y, history1)
      else OracleTemplate._run answer A (2 * n)
        (history1 ++ [((1, (p.eta * p.m, work)), reply)])
        (Function.update (Function.update (fun _ : Fin 2 => n + 1) 0 n) 1 n)
        (⟨reply, reply, false⟩ : Core.State p.d)) = _
    rw [ite_eq_right (show n + 1 ≠ 0 by omega)]
    have hremaining : Function.update (Function.update (fun _ : Fin 2 => n + 1) 0 n) 1 n =
        (fun _ : Fin 2 => n) := by
      funext i
      fin_cases i <;> rfl
    erw [hremaining]
  let X : ℕ → Core.Vec p.d := fun t => Core.trajectory I p.eta p.x0
    (fun t path => decodeI (2 * t) (path (2 * t)))
    (fun t path => decodeJ (2 * t + 1) (path (2 * t + 1))) t omega
  have hscale : 0 < p.eta * (p.m : ℝ) := mul_pos heta (by exact_mod_cast hm)
  have hgrad (t : ℕ) (history : H) (hlen : history.length = 2 * t) :
      answer history (0, (0, X t)) = I.grad (decodeI (2 * t) (omega (2 * t))) (X t) := by
    have he := (hO.2 history (0, (0, X t)) (omega history.length)).1 rfl
    have hd := congrArg (fun k : ℕ => decodeI k (omega k)) hlen
    exact he.trans (congrArg (fun sample => I.grad sample (X t)) hd)
  have hprox (t : ℕ) (history : H) (hlen : history.length = 2 * t + 1)
      (work : Core.Vec p.d) :
      answer history (1, (p.eta * p.m, work)) =
        Core.prox (I.regularizers (decodeJ (2 * t + 1) (omega (2 * t + 1))))
          (p.eta * p.m) work := by
    have he := (hO.2 history (1, (p.eta * p.m, work)) (omega history.length)).2 rfl hscale
    have hd := congrArg (fun k : ℕ => decodeJ k (omega k)) hlen
    exact he.trans (congrArg (fun sample => Core.prox (I.regularizers sample)
      (p.eta * p.m) work) hd)
  have hX (t : ℕ) : X (t + 1) =
      Core.prox (I.regularizers (decodeJ (2 * t + 1) (omega (2 * t + 1)))) (p.eta * p.m)
        (X t - p.eta • I.grad (decodeI (2 * t) (omega (2 * t))) (X t)) := rfl
  have hloop : ∀ n t : ℕ, ∀ history : H, history.length = 2 * t →
      (OracleTemplate._run answer A (2 * n) history (fun _ => n)
        (⟨X t, X t, false⟩ : Core.State p.d)).1 = X (t + n) := by
    intro n
    induction n with
    | zero =>
        intro t history hlen
        rfl
    | succ n ih =>
        intro t history hlen
        let g := answer history (0, (0, X t))
        let history1 := history ++ [((0, (0, X t)), g)]
        let work := X t - p.eta • g
        let reply := answer history1 (1, (p.eta * p.m, work))
        let history2 := history1 ++ [((1, (p.eta * p.m, work)), reply)]
        have hlen1 : history1.length = 2 * t + 1 := by
          dsimp only [history1]
          rw [List.length_append, List.length_singleton, hlen]
        have hlen2 : history2.length = 2 * (t + 1) := by
          dsimp only [history2]
          rw [List.length_append, List.length_singleton, hlen1]
          omega
        have hg : g = I.grad (decodeI (2 * t) (omega (2 * t))) (X t) := hgrad t history hlen
        have hreply : reply = X (t + 1) := by
          change answer history1 (1, (p.eta * p.m, work)) = X (t + 1)
          rw [hprox t history1 hlen1 work, hX t]
          dsimp only [work]
          rw [hg]
        have hp := hpair n history (X t)
        change (OracleTemplate._run answer A (2 * (n + 1)) history (fun _ => n + 1)
          (⟨X t, X t, false⟩ : Core.State p.d)).1 = X (t + (n + 1))
        rw [hp]
        change (OracleTemplate._run answer A (2 * n) history2 (fun _ => n)
          (⟨reply, reply, false⟩ : Core.State p.d)).1 = X (t + (n + 1))
        rw [hreply, show t + (n + 1) = (t + 1) + n by omega]
        exact ih (t + 1) history2 hlen2
  have hbudget : (∑ _i : Fin 2, (T + 1)) = 2 * (T + 1) := by
    rw [Fin.sum_univ_two]
    omega
  delta OracleTemplate.execute OracleTemplate.executeWithTrace
  change (OracleTemplate._run answer A (∑ _i : Fin 2, (T + 1)) [] (fun _ => T + 1)
    (⟨X 0, X 0, false⟩ : Core.State p.d)).1 = X (T + 1)
  rw [hbudget]
  simpa only [Nat.zero_add] using hloop (T + 1) 0 [] rfl

lemma trace_cost (p : Core.Public)
    (O : OracleTemplate.Oracle (ℝ × Core.Vec p.d) (Core.Vec p.d) 2)
    (T : ℕ) (seed : (method p).Seed) (omega : (k : ℕ) → O.Seed k) (q : Fin 2) :
    ((OracleTemplate.executeWithTrace O (method p) (fun _ => T + 1) seed omega).2.countP
      (fun entry => entry.1.1 == q)) = T + 1 := by
  let A := method p
  let H := List ((Fin 2 × (ℝ × Core.Vec p.d)) × Core.Vec p.d)
  let answer : H → (Fin 2 × (ℝ × Core.Vec p.d)) → Core.Vec p.d :=
    fun history query => O.answer history query (omega history.length)
  have hstep (n : ℕ) (history : H) (remaining : Fin 2 → ℕ) (s : A.State) :
      OracleTemplate._run answer A (n + 1) history remaining s =
        if remaining (A.query s).1 = 0 then (A.output s, history)
        else OracleTemplate._run answer A n
          (history ++ [(A.query s, answer history (A.query s))])
          (Function.update remaining (A.query s).1 (remaining (A.query s).1 - 1))
          (A.update s (answer history (A.query s))) := rfl
  have hpair (n : ℕ) (history : H) (y : Core.Vec p.d) :
      let g := answer history (0, (0, y))
      let history1 := history ++ [((0, (0, y)), g)]
      let work := y - p.eta • g
      let reply := answer history1 (1, (p.eta * p.m, work))
      OracleTemplate._run answer A (2 * (n + 1)) history (fun _ => n + 1)
          (⟨y, y, false⟩ : Core.State p.d) =
        OracleTemplate._run answer A (2 * n)
          (history1 ++ [((1, (p.eta * p.m, work)), reply)]) (fun _ => n)
          (⟨reply, reply, false⟩ : Core.State p.d) := by
    let g := answer history (0, (0, y))
    let history1 := history ++ [((0, (0, y)), g)]
    let work := y - p.eta • g
    let reply := answer history1 (1, (p.eta * p.m, work))
    change OracleTemplate._run answer A (2 * (n + 1)) history (fun _ => n + 1)
        (⟨y, y, false⟩ : Core.State p.d) =
      OracleTemplate._run answer A (2 * n)
        (history1 ++ [((1, (p.eta * p.m, work)), reply)]) (fun _ => n)
        (⟨reply, reply, false⟩ : Core.State p.d)
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
    erw [hstep]
    change (if n + 1 = 0 then (y, history)
      else OracleTemplate._run answer A (2 * n + 1) history1
        (Function.update (fun _ : Fin 2 => n + 1) 0 n)
        (⟨y, work, true⟩ : Core.State p.d)) = _
    rw [ite_eq_right (show n + 1 ≠ 0 by omega)]
    erw [hstep]
    change (if n + 1 = 0 then (y, history1)
      else OracleTemplate._run answer A (2 * n)
        (history1 ++ [((1, (p.eta * p.m, work)), reply)])
        (Function.update (Function.update (fun _ : Fin 2 => n + 1) 0 n) 1 n)
        (⟨reply, reply, false⟩ : Core.State p.d)) = _
    rw [ite_eq_right (show n + 1 ≠ 0 by omega)]
    have hremaining : Function.update (Function.update (fun _ : Fin 2 => n + 1) 0 n) 1 n =
        (fun _ : Fin 2 => n) := by
      funext i
      fin_cases i <;> rfl
    erw [hremaining]
  have hcount : ∀ n : ℕ, ∀ history : H, ∀ y : Core.Vec p.d, ∀ q : Fin 2,
      ((OracleTemplate._run answer A (2 * n) history (fun _ => n)
        (⟨y, y, false⟩ : Core.State p.d)).2.countP (fun entry => entry.1.1 == q)) =
        history.countP (fun entry => entry.1.1 == q) + n := by
    intro n
    induction n with
    | zero =>
        intro history y q
        change history.countP (fun entry => entry.1.1 == q) =
          history.countP (fun entry => entry.1.1 == q) + 0
        omega
    | succ n ih =>
        intro history y q
        let g := answer history (0, (0, y))
        let history1 := history ++ [((0, (0, y)), g)]
        let work := y - p.eta • g
        let reply := answer history1 (1, (p.eta * p.m, work))
        let history2 := history1 ++ [((1, (p.eta * p.m, work)), reply)]
        have hadded : ([((0, (0, y)), g)] : H).countP (fun entry => entry.1.1 == q) +
            ([((1, (p.eta * p.m, work)), reply)] : H).countP (fun entry => entry.1.1 == q) = 1 := by
          fin_cases q <;> rfl
        have hcounts : history2.countP (fun entry => entry.1.1 == q) =
            history.countP (fun entry => entry.1.1 == q) + 1 := by
          dsimp only [history2, history1]
          erw [List.countP_append, List.countP_append]
          omega
        erw [hpair, ih]
        change history2.countP (fun entry => entry.1.1 == q) + n =
          history.countP (fun entry => entry.1.1 == q) + (n + 1)
        rw [hcounts]
        omega
  have hbudget : (∑ _i : Fin 2, (T + 1)) = 2 * (T + 1) := by
    rw [Fin.sum_univ_two]
    omega
  delta OracleTemplate.executeWithTrace
  change ((OracleTemplate._run answer A (∑ _i : Fin 2, (T + 1)) []
    (fun _ => T + 1) (⟨p.x0, p.x0, false⟩ : Core.State p.d)).2.countP
      (fun entry => entry.1.1 == q)) = T + 1
  rw [hbudget]
  simpa using hcount (T + 1) [] p.x0 q

end

end LongTails.Proofs.RipmExecution
