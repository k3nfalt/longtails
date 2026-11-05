import LongTails.Algorithms.FiniteSumNondual
import LongTails.Proofs.FiniteSumNondualProxEpoch
import LongTails.Proofs.FiniteSumNondualProxFeasibility

open Classical
open scoped BigOperators

namespace LongTails.Proofs.FiniteSumNondualSampling

open LongTails.Algorithms.FiniteSumNondual
open OracleTemplate.ComponentEnvelope (Program)
open FiniteSumNondualProxEpoch (expect_fin_succ)
open FiniteSumNondualProxFeasibility

variable {Q Reply U Sample BaseQ BaseReply : Type*}

def Within : ℕ → Program Q Reply U → Prop
  | _, .done _ => True
  | 0, .ask _ _ => False
  | fuel + 1, .ask _ next => ∀ reply, Within fuel (next reply)

lemma guardedPlan_eval (solver : Q → Sample → Program BaseQ BaseReply Reply)
    (accept : Q → Reply → Prop) (fallback : U) (g : BaseQ → BaseReply)
    (fuel : ℕ) (program : Program Q Reply U) (seed : Fin fuel → Sample) :
    Program.eval g (guardedPlan solver accept fallback fuel program seed) =
      (guardedResult (fun q sample => Program.eval g (solver q sample)) accept fuel program seed).getD fallback := by
  induction fuel generalizing program with
  | zero => cases program <;> rfl
  | succ fuel ih =>
    cases program with
    | done u => rfl
    | ask q next =>
      simp only [guardedPlan, Program.eval_bind, guardedResult]
      split_ifs <;> simp only [ih, Program.eval, Option.getD_none]

lemma guardedPlan_cost (solver : Q → Sample → Program BaseQ BaseReply Reply)
    (accept : Q → Reply → Prop) (fallback : U) (g : BaseQ → BaseReply)
    (C : ℕ) (hc : ∀ q sample, Program.cost g (solver q sample) ≤ C)
    (fuel : ℕ) (program : Program Q Reply U) (seed : Fin fuel → Sample) :
    Program.cost g (guardedPlan solver accept fallback fuel program seed) ≤ fuel * C := by
  induction fuel generalizing program with
  | zero => cases program <;> simp [guardedPlan, Program.cost]
  | succ fuel ih =>
    cases program with
    | done u => simp [guardedPlan, Program.cost]
    | ask q next =>
      simp only [guardedPlan, Program.cost_bind]
      split_ifs
      · have hh := ih (next (Program.eval g (solver q (seed 0)))) (fun j => seed j.succ)
        have hs := hc q (seed 0)
        nlinarith
      · simp only [Program.cost]
        have hs := hc q (seed 0)
        nlinarith

lemma failure_fraction [Fintype Sample] [Nonempty Sample]
    (solver : Q → Sample → Reply) (accept : Q → Reply → Prop) {q : ℝ} (hq : 0 ≤ q)
    (hfail : ∀ query, (𝔼 sample, if accept query (solver query sample) then (0 : ℝ) else 1) ≤ q)
    (fuel : ℕ) (program : Program Q Reply U) (hwithin : Within fuel program) :
    (𝔼 seed : Fin fuel → Sample,
      if guardedResult solver accept fuel program seed = none then (1 : ℝ) else 0) ≤ (fuel : ℝ) * q := by
  induction fuel generalizing program with
  | zero =>
    cases program with
    | done u => simp [guardedResult]
    | ask query next => exact False.elim hwithin
  | succ fuel ih =>
    cases program with
    | done u => simp only [guardedResult, reduceCtorEq, ite_false, Fintype.expect_const]; positivity
    | ask query next =>
      rw [expect_fin_succ]
      simp only [guardedResult, Fin.cons_zero, Fin.cons_succ]
      have hp (sample : Sample) :
          (𝔼 tail : Fin fuel → Sample,
            if (if accept query (solver query sample) then
              guardedResult solver accept fuel (next (solver query sample)) tail else none) = none
            then (1 : ℝ) else 0) ≤
          (if accept query (solver query sample) then (0 : ℝ) else 1) + (fuel : ℝ) * q := by
        by_cases ha : accept query (solver query sample)
        · simpa only [ha, ite_true, zero_add] using ih _ (hwithin (solver query sample))
        · simp only [ha, ite_false, ite_true, Fintype.expect_const]
          linarith [mul_nonneg (Nat.cast_nonneg fuel) hq]
      have hh := Finset.expect_le_expect (s := Finset.univ) (fun sample _ => hp sample)
      simp only [Finset.expect_add_distrib, Fintype.expect_const] at hh
      have hf := hfail query
      push_cast
      linarith

def Contract (good : Q → Reply → Prop) (post : U → Prop) : Program Q Reply U → Prop
  | .done u => post u
  | .ask q next => ∀ reply, good q reply → Contract good post (next reply)

lemma guardedResult_correct (solver : Q → Sample → Reply) (accept good : Q → Reply → Prop)
    (post : U → Prop) (hs : ∀ query sample, accept query (solver query sample) → good query (solver query sample))
    (fuel : ℕ) (program : Program Q Reply U) (hc : Contract good post program)
    (seed : Fin fuel → Sample) (u : U) (hu : guardedResult solver accept fuel program seed = some u) :
    post u := by
  induction fuel generalizing program with
  | zero =>
    cases program with
    | done v => cases Option.some.inj hu; exact hc
    | ask query next => cases hu
  | succ fuel ih =>
    cases program with
    | done v => cases Option.some.inj hu; exact hc
    | ask query next =>
      simp only [guardedResult] at hu
      split_ifs at hu with ha
      exact ih _ (hc _ (hs query (seed 0) ha)) _ hu

lemma guardedPlan_checked (solver : Q → Sample → Program BaseQ BaseReply Reply)
    (accept : Q → Reply → Prop) (fallback : U) (pq : BaseQ → Prop) (pu : U → Prop)
    (hs : ∀ query sample, Checked pq (fun _ => True) (solver query sample))
    (hf : pu fallback) (fuel : ℕ) (program : Program Q Reply U)
    (hp : Checked (fun _ => True) pu program) (seed : Fin fuel → Sample) :
    Checked pq pu (guardedPlan solver accept fallback fuel program seed) := by
  induction fuel generalizing program with
  | zero => cases program with
    | done u => exact hp
    | ask query next => exact hf
  | succ fuel ih =>
    cases program with
    | done u => exact hp
    | ask query next =>
      apply checked_bind (hs query (seed 0))
      intro reply _
      split_ifs
      · exact ih _ (hp.2 reply) _
      · exact hf

lemma expected_loss [Fintype Sample] [Nonempty Sample]
    (solver : Q → Sample → Reply) (accept good : Q → Reply → Prop)
    (loss : U → ℝ) (fallback : U) {a b q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q)
    (hfb : loss fallback ≤ b)
    (hs : ∀ query sample, accept query (solver query sample) → good query (solver query sample))
    (hfail : ∀ query, (𝔼 sample, if accept query (solver query sample) then (0 : ℝ) else 1) ≤ q)
    (fuel : ℕ) (program : Program Q Reply U) (hwithin : Within fuel program)
    (hc : Contract good (fun u => loss u ≤ a) program) :
    (𝔼 seed : Fin fuel → Sample,
      loss ((guardedResult solver accept fuel program seed).getD fallback)) ≤ a + b * (fuel : ℝ) * q := by
  have hp (seed : Fin fuel → Sample) :
      loss ((guardedResult solver accept fuel program seed).getD fallback) ≤
        a + b * (if guardedResult solver accept fuel program seed = none then (1 : ℝ) else 0) := by
    cases he : guardedResult solver accept fuel program seed with
    | none => simpa only [Option.getD_none, ite_true, mul_one] using hfb.trans (by linarith)
    | some u =>
      simp only [Option.getD_some, reduceCtorEq, ite_false, mul_zero, add_zero]
      exact guardedResult_correct solver accept good _ hs fuel program hc seed u he
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun seed _ => hp seed)
  simp only [Finset.expect_add_distrib, Fintype.expect_const, ← Finset.mul_expect] at hh
  have hf := mul_le_mul_of_nonneg_left (failure_fraction solver accept hq hfail fuel program hwithin) hb
  nlinarith

lemma contract_mono {good : Q → Reply → Prop} {post post' : U → Prop}
    {program : Program Q Reply U} (hc : Contract good post program)
    (hp : ∀ u, post u → post' u) : Contract good post' program := by
  induction program with
  | done u => exact hp u hc
  | ask query next ih => exact fun reply hr => ih reply (hc reply hr)

lemma contract_bind {V : Type*} {good : Q → Reply → Prop} {pu : U → Prop} {pv : V → Prop}
    {program : Program Q Reply U} (hc : Contract good pu program) (next : U → Program Q Reply V)
    (hn : ∀ u, pu u → Contract good pv (next u)) : Contract good pv (program.bind next) := by
  induction program with
  | done u => exact hn u hc
  | ask query rest ih => exact fun reply hr => ih reply (hc reply hr)

lemma within_mono {m n : ℕ} {program : Program Q Reply U} (hm : Within m program) (hmn : m ≤ n) :
    Within n program := by
  induction m generalizing n program with
  | zero => cases program with
    | done u => simp [Within]
    | ask query next => exact False.elim hm
  | succ m ih =>
    cases program with
    | done u => simp [Within]
    | ask query next =>
      cases n with
      | zero => omega
      | succ n => exact fun reply => ih (hm reply) (by omega)

lemma within_bind {V : Type*} {m n : ℕ} {program : Program Q Reply U} (hm : Within m program)
    (next : U → Program Q Reply V) (hn : ∀ u, Within n (next u)) :
    Within (m + n) (program.bind next) := by
  induction m generalizing program with
  | zero => cases program with
    | done u => simpa only [Nat.zero_add, Program.bind] using hn u
    | ask query rest => exact False.elim hm
  | succ m ih =>
    cases program with
    | done u => exact within_mono (hn u) (by omega)
    | ask query rest =>
      rw [Nat.succ_add]
      exact fun reply => ih (hm reply)

end LongTails.Proofs.FiniteSumNondualSampling
