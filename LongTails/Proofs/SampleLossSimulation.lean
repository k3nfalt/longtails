import LongTails.Proofs.SampleLossEpoch
import LongTails.Proofs.SampleLossInstance
import LongTails.Proofs.Execution

open OracleTemplate LongTails.Setups.NonnegativeSmoothSampleLossEuclidean
open LongTails.Proofs.SampleLossFrame LongTails.Proofs.SampleLossScaling
open LongTails.Proofs.SampleLossEpoch LongTails.Proofs.SampleLossInstance
open LongTails.Proofs.SampleLossFrontier LongTails.Proofs.SampleLossChain

namespace LongTails.Proofs.SampleLossSimulation

abbrev Method (q : Params) := Algorithm (Domain q × Domain q) (Domain q × Domain q) (Domain q)

noncomputable def epoch (q : Params) (s : ℕ) := s/(stages q)^2

noncomputable def simulated (q : Params) (A : Method q) (seed : A.Seed) (ξ : ℕ → Index q)
    (π : Hidden q) : ℕ → A.State
  | 0 => A.initial seed
  | t+1 =>
    let state := simulated q A seed ξ π t
    let xy := (A.query state).2
    let ans := reply π (ξ t) (epoch q t) (dilation q) (amplitude q*dilation q)
    A.update state (ans xy.1, ans xy.2)

lemma epoch_lt (q : Params) (hq : spec.valid q) {s : ℕ} (hs : s < (stages q)^3) :
    epoch q s < stages q := by
  have hn := stages_pos hq
  apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < (stages q)^2)).mpr
  simpa [pow_succ, Nat.mul_comm] using hs

lemma sim_stable (q : Params) (hq : spec.valid q) (A : Method q) (seed : A.Seed) (ξ : ℕ → Index q)
    (π ρ : Hidden q) (t k : ℕ) (hk : k < stages q) (ht : ∀ s < t, epoch q s ≤ k)
    (he : ∀ l ∈ exposed ξ ((stages q)^2) k, π l = ρ l) :
    simulated q A seed ξ π t = simulated q A seed ξ ρ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hp := ih (fun s hs => ht s (by omega))
    have ht' := ht t (Nat.lt_succ_self t)
    have hn := stages_pos hq
    have hh := reply_stable π ρ ξ (show 0<(stages q)^2 by positivity) t (ht'.trans_lt hk)
      (fun l hl => he l (exposed_mono ξ _ ht' hl)) (dilation q) (amplitude q*dilation q)
    simp only [simulated, hp, epoch, hh]

abbrev Point (b : ℕ) := Option (Fin b × Bool)

noncomputable def pointStage (q : Params) {b : ℕ} : Point b → ℕ
  | none => stages q - 1
  | some (s,_) => epoch q s

noncomputable def point (q : Params) (A : Method q) (seed : A.Seed) (ξ : ℕ → Index q) (b : ℕ)
    (a : Point b) (π : Hidden q) : Domain q :=
  dilation q • match a with
  | none => A.output (simulated q A seed ξ π b)
  | some (s,u) =>
    let xy := (A.query (simulated q A seed ξ π s)).2
    if u then xy.1 else xy.2

lemma point_stable (q : Params) (hq : spec.valid q) (A : Method q) (seed : A.Seed) (ξ : ℕ → Index q)
    {b : ℕ} (hb : b ≤ (stages q)^3) (a : Point b) (π ρ : Hidden q)
    (he : ∀ l ∈ exposed ξ ((stages q)^2) (pointStage q a), π l = ρ l) :
    point q A seed ξ b a π = point q A seed ξ b a ρ := by
  cases a with
  | none =>
    have hn := stages_pos hq
    have hs := sim_stable q hq A seed ξ π ρ b (stages q - 1) (by omega)
      (fun s hs => by have := epoch_lt q hq (hs.trans_le hb); omega) he
    simp [point,hs]
  | some a =>
    obtain ⟨s,u⟩ := a
    have hs := sim_stable q hq A seed ξ π ρ s (epoch q s) (epoch_lt q hq (s.isLt.trans_le hb))
      (fun j hj => Nat.div_le_div_right hj.le) he
    simp [point,hs]

lemma sim_execute (q : Params) (hq : spec.valid q) (A : Method q) (seed : A.Seed) (ξ : ℕ → Index q)
    (π : Hidden q) (b : ℕ) (hb : b ≤ (stages q)^3)
    (small : ∀ a : Point b, ∀ j : Fin (stages q), pointStage q a ≤ j.val →
      signal proj (direction π) j (point q A seed ξ b a π) < 1/128) :
    execute (oracle q π) A (fun _ => b) seed ξ = A.output (simulated q A seed ξ π b) := by
  let response := fun t (z : Fin 1 × (Domain q × Domain q)) =>
    (gradient (loss q π (ξ t)) z.2.1, gradient (loss q π (ξ t)) z.2.2)
  erw [execute_indexed_of_answer (oracle q π) A b seed ξ response (fun _ _ => rfl)]
  let step := fun p : A.State × ℕ => (A.update p.1 (response p.2 (A.query p.1)), p.2+1)
  suffices h : ∀ t ≤ b, step^[t] (A.initial seed,0) = (simulated q A seed ξ π t,t) by rw [show
      (fun sc : A.State × ℕ => (A.update sc.1 (response sc.2 (A.query sc.1)),sc.2+1)) = step from rfl, h b le_rfl]
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    let xy := (A.query (simulated q A seed ξ π t)).2
    have ht' : t < b := by omega
    let s : Fin b := ⟨t,ht'⟩
    have he (u : Bool) : let z := if u then xy.1 else xy.2
        gradient (loss q π (ξ t)) z = reply π (ξ t) (epoch q t) (dilation q) (amplitude q*dilation q) z := by
      intro z
      rw [(loss_deriv _ _ _ _).gradient]
      apply congrArg (fun v => (amplitude q*dilation q) • v)
      apply frontier_gradient _ _ _ _ _ _ _ (epoch_lt q hq (ht'.trans_le hb)) _ (payload_signal π (ξ t) _)
      intro j hj hj'
      exact small (some (s,u)) ⟨j,hj'⟩ hj
    have h1 := he true
    have h2 := he false
    simp only [↓reduceIte, Bool.false_eq_true] at h1 h2
    change (A.update _ (gradient (loss q π (ξ t)) xy.1, gradient (loss q π (ξ t)) xy.2),_) = _
    rw [h1,h2]
    rfl

end LongTails.Proofs.SampleLossSimulation
