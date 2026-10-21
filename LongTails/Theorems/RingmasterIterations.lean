import LongTails.Setups.RingmasterIterations
import LongTails.Proofs.RingmasterExecution
import LongTails.Proofs.RennalaConvergence

open MeasureTheory

namespace OracleTemplate.RingmasterIterations

open Rennala RingmasterAsgd

noncomputable def budget : (let S := LongTails.Setups.RingmasterIterations.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => p.K

theorem result : Convergence LongTails.Setups.RingmasterIterations.spec budget := by
  classical
  refine ⟨RingmasterAsgd.ringmaster, ?_, fun p _ => rfl⟩
  intro p hp I O hO
  obtain ⟨hf, Ω, m, μ, P, g, arrive, hiid, ho, rfl⟩ := hO
  let := m
  obtain ⟨hL, hsig, heps, hR1, hK⟩ := hp
  let q := LongTails.Setups.RingmasterIterations.publicInput p
  let event : ℕ → (Fin q.n → ℝ) → Option (Fin q.n × ℝ) := fun k _ => some (arrive k, 0)
  let ans : ℕ → Query q → Ω → Reply q := fun k qq b =>
    Option.elim qq none (fun r => some (arrive k, 0, g (r.1 (arrive k)) b))
  have hev : ∀ k < q.K, event k (timing q.R event k).starts ≠ none := fun k _ => Option.some_ne_none _
  let a : ℕ → ℕ := fun k => if k < q.K then delays q.R event k else k
  have hab := delays_bound q.R hR1 event q.K hev
  have hexe (j : Fin (q.K + 1)) (ω : ℕ → Ω) :
      execute (arrivalOracle q arrive P g) (ringmaster q) (budget p) j ω =
        (delayedIterate g q.gamma a q.x0 ω j.val, (timing q.R event q.K).clock) := by
    have hadv := advance_ringmaster q hR1 g event ans (fun _ _ _ _ => rfl) hev j ω q.K le_rfl
    erw [StochasticGradient.execute_advance]
    change (ringmaster q).output (StochasticGradient.advance (fun c s => (ringmaster q).update s
      (ans c ((ringmaster q).query s).2 (ω c))) q.K 0 ((ringmaster q).initial j)) = _
    rw [hadv]
    exact Prod.ext (ite_eq_left (show j.val ≤ q.K by omega)) rfl
  let x : Fin (q.K + 1) → (ℕ → Ω) → Point p.d := fun j ω => delayedIterate g q.gamma a q.x0 ω j.val
  have hm (j : Fin (q.K + 1)) : Measurable (x j) :=
    (iterate_moments I.f g μ P (fun k ω => ω k) p.L p.sigma q.gamma q.x0 a hL hf.hasGradient
      hf.lipschitz ho hiid (fun k => (hab k).1) j.val).1
  have hi (j : Fin (q.K + 1)) : Integrable (fun ω => ‖gradient I.f (x j ω)‖ ^ 2) (P : Measure _) :=
    (iterate_moments I.f g μ P (fun k ω => ω k) p.L p.sigma q.gamma q.x0 a hL hf.hasGradient
      hf.lipschitz ho hiid (fun k => (hab k).1) j.val).2.2.1
  have hgap : I.f p.x0 - I.lower = p.Delta := hf.gap
  have hacc := iteration_accuracy I.f g μ P (fun k ω => ω k) p.L p.sigma p.eps I.lower p.x0 a p.R p.K
    hL hsig heps hf.hasGradient hf.lipschitz hf.lower ho hiid (fun k => (hab k).1) (fun k => (hab k).2)
    (by rw [hgap]; exact hK)
  have ha : (1 / ((q.K + 1 : ℕ) : ℝ)) * ∑ j : Fin (q.K + 1),
      (∫ ω, ‖gradient I.f (x j ω)‖ ^ 2 ∂(P : Measure _)) ≤ p.eps := by
    have hs := Fin.sum_univ_eq_sum_range (fun k => ∫ ω, ‖gradient I.f (delayedIterate g q.gamma a q.x0 ω k)‖ ^ 2
      ∂(P : Measure (ℕ → Ω))) (q.K + 1)
    show (1 / ((q.K + 1 : ℕ) : ℝ)) * ∑ j : Fin (q.K + 1), (fun k => ∫ ω, ‖gradient I.f
      (delayedIterate g q.gamma a q.x0 ω k)‖ ^ 2 ∂(P : Measure (ℕ → Ω))) (j : ℕ) ≤ p.eps
    rw [hs]
    push_cast
    exact hacc
  have hu := uniform_prefix_accuracy P I.f q.K x p.eps hm hi ha
  have hfun : (fun z : Fin (q.K + 1) × (ℕ → Ω) =>
      execute (arrivalOracle q arrive P g) (ringmaster q) (budget p) z.1 z.2) =
      fun z => (x z.1 z.2, (timing q.R event q.K).clock) := by
    funext z
    exact hexe z.1 z.2
  change LongTails.Setups.RingmasterIterations.spec.successful p I
    (fun z : Fin (q.K + 1) × (ℕ → Ω) => execute (arrivalOracle q arrive P g) (ringmaster q) (budget p) z.1 z.2)
    ⟨((PMF.uniformOfFintype (Fin (q.K + 1))).toMeasure).prod (P : Measure (ℕ → Ω)), inferInstance⟩
  rw [hfun]
  exact ⟨hu.1.prodMk measurable_const, ⟨hu.2.1, hu.2.2.2⟩⟩

end OracleTemplate.RingmasterIterations
