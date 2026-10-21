import LongTails.Setups.RingmasterUniversalTime
import LongTails.Proofs.RingmasterExecution
import LongTails.Theorems.RingmasterIterations
import LongTails.Proofs.RennalaConvergence

open MeasureTheory

namespace OracleTemplate.RingmasterUniversalTime

open Rennala RingmasterAsgd

noncomputable def budget : (let S := LongTails.Setups.RingmasterUniversalTime.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => max 1 ⌈p.sigma ^ 2 / p.eps⌉₊ * ⌈48 * p.L * p.Delta / p.eps⌉₊

theorem result : Convergence LongTails.Setups.RingmasterUniversalTime.spec budget := by
  classical
  refine ⟨RingmasterAsgd.ringmaster, ?_, fun p _ => rfl⟩
  intro p hp I O hO
  obtain ⟨hf, Ω, m, μ, P, g, hiid, ho, rfl⟩ := hO
  let := m
  obtain ⟨hL, hsig, heps, hpow⟩ := hp
  let q := LongTails.Setups.RingmasterUniversalTime.publicInput p
  let R := LongTails.Setups.RingmasterUniversalTime.threshold p.sigma p.eps
  let Kbar := ⌈48 * p.L * p.Delta / p.eps⌉₊
  have hR1 : 1 ≤ R := le_max_left _ _
  let V : Fin p.n → ℝ → ℝ := fun i => RennalaUniform.work (p.power i)
  have hV : ∀ i, ContinuousOn (V i) (Set.Ici 0) ∧ MonotoneOn (V i) (Set.Ici 0) := fun i =>
    RennalaUniform.work_properties (p.power i) (hpow i)
  let event : ℕ → (Fin q.n → ℝ) → Option (Fin q.n × ℝ) := completionEvent V
  let ans : ℕ → Query q → Ω → Reply q := fun _ qq b => eventAnswer q V g qq b
  change LongTails.Setups.RingmasterUniversalTime.spec.successful p I
    (fun z : Fin (q.K + 1) × (ℕ → Ω) =>
      execute (eventOracle q V P g) (ringmaster q) (budget p) z.1 z.2)
    ⟨((PMF.uniformOfFintype (Fin (q.K + 1))).toMeasure).prod (P : Measure (ℕ → Ω)), inferInstance⟩
  intro hfin
  obtain ⟨hev0, hclk⟩ := deadline_updates R hR1 V hV Kbar hfin
  have hKq : q.K = Kbar * R := Nat.mul_comm _ _
  have hev : ∀ k < q.K, event k (timing q.R event k).starts ≠ none := fun k hk =>
    hev0 k (by rw [← hKq]; exact hk)
  let a : ℕ → ℕ := fun k => if k < q.K then delays q.R event k else k
  have hab := delays_bound q.R hR1 event q.K hev
  have hexe (j : Fin (q.K + 1)) (ω : ℕ → Ω) :
      execute (eventOracle q V P g) (ringmaster q) (budget p) j ω =
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
  have hΔ0 : 0 ≤ p.Delta := by rw [← hgap]; linarith [hf.lower p.x0]
  have hK : 8 * R * p.L * (I.f p.x0 - I.lower) / p.eps +
      16 * p.sigma ^ 2 * p.L * (I.f p.x0 - I.lower) / p.eps ^ 2 ≤ (q.K : ℝ) := by
    rw [hgap]
    have hRs : p.sigma ^ 2 / p.eps ≤ (R : ℝ) := by
      have h1 := Nat.le_ceil (p.sigma ^ 2 / p.eps)
      have h2 : (⌈p.sigma ^ 2 / p.eps⌉₊ : ℝ) ≤ (R : ℝ) := by exact_mod_cast le_max_right _ _
      linarith
    have hKb : 48 * p.L * p.Delta / p.eps ≤ (Kbar : ℝ) := Nat.le_ceil _
    have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR1
    have hLD : 0 ≤ p.L * p.Delta / p.eps := by positivity
    have e1 : 8 * (R : ℝ) * p.L * p.Delta / p.eps = 8 * R * (p.L * p.Delta / p.eps) := by ring
    have e2 : 16 * p.sigma ^ 2 * p.L * p.Delta / p.eps ^ 2 =
        16 * (p.sigma ^ 2 / p.eps) * (p.L * p.Delta / p.eps) := by
      field_simp
    have e3 : 48 * p.L * p.Delta / p.eps = 48 * (p.L * p.Delta / p.eps) := by ring
    have hq : (q.K : ℝ) = (R : ℝ) * (Kbar : ℝ) := by
      show ((R * Kbar : ℕ) : ℝ) = _
      push_cast
      ring
    rw [e1, e2, hq]
    rw [e3] at hKb
    nlinarith [mul_le_mul_of_nonneg_right hRs hLD, mul_le_mul_of_nonneg_left hKb
      (by positivity : (0 : ℝ) ≤ R)]
  have hacc := iteration_accuracy I.f g μ P (fun k ω => ω k) p.L p.sigma p.eps I.lower p.x0 a R q.K
    hL hsig heps hf.hasGradient hf.lipschitz hf.lower ho hiid (fun k => (hab k).1) (fun k => (hab k).2) hK
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
      execute (eventOracle q V P g) (ringmaster q) (budget p) z.1 z.2) =
      fun z => (x z.1 z.2, (timing q.R event q.K).clock) := by
    funext z
    exact hexe z.1 z.2
  rw [hfun]
  have hclk' : ENNReal.ofReal (timing q.R event q.K).clock ≤ RennalaUniform.deadline
      (fun i t => RennalaUniform.work (p.power i) t / 4) (LongTails.Setups.RingmasterUniversalTime.threshold p.sigma p.eps)
        ⌈48 * p.L * p.Delta / p.eps⌉₊ := by
    have e : (timing q.R event q.K).clock = (timing R (completionEvent V) (Kbar * R)).clock :=
      congrArg (fun k => (timing R (completionEvent V) k).clock) hKq
    rw [e]
    exact hclk
  exact ⟨hu.1.prodMk measurable_const, ⟨hu.2.1, hu.2.2.2⟩, Filter.Eventually.of_forall (fun _ => hclk')⟩

end OracleTemplate.RingmasterUniversalTime
