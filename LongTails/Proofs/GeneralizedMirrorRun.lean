import LongTails.Proofs.GeneralizedMirrorConcentration

open MeasureTheory Set
open LongTails.Setups.StochasticGeneralizedMirror
open LongTails.Algorithms.StochasticGeneralizedMirror
open LongTails.Proofs.GeneralizedMirrorProcess
open LongTails.Proofs.GeneralizedMirrorStopped
open LongTails.Proofs.GeneralizedMirrorWeights
open LongTails.Proofs.GeneralizedMirrorConcentration
open OracleTemplate.StochasticGeneralized

namespace LongTails.Proofs.GeneralizedMirrorRun

noncomputable def blockSum (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (F : State q m → (Fin (m + 2) → q.Ω) → ℝ)
    (k : ℕ) (s : State q m) (ξ : ℕ → q.Ω) : ℝ :=
  accumulated (fun _ => m + 2) (liftedNext q ell m I g) (liftScalar q m F) k s ξ

lemma blockSum_eq_sum (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (F : State q m → (Fin (m + 2) → q.Ω) → ℝ)
    (k : ℕ) (s : State q m) (ξ : ℕ → q.Ω) :
    blockSum q ell m I g F k s ξ = ∑ i ∈ Finset.range k,
      F (trace q ell m I g s ξ i).1 (fun j => (trace q ell m I g s ξ i).2 j) := by
  rw [blockSum, accumulated_eq_sum]
  simp only [liftScalar_full, trace]

lemma blockSum_zero (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (F : State q m → (Fin (m + 2) → q.Ω) → ℝ)
    (s : State q m) (ξ : ℕ → q.Ω) : blockSum q ell m I g F 0 s ξ = 0 := rfl

lemma blockSum_succ (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (F : State q m → (Fin (m + 2) → q.Ω) → ℝ)
    (k : ℕ) (s : State q m) (ξ : ℕ → q.Ω) :
    blockSum q ell m I g F (k + 1) s ξ = blockSum q ell m I g F k s ξ +
      F (trace q ell m I g s ξ k).1 (fun j => (trace q ell m I g s ξ k).2 j) := by
  rw [blockSum_eq_sum, blockSum_eq_sum, Finset.sum_range_succ]

lemma goodPilot_of_failure_sum (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (u : q.E) (s : State q m) (ξ : ℕ → q.Ω)
    (K j : ℕ) (hj : j < K)
    (hf : blockSum q ell m I g (failureBlock q ell m I g u) K s ξ < 1)
    (hr : Ready I u (trace q ell m I g s ξ j).1) :
    GoodPilot q ell m I g (trace q ell m I g s ξ j).1
      (fun i => (trace q ell m I g s ξ j).2 i) := by
  rw [blockSum_eq_sum] at hf
  have hh := Finset.single_le_sum
    (fun i (_ : i ∈ Finset.range K) => (failureBlock_range q ell m I g u
      (trace q ell m I g s ξ i).1 (fun j => (trace q ell m I g s ξ i).2 j)).1)
    (Finset.mem_range.mpr hj)
  by_contra h
  have he : failureBlock q ell m I g u (trace q ell m I g s ξ j).1
      (fun i => (trace q ell m I g s ξ j).2 i) = 1 := by
    simp only [failureBlock, hr, h, not_false_eq_true, and_self, ↓reduceIte]
  rw [he] at hh
  linarith

lemma phaseNext_energy (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 1 ≤ ell)
    (m : ℕ) (I : Instance q) (O : OracleTemplate.Oracle (Query q) (Reply q))
    (hI : spec.admissible q I O) (g : q.E → q.Ω → Dual q)
    (u : q.E) (hu : u ∈ I.Q) (hmin : IsMinOn (objective I) I.Q u) (hG : ‖I.df u‖ ≤ q.G)
    (s : State q m) (b : Fin (m + 2) → q.Ω) (hr : Ready I u s)
    (hg : GoodPilot q ell m I g s b) :
    let t := phaseNext q ell m I g s b
    t.x ∈ I.Q ∩ I.U ∧ t.z ∈ I.Q ∩ I.U ∧ potential I u t ≤
      potential I u s + signedBlock q ell m I g u s b + energyBlock q ell m I g u s b := by
  have hell0 : 0 < ell := by linarith
  have ha := GeneralizedMirrorTuning.stepWeight_pos q hq hell0 hr.1
  have hactive : 0 < s.A ∧ s.A < q.R ^ 2 / q.ε := ⟨hr.1, hr.2.1⟩
  have hdh : ∀ z ∈ I.U, HasFDerivAt I.h (I.dh z) z := by
    rcases hI with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdh, _⟩
    exact hdh
  have henergy : s.A * (objective I s.x - objective I u) + divergence I u s.z ≤ q.R ^ 2 := by
    have hh := hr.2.2.2.2.1
    unfold potential at hh
    rwa [measurableDivergence_eq I hdh u s.z hr.2.2.2.1.2] at hh
  have hB := GeneralizedMirrorTuning.clipRadius_pos q hq.2.2.1
    hq.2.2.2.2.2.1 hq.2.2.2.2.2.2.2.2.1
  have he : ‖blockDirection q ell m g s b - I.df (queryPoint q ell s)‖ ≤ 3 * clipRadius q / 2 :=
    GeneralizedMirrorNoise.centered_error_bounded hB.le _ _ _ hg
  have ht := GeneralizedMirrorInvariant.admissible_energy_step q hq I O hI hell hr.1
    s.x s.z u hr.2.2.1 hr.2.2.2.1 hu hmin hG henergy hr.2.2.2.2.2
    (blockDirection q ell m g s b) he
  dsimp only at ht ⊢
  simp only [phaseNext, hactive, ↓reduceIte, guardedProx, ha]
  refine ⟨ht.2.1, ht.1, ?_⟩
  simp only [potential, signedBlock, energyBlock, activeWeight, hactive, ↓reduceIte,
    stoppedError, hr, hg, and_self]
  rw [measurableDivergence_eq I hdh u _ ht.1.2,
    measurableDivergence_eq I hdh u s.z hr.2.2.2.1.2]
  exact ht.2.2

noncomputable def Safe {q : Public} {m : ℕ} (I : Instance q) (u : q.E) (s : State q m) : Prop :=
  0 < s.A ∧ s.x ∈ I.Q ∩ I.U ∧ s.z ∈ I.Q ∩ I.U ∧
    potential I u s ≤ q.R ^ 2 ∧ ‖s.x - u‖ ≤ 2 * q.R

lemma Safe.ready {q : Public} {m : ℕ} {I : Instance q} {u : q.E} {s : State q m}
    (hs : Safe I u s) (hA : s.A < q.R ^ 2 / q.ε) : Ready I u s :=
  ⟨hs.1, hA, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2⟩

lemma Ready.safe {q : Public} {m : ℕ} {I : Instance q} {u : q.E} {s : State q m}
    (hs : Ready I u s) : Safe I u s :=
  ⟨hs.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2⟩


lemma phaseNext_safe (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 1 ≤ ell)
    (m : ℕ) (I : Instance q) (O : OracleTemplate.Oracle (Query q) (Reply q))
    (hI : spec.admissible q I O) (g : q.E → q.Ω → Dual q)
    (u : q.E) (hu : u ∈ I.Q) (hmin : IsMinOn (objective I) I.Q u) (hG : ‖I.df u‖ ≤ q.G)
    (s : State q m) (b : Fin (m + 2) → q.Ω) (hs : Safe I u s)
    (hg : Ready I u s → GoodPilot q ell m I g s b)
    (hp : potential I u (phaseNext q ell m I g s b) ≤ q.R ^ 2) :
    Safe I u (phaseNext q ell m I g s b) := by
  have hell0 : 0 < ell := by linarith
  by_cases ht : s.A < q.R ^ 2 / q.ε
  · have hr := hs.ready ht
    have hact : 0 < s.A ∧ s.A < q.R ^ 2 / q.ε := ⟨hs.1, ht⟩
    have he := phaseNext_energy q hq hell m I O hI g u hu hmin hG s b hr (hg hr)
    have hpos := phaseNext_positive q hq hell0 m I g s b hs.1
    have ha := GeneralizedMirrorTuning.stepWeight_pos q hq hell0 hs.1
    have hdh : ∀ z ∈ I.U, HasFDerivAt I.h (I.dh z) z := by
      rcases hI with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdh, _⟩
      exact hdh
    have hstrong : ∀ z ∈ I.Q ∩ I.U, ∀ v ∈ I.Q, ‖v - z‖ ^ 2 / 2 ≤ divergence I v z := by
      rcases hI with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hstrong, _⟩
      exact hstrong
    have hz := potential_zradius I u hu hmin hq.2.2.1 hdh hstrong
      (phaseNext q ell m I g s b) hpos.le he.1.1 he.2.1 hp
    refine ⟨hpos, he.1, he.2.1, hp, ?_⟩
    simp only [phaseNext, hact, ↓reduceIte, guardedProx, ha] at hz ⊢
    exact GeneralizedMirrorStep.mix_radius hs.1.le ha s.x _ u hs.2.2.2.2 hz
  · have he : phaseNext q ell m I g s b = s := by simp [phaseNext, ht]
    rwa [he]

lemma safe_energy_step (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 1 ≤ ell)
    (m : ℕ) (I : Instance q) (O : OracleTemplate.Oracle (Query q) (Reply q))
    (hI : spec.admissible q I O) (g : q.E → q.Ω → Dual q)
    (u : q.E) (hu : u ∈ I.Q) (hmin : IsMinOn (objective I) I.Q u) (hG : ‖I.df u‖ ≤ q.G)
    (s : State q m) (b : Fin (m + 2) → q.Ω) (hs : Safe I u s)
    (hg : Ready I u s → GoodPilot q ell m I g s b) :
    potential I u (phaseNext q ell m I g s b) ≤ potential I u s +
      signedBlock q ell m I g u s b + energyBlock q ell m I g u s b := by
  by_cases ht : s.A < q.R ^ 2 / q.ε
  · exact (phaseNext_energy q hq hell m I O hI g u hu hmin hG s b (hs.ready ht)
      (hg (hs.ready ht))).2.2
  · have hr : ¬Ready I u s := fun h => ht h.2.1
    simp [phaseNext, ht, signedBlock, energyBlock, stoppedError, hr]

lemma trace_safe_of_sums (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 1 ≤ ell)
    (m : ℕ) (I : Instance q) (O : OracleTemplate.Oracle (Query q) (Reply q))
    (hI : spec.admissible q I O) (g : q.E → q.Ω → Dual q)
    (u : q.E) (hu : u ∈ I.Q) (hmin : IsMinOn (objective I) I.Q u) (hG : ‖I.df u‖ ≤ q.G)
    (s : State q m) (hs : Safe I u s) (hp : potential I u s ≤ 5 * q.R ^ 2 / 8)
    (ξ : ℕ → q.Ω) (K : ℕ)
    (hf : blockSum q ell m I g (failureBlock q ell m I g u) K s ξ < 1)
    (hS : ∀ k ≤ K, blockSum q ell m I g (signedBlock q ell m I g u) k s ξ ≤ q.R ^ 2 / 8)
    (hV : ∀ k ≤ K, blockSum q ell m I g (energyBlock q ell m I g u) k s ξ ≤ q.R ^ 2 / 16) :
    ∀ k ≤ K, Safe I u (trace q ell m I g s ξ k).1 ∧
      potential I u (trace q ell m I g s ξ k).1 ≤ potential I u s +
        blockSum q ell m I g (signedBlock q ell m I g u) k s ξ +
        blockSum q ell m I g (energyBlock q ell m I g u) k s ξ := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨hs, by simp [trace, blockTrace, blockSum_zero]⟩
  | succ k ih =>
    intro hk
    have hk' : k ≤ K := by omega
    have hklt : k < K := by omega
    obtain ⟨hsafe, hpot⟩ := ih hk'
    let t := (trace q ell m I g s ξ k).1
    let b := fun i : Fin (m + 2) => (trace q ell m I g s ξ k).2 i
    have hgood : Ready I u t → GoodPilot q ell m I g t b :=
      goodPilot_of_failure_sum q ell m I g u s ξ K k hklt hf
    have hstep := safe_energy_step q hq hell m I O hI g u hu hmin hG t b hsafe hgood
    have he : (trace q ell m I g s ξ (k + 1)).1 = phaseNext q ell m I g t b := by
      rw [trace_succ]
    have hnext : potential I u (trace q ell m I g s ξ (k + 1)).1 ≤ potential I u s +
        blockSum q ell m I g (signedBlock q ell m I g u) (k + 1) s ξ +
        blockSum q ell m I g (energyBlock q ell m I g u) (k + 1) s ξ := by
      rw [he, blockSum_succ, blockSum_succ]
      dsimp [t, b] at hstep
      linarith
    have hupper : potential I u (trace q ell m I g s ξ (k + 1)).1 ≤ q.R ^ 2 := by
      have hhS := hS (k + 1) hk
      have hhV := hV (k + 1) hk
      nlinarith [sq_nonneg q.R]
    refine ⟨?_, hnext⟩
    rw [he] at hupper ⊢
    exact phaseNext_safe q hq hell m I O hI g u hu hmin hG t b hsafe hgood hupper

noncomputable def Bad (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (u : q.E) (s : State q m) (K : ℕ) (ξ : ℕ → q.Ω) : Prop :=
  (∃ i : Fin K, q.R ^ 2 / 8 ≤ blockSum q ell m I g (signedBlock q ell m I g u) (i.val + 1) s ξ) ∨
  (∃ i : Fin K, q.R ^ 2 / 16 ≤ blockSum q ell m I g (energyBlock q ell m I g u) (i.val + 1) s ξ) ∨
  1 ≤ blockSum q ell m I g (failureBlock q ell m I g u) K s ξ

lemma not_bad_sums (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (u : q.E) (s : State q m) (K : ℕ) (ξ : ℕ → q.Ω)
    (h : ¬Bad q ell m I g u s K ξ) :
    blockSum q ell m I g (failureBlock q ell m I g u) K s ξ < 1 ∧
    (∀ k ≤ K, blockSum q ell m I g (signedBlock q ell m I g u) k s ξ ≤ q.R ^ 2 / 8) ∧
    (∀ k ≤ K, blockSum q ell m I g (energyBlock q ell m I g u) k s ξ ≤ q.R ^ 2 / 16) := by
  refine ⟨lt_of_not_ge (fun hh => h (Or.inr (Or.inr hh))), ?_, ?_⟩
  · intro k hk
    cases k with
    | zero => rw [blockSum_zero]; positivity
    | succ k =>
      exact (lt_of_not_ge (fun hh => h (Or.inl ⟨⟨k, by omega⟩, hh⟩))).le
  · intro k hk
    cases k with
    | zero => rw [blockSum_zero]; positivity
    | succ k =>
      exact (lt_of_not_ge (fun hh => h (Or.inr (Or.inl ⟨⟨k, by omega⟩, hh⟩)))).le

lemma bad_probability (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (u : q.E) (s : State q m) (K : ℕ)
    (P : Measure (ℕ → q.Ω))
    (hS : ∀ k ≤ K, P.real {ξ | q.R ^ 2 / 8 ≤
      blockSum q ell m I g (signedBlock q ell m I g u) k s ξ} ≤ Real.exp (-4 * ell))
    (hV : ∀ k ≤ K, P.real {ξ | q.R ^ 2 / 16 ≤
      blockSum q ell m I g (energyBlock q ell m I g u) k s ξ} ≤ Real.exp (-4 * ell))
    (hF : P.real {ξ | 1 ≤ blockSum q ell m I g (failureBlock q ell m I g u) K s ξ} ≤
      K * (1 / 2 : ℝ) ^ m) :
    P.real {ξ | Bad q ell m I g u s K ξ} ≤
      2 * K * Real.exp (-4 * ell) + K * (1 / 2 : ℝ) ^ m := by
  let S := fun i : Fin K => {ξ | q.R ^ 2 / 8 ≤
    blockSum q ell m I g (signedBlock q ell m I g u) (i.val + 1) s ξ}
  let V := fun i : Fin K => {ξ | q.R ^ 2 / 16 ≤
    blockSum q ell m I g (energyBlock q ell m I g u) (i.val + 1) s ξ}
  let F := {ξ | 1 ≤ blockSum q ell m I g (failureBlock q ell m I g u) K s ξ}
  have he : {ξ | Bad q ell m I g u s K ξ} = (⋃ i, S i) ∪ ((⋃ i, V i) ∪ F) := by
    ext ξ
    simp only [Bad, Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion, S, V, F]
  have hs : P.real (⋃ i, S i) ≤ K * Real.exp (-4 * ell) := by
    apply (measureReal_iUnion_fintype_le S).trans
    calc
      _ ≤ ∑ _ : Fin K, Real.exp (-4 * ell) := Finset.sum_le_sum (fun i _ => hS _ (by omega))
      _ = _ := by simp
  have hv : P.real (⋃ i, V i) ≤ K * Real.exp (-4 * ell) := by
    apply (measureReal_iUnion_fintype_le V).trans
    calc
      _ ≤ ∑ _ : Fin K, Real.exp (-4 * ell) := Finset.sum_le_sum (fun i _ => hV _ (by omega))
      _ = _ := by simp
  rw [he]
  have hh := (measureReal_union_le (μ := P) (⋃ i, S i) ((⋃ i, V i) ∪ F)).trans
    (add_le_add hs ((measureReal_union_le (μ := P) (⋃ i, V i) F).trans (add_le_add hv hF)))
  linarith

lemma safe_accuracy {q : Public} {m : ℕ} (hq : spec.valid q) (I : Instance q)
    (u : q.E) (hu : u ∈ I.Q) (hmin : IsMinOn (objective I) I.Q u)
    (hd : ∀ z ∈ I.U, HasFDerivAt I.h (I.dh z) z)
    (hstrong : ∀ z ∈ I.Q ∩ I.U, ∀ v ∈ I.Q, ‖v - z‖ ^ 2 / 2 ≤ divergence I v z)
    (s : State q m) (hs : Safe I u s) (hA : q.R ^ 2 / q.ε ≤ s.A) :
    s.x ∈ I.Q ∧ objective I s.x - objective I u ≤ q.ε := by
  refine ⟨hs.2.1.1, ?_⟩
  have hε := hq.2.2.2.2.2.2.2.2.1
  have hupper := hs.2.2.2.1
  unfold potential at hupper
  rw [measurableDivergence_eq I hd u s.z hs.2.2.1.2] at hupper
  have hD := hstrong s.z hs.2.2.1 u hu
  have htarget := (div_le_iff₀ hε).mp hA
  have hgap : 0 ≤ objective I s.x - objective I u := sub_nonneg.mpr (hmin hs.2.1.1)
  nlinarith [sq_nonneg ‖u - s.z‖, hs.1]

lemma accuracy_of_not_bad (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 1 ≤ ell)
    (m : ℕ) (I : Instance q) (O : OracleTemplate.Oracle (Query q) (Reply q))
    (hI : spec.admissible q I O) (g : q.E → q.Ω → Dual q)
    (u : q.E) (hu : u ∈ I.Q) (hmin : IsMinOn (objective I) I.Q u) (hG : ‖I.df u‖ ≤ q.G)
    (hD : divergence I u q.x0 ≤ q.R ^ 2 / 2)
    (hgap : objective I q.x0 - objective I u ≤ q.Δ)
    (ξ : ℕ → q.Ω) (K : ℕ) (hK : horizonScale q * ell ≤ K)
    (hb : ¬Bad q ell m I g u (initialState q m) K ξ) :
    (trace q ell m I g (initialState q m) ξ K).1.x ∈ I.Q ∧
      objective I (trace q ell m I g (initialState q m) ξ K).1.x - objective I u ≤ q.ε := by
  have hdh : ∀ z ∈ I.U, HasFDerivAt I.h (I.dh z) z := by
    rcases hI with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdh, _⟩
    exact hdh
  have hstrong : ∀ z ∈ I.Q ∩ I.U, ∀ v ∈ I.Q, ‖v - z‖ ^ 2 / 2 ≤ divergence I v z := by
    rcases hI with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hstrong, _⟩
    exact hstrong
  have hx : q.x0 ∈ I.Q ∩ I.U := by
    rcases hI with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hx, _⟩
    exact hx
  have hi := initial_ready hq m I u hu hx hdh hstrong hD hgap
  have hbds := not_bad_sums q ell m I g u (initialState q m) K ξ hb
  have hs := trace_safe_of_sums q hq hell m I O hI g u hu hmin hG (initialState q m)
    (Ready.safe hi.1) hi.2 ξ K hbds.1 hbds.2.1 hbds.2.2 K le_rfl
  have ht := trace_reaches_target q hq hell m I g ξ K hK
  exact safe_accuracy hq I u hu hmin hdh hstrong _ hs.1 ht

end LongTails.Proofs.GeneralizedMirrorRun
