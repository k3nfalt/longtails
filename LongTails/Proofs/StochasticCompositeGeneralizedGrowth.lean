import LongTails.Proofs.CompositeGeneralizedRun
import LongTails.Proofs.StochasticCompositeGeneralizedLedger

open Set MeasureTheory
namespace OracleTemplate.CompositeGeneralized

lemma weight_antitone_curvature {L1 R A M N : ℝ} (hA : 0 < A) (hM : 0 < M) (hMN : M ≤ N) :
    weight L1 R A N ≤ weight L1 R A M := by
  have hN : 0 < N := hM.trans_le hMN
  let r (C : ℝ) := (1 + Real.sqrt (1 + 16 * C * A)) / (8 * C)
  have hr (C : ℝ) (hC : 0 < C) : 0 < r C := by dsimp [r]; positivity
  have hid (C : ℝ) (hC : 0 < C) : 4 * C * (r C) ^ 2 = A + r C := by
    have hs := Real.sq_sqrt (by positivity : 0 ≤ 1 + 16 * C * A)
    have hsC := congrArg (fun x : ℝ => C * x) hs
    dsimp only [r]
    field_simp
    simp only [mul_comm C (16 : ℝ)]
    nlinarith
  have hroot : 1 ≤ Real.sqrt (1 + 16 * M * A) := Real.one_le_sqrt.mpr (by nlinarith)
  have hMr : 1 ≤ 4 * M * r M := by
    dsimp only [r]
    field_simp
    simp only [mul_comm M (16 : ℝ)]
    nlinarith
  have hquad : 4 * M * (r N) ^ 2 ≤ A + r N := by
    have hh := mul_le_mul_of_nonneg_right hMN (sq_nonneg (r N))
    nlinarith [hid N hN]
  have hle : r N ≤ r M := by
    by_contra hn
    have hgt := lt_of_not_ge hn
    have hp : 0 < (r N - r M) * (4 * M * (r N + r M) - 1) := by
      apply mul_pos (by linarith)
      nlinarith [hr N hN]
    nlinarith [hid M hM]
  exact min_le_min_right _ hle

lemma Hyp.increase_L0 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f ψ : E → ℝ} {g : E → E} {Q : Set E} {prox : ℝ → E → E → E} {L0 L0' L1 : ℝ}
    (h : Hyp f ψ g Q prox L0 L1) (hL : L0 ≤ L0') : Hyp f ψ g Q prox L0' L1 := by
  refine { h with hL0 := h.hL0.trans_le hL, smooth := ?_ }
  intro x y M hm
  apply (h.smooth x y M hm).trans
  exact mul_le_mul_of_nonneg_right (by linarith : L0 + L1 * M ≤ L0' + L1 * M) (norm_nonneg _)


lemma potential_threshold {L0 L1 R Δ ε Ms A K : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (hR : 0 < R) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hMsL : L0 ≤ Ms) (hA : 0 < A)
    (hpot : let δ := 1 / (4 * Real.sqrt (3 * Ms)); let ρ := 1 / (3 + 192 * L1 * R)
      potential δ ρ (Real.sqrt (R ^ 2 / (4 * Δ))) + 3 / 4 * K ≤ potential δ ρ (Real.sqrt A))
    (hK : 20 * Real.sqrt (Ms * R ^ 2 / ε) +
      (6 + 256 * L1 * R) * Real.log (2 + (3 + 192 * L1 * R) * Real.sqrt (Δ / (L0 * R ^ 2))) ≤ K) :
    4 * R ^ 2 / ε ≤ A := by
  by_contra hn
  have hsmall : A < 4 * R ^ 2 / ε := lt_of_not_ge hn
  have hMs : 0 < Ms := hL0.trans_le hMsL
  have hq0 : 0 < Real.sqrt (3 * Ms) := Real.sqrt_pos.mpr (by positivity)
  have hq2 : Real.sqrt (3 * Ms) ^ 2 = 3 * Ms := Real.sq_sqrt (by positivity)
  let δ := 1 / (4 * Real.sqrt (3 * Ms))
  let ρ := 1 / (3 + 192 * L1 * R)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hδ2 : δ ^ 2 * (48 * Ms) = 1 := by
    dsimp only [δ]
    rw [div_pow, one_pow, mul_pow, hq2]
    field_simp
    ring
  let A0 := R ^ 2 / (4 * Δ)
  have hA0 : 0 < A0 := by dsimp [A0]; positivity
  let s0 := Real.sqrt A0
  let sK := Real.sqrt A
  have hs0 : 0 < s0 := Real.sqrt_pos.mpr hA0
  have hsK : 0 < sK := Real.sqrt_pos.mpr hA
  have hs02 : s0 ^ 2 = A0 := Real.sq_sqrt hA0.le
  have hsK2 : sK ^ 2 = A := Real.sq_sqrt hA.le
  change potential δ ρ s0 + 3 / 4 * K ≤ potential δ ρ sK at hpot
  unfold potential at hpot
  let cap := δ / ρ
  have hcap : 0 < cap := by dsimp [cap]; positivity
  let c := (1 + ρ) / ρ
  have hc : c = 4 + 192 * L1 * R := by dsimp [c, ρ]; field_simp; ring
  have hup : Real.log (min sK cap) ≤ Real.log cap :=
    (Real.log_le_log_iff (lt_min hsK hcap) hcap).mpr (min_le_right _ _)
  let X := Real.sqrt (Δ / (L0 * R ^ 2))
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hX2 : X ^ 2 = Δ / (L0 * R ^ 2) := Real.sq_sqrt (by positivity)
  have hδX : δ ≤ X * s0 := by
    apply le_of_sq_le_sq' (by positivity)
    rw [mul_pow, hX2, hs02]
    have he : Δ / (L0 * R ^ 2) * A0 = 1 / (4 * L0) := by dsimp [A0]; field_simp
    rw [he]
    have hh : δ ^ 2 = 1 / (48 * Ms) := by
      rw [eq_div_iff (by positivity)]
      linarith [hδ2]
    rw [hh, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  let Y := 2 + (3 + 192 * L1 * R) * X
  have hY : 2 ≤ Y := by dsimp [Y]; nlinarith [mul_nonneg hL1 hR.le]
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hratio : cap / min s0 cap ≤ Y := by
    rcases le_total s0 cap with hle | hle
    · rw [min_eq_left hle, div_le_iff₀ hs0]
      have he : cap = (3 + 192 * L1 * R) * δ := by dsimp [cap, ρ]; field_simp
      rw [he]
      have hm := mul_le_mul_of_nonneg_left hδX (show 0 ≤ 3 + 192 * L1 * R by positivity)
      dsimp only [Y]
      nlinarith
    · rw [min_eq_right hle, div_self hcap.ne']
      linarith
  have hlogdiff : Real.log cap - Real.log (min s0 cap) ≤ Real.log Y := by
    rw [← Real.log_div hcap.ne' (lt_min hs0 hcap).ne']
    exact (Real.log_le_log_iff (div_pos hcap (lt_min hs0 hcap)) (by linarith)).mpr hratio
  have hsKδ : sK / δ < 15 * Real.sqrt (Ms * R ^ 2 / ε) := by
    have hm : sK / δ = 4 * Real.sqrt (3 * Ms) * sK := by dsimp [δ]; field_simp
    rw [hm]
    apply lt_of_sq_lt_sq' (by positivity)
    rw [mul_pow, mul_pow, mul_pow, hq2, hsK2, Real.sq_sqrt (by positivity)]
    have hAE : A * ε < 4 * R ^ 2 := (lt_div_iff₀ hε).mp hsmall
    have hh := mul_lt_mul_of_pos_left hAE hMs
    rw [show 4 ^ 2 * (3 * Ms) * A = 48 * Ms * A by ring,
      show (15 : ℝ) ^ 2 * (Ms * R ^ 2 / ε) = 225 * Ms * R ^ 2 / ε by ring,
      lt_div_iff₀ hε]
    nlinarith
  have hs0δ : 0 ≤ s0 / δ := by positivity
  have hcl : c * Real.log Y ≤ 3 / 4 * (6 + 256 * L1 * R) * Real.log Y := by
    rw [hc]
    exact mul_le_mul_of_nonneg_right (by nlinarith only []) hlogY
  have hc0 : 0 ≤ c := by positivity
  have hmain : 3 / 4 * K < 15 * Real.sqrt (Ms * R ^ 2 / ε) + c * Real.log Y := by
    have h1 := mul_le_mul_of_nonneg_left hup hc0
    have h2 := mul_le_mul_of_nonneg_left hlogdiff hc0
    nlinarith only [hpot, h1, h2, hsKδ, hs0δ]
  linarith only [hK, hcl, hmain]


end OracleTemplate.CompositeGeneralized

namespace OracleTemplate.StochasticCompositeGeneralized
open LongTails.Setups.StochasticCompositeGeneralizedSmooth

lemma controlled_sqrt_growth (p : Public) (I : Instance p)
    (h : CompositeGeneralized.Hyp I.f I.ψ I.grad I.Q I.prox p.L0 p.L1)
    (hR : 0 < p.R) (hσ : 0 ≤ p.σ) (xs : p.E) (hxs : xs ∈ I.Q)
    (hmin : IsMinOn (fun u => I.f u + I.ψ u) I.Q xs) {G : ℝ} (hG : ‖I.grad xs‖ ≤ G)
    (s : State p.E) (hs : PhaseControl p I xs s)
    (hstage : s.stage = 1 ∨ s.stage = 2 ∨ s.stage = 3) :
    Real.sqrt s.A + 1 / (4 * Real.sqrt (3 * (p.L0 + 192 * p.L1 * p.σ + p.L1 * G))) ≤
        Real.sqrt (s.A + stepWeight p s) ∨
      (1 + 1 / (3 + 192 * p.L1 * p.R)) * Real.sqrt s.A ≤
        Real.sqrt (s.A + stepWeight p s) := by
  have hL : p.L0 ≤ p.L0 + 192 * p.L1 * p.σ := by
    have hh := mul_nonneg h.hL1 hσ
    nlinarith
  have h' := h.increase_L0 hL
  have hg := CompositeGeneralized.sqrt_growth h' (by positivity : 0 < 2 * p.R) hxs hmin hG hs.1
  have hM : 0 < s.M := by
    have hh := (hs.2.1 hstage).1
    have hn := mul_nonneg h.hL1 (norm_nonneg (I.grad s.x))
    linarith [h.hL0]
  have hMN : s.M ≤ p.L0 + 192 * p.L1 * p.σ + p.L1 * ‖I.grad s.x‖ := by
    linarith [(hs.2.1 hstage).2]
  have ha := CompositeGeneralized.weight_antitone_curvature (L1 := p.L1) (R := 2 * p.R) hs.1.1 hM hMN
  have hr : Real.sqrt (s.A + CompositeGeneralized.weight p.L1 (2 * p.R) s.A
      (p.L0 + 192 * p.L1 * p.σ + p.L1 * ‖I.grad s.x‖)) ≤ Real.sqrt (s.A + stepWeight p s) := by
    apply Real.sqrt_le_sqrt
    dsimp only [stepWeight]
    linarith
  change Real.sqrt s.A + _ ≤ Real.sqrt (s.A +
      CompositeGeneralized.weight p.L1 (2 * p.R) s.A (p.L0 + 192 * p.L1 * p.σ + p.L1 * ‖I.grad s.x‖)) ∨
    (1 + 1 / (3 + 96 * p.L1 * (2 * p.R))) * Real.sqrt s.A ≤ Real.sqrt (s.A +
      CompositeGeneralized.weight p.L1 (2 * p.R) s.A (p.L0 + 192 * p.L1 * p.σ + p.L1 * ‖I.grad s.x‖)) at hg
  rcases hg with hleft | hright
  · exact Or.inl (hleft.trans hr)
  · apply Or.inr
    convert hright.trans hr using 1; ring


def PhaseProtocol {E : Type*} (k : ℕ) (s : State E) : Prop :=
  s.stage ≤ 4 ∧ 4 * s.iteration ≤ k ∧ (s.stage ≤ 3 → 4 * s.iteration + s.stage = k)

lemma initial_phaseProtocol (p : Public) : PhaseProtocol 0 (initialState p) := by
  by_cases hf : p.Δ ≤ p.ε <;> simp [PhaseProtocol, initialState, hf]

lemma phaseNext_protocol (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (s : State p.E) (hw : WellFormed s) (he : PhaseEntry s) (k : ℕ) (hk : PhaseProtocol k s)
    (ξ : Fin (phaseCost p s) → p.Ω) :
    PhaseProtocol (k + 1) (phaseNext p I g (phaseCost p s) s ξ) := by
  by_cases h0 : s.stage = 0
  · have hcost : phaseCost p s = pilotSize p s.iteration := by simp [phaseCost, h0]
    have ht := phaseNext_first_pilot p I g hL0 hL1 hR hσ s hw h0
      (he.1 (Or.inl h0)).1 (he.1 (Or.inl h0)).2
    rw [← hcost] at ht
    rw [ht ξ]
    have hold := hk.2.2 (by omega)
    dsimp only [PhaseProtocol]
    omega
  by_cases h1 : s.stage = 1
  · have hcost : phaseCost p s = pilotSize p s.iteration := by simp [phaseCost, h1]
    have ht := phaseNext_second_pilot p I g hL0 hL1 hR hσ s hw h1
      (he.1 (Or.inr h1)).1 (he.1 (Or.inr h1)).2
    rw [← hcost] at ht
    rw [ht ξ]
    have hold := hk.2.2 (by omega)
    dsimp only [PhaseProtocol]
    omega
  by_cases h2 : s.stage = 2
  · have hcost : phaseCost p s = batchSize p s.iteration (stepWeight p s) := by simp [phaseCost, h2]
    have ht := phaseNext_evaluation p I g hL0 hL1 hR hσ s hw h2 (he.2 h2).1 (he.2 h2).2
    rw [← hcost] at ht
    rw [ht ξ]
    have hold := hk.2.2 (by omega)
    dsimp only [PhaseProtocol]
    omega
  have hcost : phaseCost p s = 1 := by simp [phaseCost, h0, h1, h2]
  by_cases h3 : s.stage = 3
  · have ht := phaseNext_prox p I g hL1 hR s hw h3
    rw [← hcost] at ht
    rw [ht ξ]
    have hold := hk.2.2 (by omega)
    simp only [PhaseProtocol, update, h3, Nat.reduceEqDiff, ite_false, ite_true]
    split_ifs <;> omega
  · have ht := phaseNext_frozen p I g s (by omega)
    rw [← hcost] at ht
    rw [ht ξ]
    obtain ⟨hst, hit, ha⟩ := hk
    unfold PhaseProtocol
    omega

lemma blockTrace_protocol (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ) (hΔ : 0 < p.Δ)
    (ξ : ℕ → p.Ω) (n : ℕ) : PhaseProtocol n
      (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) (initialState p) ξ n).1 := by
  induction n with
  | zero => exact initial_phaseProtocol p
  | succ n ih =>
    rw [StochasticGeneralized.blockTrace_succ]
    dsimp only [StochasticGeneralized.blockAdvance]
    exact phaseNext_protocol p I g hL0 hL1 hR hσ _
      (blockTrace_wellFormed p I g hL0 hL1 hR hσ ξ (initialState p) (initialState_wellFormed p hR hΔ) n)
      (blockTrace_phaseEntry p I g hL0 hL1 hR hσ ξ (initialState p)
        (initialState_wellFormed p hR hΔ) (initialState_phaseEntry p) n) n ih _

lemma PhaseProtocol.cycle (p : Public) (K : ℕ) {s : State p.E} (hs : PhaseProtocol (4 * K) s) :
    s.stage = 4 ∨ s.iteration = K ∧ s.stage = 0 := by
  obtain ⟨hst, hit, ha⟩ := hs
  by_cases h4 : s.stage = 4
  · exact Or.inl h4
  · have hh := ha (by omega)
    right
    omega

lemma PhaseProtocol.iteration_le {E : Type*} {s : State E} {k : ℕ} (hs : PhaseProtocol k s) :
    s.iteration ≤ k := by
  have hh := hs.2.1
  omega


lemma phaseNext_metadata (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (s : State p.E) (hw : WellFormed s) (he : PhaseEntry s)
    (ξ : Fin (phaseCost p s) → p.Ω) :
    ((phaseNext p I g (phaseCost p s) s ξ).A, (phaseNext p I g (phaseCost p s) s ξ).iteration) =
      if s.stage = 3 then (s.A + stepWeight p s, s.iteration + 1) else (s.A, s.iteration) := by
  by_cases h0 : s.stage = 0
  · have hcost : phaseCost p s = pilotSize p s.iteration := by simp [phaseCost, h0]
    have ht := phaseNext_first_pilot p I g hL0 hL1 hR hσ s hw h0
      (he.1 (Or.inl h0)).1 (he.1 (Or.inl h0)).2
    rw [← hcost] at ht
    rw [ht ξ]
    simp [h0]
  by_cases h1 : s.stage = 1
  · have hcost : phaseCost p s = pilotSize p s.iteration := by simp [phaseCost, h1]
    have ht := phaseNext_second_pilot p I g hL0 hL1 hR hσ s hw h1
      (he.1 (Or.inr h1)).1 (he.1 (Or.inr h1)).2
    rw [← hcost] at ht
    rw [ht ξ]
    simp [h1]
  by_cases h2 : s.stage = 2
  · have hcost : phaseCost p s = batchSize p s.iteration (stepWeight p s) := by simp [phaseCost, h2]
    have ht := phaseNext_evaluation p I g hL0 hL1 hR hσ s hw h2 (he.2 h2).1 (he.2 h2).2
    rw [← hcost] at ht
    rw [ht ξ]
    simp [h2]
  have hcost : phaseCost p s = 1 := by simp [phaseCost, h0, h1, h2]
  by_cases h3 : s.stage = 3
  · have ht := phaseNext_prox p I g hL1 hR s hw h3
    rw [← hcost] at ht
    rw [ht ξ]
    simp [update, h3]
  · have ht := phaseNext_frozen p I g s (by omega)
    rw [← hcost] at ht
    rw [ht ξ]
    simp [h3]



lemma phaseNext_growthPotential (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (h : CompositeGeneralized.Hyp I.f I.ψ I.grad I.Q I.prox p.L0 p.L1)
    (hR : 0 < p.R) (hσ : 0 ≤ p.σ) (xs : p.E) (hxs : xs ∈ I.Q)
    (hmin : IsMinOn (fun u => I.f u + I.ψ u) I.Q xs) {G : ℝ} (hG : ‖I.grad xs‖ ≤ G)
    (s : State p.E) (hw : WellFormed s) (he : PhaseEntry s) (hs : PhaseControl p I xs s)
    (ξ : Fin (phaseCost p s) → p.Ω) :
    let δ := 1 / (4 * Real.sqrt (3 * (p.L0 + 192 * p.L1 * p.σ + p.L1 * G)))
    let ρ := 1 / (3 + 192 * p.L1 * p.R)
    CompositeGeneralized.potential δ ρ (Real.sqrt s.A) +
        3 / 4 * ((phaseNext p I g (phaseCost p s) s ξ).iteration : ℝ) ≤
      CompositeGeneralized.potential δ ρ (Real.sqrt (phaseNext p I g (phaseCost p s) s ξ).A) +
        3 / 4 * (s.iteration : ℝ) := by
  dsimp only
  let δ := 1 / (4 * Real.sqrt (3 * (p.L0 + 192 * p.L1 * p.σ + p.L1 * G)))
  let ρ := 1 / (3 + 192 * p.L1 * p.R)
  change CompositeGeneralized.potential δ ρ (Real.sqrt s.A) + _ ≤
    CompositeGeneralized.potential δ ρ (Real.sqrt (phaseNext p I g (phaseCost p s) s ξ).A) + _
  have hm := phaseNext_metadata p I g h.hL0 h.hL1 hR hσ s hw he ξ
  by_cases h3 : s.stage = 3
  · simp only [h3, ite_true] at hm
    have hA := congrArg Prod.fst hm
    have hit := congrArg Prod.snd hm
    dsimp only at hA hit
    rw [hA, hit, Nat.cast_add, Nat.cast_one]
    have hL0 := h.hL0
    have hL1 := h.hL1
    have hG0 : 0 ≤ G := (norm_nonneg _).trans hG
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hρ : 0 < ρ := by dsimp [ρ]; positivity
    have hρ3 : ρ ≤ 1 / 3 := by
      dsimp only [ρ]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [mul_nonneg hL1 hR.le]
    have ha := stepWeight_pos p hL1 hR hw (Or.inr (Or.inr h3))
    have hg : Real.sqrt s.A + δ ≤ Real.sqrt (s.A + stepWeight p s) ∨
        (1 + ρ) * Real.sqrt s.A ≤ Real.sqrt (s.A + stepWeight p s) :=
      controlled_sqrt_growth p I h hR hσ xs hxs hmin hG s hs (Or.inr (Or.inr h3))
    have hp := CompositeGeneralized.potential_step hδ hρ hρ3 (Real.sqrt_pos.mpr hw.1)
      (Real.sqrt_le_sqrt (by linarith : s.A ≤ s.A + stepWeight p s)) hg
    linarith
  · simp only [h3, ite_false] at hm
    have hA := congrArg Prod.fst hm
    have hit := congrArg Prod.snd hm
    dsimp only at hA hit
    rw [hA, hit]



lemma goodEvents_growthPotential (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (h : CompositeGeneralized.Hyp I.f I.ψ I.grad I.Q I.prox p.L0 p.L1) (hR : 0 < p.R)
    (hσ : 0 ≤ p.σ) (hα : 1 < p.α) (hα2 : p.α ≤ 2) (hΔ : 0 < p.Δ) (hε : 0 < p.ε)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1)
    (xs : p.E) (hxs : xs ∈ I.Q) (hmin : IsMinOn (fun u => I.f u + I.ψ u) I.Q xs)
    (hx : p.x0 ∈ I.Q) (hd : ‖p.x0 - xs‖ ≤ p.R)
    (hgap : I.f p.x0 + I.ψ p.x0 - (I.f xs + I.ψ xs) ≤ p.Δ)
    {G : ℝ} (hG : ‖I.grad xs‖ ≤ G)
    (ξ : ℕ → p.Ω) (n : ℕ) (hg : GoodEvents p I μ g xs n ξ) (j : ℕ) (hj : j ≤ n) :
    let δ := 1 / (4 * Real.sqrt (3 * (p.L0 + 192 * p.L1 * p.σ + p.L1 * G)))
    let ρ := 1 / (3 + 192 * p.L1 * p.R)
    let s := (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) (initialState p) ξ j).1
    CompositeGeneralized.potential δ ρ (Real.sqrt (p.R ^ 2 / (4 * p.Δ))) +
      3 / 4 * (s.iteration : ℝ) ≤ CompositeGeneralized.potential δ ρ (Real.sqrt s.A) := by
  dsimp only
  revert hj
  induction j with
  | zero =>
    intro hj
    simp only [StochasticGeneralized.blockTrace_zero, initialState, Nat.cast_zero, mul_zero, add_zero, le_refl]
  | succ j ih =>
    intro hj
    have hi := ih (by omega)
    have hc := (goodEvents_phaseControl_ledger p I μ ho h hR hσ hα hα2 hΔ hε hδ hδ1
      xs hxs hmin hx hd hgap ξ n hg j (by omega)).1
    have hw := blockTrace_wellFormed p I g h.hL0 h.hL1 hR hσ ξ (initialState p)
      (initialState_wellFormed p hR hΔ) j
    have he := blockTrace_phaseEntry p I g h.hL0 h.hL1 hR hσ ξ (initialState p)
      (initialState_wellFormed p hR hΔ) (initialState_phaseEntry p) j
    have ht := phaseNext_growthPotential p I g h hR hσ xs hxs hmin hG _ hw he hc
      (fun i => (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) (initialState p) ξ j).2 i)
    dsimp only at ht
    rw [StochasticGeneralized.blockTrace_succ]
    dsimp only [StochasticGeneralized.blockAdvance]
    linarith


lemma update_stopped_weight (p : Public) (s : State p.E) (v : p.E)
    (hs : s.stage = 4 → 4 * p.R ^ 2 / p.ε ≤ s.A) :
    (update p s v).stage = 4 → 4 * p.R ^ 2 / p.ε ≤ (update p s v).A := by
  unfold update
  split_ifs <;> simp_all

lemma rawAdvance_stopped_weight (p : Public) (I : Instance p) (g : p.E → p.Ω → p.E)
    (ξ : ℕ → p.Ω) (n call : ℕ) (s : State p.E)
    (hs : s.stage = 4 → 4 * p.R ^ 2 / p.ε ≤ s.A) :
    (rawAdvance p I g ξ n call s).stage = 4 →
      4 * p.R ^ 2 / p.ε ≤ (rawAdvance p I g ξ n call s).A := by
  induction n generalizing call s with
  | zero => exact hs
  | succ n ih =>
    exact ih (call + 1) _ (update_stopped_weight p s _ hs)

lemma blockTrace_stopped_weight (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (hΔ : 0 < p.Δ) (hεΔ : p.ε < p.Δ) (ξ : ℕ → p.Ω) (n : ℕ) :
    (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) (initialState p) ξ n).1.stage = 4 →
      4 * p.R ^ 2 / p.ε ≤
        (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) (initialState p) ξ n).1.A := by
  rw [blockTrace_eq_rawAdvance p I g hL0 hL1 hR hσ ξ (initialState p)
    (initialState_wellFormed p hR hΔ) n]
  apply rawAdvance_stopped_weight
  simp [initialState, not_le.mpr hεΔ]

lemma goodEvents_stopped (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (h : CompositeGeneralized.Hyp I.f I.ψ I.grad I.Q I.prox p.L0 p.L1) (hR : 0 < p.R)
    (hσ : 0 ≤ p.σ) (hα : 1 < p.α) (hα2 : p.α ≤ 2) (hΔ : 0 < p.Δ) (hε : 0 < p.ε)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1)
    (xs : p.E) (hxs : xs ∈ I.Q) (hmin : IsMinOn (fun u => I.f u + I.ψ u) I.Q xs)
    (hx : p.x0 ∈ I.Q) (hd : ‖p.x0 - xs‖ ≤ p.R)
    (hgap : I.f p.x0 + I.ψ p.x0 - (I.f xs + I.ψ xs) ≤ p.Δ)
    {G : ℝ} (hG : ‖I.grad xs‖ ≤ G) (ξ : ℕ → p.Ω) (K : ℕ)
    (hg : GoodEvents p I μ g xs (4 * K) ξ)
    (hK : 20 * Real.sqrt ((p.L0 + 192 * p.L1 * p.σ + p.L1 * G) * p.R ^ 2 / p.ε) +
      (6 + 256 * p.L1 * p.R) * Real.log (2 + (3 + 192 * p.L1 * p.R) *
        Real.sqrt (p.Δ / (p.L0 * p.R ^ 2))) ≤ K) :
    (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) (initialState p) ξ (4 * K)).1.stage = 4 := by
  have hp := blockTrace_protocol p I g h.hL0 h.hL1 hR hσ hΔ ξ (4 * K)
  rcases hp.cycle p K with h4 | ⟨hit, hst⟩
  · exact h4
  · have hpot := goodEvents_growthPotential p I μ ho h hR hσ hα hα2 hΔ hε hδ hδ1
      xs hxs hmin hx hd hgap hG ξ (4 * K) hg (4 * K) le_rfl
    dsimp only at hpot
    rw [hit] at hpot
    have hw := blockTrace_wellFormed p I g h.hL0 h.hL1 hR hσ ξ (initialState p)
      (initialState_wellFormed p hR hΔ) (4 * K)
    have hMs : p.L0 ≤ p.L0 + 192 * p.L1 * p.σ + p.L1 * G := by
      have hG0 := (norm_nonneg _).trans hG
      nlinarith [mul_nonneg h.hL1 hσ, mul_nonneg h.hL1 hG0]
    have ht := CompositeGeneralized.potential_threshold h.hL0 h.hL1 hR hΔ hε hMs hw.1 hpot hK
    have ha := blockTrace_active_weight_bound p I g h.hL0 h.hL1 hR hσ hΔ hε ξ (4 * K)
      (by rw [hst]; norm_num)
    exact False.elim ((not_le_of_gt ha) ht)


lemma goodEvents_phase_accuracy (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (h : CompositeGeneralized.Hyp I.f I.ψ I.grad I.Q I.prox p.L0 p.L1) (hR : 0 < p.R)
    (hσ : 0 ≤ p.σ) (hα : 1 < p.α) (hα2 : p.α ≤ 2) (hΔ : 0 < p.Δ) (hε : 0 < p.ε)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1)
    (xs : p.E) (hxs : xs ∈ I.Q) (hmin : IsMinOn (fun u => I.f u + I.ψ u) I.Q xs)
    (hx : p.x0 ∈ I.Q) (hd : ‖p.x0 - xs‖ ≤ p.R)
    (hgap : I.f p.x0 + I.ψ p.x0 - (I.f xs + I.ψ xs) ≤ p.Δ)
    {G : ℝ} (hG : ‖I.grad xs‖ ≤ G) (ξ : ℕ → p.Ω) (K : ℕ)
    (hg : GoodEvents p I μ g xs (4 * K) ξ)
    (hK : 20 * Real.sqrt ((p.L0 + 192 * p.L1 * p.σ + p.L1 * G) * p.R ^ 2 / p.ε) +
      (6 + 256 * p.L1 * p.R) * Real.log (2 + (3 + 192 * p.L1 * p.R) *
        Real.sqrt (p.Δ / (p.L0 * p.R ^ 2))) ≤ K) :
    let s := (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) (initialState p) ξ (4 * K)).1
    s.x ∈ I.Q ∧ I.f s.x + I.ψ s.x - (I.f xs + I.ψ xs) ≤ p.ε := by
  let s := (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) (initialState p) ξ (4 * K)).1
  change s.x ∈ I.Q ∧ I.f s.x + I.ψ s.x - (I.f xs + I.ψ xs) ≤ p.ε
  have hc := (goodEvents_phaseControl_ledger p I μ ho h hR hσ hα hα2 hΔ hε hδ hδ1
    xs hxs hmin hx hd hgap ξ (4 * K) hg (4 * K) le_rfl).1.1
  refine ⟨hc.2.1, ?_⟩
  by_cases hf : p.Δ ≤ p.ε
  · have hstate : s = initialState p := by
      dsimp only [s]
      rw [blockTrace_eq_rawAdvance p I g h.hL0 h.hL1 hR hσ ξ (initialState p)
        (initialState_wellFormed p hR hΔ)]
      exact rawAdvance_frozen p I g ξ (initialState p) (by simp [initialState, hf]) _ 0
    rw [hstate]
    exact hgap.trans hf
  · have ht := goodEvents_stopped p I μ ho h hR hσ hα hα2 hΔ hε hδ hδ1
      xs hxs hmin hx hd hgap hG ξ K hg hK
    have hA : 4 * p.R ^ 2 / p.ε ≤ s.A :=
      blockTrace_stopped_weight p I g h.hL0 h.hL1 hR hσ hΔ (lt_of_not_ge hf) ξ (4 * K) ht
    have hg0 : 0 ≤ I.f s.x + I.ψ s.x - (I.f xs + I.ψ xs) := sub_nonneg.mpr (hmin hc.2.1)
    have hAg : s.A * (I.f s.x + I.ψ s.x - (I.f xs + I.ψ xs)) ≤ 4 * p.R ^ 2 := by
      have hh := hc.2.2.2.1
      change s.A * _ + ‖s.z - xs‖ ^ 2 / 2 ≤ (2 * p.R) ^ 2 at hh
      nlinarith [sq_nonneg ‖s.z - xs‖]
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < 4 * p.R ^ 2 / p.ε)).mp
    calc
      _ ≤ s.A * (I.f s.x + I.ψ s.x - (I.f xs + I.ψ xs)) := mul_le_mul_of_nonneg_right hA hg0
      _ ≤ 4 * p.R ^ 2 := hAg
      _ = (4 * p.R ^ 2 / p.ε) * p.ε := by field_simp

lemma rawAdvance_after_stopped_phase (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ) (hΔ : 0 < p.Δ)
    (ξ : ℕ → p.Ω) (n B : ℕ)
    (hc : StochasticGeneralized.blockCalls (phaseCost p) (phaseNext p I g) (initialState p) ξ n ≤ B)
    (hs : (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) (initialState p) ξ n).1.stage = 4) :
    rawAdvance p I g ξ B 0 (initialState p) =
      (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) (initialState p) ξ n).1 := by
  have hr := blockTrace_eq_rawAdvance p I g hL0 hL1 hR hσ ξ (initialState p)
    (initialState_wellFormed p hR hΔ) n
  rw [← Nat.add_sub_of_le hc, rawAdvance_add, Nat.zero_add, ← hr]
  exact rawAdvance_frozen p I g ξ _ (by omega) _ _


end OracleTemplate.StochasticCompositeGeneralized
