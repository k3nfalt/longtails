import LongTails.Proofs.BirchResourceEuclidean
import LongTails.Proofs.BirchResourceAtomic
import LongTails.Proofs.BirchResourceLabels

namespace LongTails.Proofs.BirchResourceTimedTrace

open Finset MeasureTheory OracleTemplate
open OracleTemplate.Rennala (Point Instance)
open OracleTemplate.BirchSgd (gradientOracle main_theorem vertex_measurable)
open LongTails.Setups.BirchSgd
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Proofs.BirchResourceForest
open LongTails.Proofs.BirchResourceReplay
open LongTails.Proofs.BirchResourceEuclidean
open LongTails.Proofs.BirchResourceAtomic
open LongTails.Proofs.BirchResourceDispatch
open LongTails.Proofs.BirchResourceLabels
open LongTails.Proofs.BirchResourcePlans
open LongTails.Setups

def history {d : ℕ} {Ω : Type} (s : Forest) (γ : ℝ) (x₀ : Point d)
    (g : Point d → Ω → Point d) (raw : ℕ → ℕ) (ξ : ℕ → Ω) (v : ℕ) : Point d :=
  (tree s).vertex γ x₀ g (fun j => ξ (padded raw j)) v

lemma private_update {d : ℕ} {Ω : Type} (s : Forest) (B : ℕ) (hs : s.Valid B)
    (γ : ℝ) (x₀ : Point d) (g : Point d → Ω → Point d) (raw : ℕ → ℕ)
    (ξ : ℕ → Ω) (k : ℕ) :
    history s γ x₀ g raw ξ (2 * k + 1) = history s γ x₀ g raw ξ (s.head k) -
      γ • g (history s γ x₀ g raw ξ (s.saved k)) (ξ (2 * raw k)) := by
  simpa only [history, padded_even] using
    private_value s B hs γ x₀ g (fun j => ξ (padded raw j)) k

lemma global_update {d : ℕ} {Ω : Type} (s : Forest) (B : ℕ) (hs : s.Valid B)
    (γ : ℝ) (x₀ : Point d) (g : Point d → Ω → Point d) (raw : ℕ → ℕ)
    (ξ : ℕ → Ω) (k : ℕ) :
    history s γ x₀ g raw ξ (branch (k + 1)) = history s γ x₀ g raw ξ (branch k) -
      γ • g (history s γ x₀ g raw ξ (s.saved k)) (ξ (2 * raw k)) := by
  simpa only [history, branch, padded_even] using
    global_value s B hs γ x₀ g (fun j => ξ (padded raw j)) k

lemma packet_point {Packet Pool : Type*} [DecidableEq Packet] {d : ℕ} {Ω : Type}
    (packet : ℕ → Packet) (dsp : Dispatch Pool) (B : ℕ) (γ : ℝ) (x₀ : Point d)
    (g : Point d → Ω → Point d) (raw : ℕ → ℕ) (ξ : ℕ → Ω) (i k : ℕ)
    (hphase : phaseRoot B i = phaseRoot B k) (hp : packet i = packet k) :
    let s := packetForest packet dsp B
    history s γ x₀ g raw ξ (s.saved i) = history s γ x₀ g raw ξ (s.saved k) := by
  dsimp only
  rw [packet_saved_eq packet dsp B i k hphase hp]

lemma history_stationary {Ω : Type} [MeasurableSpace Ω] (p : Params) (s : Forest)
    (hs : s.Valid (blockSize p)) (hL : 0 < p.L) (hσ : 0 ≤ p.σ) (hε : 0 < p.ε) (hΔ : 0 ≤ p.Δ)
    (I : Instance p.d) (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (g : Point p.d → Ω → Point p.d)
    (hsmooth : SmoothObjective I.f p.L) (hlower : LowerBounded I.f I.lower)
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point p.d) Ω
      (μ : Measure Ω) I.f g p.σ)
    (hiid : IID (fun j (ξ : ℕ → Ω) => ξ j) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (hgap : I.f p.x0 - I.lower ≤ p.Δ) (raw : ℕ → ℕ) (hraw : Function.Injective raw) :
    let q := forestParams p s
    let γ := (publicInput q).gamma
    let K := phases p * blockSize p
    (1 / (K : ℝ) * ∑ k ∈ range K, ∫ ξ, ‖gradient I.f
      (history s γ p.x0 g raw ξ (branch k))‖ ^ 2 ∂(P : Measure (ℕ → Ω))) ≤ p.ε := by
  dsimp only
  let q := forestParams p s
  let γ := (publicInput q).gamma
  let K := phases p * blockSize p
  have hq := forestParams_valid p s hs hL hσ hε hΔ
  have hB : 0 < blockSize p := by unfold blockSize; omega
  have hR : q.R + 1 ≤ (blockSize p : ℝ) := by
    change (((blockSize p - 1 : ℕ) : ℝ) + 1) ≤ _
    rw [Nat.cast_sub (by omega : 1 ≤ blockSize p), Nat.cast_one, sub_add_cancel]
  have hbound := tuned_edges q hq hR _ hgap
  have hmain := (main_theorem I.f p.L p.σ p.ε q.R I.lower p.x0 (tree s) branch μ P g
    hL hσ hε hq.2.2.2.2.1 hsmooth hlower hg hiid.marginal
    (tree_wellFormed s _ hs) (main_branch s)
    (iid_independent s _ hs γ p.x0 g hg.measurable μ P hiid)
    (contained s _ hs) (distance s _ hs) K hbound).2
  convert hmain using 2
  apply sum_congr rfl
  intro k _
  have hv := vertex_measurable (tree s) γ p.x0 g hg.measurable (branch k)
  have hlip : LipschitzWith ⟨p.L, hL.le⟩ (gradient I.f) :=
    LipschitzWith.of_dist_le_mul (fun x y => by
      rw [dist_eq_norm, dist_eq_norm]
      change ‖gradient I.f x - gradient I.f y‖ ≤ p.L * ‖x - y‖
      exact hsmooth.2 x y)
  have hf : Measurable (fun ξ => ‖gradient I.f ((tree s).vertex γ p.x0 g ξ (branch k))‖ ^ 2) :=
    ((hlip.continuous.measurable.comp hv).norm).pow_const 2
  exact integral_reindex μ P hiid (padded raw) (padded_injective raw hraw) _ hf

lemma finish_before_deadline {Pool : Type*} (dsp : Dispatch Pool) (B H : ℕ)
    (hB : 0 < B) (T : ℝ) (hT : 0 ≤ T) (hphase : ∀ j < B, 0 ≤ dsp.launch j ∧ dsp.finish j ≤ T)
    (k : ℕ) (hk : k < H * B) :
    (k / B : ℕ) * T ≤ (repeated dsp B T).launch k ∧ (repeated dsp B T).finish k ≤ H * T := by
  have h := repeated_window dsp B hB T hphase k
  have he : k / B < H := (Nat.div_lt_iff_lt_mul hB).2 hk
  exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr (Nat.succ_le_of_lt he)) hT)⟩

lemma routed_timed {Route Device : Type*} [Fintype Route] [Fintype Device]
    [DecidableEq Device] {Ω : Type} [MeasurableSpace Ω] (p : Params)
    (profile : BirchRoutedTime.Profile Route Device) (J : ℕ) (hJ : 0 < J)
    (hp : profile.Valid J) (t : ℝ) (ht : 0 < t) (rate : Route → ℝ)
    (hrate : BirchRoutedTime.FeasibleRate profile t rate) (hr : 0 < ∑ r, rate r)
    (hL : 0 < p.L) (hσ : 0 ≤ p.σ) (hε : 0 < p.ε) (hΔ : 0 ≤ p.Δ)
    (I : Instance p.d) (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (g : Point p.d → Ω → Point p.d)
    (hsmooth : SmoothObjective I.f p.L) (hlower : LowerBounded I.f I.lower)
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point p.d) Ω
      (μ : Measure Ω) I.f g p.σ)
    (hiid : IID (fun j (ξ : ℕ → Ω) => ξ j) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (hgap : I.f p.x0 - I.lower ≤ p.Δ) :
    let B := blockSize p
    let H := phases p
    let T := 2 * (J : ℝ) * ((J : ℝ) * B / (∑ r, rate r)) + (4 * J + 2) * t
    ∃ jobs : ℕ → BirchRoutedTime.Job Route,
      BirchRoutedTime.Legal profile jobs (range B) ∧
      let dsp := repeated (routed profile jobs id) B T
      let s := localForest dsp B
      let γ := (publicInput (forestParams p s)).gamma
      (∀ k < H * B, (k / B : ℕ) * T ≤ dsp.launch k ∧ dsp.finish k ≤ H * T) ∧
      (1 / ((H * B : ℕ) : ℝ) * ∑ k ∈ range (H * B), ∫ ξ, ‖gradient I.f
        (history s γ p.x0 g id ξ (branch k))‖ ^ 2 ∂(P : Measure (ℕ → Ω))) ≤ p.ε := by
  let B := blockSize p
  let T := 2 * (J : ℝ) * ((J : ℝ) * B / (∑ r, rate r)) + (4 * J + 2) * t
  have hB : 0 < B := by dsimp only [B]; unfold blockSize; omega
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  obtain ⟨jobs, hlegal, hphase⟩ := routed_plan profile J B hJ hp t ht rate hrate hr id
  let dsp := repeated (routed profile jobs id) B T
  let s := localForest dsp B
  exact ⟨jobs, hlegal, fun k hk => finish_before_deadline (routed profile jobs id) B
    (phases p) hB T hT hphase k hk,
    history_stationary p s (localForest_valid dsp B hB) hL hσ hε hΔ I μ P g
      hsmooth hlower hg hiid hgap id Function.injective_id⟩

lemma power_timed {Mode Device : Type*} [Fintype Mode] [DecidableEq Mode]
    {Ω : Type} [MeasurableSpace Ω] (p : Params) (profile : BirchPowerTime.Profile Mode Device)
    (hp : profile.Valid) (t : ℝ) (ht : 0 < t) (u : ℕ)
    (hr : 0 < BirchPowerTime.envelope profile t u)
    (hL : 0 < p.L) (hσ : 0 ≤ p.σ) (hε : 0 < p.ε) (hΔ : 0 ≤ p.Δ)
    (I : Instance p.d) (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (g : Point p.d → Ω → Point p.d)
    (hsmooth : SmoothObjective I.f p.L) (hlower : LowerBounded I.f I.lower)
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point p.d) Ω
      (μ : Measure Ω) I.f g p.σ)
    (hiid : IID (fun j (ξ : ℕ → Ω) => ξ j) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (hgap : I.f p.x0 - I.lower ≤ p.Δ) :
    let B := blockSize p
    let H := phases p
    let T := t + (B : ℝ) / BirchPowerTime.envelope profile t u
    let scheduled := LongTails.Proofs.BirchPowerTime.scheduled profile
    let samples := fun j => profile.samples (scheduled j).mode
    ∃ (jobs : Finset (Σ _ : Mode, ℕ)) (pick : Fin B ↪ {j // j ∈ slots jobs samples}),
      BirchPowerTime.Legal profile scheduled jobs ∧
      B ≤ (∑ j ∈ jobs, samples j) ∧ (∑ j ∈ jobs, samples j) ≤ B + u ∧
      let hB : 0 < B := by dsimp only [B]; unfold blockSize; omega
      let packet := fun k : ℕ => (pick ⟨k % B, Nat.mod_lt _ hB⟩).val.1
      let dsp := repeated (power profile (scheduled ∘ packet)) B T
      let s := packetForest (fun k => (k / B, packet k)) dsp B
      let raw := issued hB (paidLabel jobs samples pick)
      let γ := (publicInput (forestParams p s)).gamma
      (∀ k < H * B, (k / B : ℕ) * T ≤ dsp.launch k ∧ dsp.finish k ≤ H * T ∧ raw k < H * (∑ j ∈ jobs, samples j)) ∧
      (1 / ((H * B : ℕ) : ℝ) * ∑ k ∈ range (H * B), ∫ ξ, ‖gradient I.f
        (history s γ p.x0 g raw ξ (branch k))‖ ^ 2 ∂(P : Measure (ℕ → Ω))) ≤ p.ε := by
  let B := blockSize p
  let H := phases p
  let T := t + (B : ℝ) / BirchPowerTime.envelope profile t u
  let scheduled := LongTails.Proofs.BirchPowerTime.scheduled profile
  let samples := fun j => profile.samples (scheduled j).mode
  have hB : 0 < B := by dsimp only [B]; unfold blockSize; omega
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  obtain ⟨jobs, pick, hlegal, hlo, hhi, hphase⟩ := power_plan profile hp t u B hB hr
  let packet := fun k : ℕ => (pick ⟨k % B, Nat.mod_lt _ hB⟩).val.1
  let dsp := repeated (power profile (scheduled ∘ packet)) B T
  let s := packetForest (fun k => (k / B, packet k)) dsp B
  let raw := issued hB (paidLabel jobs samples pick)
  refine ⟨jobs, pick, hlegal, hlo, hhi, ?_, ?_⟩
  · intro k hk
    have h := finish_before_deadline (power profile (scheduled ∘ packet)) B H hB T hT hphase k hk
    have he : k / B < H := (Nat.div_lt_iff_lt_mul hB).2 hk
    have hw := (issued_window hB (paidLabel jobs samples pick) k).2
    exact ⟨h.1, h.2, hw.trans_le (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt he))⟩
  · exact history_stationary p s (packetForest_valid _ dsp B hB) hL hσ hε hΔ I μ P g
      hsmooth hlower hg hiid hgap raw (issued_injective hB _)

end LongTails.Proofs.BirchResourceTimedTrace
