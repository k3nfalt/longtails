import LongTails.Proofs.BirchResourceAdaptiveLower
import LongTails.Proofs.BirchRoutedBuffered
import LongTails.Proofs.BirchPowerTime

namespace LongTails.Proofs.BirchResourceLowerWindow

open Finset Set MeasureTheory
open LongTails.Setups
open LongTails.Proofs.BirchResourceLower
open LongTails.Proofs.BirchResourceAdaptiveLower
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)

def routedPrices {Route Device : Type*} [Fintype Route] [DecidableEq Device]
    (p : BirchRoutedTime.Profile Route Device) (b : ℝ) : Set ℝ :=
  {c | ∃ t > 0, ∃ x : Route → ℝ, BirchRoutedTime.FeasibleRate p t x ∧
    0 < ∑ r, x r ∧ c = t + b / (∑ r, x r)}

def powerPrices {Mode Device : Type*} [Fintype Mode]
    (p : BirchPowerTime.Profile Mode Device) (u : ℕ) (b : ℝ) : Set ℝ :=
  {c | ∃ t > 0, 0 < BirchPowerTime.envelope p t u ∧ c = t + b / BirchPowerTime.envelope p t u}

lemma routed_price_lower {Route Device : Type*} [Fintype Route] [DecidableEq Device]
    (p : BirchRoutedTime.Profile Route Device) (b : ℝ) (hb : 0 ≤ b) :
    BddBelow (routedPrices p b) := by
  refine ⟨0, ?_⟩
  rintro c ⟨t, ht, x, _, hx, rfl⟩
  exact add_nonneg ht.le (div_nonneg hb hx.le)

lemma power_price_lower {Mode Device : Type*} [Fintype Mode]
    (p : BirchPowerTime.Profile Mode Device) (u : ℕ) (b : ℝ) (hb : 0 ≤ b) :
    BddBelow (powerPrices p u b) := by
  refine ⟨0, ?_⟩
  rintro c ⟨t, ht, hr, rfl⟩
  exact add_nonneg ht.le (div_nonneg hb hr.le)

lemma routed_short_window {Route Device Job : Type*} [Fintype Route] [DecidableEq Route]
    [DecidableEq Device] (p : BirchRoutedTime.Profile Route Device) (J : ℕ)
    (hp : p.Valid J) (jobs : Job → BirchRoutedTime.BufferedJob Route Device) (s : Finset Job)
    (q : ℝ) (hq : 0 < q) (t : ℝ) (ht : 0 < t) (htΦ : t = sInf (routedPrices p (1 / q)) / 9)
    (hl : BirchRoutedTime.BufferedLegal p jobs s)
    (hwindow : ∀ j ∈ s, ∀ i ∈ p.path (jobs j).route,
      0 ≤ (jobs j).start i ∧ (jobs j).start i + p.duration i ≤ t) :
    (s.card : ℝ) ≤ 1 / (8 * q) := by
  by_cases hz : s.card = 0
  · simp [hz, hq.le]
  let nominal := fun j => BirchRoutedTime.Job.mk (jobs j).route 0
  let x := LongTails.Proofs.BirchRoutedTime.windowRate nominal s t
  obtain ⟨hx, hsum⟩ := LongTails.Proofs.BirchRoutedTime.buffered_window_rate p J hp jobs s t ht hl hwindow
  have hsum' : (∑ r, x r) = (s.card : ℝ) / t := hsum
  have hr : 0 < ∑ r, x r := by
    rw [hsum']
    exact div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz)) ht
  have hprice : t + (1 / q) / (∑ r, x r) ∈ routedPrices p (1 / q) :=
    ⟨t, ht, x, hx, hr, rfl⟩
  have h := fast_probability_from_rate q (∑ r, x r) t _ hq hr.le htΦ
    (csInf_le (routed_price_lower p _ (by positivity)) hprice)
  rw [hsum', show t * ((s.card : ℝ) / t) = s.card by field_simp] at h
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * q)).2
  nlinarith only [h]

lemma power_short_window {Mode Device Job : Type*} [Fintype Mode]
    (p : BirchPowerTime.Profile Mode Device) (hp : p.Valid)
    (jobs : Job → BirchPowerTime.Job Mode) (s : Finset Job) (u : ℕ)
    (q : ℝ) (hq : 0 < q) (t : ℝ) (ht : 0 < t)
    (htΦ : t = sInf (powerPrices p u (1 / q)) / 9)
    (hl : BirchPowerTime.Legal p jobs s)
    (hwindow : ∀ j ∈ s, 0 ≤ (jobs j).launch ∧ (jobs j).launch + p.duration (jobs j).mode ≤ t)
    (hsize : ∀ j ∈ s, p.samples (jobs j).mode ≤ u) :
    (∑ j ∈ s, (p.samples (jobs j).mode : ℝ)) ≤ 1 / (8 * q) := by
  let r := BirchPowerTime.envelope p t u
  have hcap := LongTails.Proofs.BirchPowerTime.window_capacity p hp jobs s t u ht.le hl hwindow hsize
  by_cases hr : 0 < r
  · have hprice : t + (1 / q) / r ∈ powerPrices p u (1 / q) := ⟨t, ht, hr, rfl⟩
    have h := fast_probability_from_rate q r t _ hq hr.le htΦ
      (csInf_le (power_price_lower p u _ (by positivity)) hprice)
    refine hcap.trans ?_
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * q)).2
    nlinarith only [h]
  · refine hcap.trans ?_
    exact (mul_nonpos_of_nonneg_of_nonpos ht.le (le_of_not_gt hr)).trans (by positivity)

lemma adaptive_count_bound {Ω : Type*} [MeasurableSpace Ω] (μ : ProbabilityMeasure Ω)
    (P : ProbabilityMeasure (ℕ → Ω)) (hiid : IID (fun i (ξ : ℕ → Ω) => ξ i)
      (μ : Measure Ω) (P : Measure (ℕ → Ω))) (N : ℕ)
    (eligible : ∀ i, Set (Fin i → Ω)) (coin : Set Ω) (fast : Set (ℕ → Ω))
    (he : ∀ i, MeasurableSet (eligible i)) (hc : MeasurableSet coin) (hf : MeasurableSet fast)
    (hp : 0 < (μ : Measure Ω).real coin)
    (hcount : ∀ ξ, (∑ i ∈ range N, (past i ⁻¹' eligible i).indicator (fun _ => (1 : ℝ)) ξ)
      ≤ 1 / (8 * (μ : Measure Ω).real coin))
    (hcover : fast ⊆ ⋃ i ∈ range N, (past i ⁻¹' eligible i) ∩ ((fun ξ => ξ i) ⁻¹' coin)) :
    (P : Measure (ℕ → Ω)).real fast ≤ 1 / 8 := by
  let q := (μ : Measure Ω).real coin
  let R := 1 / (8 * q)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hΦ : (9 : ℝ) ≤ 1 + (1 / q) / R := by
    have hq : 0 < q := hp
    have he : (1 / q) / R = 8 := by
      dsimp only [R]
      field_simp [hq.ne']
    rw [he]
    norm_num
  exact adaptive_reveal μ P hiid N eligible coin fast he hc hf hp hR (by norm_num) hΦ
    (fun ξ => by rw [one_mul]; exact hcount ξ) hcover

end LongTails.Proofs.BirchResourceLowerWindow
