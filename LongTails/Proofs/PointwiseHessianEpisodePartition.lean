import LongTails.Proofs.PointwiseHessianEpisodes
import LongTails.Proofs.PointwiseHessianEvents

open scoped Classical

namespace LongTails.Proofs.PointwiseHessianEpisodePartition

open LongTails.Setups.PointwiseHessianConvex
open LongTails.Algorithms.PointwiseHessianAccelerated
open LongTails.Proofs.PointwiseHessianEpisodes

lemma center_starts_radius {p : Public} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (hs : s.phase = .centerGradient)
    (hn : (update s reply).phase ≠ .finished) : RadiusStart s (update s reply) := by
  refine ⟨Or.inl hs, ?_⟩
  by_cases hg : ‖readGradient reply‖ ≤ gradientThreshold p
  · exact False.elim (hn (by simp [update, hs, hg, finish]))
  · simp [update, hs, hg, startTrial]

lemma failed_hessian_starts_radius {p : Public} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (hs : s.phase = .newtonHessian)
    (hg : ¬ ‖newtonPoint p s.b s.center s.x s.g (readHessian reply) - s.center‖ ≤ 2 * s.r) :
    RadiusStart s (update s reply) := by
  refine ⟨Or.inr hs, ?_⟩
  simp only [update, hs, hg, ite_false, failedTrial]
  split_ifs <;> rfl

noncomputable def innerEnd {p : Public} (s : ℕ → State p) (b : ℕ) : ℕ :=
  if (s (b - 1)).phase = .centerGradient then b - 2 else b - 1

lemma innerEnd_le {p : Public} (s : ℕ → State p) (b : ℕ) : innerEnd s b ≤ b - 1 := by
  unfold innerEnd
  split_ifs <;> omega

lemma start_le_innerEnd {p : Public} (s : ℕ → State p) {a b : ℕ} (hab : a < b)
    (ha : (s a).phase = .newtonHessian) : a ≤ innerEnd s b := by
  unfold innerEnd
  split_ifs with hc
  · have hne : a ≠ b - 1 := by
      intro he
      rw [← he, ha] at hc
      contradiction
    omega
  · omega

lemma center_before_innerEnd {p : Public} (s : ℕ → State p) {b k : ℕ}
    (hk : k ≤ innerEnd s b) (hc : (s k).phase = .centerGradient) (hb : 2 ≤ b) : k + 1 < b := by
  unfold innerEnd at hk
  split_ifs at hk with he
  · omega
  · have hne : k ≠ b - 1 := by
      intro hh
      exact he (by rwa [← hh])
    omega

lemma inner_interval_phase {p : Public} (s : ℕ → State p)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) {N a b : ℕ} (hab : a < b) (hb : b ≤ N + 1)
    (ha : (s a).phase = .newtonHessian)
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k))
    (hn : ∀ k ≤ N, (s k).phase ≠ .finished)
    (hstart : ∀ k, a ≤ k → k + 1 < b → ¬ RadiusStart (s k) (s (k + 1)))
    {k : ℕ} (hak : a ≤ k) (hke : k ≤ innerEnd s b) :
    (s k).phase = .newtonHessian ∨ (s k).phase = .newtonGradient := by
  have hkb := hke.trans (innerEnd_le s b)
  cases hp : (s k).phase with
  | centerGradient =>
    have hb2 : 2 ≤ b := by
      by_contra h
      have he : k = a := by omega
      rw [he, ha] at hp
      contradiction
    have hnext := center_before_innerEnd s hke hp hb2
    have hkN : k < N := by omega
    apply False.elim
    apply hstart k hak hnext
    rw [hs k hkN]
    exact center_starts_radius (s k) (reply k) hp
      (by rw [← hs k hkN]; exact hn (k + 1) (by omega))
  | newtonHessian => exact Or.inl rfl
  | newtonGradient => exact Or.inr rfl
  | finished => exact False.elim (hn k (by omega) hp)

lemma inner_interval_guard {p : Public} (s : ℕ → State p)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) {N a b : ℕ} (hb : b ≤ N + 1)
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k))
    (hstart : ∀ k, a ≤ k → k + 1 < b → ¬ RadiusStart (s k) (s (k + 1)))
    {k : ℕ} (hak : a ≤ k) (hke : k < innerEnd s b) (hp : (s k).phase = .newtonHessian) :
    ‖newtonPoint p (s k).b (s k).center (s k).x (s k).g (readHessian (reply k)) - (s k).center‖ ≤ 2 * (s k).r := by
  have hkb := innerEnd_le s b
  have hkN : k < N := by omega
  by_contra hg
  apply hstart k hak (by omega)
  rw [hs k hkN]
  exact failed_hessian_starts_radius (s k) (reply k) hp hg

lemma inner_tail_gradient_count {p : Public} (s : ℕ → State p) (b : ℕ) :
    (∑ k ∈ Finset.Ico (innerEnd s b) b, if (s k).phase = .newtonGradient then 1 else 0 : ℕ) ≤ 1 := by
  by_cases he : innerEnd s b < b
  · rw [Finset.sum_eq_single_of_mem (innerEnd s b) (Finset.mem_Ico.mpr ⟨le_rfl, he⟩)]
    · split_ifs <;> norm_num
    · intro k hk hne
      have hk' := Finset.mem_Ico.mp hk
      by_cases hc : (s (b - 1)).phase = .centerGradient
      · have he' : innerEnd s b = b - 2 := by simp only [innerEnd, ite_eq_left hc]
        have hkb : k = b - 1 := by omega
        simp only [hkb, hc, reduceCtorEq, ite_false]
      · have he' : innerEnd s b = b - 1 := by simp only [innerEnd, ite_eq_right hc]
        omega
  · simp [Finset.Ico_eq_empty_of_le (le_of_not_gt he)]

lemma interval_gradient_count {p : Public} (s : ℕ → State p) {a b : ℕ}
    (hab : a < b) (ha : (s a).phase = .newtonHessian) :
    (∑ k ∈ Finset.Ico a b, if (s k).phase = .newtonGradient then 1 else 0 : ℕ) ≤
      (∑ k ∈ Finset.Ico a (innerEnd s b), if (s k).phase = .newtonGradient then 1 else 0) + 1 := by
  have he := start_le_innerEnd s hab ha
  have heb : innerEnd s b ≤ b := (innerEnd_le s b).trans (Nat.sub_le _ _)
  rw [← Finset.sum_Ico_consecutive (fun k => if (s k).phase = .newtonGradient then (1 : ℕ) else 0) he heb]
  exact Nat.add_le_add_left (inner_tail_gradient_count s b) _

lemma adjacent_first_le (a : ℕ → ℕ) (N : ℕ) (hm : ∀ k < N, a k ≤ a (k + 1)) : a 0 ≤ a N := by
  induction N with
  | zero => exact le_rfl
  | succ N ih => exact (ih (fun k hk => hm k (by omega))).trans (hm N (by omega))

lemma sum_adjacent_intervals (a : ℕ → ℕ) (f : ℕ → ℝ) (N : ℕ)
    (hm : ∀ k < N, a k ≤ a (k + 1)) :
    (∑ i ∈ Finset.range N, ∑ k ∈ Finset.Ico (a i) (a (i + 1)), f k) =
      ∑ k ∈ Finset.Ico (a 0) (a N), f k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih (fun k hk => hm k (by omega))]
    exact Finset.sum_Ico_consecutive f (adjacent_first_le a N (fun k hk => hm k (by omega)))
      (hm N (by omega))

noncomputable def radiusStartIndices {p : Public} (s : ℕ → State p) (N : ℕ) : Finset ℕ :=
  ((Finset.range N).filter (fun k => RadiusStart (s k) (s (k + 1)))).image Nat.succ

lemma mem_radiusStartIndices {p : Public} (s : ℕ → State p) (N j : ℕ) :
    j ∈ radiusStartIndices s N ↔ ∃ k < N, RadiusStart (s k) (s (k + 1)) ∧ k + 1 = j := by
  simp only [radiusStartIndices, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨k, ⟨hk, hs⟩, he⟩
    exact ⟨k, hk, hs, he⟩
  · rintro ⟨k, hk, hs, he⟩
    exact ⟨k, ⟨hk, hs⟩, he⟩

lemma radiusStartIndices_subset {p : Public} (s : ℕ → State p) (N : ℕ) :
    radiusStartIndices s N ⊆ Finset.range (N + 1) := by
  intro j hj
  obtain ⟨k, hk, _, he⟩ := (mem_radiusStartIndices s N j).mp hj
  exact Finset.mem_range.mpr (by omega)

lemma radiusStartIndices_inner {p : Public} (s : ℕ → State p) (N j : ℕ)
    (hj : j ∈ radiusStartIndices s N) : (s j).phase = .newtonHessian := by
  obtain ⟨k, _, hs, he⟩ := (mem_radiusStartIndices s N j).mp hj
  simpa only [he] using hs.2

lemma radiusStartIndices_pos {p : Public} (s : ℕ → State p) (N j : ℕ)
    (hj : j ∈ radiusStartIndices s N) : 0 < j := by
  obtain ⟨k, _, _, he⟩ := (mem_radiusStartIndices s N j).mp hj
  omega

lemma sum_radiusStartIndices {p : Public} (s : ℕ → State p) (N : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ radiusStartIndices s N, f j) =
      ∑ k ∈ Finset.range N, if RadiusStart (s k) (s (k + 1)) then f (k + 1) else 0 := by
  unfold radiusStartIndices
  rw [Finset.sum_image]
  · rw [Finset.sum_filter]
  · intro a _ b _ he
    exact Nat.succ_injective he


lemma radius_interval_gradient_bound {p : Public} {f : p.E → ℝ} {xs : p.E}
    (s : ℕ → State p) (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) {N a b : ℕ}
    (hab : a < b) (hb : b ≤ N + 1) (ha : (s a).phase = .newtonHessian)
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k))
    (hn : ∀ k ≤ N, (s k).phase ≠ .finished)
    (hstart : ∀ k, a ≤ k → k + 1 < b → ¬ RadiusStart (s k) (s (k + 1)))
    (hi : ∀ k ≤ N, PointwiseHessianExecution.PhaseInvariant f xs (s k))
    (hH : ∀ k < N, (s k).phase = .newtonHessian → reply k = .inr (fderiv ℝ (gradient f) (s k).x))
    (hg : ∀ k < N, (s k).phase = .newtonGradient → reply k = .inl (gradient f (s k).x)) :
    let t := 4 * (1 / (s a).τ) * gradientThreshold p / 3
    let E := 2 * continuationRatio p (s a).τ (s a).r * (s a).r + t
    ((∑ k ∈ Finset.Ico a b, if (s k).phase = .newtonGradient then 1 else 0 : ℕ) : ℝ) ≤
      Real.log ((1 / (s a).τ) / (s a).b) / Real.log (1 + continuationRatio p (s a).τ (s a).r / 8) +
        Real.log (E / t) / Real.log 4 + 3 := by
  dsimp only
  have he := start_le_innerEnd s hab ha
  have heN : innerEnd s b ≤ N := by have := innerEnd_le s b; omega
  have hshift := interior_gradient_count (fun j => s (a + j)) hf hc hM₀ hM₁ hR hε hT
    (fun j => reply (a + j)) (innerEnd s b - a)
    (fun j hj => hi (a + j) (by omega))
    (fun j hj => by simpa only [Nat.add_assoc] using hs (a + j) (by omega))
    (fun j hj => inner_interval_phase s reply hab hb ha hs hn hstart (by omega) (by omega))
    (fun j hj hp => inner_interval_guard s reply hb hs hstart (by omega) (by omega) hp)
    (fun j hj hp => hH (a + j) (by omega) hp)
    (fun j hj hp => hg (a + j) (by omega) hp)
  dsimp only at hshift
  simp only [Nat.add_zero] at hshift
  have htail : ((∑ k ∈ Finset.Ico a b, if (s k).phase = .newtonGradient then 1 else 0 : ℕ) : ℝ) ≤
      ((∑ k ∈ Finset.Ico a (innerEnd s b), if (s k).phase = .newtonGradient then 1 else 0 : ℕ) : ℝ) + 1 := by
    exact_mod_cast interval_gradient_count s hab ha
  rw [Finset.sum_Ico_eq_sum_range (fun k => if (s k).phase = .newtonGradient then (1 : ℕ) else 0)
    a (innerEnd s b)] at htail
  linarith

open LongTails.Proofs.PointwiseHessianEvents

lemma no_start_between_radius_events {p : Public} (s : ℕ → State p) (N i : ℕ)
    (hi : i < (radiusStartIndices s N).card) {k : ℕ}
    (hak : eventIndex (radiusStartIndices s N) (N + 1) i ≤ k)
    (hkb : k + 1 < eventIndex (radiusStartIndices s N) (N + 1) (i + 1)) :
    ¬ RadiusStart (s k) (s (k + 1)) := by
  intro hk
  have hb := eventIndex_le (radiusStartIndices s N) (N + 1) (radiusStartIndices_subset s N) (i + 1)
  have hmem : k + 1 ∈ radiusStartIndices s N :=
    (mem_radiusStartIndices s N (k + 1)).mpr ⟨k, by omega, hk, rfl⟩
  exact no_event_between (radiusStartIndices s N) (N + 1) hi (by omega) hkb hmem

lemma first_radius_start {p : Public} (s : ℕ → State p)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) {N : ℕ} (hN : 0 < N)
    (h0 : (s 0).phase = .centerGradient)
    (hs : s 1 = update (s 0) (reply 0)) (hn : (s 1).phase ≠ .finished) :
    eventIndex (radiusStartIndices s N) (N + 1) 0 = 1 := by
  have hstart := center_starts_radius (s 0) (reply 0) h0 (by rwa [← hs])
  rw [← hs] at hstart
  have hmem : 1 ∈ radiusStartIndices s N :=
    (mem_radiusStartIndices s N 1).mpr ⟨0, hN, hstart, rfl⟩
  have hcard : 0 < (radiusStartIndices s N).card := Finset.card_pos.mpr ⟨1, hmem⟩
  have hpos := radiusStartIndices_pos s N _ (eventIndex_mem (radiusStartIndices s N) (N + 1) 0 hcard)
  have hle : eventIndex (radiusStartIndices s N) (N + 1) 0 ≤ 1 := by
    by_contra h
    exact no_event_before (radiusStartIndices s N) (N + 1) (lt_of_not_ge h) hmem
  omega


lemma gradient_prefix_le_radius_allowances {p : Public} (s : ℕ → State p)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) {N : ℕ} (hN : 0 < N)
    (h0 : (s 0).phase = .centerGradient)
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k))
    (hn : ∀ k ≤ N, (s k).phase ≠ .finished) (C : ℕ → ℝ)
    (hC : ∀ i < (radiusStartIndices s N).card,
      (∑ k ∈ Finset.Ico (eventIndex (radiusStartIndices s N) (N + 1) i)
        (eventIndex (radiusStartIndices s N) (N + 1) (i + 1)),
        if (s k).phase = .newtonGradient then (1 : ℝ) else 0) ≤
        C (eventIndex (radiusStartIndices s N) (N + 1) i)) :
    (∑ k ∈ Finset.range N, if (s k).phase = .newtonGradient then (1 : ℝ) else 0) ≤
      ∑ k ∈ Finset.range N, if RadiusStart (s k) (s (k + 1)) then C (k + 1) else 0 := by
  let J := radiusStartIndices s N
  let a := eventIndex J (N + 1)
  let g := fun k => if (s k).phase = .newtonGradient then (1 : ℝ) else 0
  have hfirst : a 0 = 1 := first_radius_start s reply hN h0 (hs 0 hN) (hn 1 (by omega))
  have hmono (i : ℕ) (hi : i < J.card) : a i ≤ a (i + 1) :=
    (eventIndex_lt J (N + 1) (radiusStartIndices_subset s N) (by omega) (by omega)).le
  have hsum := sum_adjacent_intervals a g J.card hmono
  have hend : a J.card = N + 1 := eventIndex_end J (N + 1)
  rw [hfirst, hend] at hsum
  have hg0 : g 0 = 0 := by simp only [g, h0, reduceCtorEq, ite_false]
  have hprefix : (∑ k ∈ Finset.range N, g k) ≤ ∑ k ∈ Finset.Ico 1 (N + 1), g k := by
    have hh := Finset.sum_range_add_sum_Ico g (show 1 ≤ N + 1 by omega)
    rw [Finset.sum_range_one, hg0, zero_add, Finset.sum_range_succ] at hh
    rw [hh]
    have hgn : 0 ≤ g N := by dsimp only [g]; split_ifs <;> norm_num
    linarith
  calc
    _ ≤ ∑ i ∈ Finset.range J.card, ∑ k ∈ Finset.Ico (a i) (a (i + 1)), g k := by
      rw [hsum]
      exact hprefix
    _ ≤ ∑ i ∈ Finset.range J.card, C (a i) :=
      Finset.sum_le_sum (fun i hi => hC i (Finset.mem_range.mp hi))
    _ = ∑ j ∈ J, C j := sum_eventIndex J (N + 1) C
    _ = _ := sum_radiusStartIndices s N C

lemma hessian_abort_starts_radius {p : Public} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (hs : s.phase = .newtonHessian)
    (hn : (update s reply).phase ≠ .newtonGradient) : RadiusStart s (update s reply) := by
  by_cases hg : ‖newtonPoint p s.b s.center s.x s.g (readHessian reply) - s.center‖ ≤ 2 * s.r
  · exact False.elim (hn (by simp [update, hs, hg]))
  · exact failed_hessian_starts_radius s reply hs hg

lemma active_calls_le_radius_counts {p : Public} (s : ℕ → State p)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k)) :
    (∑ k ∈ Finset.range N, if (s k).phase ≠ .finished then (1 : ℝ) else 0) ≤
      (∑ k ∈ Finset.range N, if PointwiseHessianLedger.Accepted (s k) (reply k) then (1 : ℝ) else 0) +
      2 * (∑ k ∈ Finset.range N, if (s k).phase = .newtonGradient then (1 : ℝ) else 0) +
      (∑ k ∈ Finset.range N, if RadiusStart (s k) (s (k + 1)) then (1 : ℝ) else 0) + 2 := by
  have hh := path_active_count s reply N hs
  have hb : (∑ k ∈ Finset.range N, if (s k).phase = .newtonHessian ∧
      (s (k + 1)).phase ≠ .newtonGradient then (1 : ℝ) else 0) ≤
      (∑ k ∈ Finset.range N, if RadiusStart (s k) (s (k + 1)) then (1 : ℝ) else 0) := by
    apply Finset.sum_le_sum
    intro k hk
    by_cases ha : (s k).phase = .newtonHessian ∧ (s (k + 1)).phase ≠ .newtonGradient
    · have hstart := hessian_abort_starts_radius (s k) (reply k) ha.1
        (by rw [← hs k (Finset.mem_range.mp hk)]; exact ha.2)
      rw [← hs k (Finset.mem_range.mp hk)] at hstart
      simp only [ite_eq_left ha, ite_eq_left hstart, le_refl]
    · simp only [ite_eq_right ha]
      split_ifs <;> norm_num
  linarith


noncomputable def gradientAllowance {p : Public} (s : State p) : ℝ :=
  let t := 4 * (1 / s.τ) * gradientThreshold p / 3
  Real.log ((1 / s.τ) / s.b) / Real.log (1 + continuationRatio p s.τ s.r / 8) +
    Real.log ((2 * continuationRatio p s.τ s.r * s.r + t) / t) / Real.log 4 + 3

lemma gradient_prefix_allowance_bound {p : Public} {f : p.E → ℝ} {xs : p.E}
    (s : ℕ → State p) (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) {N : ℕ} (hN : 0 < N)
    (h0 : (s 0).phase = .centerGradient)
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k))
    (hn : ∀ k ≤ N, (s k).phase ≠ .finished)
    (hi : ∀ k ≤ N, PointwiseHessianExecution.PhaseInvariant f xs (s k))
    (hH : ∀ k < N, (s k).phase = .newtonHessian → reply k = .inr (fderiv ℝ (gradient f) (s k).x))
    (hg : ∀ k < N, (s k).phase = .newtonGradient → reply k = .inl (gradient f (s k).x)) :
    (∑ k ∈ Finset.range N, if (s k).phase = .newtonGradient then (1 : ℝ) else 0) ≤
      ∑ k ∈ Finset.range N, if RadiusStart (s k) (s (k + 1)) then gradientAllowance (s (k + 1)) else 0 := by
  apply gradient_prefix_le_radius_allowances s reply hN h0 hs hn (fun j => gradientAllowance (s j))
  intro i hi'
  let J := radiusStartIndices s N
  change i < J.card at hi'
  let a := eventIndex J (N + 1) i
  let b := eventIndex J (N + 1) (i + 1)
  have hab : a < b := eventIndex_lt J (N + 1) (radiusStartIndices_subset s N) (by omega) (by omega)
  have hb : b ≤ N + 1 := eventIndex_le J (N + 1) (radiusStartIndices_subset s N) _
  have ha : (s a).phase = .newtonHessian := radiusStartIndices_inner s N a (eventIndex_mem J (N + 1) i hi')
  have hbound := radius_interval_gradient_bound s hf hc hM₀ hM₁ hR hε hT reply hab hb ha hs hn
    (fun k hak hkb => no_start_between_radius_events s N i hi' hak hkb) hi hH hg
  simpa only [gradientAllowance, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hbound


end LongTails.Proofs.PointwiseHessianEpisodePartition
