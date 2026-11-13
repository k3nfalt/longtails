import LongTails.Proofs.PointwiseHessianLedger
import Mathlib.Data.Finset.Sort

open scoped Classical

namespace LongTails.Proofs.PointwiseHessianEvents

noncomputable def eventIndex (S : Finset ℕ) (N k : ℕ) : ℕ :=
  if h : k < S.card then S.orderEmbOfFin rfl ⟨k, h⟩ else N

lemma eventIndex_mem (S : Finset ℕ) (N k : ℕ) (hk : k < S.card) : eventIndex S N k ∈ S := by
  simp only [eventIndex, dite_eq_left hk]
  exact S.orderEmbOfFin_mem rfl _

lemma eventIndex_end (S : Finset ℕ) (N : ℕ) : eventIndex S N S.card = N := by
  simp [eventIndex]

lemma eventIndex_lt (S : Finset ℕ) (N : ℕ) (hS : S ⊆ Finset.range N)
    {i j : ℕ} (hi : i < j) (hj : j ≤ S.card) : eventIndex S N i < eventIndex S N j := by
  have hic : i < S.card := lt_of_lt_of_le hi hj
  by_cases hjc : j < S.card
  · simp only [eventIndex, dite_eq_left hic, dite_eq_left hjc]
    exact (S.orderEmbOfFin rfl).strictMono (by exact hi)
  · have hjc' : j = S.card := by omega
    rw [hjc', eventIndex_end]
    exact Finset.mem_range.mp (hS (eventIndex_mem S N i hic))

lemma no_event_between (S : Finset ℕ) (N : ℕ) {i k : ℕ}
    (hi : i < S.card) (hlo : eventIndex S N i < k) (hhi : k < eventIndex S N (i + 1)) : k ∉ S := by
  intro hk
  have hr : k ∈ Set.range (S.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hk
  obtain ⟨r, hr⟩ := hr
  have hir : i < r.val := by
    have hh : S.orderEmbOfFin rfl ⟨i, hi⟩ < S.orderEmbOfFin rfl r := by
      simpa only [eventIndex, dite_eq_left hi, hr] using hlo
    exact (S.orderEmbOfFin rfl).lt_iff_lt.mp hh
  by_cases hn : i + 1 < S.card
  · have hh : S.orderEmbOfFin rfl r < S.orderEmbOfFin rfl ⟨i + 1, hn⟩ := by
      simpa only [eventIndex, dite_eq_left hn, hr] using hhi
    have hri : r.val < i + 1 := (S.orderEmbOfFin rfl).lt_iff_lt.mp hh
    omega
  · have hrlt := r.isLt
    omega

lemma eventIndex_le (S : Finset ℕ) (N : ℕ) (hS : S ⊆ Finset.range N) (i : ℕ) :
    eventIndex S N i ≤ N := by
  by_cases hi : i < S.card
  · exact (Finset.mem_range.mp (hS (eventIndex_mem S N i hi))).le
  · simp [eventIndex, hi]

open LongTails.Setups.PointwiseHessianConvex
open LongTails.Algorithms.PointwiseHessianAccelerated
open LongTails.Proofs.PointwiseHessianLedger

noncomputable def acceptedIndices {p : Public} (s : ℕ → State p)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun i => Accepted (s i) (reply i))

lemma accepted_event_scales {p : Public} (s : ℕ → State p)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k))
    {i : ℕ} (hi : i < (acceptedIndices s reply N).card) :
    let S := acceptedIndices s reply N
    ((s (eventIndex S N (i + 1))).A, (s (eventIndex S N (i + 1))).η) =
      ((accept (s (eventIndex S N i))).A, (accept (s (eventIndex S N i))).η) := by
  let S := acceptedIndices s reply N
  change i < S.card at hi
  have hS : S ⊆ Finset.range N := Finset.filter_subset _ _
  have him := eventIndex_mem S N i hi
  have hacc : Accepted (s (eventIndex S N i)) (reply (eventIndex S N i)) :=
    (Finset.mem_filter.mp him).2
  have hij := eventIndex_lt S N hS (show i < i + 1 by omega) (show i + 1 ≤ S.card by omega)
  apply consecutive_accept_scales s reply hij
  · intro k _ hk
    exact hs k (lt_of_lt_of_le hk (eventIndex_le S N hS _))
  · exact hacc
  · intro k hlo hhi hk
    apply no_event_between S N hi hlo hhi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (lt_of_lt_of_le hhi (eventIndex_le S N hS _)), hk⟩

lemma no_event_before (S : Finset ℕ) (N : ℕ) {k : ℕ}
    (hk : k < eventIndex S N 0) : k ∉ S := by
  intro hmem
  have hr : k ∈ Set.range (S.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hmem
  obtain ⟨r, hr⟩ := hr
  have hc : 0 < S.card := lt_of_le_of_lt (Nat.zero_le r.val) r.isLt
  have hh : S.orderEmbOfFin rfl ⟨0, hc⟩ ≤ S.orderEmbOfFin rfl r :=
    (S.orderEmbOfFin rfl).monotone (by exact Nat.zero_le r.val)
  have he : eventIndex S N 0 ≤ k := by simpa only [eventIndex, dite_eq_left hc, hr] using hh
  omega

lemma first_event_outer {p : Public} (s : ℕ → State p)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k)) :
    let j := eventIndex (acceptedIndices s reply N) N 0
    ((s j).A, (s j).η, (s j).w, (s j).z) = ((s 0).A, (s 0).η, (s 0).w, (s 0).z) := by
  let S := acceptedIndices s reply N
  have hS : S ⊆ Finset.range N := Finset.filter_subset _ _
  have hh := path_constant_outer s reply 0 (eventIndex S N 0)
    (by intro k hk; simpa using hs k (lt_of_lt_of_le hk (eventIndex_le S N hS 0)))
    (by
      intro k hk ha
      apply no_event_before S N hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        (lt_of_lt_of_le hk (eventIndex_le S N hS 0)), by simpa using ha⟩)
  simpa only [Nat.zero_add] using hh

lemma sum_eventIndex (S : Finset ℕ) (N : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range S.card, f (eventIndex S N i)) = ∑ k ∈ S, f k := by
  refine Finset.sum_bij (fun i _ => eventIndex S N i) ?_ ?_ ?_ ?_
  · intro i hi
    exact eventIndex_mem S N i (Finset.mem_range.mp hi)
  · intro i hi j hj he
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    simp only [eventIndex, dite_eq_left hi', dite_eq_left hj'] at he
    exact congrArg Fin.val ((S.orderEmbOfFin rfl).injective he)
  · intro k hk
    have hr : k ∈ Set.range (S.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hk
    obtain ⟨r, hr⟩ := hr
    refine ⟨r.val, Finset.mem_range.mpr r.isLt, ?_⟩
    simpa only [eventIndex, dite_eq_left r.isLt] using hr
  · intro i hi
    rfl

lemma damped_event_sum {p : Public} (s : ℕ → State p)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ) :
    let S := acceptedIndices s reply N
    (∑ i ∈ Finset.range S.card, if (s (eventIndex S N i)).τ = (s (eventIndex S N i)).η
      then 0 else (s (eventIndex S N i)).A * (s (eventIndex S N i)).η ^ 3) =
    ∑ k ∈ Finset.range N, if Accepted (s k) (reply k) ∧ (s k).τ ≠ (s k).η
      then (s k).A * (s k).η ^ 3 else 0 := by
  let S := acceptedIndices s reply N
  change (∑ i ∈ Finset.range S.card,
    (fun k => if (s k).τ = (s k).η then 0 else (s k).A * (s k).η ^ 3) (eventIndex S N i)) = _
  rw [sum_eventIndex S N (fun k => if (s k).τ = (s k).η then 0 else (s k).A * (s k).η ^ 3)]
  change (∑ k ∈ (Finset.range N).filter _, _) = _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases ha : Accepted (s k) (reply k) <;> by_cases ht : (s k).τ = (s k).η <;> simp [ha, ht]

lemma accepted_path_count {p : Public} {f : p.E → ℝ} (s : ℕ → State p) (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hR : 0 < p.R) (hmin : IsMinOn f Set.univ xs)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hi : ∀ k ≤ N, PointwiseHessianExecution.StateInvariant f xs (s k))
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k))
    (hcert : ∀ k < N, CertificateInvariant f (s k))
    (hg : ∀ k < N, (s k).phase = .newtonGradient → reply k = .inl (gradient f (s k).x))
    (hloss : (∑ k ∈ Finset.range N, loss (s k) (reply k)) ≤ p.R ^ 2)
    {D : ℝ} (hD : 0 < D) (hDb : 2048 * p.M₀ * p.R ≤ D) :
    let S := acceptedIndices s reply N
    (S.card : ℝ) * Real.log 2 ≤
      2 * Real.log 2 * (3 * PointwiseHessianCounting.level D (s N).A *
        (Real.log (s N).A - Real.log (s 0).A) + 8 * PointwiseHessianCounting.level D (s N).A) +
      |Real.log (s 0).η - Real.log (PointwiseHessianCounting.threshold D (s 0).A)| +
      Real.log (PointwiseHessianCounting.threshold D (s 0).A) -
      Real.log (PointwiseHessianCounting.threshold D (s N).A) := by
  let S := acceptedIndices s reply N
  let t := fun i => s (eventIndex S N i)
  have hS : S ⊆ Finset.range N := Finset.filter_subset _ _
  have ht (i : ℕ) : PointwiseHessianExecution.StateInvariant f xs (t i) :=
    hi _ (eventIndex_le S N hS i)
  have he (i : ℕ) (hi' : i < S.card) :
      (t (i + 1)).A = (accept (t i)).A ∧ (t (i + 1)).η = (accept (t i)).η := by
    have hh := accepted_event_scales s reply N hs hi'
    exact ⟨congrArg Prod.fst hh, congrArg Prod.snd hh⟩
  have hp (i : ℕ) (hi' : i < S.card) : (t i).η ≤ (t i).τ := by
    have ha := (Finset.mem_filter.mp (eventIndex_mem S N i hi')).2
    change Accepted (t i) (reply (eventIndex S N i)) at ha
    have hh := (ht i).phase
    simp only [PointwiseHessianExecution.PhaseInvariant, ha.1] at hh
    exact hh.1.η_le
  have henergy : (∑ i ∈ Finset.range S.card,
      if (t i).τ = (t i).η then 0 else (t i).A * (t i).η ^ 3) ≤ D ^ 2 := by
    rw [damped_event_sum s reply N]
    apply (path_damped_sum s xs hf hc hM₀ hR hmin reply N
      (fun k hk => hi k hk.le) hcert hg hloss).trans
    exact pow_le_pow_left₀ (by positivity) hDb 2
  have hh := PointwiseHessianOuter.outer_count t S.card hD
    (fun i _ => (ht i).outer.A_pos) (fun i _ => (ht i).outer.η_pos)
    (fun i _ => (ht i).outer.scale) hp (fun i h => (he i h).1) (fun i h => (he i h).2)
    (by
      intro i hi'
      change (s (eventIndex S N i)).A ≤ (s (eventIndex S N S.card)).A
      rw [eventIndex_end]
      exact path_weight_mono s reply N (fun k hk => hi k hk.le) hs (eventIndex_le S N hS i) le_rfl)
    henergy
  have hfirst := first_event_outer s reply N hs
  have hA0 := congrArg Prod.fst hfirst
  have hη0 := congrArg (fun v : ℝ × ℝ × p.E × p.E => v.2.1) hfirst
  dsimp only at hA0 hη0
  change (s (eventIndex S N 0)).A = (s 0).A at hA0
  change (s (eventIndex S N 0)).η = (s 0).η at hη0
  simpa only [t, eventIndex_end, hA0, hη0] using hh

end LongTails.Proofs.PointwiseHessianEvents
