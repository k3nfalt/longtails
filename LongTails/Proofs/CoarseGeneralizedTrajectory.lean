import LongTails.Proofs.CoarseGeneralizedDynamics
import LongTails.Proofs.CoarseGeneralizedCounting

open scoped RealInnerProductSpace
open Finset

namespace OracleTemplate.CoarseGeneralized

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def iterateEnergy (f : E → ℝ) (u : E) (s : Iterate E) : ℝ :=
  s.A * (f s.x - f u) + ‖s.v - u‖ ^ 2 / 2

lemma accepted_weights_nonneg (t : Tuning) (s : ℕ → Iterate E) (y h : ℕ → E) {K : ℕ}
    (hL : 0 < t.L) (hL1 : 0 < t.L1) (hinit : (s 0).A = 0)
    (hstep : ∀ i < K, s (i + 1) = advance t (s i) (y i) (h i))
    (hlarge : ∀ i < K, 4096 * t.L / t.L1 < ‖h i‖) :
    ∀ i ≤ K, 0 ≤ (s i).A := by
  intro i
  induction i with
  | zero => intro _; rw [hinit]
  | succ i ih =>
      intro hi
      have hiK : i < K := by omega
      have hA := ih (by omega)
      have hh := (div_lt_iff₀ hL1).mp (hlarge i hiK)
      have hs : 0 < ‖h i‖ := (div_pos (by positivity) hL1).trans (hlarge i hiK)
      have hD : 0 ≤ decrement t (h i) := by unfold decrement; positivity
      have hP := surplus_dominates_decrement t (h i) hL hL1 (by nlinarith)
      have hw := weight_spec t (s i) (h i) hL hL1.le hs (by linarith) hA
      rw [hstep i hiK]
      change 0 ≤ (s i).A + weight t (s i).A (h i)
      linarith [hw.1]

omit [InnerProductSpace ℝ E] in
lemma iterateEnergy_nonneg {f : E → ℝ} {u : E} {s : Iterate E}
    (hA : 0 ≤ s.A) (hmin : ∀ x, f u ≤ f x) : 0 ≤ iterateEnergy f u s := by
  unfold iterateEnergy
  exact add_nonneg (mul_nonneg hA (sub_nonneg.mpr (hmin s.x))) (by positivity)

lemma accepted_energy_bound [CompleteSpace E] (t : Tuning) (s : ℕ → Iterate E)
    (y h : ℕ → E) {K : ℕ} {f : E → ℝ} {g : E → E} {u : E} {R : ℝ}
    (hL : 0 < t.L) (hL1 : 0 < t.L1) (hζ : 0 ≤ t.ζ)
    (hR : 1 ≤ t.L1 * R) (hinflate : t.L1 ^ 2 * R * t.ζ ≤ t.L)
    (hc : ConvexOn ℝ Set.univ f) (hf : ∀ x, HasGradientAt f (g x) x)
    (hg : Differentiable ℝ g) (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ t.L + t.L1 * ‖g x‖)
    (hu : g u = 0) (hinit : (s 0).A = 0) (hdist : ‖(s 0).v - u‖ ≤ R)
    (hstep : ∀ i < K, s (i + 1) = advance t (s i) (y i) (h i))
    (hlarge : ∀ i < K, 4096 * t.L / t.L1 < ‖h i‖)
    (hyr : ∀ i < K, ‖y i - u‖ ≤ R) (herr : ∀ i < K, ‖h i - g (y i)‖ ≤ t.ζ)
    (hsearch : ∀ i < K, f (y i) ≤ f (s i).x + decrement t (h i) / 256)
    (halign : ∀ i < K, ⟪h i, y i - (s i).v⟫ ≤ decrement t (h i) / 256) :
    iterateEnergy f u (s K) +
      (∑ i ∈ range K, (weight t (s i).A (h i)) ^ 2 * ‖h i‖ ^ 2) / 2 ≤ R ^ 2 / 2 := by
  have hA := accepted_weights_nonneg t s y h hL hL1 hinit hstep hlarge
  have hinc : ∀ i < K, iterateEnergy f u (s (i + 1)) +
      ((weight t (s i).A (h i)) ^ 2 * ‖h i‖ ^ 2) / 2 ≤ iterateEnergy f u (s i) := by
    intro i hi
    have hn := high_reply_noise t (h i) hL hL1 hζ hR hinflate (hlarge i hi)
    have hh := (div_lt_iff₀ hL1).mp (hlarge i hi)
    have hs : 0 < ‖h i‖ := (div_pos (by positivity) hL1).trans (hlarge i hi)
    have hD : 0 ≤ decrement t (h i) := by unfold decrement; positivity
    have hP := surplus_dominates_decrement t (h i) hL hL1 (by nlinarith)
    have hsupport := high_reply_support t hL hL1 hζ hR hinflate hc hf hg hH hu
      (hyr i hi) (herr i hi) (hlarge i hi)
    have he := advance_energy t (s i) hL hL1.le hf hg hH hs (hA i hi.le)
      (by linarith) (herr i hi) hn.1 (hsearch i hi) (halign i hi) hsupport
    rw [hstep i hi]
    unfold iterateEnergy
    nlinarith only [he]
  have ht := energy_sum_bound (fun i => iterateEnergy f u (s i))
    (fun i => (weight t (s i).A (h i)) ^ 2 * ‖h i‖ ^ 2) hinc
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hdist 2
  unfold iterateEnergy at ht ⊢
  rw [hinit, zero_mul, zero_add] at ht
  linarith

lemma accepted_count (t : Tuning) (s : ℕ → Iterate E) (y h : ℕ → E) {K : ℕ}
    {R : ℝ} (hL : 0 < t.L) (hL1 : 0 < t.L1) (hR : 1 ≤ t.L1 * R)
    (hinit : (s 0).A = 0)
    (hstep : ∀ i < K, s (i + 1) = advance t (s i) (y i) (h i))
    (hlarge : ∀ i < K, 4096 * t.L / t.L1 < ‖h i‖)
    (hfinal : t.L * (s K).A ≤ (t.L1 * R) ^ 2)
    (henergy : (∑ i ∈ range K, (weight t (s i).A (h i)) ^ 2 * ‖h i‖ ^ 2) ≤ R ^ 2) :
    (K : ℝ) ≤ 2050 * (t.L1 * R) := by
  let b := fun i => t.L1 * weight t (s i).A (h i) * ‖h i‖
  let u := fun i => t.L1 * ‖h i‖ / t.L
  let w := fun i => t.L * (s i).A
  have hA := accepted_weights_nonneg t s y h hL hL1 hinit hstep hlarge
  have hnorm : ∀ i < K, 0 < ‖h i‖ := by
    intro i hi
    exact (div_pos (by positivity) hL1).trans (hlarge i hi)
  have hP : ∀ i < K, 0 ≤ surplus t (h i) := by
    intro i hi
    have hh := (div_lt_iff₀ hL1).mp (hlarge i hi)
    have hd : 0 ≤ decrement t (h i) := by unfold decrement; positivity
    have hp := surplus_dominates_decrement t (h i) hL hL1 (by nlinarith)
    linarith
  have hb : ∀ i < K, 0 < b i := by
    intro i hi
    have ha := (weight_spec t (s i) (h i) hL hL1.le (hnorm i hi) (hP i hi)
      (hA i hi.le)).1
    exact mul_pos (mul_pos hL1 ha) (hnorm i hi)
  have hu : ∀ i < K, 2 ≤ u i := by
    intro i hi
    have hh := (div_lt_iff₀ hL1).mp (hlarge i hi)
    dsimp [u]
    apply (le_div_iff₀ hL).mpr
    nlinarith
  have hw : ∀ i ≤ K, 0 ≤ w i := by
    intro i hi
    exact mul_nonneg hL.le (hA i hi)
  have hs : ∀ i < K, w (i + 1) = w i + b i / u i := by
    intro i hi
    dsimp [w, b, u]
    rw [hstep i hi]
    change t.L * ((s i).A + weight t (s i).A (h i)) = _
    field_simp [ne_of_gt hL, ne_of_gt hL1, ne_of_gt (hnorm i hi)]
  have he : ∀ i < K,
      w (i + 1) * (u i) ^ 2 / (128 * (1 + u i)) ≤ (b i) ^ 2 ∧
      Real.log (u i / 2) ≤ 128 * b i := by
    intro i hi
    apply normalized_weight_bounds (hb i hi) (hu i hi) (hw (i + 1) (by omega))
    have hh := normalized_weight_identity t (s i) (h i) hL hL1 (hnorm i hi)
      (hP i hi) (hA i hi.le)
    dsimp [b, u, w]
    rw [hstep i hi]
    exact hh
  apply trajectory_count b u w hR hb (fun i hi => (by linarith [hu i hi])) hw hs
    (fun i hi => (he i hi).1) (fun i hi => (he i hi).2) hfinal
  calc
    (∑ i ∈ range K, b i ^ 2) = t.L1 ^ 2 *
        (∑ i ∈ range K, (weight t (s i).A (h i)) ^ 2 * ‖h i‖ ^ 2) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      dsimp [b]
      ring
    _ ≤ t.L1 ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_left henergy (sq_nonneg _)
    _ = (t.L1 * R) ^ 2 := by ring

lemma accepted_gap (t : Tuning) (s : ℕ → Iterate E) (y h : ℕ → E) {K : ℕ}
    {f : E → ℝ} {u : E} {R : ℝ}
    (hL : 0 < t.L) (hL1 : 0 < t.L1) (hR : 1 ≤ t.L1 * R)
    (hinit : (s 0).A = 0) (hmin : ∀ x, f u ≤ f x)
    (hstep : ∀ i < K, s (i + 1) = advance t (s i) (y i) (h i))
    (hlarge : ∀ i < K, 4096 * t.L / t.L1 < ‖h i‖)
    (henergy : iterateEnergy f u (s K) +
      (∑ i ∈ range K, (weight t (s i).A (h i)) ^ 2 * ‖h i‖ ^ 2) / 2 ≤ R ^ 2 / 2)
    (hK : 2050 * (t.L1 * R) < K) :
    f (s K).x - f u ≤ t.L / t.L1 ^ 2 := by
  have hA := accepted_weights_nonneg t s y h hL hL1 hinit hstep hlarge
  have hen := iterateEnergy_nonneg (hA K le_rfl) hmin
  have hsum : 0 ≤ ∑ i ∈ range K, (weight t (s i).A (h i)) ^ 2 * ‖h i‖ ^ 2 := by
    exact sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have he : (∑ i ∈ range K, (weight t (s i).A (h i)) ^ 2 * ‖h i‖ ^ 2) ≤ R ^ 2 := by
    linarith
  by_contra hg
  have hg' : t.L < (f (s K).x - f u) * t.L1 ^ 2 :=
    (div_lt_iff₀ (sq_pos_of_pos hL1)).mp (lt_of_not_ge hg)
  have hm := mul_le_mul_of_nonneg_left hg'.le (hA K le_rfl)
  have hr : (s K).A * (f (s K).x - f u) ≤ R ^ 2 / 2 := by
    unfold iterateEnergy at henergy
    nlinarith only [henergy, hsum, sq_nonneg ‖(s K).v - u‖]
  have hr' := mul_le_mul_of_nonneg_right hr (sq_nonneg t.L1)
  have hf : t.L * (s K).A ≤ (t.L1 * R) ^ 2 := by
    nlinarith only [hm, hr', sq_nonneg (t.L1 * R)]
  have hc := accepted_count t s y h hL hL1 hR hinit hstep hlarge hf he
  linarith

structure AcceptedTrace (t : Tuning) (f : E → ℝ) (u : E) (R : ℝ) (last : Iterate E) where
  states : ℕ → Iterate E
  points : ℕ → E
  replies : ℕ → E
  initial : (states 0).A = 0
  terminal : states last.index = last
  steps : ∀ i < last.index, states (i + 1) = advance t (states i) (points i) (replies i)
  large : ∀ i < last.index, 4096 * t.L / t.L1 < ‖replies i‖
  energy : iterateEnergy f u last +
    (∑ i ∈ range last.index, (weight t (states i).A (replies i)) ^ 2 * ‖replies i‖ ^ 2) / 2 ≤ R ^ 2 / 2

lemma initial_trace (t : Tuning) (f : E → ℝ) (u x0 : E) {R : ℝ}
    (hdist : ‖x0 - u‖ ≤ R) :
    Nonempty (AcceptedTrace t f u R ⟨x0, x0, 0, 0⟩) := by
  refine ⟨⟨(fun _ => ⟨x0, x0, 0, 0⟩), (fun _ => x0), (fun _ => 0), rfl, rfl,
    (by simp), (by simp), ?_⟩⟩
  simp only [sum_range_zero, zero_div, add_zero, iterateEnergy, zero_mul, zero_add]
  have hh := pow_le_pow_left₀ (norm_nonneg _) hdist 2
  linarith

lemma trace_gap (t : Tuning) {f : E → ℝ} {u : E} {R : ℝ} {last : Iterate E}
    (tr : AcceptedTrace t f u R last)
    (hL : 0 < t.L) (hL1 : 0 < t.L1) (hR : 1 ≤ t.L1 * R)
    (hmin : ∀ x, f u ≤ f x) (hK : 2050 * (t.L1 * R) < last.index) :
    f last.x - f u ≤ t.L / t.L1 ^ 2 := by
  have hh := accepted_gap t tr.states tr.points tr.replies hL hL1 hR tr.initial hmin
    tr.steps tr.large (by simpa only [tr.terminal] using tr.energy) hK
  simpa only [tr.terminal] using hh

lemma extend_trace (t : Tuning) {f : E → ℝ} {u : E} {R : ℝ} {last : Iterate E}
    (tr : AcceptedTrace t f u R last) (y h : E)
    (hlarge : 4096 * t.L / t.L1 < ‖h‖)
    (he : iterateEnergy f u (advance t last y h) +
      (weight t last.A h) ^ 2 * ‖h‖ ^ 2 / 2 ≤ iterateEnergy f u last) :
    Nonempty (AcceptedTrace t f u R (advance t last y h)) := by
  classical
  let states := fun i => if i ≤ last.index then tr.states i else advance t last y h
  let points := fun i => if i < last.index then tr.points i else y
  let replies := fun i => if i < last.index then tr.replies i else h
  have hs : ∀ i ≤ last.index, states i = tr.states i := by
    intro i hi
    simp [states, hi]
  have hr : ∀ i < last.index, replies i = tr.replies i := by
    intro i hi
    simp [replies, hi]
  have hp : ∀ i < last.index, points i = tr.points i := by
    intro i hi
    simp [points, hi]
  have hlast : states last.index = last := by rw [hs _ le_rfl, tr.terminal]
  refine ⟨⟨states, points, replies, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hs _ (Nat.zero_le _)]
    exact tr.initial
  · simp [states, advance]
  · intro i hi
    change i < last.index + 1 at hi
    by_cases hil : i < last.index
    · rw [hs _ (by omega), hs _ (by omega), hp _ hil, hr _ hil]
      exact tr.steps i hil
    · have hie : i = last.index := by omega
      subst i
      rw [hlast]
      simp [states, points, replies]
  · intro i hi
    change i < last.index + 1 at hi
    by_cases hil : i < last.index
    · rw [hr _ hil]
      exact tr.large i hil
    · have hie : i = last.index := by omega
      subst i
      simpa [replies] using hlarge
  · change iterateEnergy f u (advance t last y h) +
      (∑ i ∈ range (last.index + 1), (weight t (states i).A (replies i)) ^ 2 * ‖replies i‖ ^ 2) / 2 ≤ _
    rw [sum_range_succ, hlast]
    have hreply : replies last.index = h := by simp [replies]
    rw [hreply]
    have hsum : (∑ i ∈ range last.index, (weight t (states i).A (replies i)) ^ 2 * ‖replies i‖ ^ 2) =
        ∑ i ∈ range last.index, (weight t (tr.states i).A (tr.replies i)) ^ 2 * ‖tr.replies i‖ ^ 2 := by
      apply sum_congr rfl
      intro i hi
      have hil := mem_range.mp hi
      rw [hs _ hil.le, hr _ hil]
    rw [hsum]
    linarith [tr.energy]

lemma trace_weight_nonneg (t : Tuning) {f : E → ℝ} {u : E} {R : ℝ} {last : Iterate E}
    (tr : AcceptedTrace t f u R last) (hL : 0 < t.L) (hL1 : 0 < t.L1) : 0 ≤ last.A := by
  have hh := accepted_weights_nonneg t tr.states tr.points tr.replies hL hL1 tr.initial
    tr.steps tr.large last.index le_rfl
  simpa only [tr.terminal] using hh

lemma trace_radius (t : Tuning) {f : E → ℝ} {u : E} {R : ℝ} {last : Iterate E}
    (tr : AcceptedTrace t f u R last) (hL : 0 < t.L) (hL1 : 0 < t.L1)
    (hR : 0 ≤ R) (hmin : ∀ x, f u ≤ f x) : ‖last.v - u‖ ≤ R := by
  have hA := trace_weight_nonneg t tr hL hL1
  have hgap := mul_nonneg hA (sub_nonneg.mpr (hmin last.x))
  have hsum : 0 ≤ ∑ i ∈ range last.index,
      (weight t (tr.states i).A (tr.replies i)) ^ 2 * ‖tr.replies i‖ ^ 2 :=
    sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have he := tr.energy
  unfold iterateEnergy at he
  nlinarith only [he, hgap, hsum, hR, norm_nonneg (last.v - u)]

end OracleTemplate.CoarseGeneralized
