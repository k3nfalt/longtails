import LongTails.Proofs.CovarianceAcceleratedExecution
import LongTails.Proofs.CovarianceAcceleratedCoupling
import LongTails.Proofs.CovarianceAcceleratedGeometry
import LongTails.Proofs.MultiplicativeRobustMedoid

open MeasureTheory ProbabilityTheory Convexity
open scoped RealInnerProductSpace
open LongTails.Algorithms.CovarianceAccelerated
open LongTails.Algorithms.CovarianceAcceleratedMixture
open LongTails.Proofs.CovarianceAcceleratedExecution

namespace LongTails.Proofs.CovarianceAcceleratedRun

lemma cumulative_succ (η : ℝ) (t : ℕ) : cumulative η (t + 1) = cumulative η t + weight η t := by
  simp only [cumulative, weight, Nat.cast_add, Nat.cast_one]
  ring

lemma weight_pos {η : ℝ} (hη : 0 < η) (t : ℕ) : 0 < weight η t := by
  unfold weight
  positivity

lemma cumulative_nonneg {η : ℝ} (hη : 0 ≤ η) (t : ℕ) : 0 ≤ cumulative η t := by
  unfold cumulative
  positivity

lemma curvature_bound {η L : ℝ} (hη : 0 < η) (hL : 0 ≤ L) (t : ℕ) :
    L * weight η t ^ 2 / (cumulative η t + weight η t) ≤ 2 * η * L := by
  have hB : 0 < cumulative η t + weight η t :=
    add_pos_of_nonneg_of_pos (cumulative_nonneg hη.le t) (weight_pos hη t)
  apply (div_le_iff₀ hB).mpr
  have he : 2 * η * L * (cumulative η t + weight η t) - L * weight η t ^ 2 =
      L * η ^ 2 * ((t : ℝ) + 1) := by unfold cumulative weight; ring
  have hn : 0 ≤ L * η ^ 2 * ((t : ℝ) + 1) := by positivity
  linarith

lemma weight_ratio {η : ℝ} (hη : 0 < η) (t : ℕ) :
    weight η t / (cumulative η t + weight η t) = 2 / ((t : ℝ) + 2) := by
  have hB := add_pos_of_nonneg_of_pos (cumulative_nonneg hη.le t) (weight_pos hη t)
  have ht : 0 < (t : ℝ) + 2 := by positivity
  apply (div_eq_div_iff hB.ne' ht.ne').mpr
  unfold weight cumulative
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] {n : ℕ} (c : Config E n)

noncomputable def phase {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω) (t : ℕ) : State c :=
  trajectory c g ξ (c.window + 1 + t)

lemma phase_zero {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω) :
    (phase c g ξ 0).2.1 = c.x0 ∧
      (phase c g ξ 0).2.2.1 = StdSimplex.single c.initialIndex := by
  simpa only [phase, Nat.add_zero] using warmup_state c g ξ (N := c.window + 1) le_rfl

lemma phase_query {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω) (t : ℕ) :
    query c (phase c g ξ t) = couple (cumulative c.η t) (weight c.η t)
      (phase c g ξ t).2.1 (c.x0 + c.a • mean c.centers (phase c g ξ t).2.2.1) := by
  unfold query
  rw [show (phase c g ξ t).1 = c.window + 1 + t from trajectory_clock c g ξ _]
  simp [show ¬c.window + 1 + t < c.window + 1 by omega]

lemma phase_succ {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω) (t : ℕ) :
    let s := phase c g ξ t
    let h := OracleTemplate.MultiplicativeRobustEstimator.medoid s.2.2.2
    let reply := g (query c s) (ξ (c.window + 1 + t))
    let p := step c.centers c.x0 c.a (weight c.η t) c.β c.γ s.2.2.1 h reply
    phase c g ξ (t + 1) =
      (c.window + 1 + t + 1,
        couple (cumulative c.η t) (weight c.η t) s.2.1 (c.x0 + c.a • mean c.centers p),
        p, push s.2.2.2 reply) := by
  dsimp only
  change trajectory c g ξ (c.window + 1 + (t + 1)) = _
  rw [show c.window + 1 + (t + 1) = c.window + 1 + t + 1 by omega, trajectory]
  unfold advance
  rw [trajectory_clock]
  simp [show ¬c.window + 1 + t < c.window + 1 by omega, phase]

noncomputable def residual {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω) (v : E → E)
    (t : ℕ) (u : E) : ℝ :=
  let s := phase c g ξ t
  let b := c.x0 + c.a • mean c.centers s.2.2.1
  let h := OracleTemplate.MultiplicativeRobustEstimator.medoid s.2.2.2
  let x := query c s
  weight c.η t * ⟪v x - h, c.x0 + c.a • u - b⟫ -
    max (-1) (min 1 (weight c.η t * ⟪g x (ξ (c.window + 1 + t)) - h, c.x0 + c.a • u - b⟫))

variable [BorelSpace E]

lemma phase_energy_step {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω)
    {f : E → ℝ} {v : E → E} {L : ℝ} (hη : 0 < c.η) (hL0 : 0 ≤ L)
    (hβ : 2 * c.η * L ≤ c.β) (hγ : 0 ≤ c.γ)
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (v x) x)
    (hlip : ∀ x y, ‖v x - v y‖ ≤ L * ‖x - y‖)
    {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, ‖c.centers i‖ ≤ M)
    (w : StdSimplex ℝ (Fin n)) (t : ℕ) :
    cumulative c.η (t + 1) * (f (phase c g ξ (t + 1)).2.1 - f (c.x0 + c.a • mean c.centers w)) +
      potential c.centers c.a c.β c.γ w (phase c g ξ (t + 1)).2.2.1 ≤
    cumulative c.η t * (f (phase c g ξ t).2.1 - f (c.x0 + c.a • mean c.centers w)) +
      potential c.centers c.a c.β c.γ w (phase c g ξ t).2.2.1 +
      Real.log (∫ u, mixture c.centers (phase c g ξ t).2.2.1 u *
        Real.exp (residual c g ξ v t u) ∂stdGaussian E) -
      ∫ u, mixture c.centers w u * residual c g ξ v t u ∂stdGaussian E := by
  have hB : 0 < cumulative c.η t + weight c.η t :=
    add_pos_of_nonneg_of_pos (cumulative_nonneg hη.le t) (weight_pos hη t)
  have hs := CovarianceAcceleratedCoupling.accelerated_step (a := c.a) c.centers c.x0
    (phase c g ξ t).2.1 (phase c g ξ t).2.2.1 w
    (OracleTemplate.MultiplicativeRobustEstimator.medoid (phase c g ξ t).2.2.2)
    (g (query c (phase c g ξ t)) (ξ (c.window + 1 + t)))
    (cumulative_nonneg hη.le t) (weight_pos hη t).le hB
    ((curvature_bound hη hL0 t).trans hβ) hγ hc hg hlip hM hz
  dsimp only at hs
  rw [cumulative_succ, phase_succ]
  simpa only [residual, phase_query] using hs

lemma telescoping_energy {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω)
    {f : E → ℝ} {v : E → E} {L : ℝ} (hη : 0 < c.η) (hL0 : 0 ≤ L)
    (hβ : 2 * c.η * L ≤ c.β) (hγ : 0 ≤ c.γ)
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (v x) x)
    (hlip : ∀ x y, ‖v x - v y‖ ≤ L * ‖x - y‖)
    {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, ‖c.centers i‖ ≤ M)
    (w : StdSimplex ℝ (Fin n)) (T : ℕ) :
    cumulative c.η T * (f (output c g ξ (c.window + 1 + T)) -
      f (c.x0 + c.a • mean c.centers w)) +
      potential c.centers c.a c.β c.γ w (phase c g ξ T).2.2.1 ≤
    potential c.centers c.a c.β c.γ w (StdSimplex.single c.initialIndex) +
      ∑ t ∈ Finset.range T,
        (Real.log (∫ u, mixture c.centers (phase c g ξ t).2.2.1 u *
          Real.exp (residual c g ξ v t u) ∂stdGaussian E) -
          ∫ u, mixture c.centers w u * residual c g ξ v t u ∂stdGaussian E) := by
  induction T with
  | zero =>
    simp only [cumulative, Nat.cast_zero, mul_zero, zero_mul, zero_div, zero_add,
      Finset.sum_range_zero, add_zero, (phase_zero c g ξ).2]
    exact le_rfl
  | succ T ih =>
    have hs := phase_energy_step c g ξ hη hL0 hβ hγ hc hg hlip hM hz w T
    rw [Finset.sum_range_succ]
    change cumulative c.η (T + 1) * (f (phase c g ξ (T + 1)).2.1 -
      f (c.x0 + c.a • mean c.centers w)) + _ ≤ _
    change cumulative c.η T * (f (phase c g ξ T).2.1 -
      f (c.x0 + c.a • mean c.centers w)) + _ ≤ _ at ih
    linarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma physical_mean_radius {M R : ℝ} (hz : ∀ i, ‖c.centers i‖ ≤ M)
    (ha : |c.a| * M ≤ R) (w : StdSimplex ℝ (Fin n)) :
    ‖c.x0 + c.a • mean c.centers w - c.x0‖ ≤ R := by
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left
    (CovarianceAcceleratedGeometry.mean_norm_le c.centers w hz) (abs_nonneg _)).trans ha

omit [BorelSpace E] in
lemma phase_radius {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω)
    (hη : 0 < c.η) {M R : ℝ} (hR : 0 ≤ R)
    (hz : ∀ i, ‖c.centers i‖ ≤ M) (ha : |c.a| * M ≤ R) (t : ℕ) :
    ‖(phase c g ξ t).2.1 - c.x0‖ ≤ R := by
  induction t with
  | zero => simpa only [(phase_zero c g ξ).1, sub_self, norm_zero] using hR
  | succ t ih =>
    rw [phase_succ]
    exact CovarianceAcceleratedGeometry.couple_radius
      (cumulative_nonneg hη.le t) (weight_pos hη t).le
      (add_pos_of_nonneg_of_pos (cumulative_nonneg hη.le t) (weight_pos hη t))
      ih (physical_mean_radius c hz ha _)

omit [BorelSpace E] in
lemma phase_query_radius {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω)
    (hη : 0 < c.η) {M R : ℝ} (hR : 0 ≤ R)
    (hz : ∀ i, ‖c.centers i‖ ≤ M) (ha : |c.a| * M ≤ R) (t : ℕ) :
    ‖query c (phase c g ξ t) - c.x0‖ ≤ R := by
  rw [phase_query]
  exact CovarianceAcceleratedGeometry.couple_radius
    (cumulative_nonneg hη.le t) (weight_pos hη t).le
    (add_pos_of_nonneg_of_pos (cumulative_nonneg hη.le t) (weight_pos hη t))
    (phase_radius c g ξ hη hR hz ha t) (physical_mean_radius c hz ha _)

omit [BorelSpace E] in
lemma query_output_move {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω)
    (hη : 0 < c.η) {M R : ℝ} (hR : 0 ≤ R)
    (hz : ∀ i, ‖c.centers i‖ ≤ M) (ha : |c.a| * M ≤ R) (t : ℕ) :
    ‖query c (phase c g ξ t) - (phase c g ξ t).2.1‖ ≤ 4 * R / ((t : ℝ) + 2) := by
  rw [phase_query]
  have h := CovarianceAcceleratedGeometry.couple_move_le
    (weight_pos hη t).le
    (add_pos_of_nonneg_of_pos (cumulative_nonneg hη.le t) (weight_pos hη t))
    (phase_radius c g ξ hη hR hz ha t) (physical_mean_radius c hz ha (phase c g ξ t).2.2.1)
  rw [weight_ratio hη] at h
  convert h using 1; ring

omit [BorelSpace E] in
lemma next_output_query_move {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω)
    (hη : 0 < c.η) {M R : ℝ}
    (hz : ∀ i, ‖c.centers i‖ ≤ M) (ha : |c.a| * M ≤ R) (t : ℕ) :
    ‖(phase c g ξ (t + 1)).2.1 - query c (phase c g ξ t)‖ ≤
      4 * R / ((t : ℝ) + 2) := by
  have h := CovarianceAcceleratedGeometry.couple_pair_move_le
    (y := (phase c g ξ t).2.1) (weight_pos hη t).le
    (add_pos_of_nonneg_of_pos (cumulative_nonneg hη.le t) (weight_pos hη t))
    (physical_mean_radius c hz ha (phase c g ξ (t + 1)).2.2.1)
    (physical_mean_radius c hz ha (phase c g ξ t).2.2.1)
  have he : weight c.η t / (cumulative c.η t + weight c.η t) * (2 * R) =
      4 * R / ((t : ℝ) + 2) := by rw [weight_ratio hη]; ring
  rw [he] at h
  simpa only [phase_succ, phase_query] using h

omit [BorelSpace E] in
lemma query_adjacent_move {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω)
    (hη : 0 < c.η) {M R : ℝ} (hR : 0 ≤ R)
    (hz : ∀ i, ‖c.centers i‖ ≤ M) (ha : |c.a| * M ≤ R) (t : ℕ) :
    ‖query c (phase c g ξ (t + 1)) - query c (phase c g ξ t)‖ ≤
      8 * R / ((t : ℝ) + 2) := by
  have h1 := query_output_move c g ξ hη hR hz ha (t + 1)
  have h2 := next_output_query_move c g ξ hη hz ha t
  have ht : 0 < (t : ℝ) + 2 := by positivity
  have hr : 0 ≤ 4 * R := by positivity
  have hd : 4 * R / ((t + 1 : ℕ) + 2 : ℝ) ≤ 4 * R / ((t : ℝ) + 2) := by
    apply div_le_div_of_nonneg_left hr ht
    push_cast
    linarith
  have he : query c (phase c g ξ (t + 1)) - query c (phase c g ξ t) =
      (query c (phase c g ξ (t + 1)) - (phase c g ξ (t + 1)).2.1) +
      ((phase c g ξ (t + 1)).2.1 - query c (phase c g ξ t)) := by abel
  rw [he]
  have hh := (norm_add_le _ _).trans (add_le_add (h1.trans hd) h2)
  convert hh using 1; ring

omit [BorelSpace E] in
lemma query_interval_move {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω)
    (hη : 0 < c.η) {M R : ℝ} (hR : 0 ≤ R)
    (hz : ∀ i, ‖c.centers i‖ ≤ M) (ha : |c.a| * M ≤ R) (j d : ℕ) :
    ‖query c (phase c g ξ (j + d)) - query c (phase c g ξ j)‖ ≤
      8 * R * d / ((j : ℝ) + 2) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hstep := query_adjacent_move c g ξ hη hR hz ha (j + d)
    have hd : 8 * R / ((j + d : ℕ) + 2 : ℝ) ≤ 8 * R / ((j : ℝ) + 2) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) d]
    have he : query c (phase c g ξ (j + (d + 1))) - query c (phase c g ξ j) =
        (query c (phase c g ξ (j + d + 1)) - query c (phase c g ξ (j + d))) +
        (query c (phase c g ξ (j + d)) - query c (phase c g ξ j)) := by
      rw [Nat.add_assoc]
      abel
    rw [he]
    have hh := (norm_add_le _ _).trans (add_le_add (hstep.trans hd) ih)
    convert hh using 1
    push_cast
    ring

omit [BorelSpace E] in
lemma trajectory_query_radius {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω)
    (hη : 0 < c.η) {M R : ℝ} (hR : 0 ≤ R)
    (hz : ∀ i, ‖c.centers i‖ ≤ M) (ha : |c.a| * M ≤ R) (N : ℕ) :
    ‖query c (trajectory c g ξ N) - c.x0‖ ≤ R := by
  by_cases hN : N < c.window + 1
  · rw [warmup_query c g ξ hN, sub_self, norm_zero]
    exact hR
  · have he : c.window + 1 + (N - (c.window + 1)) = N :=
      Nat.add_sub_of_le (Nat.le_of_not_gt hN)
    simpa only [phase, he] using phase_query_radius c g ξ hη hR hz ha (N - (c.window + 1))

omit [BorelSpace E] in
lemma history_query_move {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω)
    (hη : 0 < c.η) {M R : ℝ} (hR : 0 ≤ R)
    (hz : ∀ i, ‖c.centers i‖ ≤ M) (ha : |c.a| * M ≤ R)
    (t : ℕ) (j : Fin (c.window + 1)) :
    ‖query c (trajectory c g ξ (c.window + 1 + t - 1 - j.val)) - query c (phase c g ξ t)‖ ≤
      16 * R * (c.window + 1) / ((t : ℝ) + 1) := by
  have htpos : 0 < (t : ℝ) + 1 := by positivity
  by_cases ht : t < 2 * (c.window + 1)
  · have hb := CovarianceAcceleratedGeometry.ball_pair_distance
      (trajectory_query_radius c g ξ hη hR hz ha (c.window + 1 + t - 1 - j.val))
      (phase_query_radius c g ξ hη hR hz ha t)
    apply hb.trans
    apply (le_div_iff₀ htpos).mpr
    have hh : (t : ℝ) + 1 ≤ 2 * ((c.window : ℝ) + 1) := by exact_mod_cast (show t + 1 ≤ 2 * (c.window + 1) by omega)
    nlinarith [mul_nonneg hR (show 0 ≤ 2 * ((c.window : ℝ) + 1) - ((t : ℝ) + 1) by linarith)]
  · let r := t - 1 - j.val
    have hr : r ≤ t := by dsimp [r]; omega
    have he : c.window + 1 + t - 1 - j.val = c.window + 1 + r := by dsimp [r]; omega
    have hd : t - r ≤ c.window + 1 := by dsimp [r]; omega
    have hl : t + 1 ≤ 2 * (r + 2) := by dsimp [r]; omega
    have hmove := query_interval_move c g ξ hη hR hz ha r (t - r)
    rw [Nat.add_sub_of_le hr, norm_sub_rev] at hmove
    rw [he]
    change ‖query c (phase c g ξ r) - query c (phase c g ξ t)‖ ≤ _
    apply hmove.trans
    have hdr : ((t - r : ℕ) : ℝ) ≤ (c.window : ℝ) + 1 := by exact_mod_cast hd
    have hlr : (t : ℝ) + 1 ≤ 2 * ((r : ℝ) + 2) := by exact_mod_cast hl
    have hrpos : 0 < (r : ℝ) + 2 := by positivity
    calc
      _ ≤ 8 * R * ((c.window : ℝ) + 1) / ((r : ℝ) + 2) := by gcongr
      _ ≤ 16 * R * ((c.window : ℝ) + 1) / ((t : ℝ) + 1) := by
        apply (div_le_div_iff₀ hrpos htpos).mpr
        nlinarith [mul_nonneg (show 0 ≤ R * ((c.window : ℝ) + 1) by positivity)
          (show 0 ≤ 2 * ((r : ℝ) + 2) - ((t : ℝ) + 1) by linarith)]

omit [BorelSpace E] in
lemma medoid_residual {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω)
    (hη : 0 < c.η) {M R σ L : ℝ} (hR : 0 ≤ R) (hσ : 0 ≤ σ) (hL : 0 ≤ L)
    (hz : ∀ i, ‖c.centers i‖ ≤ M) (ha : |c.a| * M ≤ R)
    (v : E → E) (hlip : ∀ x y, ‖v x - v y‖ ≤ L * ‖x - y‖)
    (t : ℕ) (G : Finset (Fin (c.window + 1)))
    (hcard : 3 * (c.window + 1) ≤ 4 * G.card)
    (hgood : ∀ j ∈ G,
      ‖g (query c (trajectory c g ξ (c.window + 1 + t - 1 - j.val)))
        (ξ (c.window + 1 + t - 1 - j.val)) -
        v (query c (trajectory c g ξ (c.window + 1 + t - 1 - j.val)))‖ ≤ 8 * σ) :
    ‖v (query c (phase c g ξ t)) -
      OracleTemplate.MultiplicativeRobustEstimator.medoid (phase c g ξ t).2.2.2‖ ≤
      48 * σ + 96 * L * R * (c.window + 1) / ((t : ℝ) + 1) := by
  have hr : 0 ≤ 8 * σ + 16 * L * R * (c.window + 1) / ((t : ℝ) + 1) := by positivity
  have hh (j : Fin (c.window + 1)) (hj : j ∈ G) :
      ‖(phase c g ξ t).2.2.2 j - v (query c (phase c g ξ t))‖ ≤
        8 * σ + 16 * L * R * (c.window + 1) / ((t : ℝ) + 1) := by
    have he := history_after_warmup c g ξ (N := c.window + 1 + t) (by omega) j
    change (phase c g ξ t).2.2.2 j = _ at he
    rw [he]
    have hd := (hlip (query c (trajectory c g ξ (c.window + 1 + t - 1 - j.val)))
      (query c (phase c g ξ t))).trans
      (mul_le_mul_of_nonneg_left (history_query_move c g ξ hη hR hz ha t j) hL)
    have hb := norm_sub_le_norm_sub_add_norm_sub
      (g (query c (trajectory c g ξ (c.window + 1 + t - 1 - j.val)))
        (ξ (c.window + 1 + t - 1 - j.val)))
      (v (query c (trajectory c g ξ (c.window + 1 + t - 1 - j.val))))
      (v (query c (phase c g ξ t)))
    have hm := hb.trans (add_le_add (hgood j hj) hd)
    convert hm using 1; ring
  have hm := OracleTemplate.MultiplicativeRobustEstimator.medoid_accuracy
    (phase c g ξ t).2.2.2 (v (query c (phase c g ξ t))) G hr hh hcard
  rw [norm_sub_rev] at hm
  convert hm using 1; ring

end LongTails.Proofs.CovarianceAcceleratedRun
