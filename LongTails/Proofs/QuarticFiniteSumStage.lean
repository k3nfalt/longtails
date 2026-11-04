import LongTails.Proofs.QuarticFiniteSum
import LongTails.Proofs.AcceleratedFiniteSum

namespace LongTails.Proofs.QuarticFiniteSumStage

open OracleTemplate OracleTemplate.QueryPlan
open LongTails.Algorithms.QuarticProximal
open LongTails.Algorithms.TaylorCorrectedNewton
open LongTails.Setups.FiniteSumSmoothAndConvex
open scoped RealInnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [NeZero n]

omit [NeZero n] in
lemma exists_quartic_min {f : E → ℝ} (hf : Continuous f) {γ : ℝ}
    (hγ : 0 < γ) (c xstar : E) (hmin : ∀ x, f xstar ≤ f x) :
    ∃ v, ∀ x, f v + γ * value (v - c) ≤ f x + γ * value (x - c) := by
  let t := 4 * (f c - f xstar) / γ
  have ht : 0 ≤ t := by dsimp [t]; exact div_nonneg (by linarith [hmin c]) hγ.le
  have htm : γ * t = 4 * (f c - f xstar) := by dsimp [t]; field_simp
  let r := 1 + t
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hcont : Continuous (fun x => f x + γ * value (x - c)) := by
    unfold value
    fun_prop
  obtain ⟨v, _, hv⟩ := (isCompact_closedBall c r).exists_isMinOn
    (show (Metric.closedBall c r).Nonempty from ⟨c, by simpa using hr⟩) hcont.continuousOn
  refine ⟨v, fun x => ?_⟩
  by_cases hx : x ∈ Metric.closedBall c r
  · exact hv hx
  · have hd : r < ‖x - c‖ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hs : t ≤ ‖x - c‖ ^ 4 := by
      have hh := pow_le_pow_left₀ hr hd.le 4
      dsimp [r] at hh
      nlinarith [pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4]
    have hb := mul_le_mul_of_nonneg_left hs hγ.le
    have hc := hv (show c ∈ Metric.closedBall c r by simpa using hr)
    change f v + γ * value (v - c) ≤ f c + γ * value (c - c) at hc
    simp only [value, sub_self, norm_zero, zero_pow (by decide : 4 ≠ 0), zero_div,
      mul_zero, add_zero] at hc
    unfold value
    linarith [hmin x]

omit [NeZero n] in
lemma quartic_min_growth {f : E → ℝ} (hf : Differentiable ℝ f)
    (hc : ConvexOn ℝ Set.univ f) {γ : ℝ} (hγ : 0 ≤ γ) (c v y : E)
    (hmin : ∀ x, f v + γ * value (v - c) ≤ f x + γ * value (x - c)) :
    γ * ‖y - v‖ ^ 4 / 12 ≤ (f y + γ * value (y - c)) - (f v + γ * value (v - c)) := by
  let F := fun x => f x + penalty γ 0 c c x
  have hm : IsMinOn F Set.univ v := by
    intro x _
    simpa [F, penalty] using hmin x
  have hz : gradient F v = 0 := by
    have hh := (hm.isLocalMin Filter.univ_mem).fderiv_eq_zero
    simp [gradient, hh]
  have hg := QuarticProximalGeometry.add_penalty_hasGradientAt
    (fun x => (hf x).hasGradientAt) γ 0 c c v
  have hs := QuarticProximalGeometry.add_penalty_support
    (fun x => (hf x).hasGradientAt) hc hγ c c v y (μ := 0)
  have he : gradient F v = gradient f v + penaltyGrad γ 0 c c v := hg.gradient
  rw [← he, hz, inner_zero_left] at hs
  simp only [penalty, zero_div, zero_mul, add_zero] at hs
  linarith

omit [NeZero n] in
lemma quartic_min_mem {f : E → ℝ} (hf : Differentiable ℝ f)
    (hc : ConvexOn ℝ Set.univ f) {γ ρ Δ : ℝ} (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (hr : γ * ρ ^ 4 = 12 * Δ) (c v y0 : E)
    (hmin : ∀ x, f v + γ * value (v - c) ≤ f x + γ * value (x - c))
    (hgap : (f y0 + γ * value (y0 - c)) - (f v + γ * value (v - c)) ≤ Δ) :
    v ∈ Metric.closedBall y0 ρ := by
  have hg := quartic_min_growth hf hc hγ.le c v y0 hmin
  by_contra hv
  have hd : ρ < ‖y0 - v‖ := by
    simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hv
  have hp := pow_lt_pow_left₀ hd hρ (by decide : (4 : ℕ) ≠ 0)
  have hh := mul_lt_mul_of_pos_left hp hγ
  linarith

omit [NeZero n] in
lemma exists_stage_min (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (γ μ : ℝ) (c y0 : E)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ u ∈ Metric.closedBall y0 ρ,
      IsMinOn (objective (fun i z => f i z + penalty γ μ c y0 z))
        (Metric.closedBall y0 ρ) u := by
  have hc (i : Fin n) : Continuous (fun z => f i z + penalty γ μ c y0 z) :=
    (QuarticFiniteSum.component_contDiff f hf γ μ c y0 i).continuous
  have hF : Continuous (objective (fun i z => f i z + penalty γ μ c y0 z)) := by
    unfold objective
    exact continuous_const.mul (continuous_finsetSum _ (fun i _ => hc i))
  exact (isCompact_closedBall y0 ρ).exists_isMinOn
    ⟨y0, by simpa using hρ⟩ hF.continuousOn

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
lemma surrogate_gap (f : Fin n → E → ℝ) {γ μ ρ : ℝ}
    (hμ : 0 ≤ μ) (c y0 u v x : E)
    (hv : v ∈ Metric.closedBall y0 ρ)
    (hmin : IsMinOn (objective (fun i z => f i z + penalty γ μ c y0 z))
      (Metric.closedBall y0 ρ) u) :
    (objective f x + γ * value (x - c)) - (objective f v + γ * value (v - c)) ≤
      objective (fun i z => f i z + penalty γ μ c y0 z) x -
        objective (fun i z => f i z + penalty γ μ c y0 z) u + μ / 2 * ρ ^ 2 := by
  have hh : objective (fun i z => f i z + penalty γ μ c y0 z) u ≤
      objective (fun i z => f i z + penalty γ μ c y0 z) v := hmin hv
  rw [QuarticFiniteSum.objective_penalty, QuarticFiniteSum.objective_penalty] at hh
  rw [QuarticFiniteSum.objective_penalty, QuarticFiniteSum.objective_penalty]
  have hvn : ‖v - y0‖ ≤ ρ := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hv
  have hs : ‖v - y0‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hvn 2
  have hb := mul_le_mul_of_nonneg_left hs (show 0 ≤ μ / 2 by positivity)
  have hx : 0 ≤ μ / 2 * ‖x - y0‖ ^ 2 := by positivity
  dsimp only [penalty] at *
  linarith

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
lemma surrogate_mean_gap {S : Type*} [Fintype S] [Nonempty S]
    (f : Fin n → E → ℝ) {γ μ ρ B : ℝ} (hμ : 0 ≤ μ)
    (c y0 u v : E) (X : S → E) (hv : v ∈ Metric.closedBall y0 ρ)
    (hmin : IsMinOn (objective (fun i z => f i z + penalty γ μ c y0 z))
      (Metric.closedBall y0 ρ) u)
    (hgap : (𝔼 s, (objective (fun i z => f i z + penalty γ μ c y0 z) (X s) -
      objective (fun i z => f i z + penalty γ μ c y0 z) u)) ≤ B) :
    (𝔼 s, ((objective f (X s) + γ * value (X s - c)) -
      (objective f v + γ * value (v - c)))) ≤ B + μ / 2 * ρ ^ 2 := by
  have hh := Finset.expect_le_expect (s := Finset.univ)
    (fun s _ => surrogate_gap f hμ c y0 u v (X s) hv hmin)
  rw [Finset.expect_add_distrib, Fintype.expect_const] at hh
  linarith

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
lemma surrogate_failure_fraction {S : Type*} [Fintype S]
    (f : Fin n → E → ℝ) {γ μ ρ Δ B : ℝ} (hμ : 0 ≤ μ) (hΔ : 0 < Δ)
    (c y0 u v : E) (X : S → E) (hv : v ∈ Metric.closedBall y0 ρ)
    (hX : ∀ s, X s ∈ Metric.closedBall y0 ρ)
    (hmin : IsMinOn (objective (fun i z => f i z + penalty γ μ c y0 z))
      (Metric.closedBall y0 ρ) u) (hbias : μ / 2 * ρ ^ 2 = Δ / 32)
    (hgap : (𝔼 s, (objective (fun i z => f i z + penalty γ μ c y0 z) (X s) -
      objective (fun i z => f i z + penalty γ μ c y0 z) u)) ≤ B) :
    (𝔼 s, (if (objective f (X s) + γ * value (X s - c)) -
      (objective f v + γ * value (v - c)) > 3 * Δ / 4 then (1 : ℝ) else 0)) ≤
        B / (23 * Δ / 32) := by
  classical
  have ht : 0 < 23 * Δ / 32 := by positivity
  have hp (s : S) :
      (if (objective f (X s) + γ * value (X s - c)) -
        (objective f v + γ * value (v - c)) > 3 * Δ / 4 then (1 : ℝ) else 0) ≤
      (objective (fun i z => f i z + penalty γ μ c y0 z) (X s) -
        objective (fun i z => f i z + penalty γ μ c y0 z) u) / (23 * Δ / 32) := by
    have hh := surrogate_gap f hμ c y0 u v (X s) hv hmin
    rw [hbias] at hh
    split_ifs with h
    · apply (le_div_iff₀ ht).mpr
      linarith
    · exact div_nonneg (sub_nonneg.mpr (hmin (hX s))) ht.le
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun s _ => hp s)
  rw [← Finset.expect_div] at hh
  exact hh.trans (div_le_div_of_nonneg_right hgap ht.le)

omit [NeZero n] in
lemma reverse_gap_at_min {F : E → ℝ} (hf : ContDiff ℝ 3 F)
    (hc : ConvexOn ℝ Set.univ F) {L ρ : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient F)) x -
      fderiv ℝ (fderiv ℝ (gradient F)) y‖ ≤ L * ‖x - y‖)
    (y u : E) (hu : u ∈ Metric.closedBall y ρ)
    (hmin : IsMinOn F (Metric.closedBall y ρ) u) :
    F u - F y - ⟪gradient F y, u - y⟫ ≤ 2 * (F y - F u) + 4 * L * ρ ^ 4 := by
  have hρ : 0 ≤ ρ := (norm_nonneg (u - y)).trans
    (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hu)
  have hy : y ∈ Metric.closedBall y ρ := by simpa using hρ
  have hh := PowerMirrorGeometry.minimizer_derivative_nonneg
    (convex_closedBall y ρ) hu hy hmin
    ((hf.differentiable (by norm_num) u).hasGradientAt.hasFDerivAt)
  simp only [InnerProductSpace.toDual_apply_apply] at hh
  have hr := ThirdSmoothJensen.reverse_bregman_bound hf hc hL hT u (y - u)
  have he : u + (y - u) = y := by abel
  rw [he] at hr
  have hn : ‖y - u‖ ≤ ρ := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hu
  have hp := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg (y - u)) hn 4) (show 0 ≤ 4 * L by positivity)
  linarith

lemma initial_potential {F : E → ℝ} (hf : ContDiff ℝ 3 F)
    (hc : ConvexOn ℝ Set.univ F) {L ρ η Δ : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient F)) x -
      fderiv ℝ (fderiv ℝ (gradient F)) y‖ ≤ L * ‖x - y‖)
    (y u : E) (hu : u ∈ Metric.closedBall y ρ)
    (hmin : IsMinOn F (Metric.closedBall y ρ) u) (hgap : F y - F u ≤ Δ)
    (htune : η * (2 * Δ + 4 * L * ρ ^ 4) ≤ ρ ^ 2 / 2) :
    ‖y - u‖ ^ 2 / 2 + (n : ℝ) * (η * (F u - F y - ⟪gradient F y, u - y⟫)) ≤
      (n : ℝ) * ρ ^ 2 := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))
  have hd := reverse_gap_at_min hf hc hL hT y u hu hmin
  have hdist : ‖y - u‖ ≤ ρ := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hu
  have hs := pow_le_pow_left₀ (norm_nonneg (y - u)) hdist 2
  have hb : η * (F u - F y - ⟪gradient F y, u - y⟫) ≤ ρ ^ 2 / 2 :=
    (mul_le_mul_of_nonneg_left (hd.trans (by linarith)) hη).trans htune
  have hb' := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg n)
  have hn' := mul_le_mul_of_nonneg_right hn (sq_nonneg ρ)
  linarith

lemma regularized_initial_potential (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    {L γ μ ρ η Δ : ℝ} (hL : 0 ≤ L) (hγ : 0 ≤ γ) (hμ : 0 ≤ μ) (hη : 0 ≤ η)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖)
    (c y0 v u : E) (hu : u ∈ Metric.closedBall y0 ρ)
    (hminF : ∀ x, objective f v + γ * value (v - c) ≤ objective f x + γ * value (x - c))
    (hgap : (objective f y0 + γ * value (y0 - c)) -
      (objective f v + γ * value (v - c)) ≤ Δ)
    (hmin : IsMinOn (objective (fun i z => f i z + penalty γ μ c y0 z))
      (Metric.closedBall y0 ρ) u)
    (htune : η * (2 * Δ + 4 * (L + 6 * γ) * ρ ^ 4) ≤ ρ ^ 2 / 2) :
    let F := objective (fun i z => f i z + penalty γ μ c y0 z)
    ‖y0 - u‖ ^ 2 / 2 + (n : ℝ) * (η * (F u - F y0 - ⟪gradient F y0, u - y0⟫)) ≤
      (n : ℝ) * ρ ^ 2 := by
  let g := fun i z => f i z + penalty γ μ c y0 z
  have hgf := QuarticFiniteSum.component_contDiff f hf γ μ c y0
  have hgc := QuarticFiniteSum.component_convex f hf hc hγ hμ c y0
  have hgT := fun i x y => QuarticFiniteSum.component_third_lipschitz f hf (μ := μ) hγ hT c y0 x y i
  have hg0 : objective g y0 - objective g u ≤ Δ := by
    dsimp [g]
    rw [QuarticFiniteSum.objective_penalty, QuarticFiniteSum.objective_penalty]
    simp only [penalty, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
    have hh := hminF u
    have hp : 0 ≤ μ / 2 * ‖u - y0‖ ^ 2 := by positivity
    linarith
  exact initial_potential (FiniteSumThirdSmoothGeometry.objective_contDiff g hgf)
    (OracleTemplate.FiniteSum.objective_convex hgc) (by positivity) hη
    (FiniteSumThirdSmoothGeometry.objective_third_lipschitz g hgf hgT) y0 u hu hmin hg0 htune

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero n] in
lemma stage_tuning {L γ ρ Δ : ℝ} (hγ : 0 < γ) (hρ : 0 < ρ) (hΔ : 0 < Δ)
    (hγL : γ ≤ L) (hr : ρ ^ 4 = 12 * Δ / γ) :
    let η := 1 / (32 * L * ρ ^ 2)
    let μ := Δ / (16 * ρ ^ 2)
    32 * η * L * ρ ^ 2 = 1 ∧ μ / 2 * ρ ^ 2 = Δ / 32 ∧
      1 / (η * μ) = 6144 * L / γ ∧
      η * (2 * Δ + 4 * L * ρ ^ 4) ≤ ρ ^ 2 / 2 := by
  have hL : 0 < L := hγ.trans_le hγL
  have hρ0 := ne_of_gt hρ
  have hL0 := ne_of_gt hL
  have hγ0 := ne_of_gt hγ
  have hΔ0 := ne_of_gt hΔ
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · field_simp
  · field_simp
    ring
  · have he : γ * ρ ^ 4 = 12 * Δ := by rw [hr]; field_simp
    field_simp
    nlinarith [he]
  · have he : γ * ρ ^ 4 = 12 * Δ := by rw [hr]; field_simp
    have hb := mul_le_mul_of_nonneg_right hγL (pow_nonneg hρ.le 4)
    rw [one_div, ← div_eq_inv_mul]
    apply (div_le_iff₀ (by positivity : 0 < 32 * L * ρ ^ 2)).mpr
    nlinarith

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero n] in
lemma restart_tuning_bound {η μ K ρ Δ δ : ℝ} (hη : 0 < η) (hμ : 0 < μ)
    (J : ℕ) (hK : 2 * ((n : ℝ) + 1 / (η * μ)) ≤ K)
    (hbias : μ / 2 * ρ ^ 2 = Δ / 32) (hJ : (n : ℝ) * (1 / 2 : ℝ) ^ J ≤ δ / 2) :
    (1 / (η * K)) * (1 / 2 : ℝ) ^ J * ((n : ℝ) * ρ ^ 2) ≤ δ * Δ / 64 := by
  have hKpos : 0 < K := lt_of_lt_of_le (by positivity) hK
  have hK' : 2 / (η * μ) ≤ K := by
    have hh : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    calc
      _ = 2 * (1 / (η * μ)) := by ring
      _ ≤ 2 * ((n : ℝ) + 1 / (η * μ)) := by linarith
      _ ≤ K := hK
  have hm := (div_le_iff₀ (by positivity : 0 < η * μ)).mp hK'
  have hc : 1 / (η * K) ≤ μ / 2 :=
    (div_le_iff₀ (by positivity : 0 < η * K)).mpr (by nlinarith)
  have hΔ : 0 ≤ Δ := by nlinarith [sq_nonneg ρ]
  calc
    _ ≤ (μ / 2) * (1 / 2 : ℝ) ^ J * ((n : ℝ) * ρ ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)
    _ = (Δ / 32) * ((n : ℝ) * (1 / 2 : ℝ) ^ J) := by rw [← hbias]; ring
    _ ≤ (Δ / 32) * (δ / 2) := mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = _ := by ring

lemma gap_bound (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    {L γ μ ρ η : ℝ} (hL : 0 ≤ L) (hγ : 0 < γ) (hμ : 0 < μ) (hρ : 0 ≤ ρ) (hη : 0 < η)
    (hstep : 32 * η * (L + 6 * γ) * ρ ^ 2 ≤ 1)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖)
    (c y0 y u : E) (hy : y ∈ Metric.closedBall y0 ρ) (hu : u ∈ Metric.closedBall y0 ρ)
    (hmin : IsMinOn (objective (fun i z => f i z + penalty γ μ c y0 z)) (Metric.closedBall y0 ρ) u)
    (m J : ℕ) (hK : 2 * ((n : ℝ) + 1 / (η * μ)) ≤ (n * m : ℕ)) :
    let F := objective (fun i z => f i z + penalty γ μ c y0 z)
    let Φ := fun v => ‖v - u‖ ^ 2 / 2 + (n : ℝ) *
      (η * (F u - F v - ⟪gradient F v, u - v⟫))
    let answer := fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2)
    (𝔼 seeds : Fin (J + 1) → RestartSeed n m,
      (F (eval answer (augmentPlan (augment γ μ c y0) (restarts η ρ y0 m (J + 1) y seeds))) - F u)) ≤
        (1 / (η * (n * m : ℕ))) * (1 / 2 : ℝ) ^ J * Φ y := by
  let g := fun i z => f i z + penalty γ μ c y0 z
  let F := objective g
  let Φ := fun v => ‖v - u‖ ^ 2 / 2 + (n : ℝ) *
    (η * (F u - F v - ⟪gradient F v, u - v⟫))
  let answer := fun q : Fin n × E => (gradient (g q.1) q.2, fderiv ℝ (gradient (g q.1)) q.2)
  have hgf := QuarticFiniteSum.component_contDiff f hf γ μ c y0
  have hgc := QuarticFiniteSum.component_convex f hf hc hγ.le hμ.le c y0
  have hgT := fun i x y => QuarticFiniteSum.component_third_lipschitz f hf (μ := μ) hγ.le hT c y0 x y i
  have hLs : 0 < L + 6 * γ := by positivity
  have hΦ (v : E) : 0 ≤ Φ v := add_nonneg (by positivity) (mul_nonneg (by positivity)
    (mul_nonneg hη.le (FiniteSumThirdSmoothGeometry.bregman_nonneg g hgf hgc u v)))
  have hKpos : (0 : ℝ) < (n * m : ℕ) := lt_of_lt_of_le (by positivity) hK
  have hq : ((n : ℝ) + 1 / (η * μ)) / (n * m : ℕ) ≤ 1 / 2 :=
    (div_le_iff₀ hKpos).mpr (by linarith only [hK])
  have hr (v : E) (hv : v ∈ Metric.closedBall y0 ρ) :
      (𝔼 seed : RestartSeed n m, Φ (eval answer (restart η ρ y0 v m seed.1 seed.2))) ≤ (1 / 2) * Φ v := by
    have hh := TaylorCorrectedConvergence.restart_contraction g hgf hgc hLs hρ hη hμ hstep hgT
      y0 v u hv hu hmin (fun x _ => QuarticFiniteSum.objective_strong_support f hf hc hγ.le c y0 x u) m
    simp only [RestartSeed, ← Finset.univ_product_univ, Finset.expect_product]
    exact hh.trans (mul_le_mul_of_nonneg_right hq (hΦ v))
  have hg (v : E) (hv : v ∈ Metric.closedBall y0 ρ) :
      (𝔼 seed : RestartSeed n m, (F (eval answer (restart η ρ y0 v m seed.1 seed.2)) - F u)) ≤
        (1 / (η * (n * m : ℕ))) * Φ v := by
    have hh := TaylorCorrectedConvergence.restart_gap_bound g hgf hgc hLs hρ hη hstep hgT y0 v u hv hu m
    simp only [RestartSeed, ← Finset.univ_product_univ, Finset.expect_product]
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one, Φ, F, answer] using hh
  have hh := TaylorCorrectedConvergence.restarts_gap answer hρ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by positivity : 0 ≤ 1 / (η * (n * m : ℕ))) η y0 m Φ (fun v => F v - F u) hr hg J y hy
  dsimp only [answer, g, F, Φ] at hh
  dsimp only
  simpa only [TaylorCorrectedStep.eval_augmentPlan, QuarticFiniteSum.augment_answer f hf] using hh

lemma stage_failure (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    {L γ ρ Δ δ : ℝ} (hL : 0 ≤ L) (hγ : 0 < γ) (hρ : 0 < ρ) (hΔ : 0 < Δ)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖)
    (hr : ρ ^ 4 = 12 * Δ / γ) (c y0 v : E)
    (hminF : ∀ x, objective f v + γ * value (v - c) ≤ objective f x + γ * value (x - c))
    (hgap : (objective f y0 + γ * value (y0 - c)) -
      (objective f v + γ * value (v - c)) ≤ Δ)
    (m J : ℕ) (hK : 2 * ((n : ℝ) + 6144 * (L + 6 * γ) / γ) ≤ (n * m : ℕ))
    (hJ : (n : ℝ) * (1 / 2 : ℝ) ^ J ≤ δ / 2) :
    let η := 1 / (32 * (L + 6 * γ) * ρ ^ 2)
    let μ := Δ / (16 * ρ ^ 2)
    let answer := fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2)
    let X := fun seeds : Fin (J + 1) → RestartSeed n m =>
      eval answer (augmentPlan (augment γ μ c y0) (restarts η ρ y0 m (J + 1) y0 seeds))
    (𝔼 seeds, (if (objective f (X seeds) + γ * value (X seeds - c)) -
      (objective f v + γ * value (v - c)) > 3 * Δ / 4 then (1 : ℝ) else 0)) ≤ δ / 46 := by
  classical
  have hγ0 := ne_of_gt hγ
  have hΔ0 := ne_of_gt hΔ
  let η := 1 / (32 * (L + 6 * γ) * ρ ^ 2)
  let μ := Δ / (16 * ρ ^ 2)
  let answer := fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2)
  let X := fun seeds : Fin (J + 1) → RestartSeed n m =>
    eval answer (augmentPlan (augment γ μ c y0) (restarts η ρ y0 m (J + 1) y0 seeds))
  have hη : 0 < η := by dsimp [η]; positivity
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have ht := stage_tuning hγ hρ hΔ (by linarith : γ ≤ L + 6 * γ) hr
  change 32 * η * (L + 6 * γ) * ρ ^ 2 = 1 ∧ μ / 2 * ρ ^ 2 = Δ / 32 ∧
    1 / (η * μ) = 6144 * (L + 6 * γ) / γ ∧
    η * (2 * Δ + 4 * (L + 6 * γ) * ρ ^ 4) ≤ ρ ^ 2 / 2 at ht
  have hK' : 2 * ((n : ℝ) + 1 / (η * μ)) ≤ (n * m : ℕ) := by rw [ht.2.2.1]; exact hK
  have hy0 : y0 ∈ Metric.closedBall y0 ρ := by simpa using hρ.le
  obtain ⟨u, hu, hmin⟩ := exists_stage_min f hf γ μ c y0 hρ.le
  have hv : v ∈ Metric.closedBall y0 ρ := quartic_min_mem
    ((FiniteSumThirdSmoothGeometry.objective_contDiff f hf).differentiable (by norm_num))
    (OracleTemplate.FiniteSum.objective_convex hc) hγ hρ.le
    (by rw [hr]; field_simp) c v y0 hminF hgap
  have hinit := regularized_initial_potential f hf hc hL hγ.le hμ.le hη.le hT
    c y0 v u hu hminF hgap hmin ht.2.2.2
  have hgb := gap_bound f hf hc hL hγ hμ hρ.le hη ht.1.le hT
    c y0 y0 u hy0 hu hmin m J hK'
  have hbound : (𝔼 seeds, (objective (fun i z => f i z + penalty γ μ c y0 z) (X seeds) -
      objective (fun i z => f i z + penalty γ μ c y0 z) u)) ≤ δ * Δ / 64 := by
    exact hgb.trans ((mul_le_mul_of_nonneg_left hinit (by positivity)).trans
      (restart_tuning_bound hη hμ J hK' ht.2.1 hJ))
  have hX (seeds : Fin (J + 1) → RestartSeed n m) : X seeds ∈ Metric.closedBall y0 ρ := by
    dsimp [X]
    rw [TaylorCorrectedStep.eval_augmentPlan]
    exact TaylorCorrectedConvergence.restarts_mem _ hρ.le η y0 m (J + 1) y0 hy0 seeds
  have hh := surrogate_failure_fraction f hμ.le hΔ c y0 u v X hv hX hmin ht.2.1 hbound
  have he : (δ * Δ / 64) / (23 * Δ / 32) = δ / 46 := by field_simp; ring
  rw [he] at hh
  exact hh

end LongTails.Proofs.QuarticFiniteSumStage
