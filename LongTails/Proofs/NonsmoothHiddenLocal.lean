import LongTails.Proofs.NonsmoothHiddenGeometry
import LongTails.Algorithms.NonsmoothHiddenAveraging

open Set Metric InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.NonsmoothHidden

open LocalHiddenConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma averageQuery_identity (k : ℕ) (x z : E) :
    ((k : ℝ) + 1) • averageQuery k x z = (k : ℝ) • x + z := by
  unfold averageQuery
  rw [smul_add, smul_smul, smul_smul]
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  simp

lemma averageQuery_mem (k : ℕ) {b x z : E} {r : ℝ}
    (hx : x ∈ closedBall b r) (hz : z ∈ closedBall b r) :
    averageQuery k x z ∈ closedBall b r := by
  apply (convex_closedBall b r) hx hz (by positivity) (by positivity)
  field_simp

lemma averageQuery_displacement (k : ℕ) (x z : E) :
    ‖averageQuery k x z - x‖ = ‖z - x‖ / ((k : ℝ) + 1) := by
  have he : averageQuery k x z - x = (1 / ((k : ℝ) + 1)) • (z - x) := by
    have hi := averageQuery_identity k x z
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    apply (smul_right_injective E hk)
    simp only [smul_sub, smul_smul] at hi ⊢
    rw [hi, add_smul, one_smul]
    field_simp
    simp only [one_smul]
    abel
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  ring

omit [InnerProductSpace ℝ E] in
lemma norm_sub_ball {b x y : E} {r s : ℝ}
    (hx : x ∈ closedBall b r) (hy : y ∈ closedBall b s) : ‖x - y‖ ≤ r + s := by
  have hx' : ‖x - b‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hx
  have hy' : ‖b - y‖ ≤ s := by
    simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev b y] using hy
  have he : x - y = (x - b) + (b - y) := by abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hx' hy')

lemma correction_bound [FiniteDimensional ℝ E] {c : E → E}
    {J : E → E →L[ℝ] E} {μ LJ : ℝ} (hμ : 0 < μ)
    (hJ : ∀ x v, μ * ‖v‖ ≤ ‖J x v‖)
    (hTaylor : ∀ x y, ‖c y - c x - J x (y - x)‖ ≤ LJ * ‖y - x‖ ^ 2)
    (x y : E) : ‖corr c J x y‖ ≤ LJ / μ * ‖y - x‖ ^ 2 := by
  have hp := exists_preimage hμ (hJ x) (c y - c x)
  have hb := corr_norm hp (hJ x) (hTaylor x y)
  calc ‖corr c J x y‖ ≤ (LJ * ‖y - x‖ ^ 2) / μ :=
      (le_div_iff₀ hμ).2 (by simpa only [mul_comm] using hb)
    _ = LJ / μ * ‖y - x‖ ^ 2 := by ring

lemma correction_small [FiniteDimensional ℝ E] {c : E → E}
    {J : E → E →L[ℝ] E} {μ LJ r : ℝ} (hμ : 0 < μ) (hLJ : 0 ≤ LJ)
    (hr : 0 ≤ r) (hreg : 64 * LJ * r ≤ μ)
    (hJ : ∀ x v, μ * ‖v‖ ≤ ‖J x v‖)
    (hTaylor : ∀ x y, ‖c y - c x - J x (y - x)‖ ≤ LJ * ‖y - x‖ ^ 2)
    {b x u : E} (hx : x ∈ closedBall b (2 * r)) (hu : u ∈ closedBall b r) :
    ‖corr c J x u‖ ≤ 9 * (LJ / μ) * r ^ 2 ∧ ‖corr c J x u‖ ≤ r := by
  have hn : ‖u - x‖ ≤ 3 * r := by
    have h := norm_sub_ball hu hx
    linarith
  have hb := correction_bound hμ hJ hTaylor x u
  have hM : 0 ≤ LJ / μ := div_nonneg hLJ hμ.le
  have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 2) hM
  have hsmall : 64 * (LJ / μ) * r ≤ 1 := by
    calc 64 * (LJ / μ) * r = (64 * LJ * r) / μ := by ring
      _ ≤ 1 := (div_le_one hμ).2 hreg
  constructor
  · nlinarith
  · nlinarith [mul_le_mul_of_nonneg_right hsmall hr]

lemma objective_gap_bound [FiniteDimensional ℝ E] {F H : E → ℝ} {c : E → E}
    {J : E → E →L[ℝ] E} {p : E → E} {μ LJ G R : ℝ}
    (hμ : 0 < μ) (hLJ : 0 ≤ LJ) (hG : 0 ≤ G)
    (hJ : ∀ x v, μ * ‖v‖ ≤ ‖J x v‖)
    (hTaylor : ∀ x y, ‖c y - c x - J x (y - x)‖ ≤ LJ * ‖y - x‖ ^ 2)
    (heq : ∀ x, F x = H (c x)) {x u : E}
    (hp : LongTails.Setups.NonsmoothHiddenConvex.IsPulledSubgradient H c J p x)
    (hpG : ‖p x‖ ≤ G) (hxu : ‖u - x‖ ≤ R) :
    F x - F u ≤ G * (R + (LJ / μ) * R ^ 2) := by
  have hs := subgradient_support heq hp (exists_preimage hμ (hJ x) (c u - c x))
  have hq := (correction_bound hμ hJ hTaylor x u).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hxu 2)
      (div_nonneg hLJ hμ.le))
  have hi : -⟪p x, u - x⟫ ≤ G * R :=
    ((neg_le_abs _).trans (abs_real_inner_le_norm _ _)).trans
      (mul_le_mul hpG hxu (norm_nonneg _) hG)
  have hiq : -⟪p x, corr c J x u⟫ ≤ G * ((LJ / μ) * R ^ 2) :=
    ((neg_le_abs _).trans (abs_real_inner_le_norm _ _)).trans
      (mul_le_mul hpG hq (norm_nonneg _) hG)
  linarith

lemma local_gap_abs_le [FiniteDimensional ℝ E] {F H : E → ℝ} {c : E → E}
    {J : E → E →L[ℝ] E} {p : E → E} {μ LJ G r : ℝ}
    (hμ : 0 < μ) (hLJ : 0 ≤ LJ) (hG : 0 ≤ G) (hr : 0 ≤ r)
    (hreg : 64 * LJ * r ≤ μ) (hJ : ∀ x v, μ * ‖v‖ ≤ ‖J x v‖)
    (hTaylor : ∀ x y, ‖c y - c x - J x (y - x)‖ ≤ LJ * ‖y - x‖ ^ 2)
    (heq : ∀ x, F x = H (c x))
    (hp : ∀ x, LongTails.Setups.NonsmoothHiddenConvex.IsPulledSubgradient H c J p x)
    (hpG : ∀ x, ‖p x‖ ≤ G) {b x u : E}
    (hx : x ∈ closedBall b (2 * r)) (hu : u ∈ closedBall b r) :
    |F x - F u| ≤ 4 * G * r := by
  have hxu : ‖u - x‖ ≤ 3 * r := by linarith [norm_sub_ball hu hx]
  have hux : ‖x - u‖ ≤ 3 * r := by rw [norm_sub_rev]; exact hxu
  have h1 := objective_gap_bound hμ hLJ hG hJ hTaylor heq (hp x) (hpG x) hxu
  have h2 := objective_gap_bound hμ hLJ hG hJ hTaylor heq (hp u) (hpG u) hux
  have hsmall : 64 * (LJ / μ) * r ≤ 1 := by
    calc 64 * (LJ / μ) * r = (64 * LJ * r) / μ := by ring
      _ ≤ 1 := (div_le_one hμ).2 hreg
  have hcurv : (LJ / μ) * (3 * r) ^ 2 ≤ r := by
    nlinarith [mul_le_mul_of_nonneg_right hsmall hr,
      mul_nonneg (div_nonneg hLJ hμ.le) (sq_nonneg r)]
  have hb := mul_le_mul_of_nonneg_left hcurv hG
  rw [abs_le]
  constructor <;> nlinarith

lemma correction_lipschitz_local [FiniteDimensional ℝ E] {c : E → E}
    {J : E → E →L[ℝ] E} {μ LJ r : ℝ} (hμ : 0 < μ) (hLJ : 0 ≤ LJ)
    (hr : 0 ≤ r) (hreg : 64 * LJ * r ≤ μ)
    (hJ : ∀ x v, μ * ‖v‖ ≤ ‖J x v‖)
    (hTaylor : ∀ x y, ‖c y - c x - J x (y - x)‖ ≤ LJ * ‖y - x‖ ^ 2)
    (hlip : ∀ x y, ‖J x - J y‖ ≤ LJ * ‖x - y‖)
    {b x y u : E} (hx : x ∈ closedBall b (2 * r))
    (hy : y ∈ closedBall b (2 * r)) (hu : u ∈ closedBall b r) :
    ‖corr c J x u - corr c J y u‖ ≤ 8 * (LJ / μ) * r * ‖x - y‖ := by
  have hpx := exists_preimage hμ (hJ x) (c u - c x)
  have hpy := exists_preimage hμ (hJ y) (c u - c y)
  have h := corr_lipschitz hpx hpy (hJ x) (hTaylor y x) (hlip x y)
  have hxy : ‖x - y‖ ≤ 4 * r := by linarith [norm_sub_ball hx hy]
  have hux : ‖u - x‖ ≤ 3 * r := by linarith [norm_sub_ball hu hx]
  have hqy := (correction_small hμ hLJ hr hreg hJ hTaylor hy hu).2
  have hs : ‖x - y‖ + ‖u - x‖ + ‖corr c J y u‖ ≤ 8 * r := by linarith
  have hb := h.trans (mul_le_mul_of_nonneg_left hs (by positivity))
  calc ‖corr c J x u - corr c J y u‖ ≤ (LJ * ‖x - y‖ * (8 * r)) / μ :=
      (le_div_iff₀ hμ).2 (by simpa only [mul_comm] using hb)
    _ = 8 * (LJ / μ) * r * ‖x - y‖ := by ring

lemma local_average_displacement (k : ℕ) {b x z : E} {r : ℝ}
    (hx : x ∈ closedBall b (2 * r)) (hz : z ∈ closedBall b (2 * r)) :
    ‖averageQuery k x z - x‖ ≤ 4 * r / ((k : ℝ) + 1) := by
  rw [averageQuery_displacement]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith [norm_sub_ball hz hx]

lemma correction_drift_bound {D M r t : ℝ} {z u qold q : E}
    (hD : 0 ≤ D) (hr : 0 ≤ r)
    (hzu : ‖z - u‖ ≤ 3 * r) (hq : ‖qold - q‖ ≤ 8 * M * r * (4 * r / t)) :
    D * ⟪z - u, qold - q⟫ ≤ 96 * D * M * r ^ 3 / t := by
  calc D * ⟪z - u, qold - q⟫ ≤ D * (‖z - u‖ * ‖qold - q‖) :=
      mul_le_mul_of_nonneg_left (real_inner_le_norm _ _) hD
    _ ≤ D * ((3 * r) * (8 * M * r * (4 * r / t))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hzu hq (norm_nonneg _) (by positivity)) hD
    _ = 96 * D * M * r ^ 3 / t := by ring

lemma previous_support_bound (k : ℕ) {G M r : ℝ} {p q : E}
    (hG : 0 ≤ G) (hM : 0 ≤ M)
    (hp : ‖p‖ ≤ G) (hq : ‖q‖ ≤ M * (4 * r / ((k : ℝ) + 1)) ^ 2) :
    -(k : ℝ) * ⟪p, q⟫ ≤ 16 * G * M * r ^ 2 / ((k : ℝ) + 1) := by
  have hi : -⟪p, q⟫ ≤ ‖p‖ * ‖q‖ :=
    (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
  calc -(k : ℝ) * ⟪p, q⟫ = (k : ℝ) * (-⟪p, q⟫) := by ring
    _ ≤ (k : ℝ) * (‖p‖ * ‖q‖) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ ≤ (k : ℝ) * (G * (M * (4 * r / ((k : ℝ) + 1)) ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hp hq (norm_nonneg _) hG) (by positivity)
    _ ≤ ((k : ℝ) + 1) * (G * (M * (4 * r / ((k : ℝ) + 1)) ^ 2)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 16 * G * M * r ^ 2 / ((k : ℝ) + 1) := by
      field_simp
      ring

lemma averaged_energy_step {F H : E → ℝ} {c : E → E} {J : E → E →L[ℝ] E}
    {p : E → E} {b x old z u g : E} {t r D : ℝ}
    (ht : 1 ≤ t) (hr : 0 ≤ r) (hD : 0 < D)
    (hx : t • x = (t - 1) • old + z) (hu : ‖u - b‖ ≤ r)
    (hq : ‖corr c J x u‖ ≤ r) (heq : ∀ y, F y = H (c y))
    (hp : LongTails.Setups.NonsmoothHiddenConvex.IsPulledSubgradient H c J p x)
    (hpreu : ∃ v, J x v = c u - c x) (hpreold : ∃ v, J x v = c old - c x) :
    let z' := ballProj b (2 * r) (z - D⁻¹ • g)
    t * (F x - F u) + D / 2 * ‖z' - u‖ ^ 2 - D * ⟪z' - u, corr c J x u⟫ ≤
      (t - 1) * (F old - F u) + D / 2 * ‖z - u‖ ^ 2 -
        D * ⟪z - u, corr c J old u⟫ + ‖g‖ ^ 2 / (2 * D) +
        D * ⟪z - u, corr c J old u - corr c J x u⟫ -
        ⟪g - p x, z - u - corr c J x u⟫ -
        (t - 1) * ⟪p x, corr c J x old⟫ := by
  dsimp only
  have hs := averaged_support hx heq hp hpreu hpreold ht
  have hm := corrected_projected_step (z := z) (g := g) hr hD hu hq
  dsimp only at hm
  simp only [inner_sub_left, inner_sub_right] at hs hm ⊢
  nlinarith

end OracleTemplate.NonsmoothHidden
