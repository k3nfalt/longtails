import LongTails.Proofs.PLMinimaxEnvelope
import LongTails.Proofs.AuxiliaryInner
import LongTails.Proofs.RecursiveEnvelopeGeometry
import LongTails.Proofs.PLMinimaxValue

open scoped RealInnerProductSpace

namespace LongTails.Proofs.HeavyTailSaddleGeometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma proximal_primal_bounds {G : E → E} {L : ℝ} (hL : 0 ≤ L)
    (c x y : E) (hl : ‖G x - G y‖ ≤ L * ‖x - y‖) :
    L * ‖x - y‖ ^ 2 ≤
      ⟪(G x + (2 * L) • (x - c)) - (G y + (2 * L) • (y - c)), x - y⟫ ∧
    ‖(G x + (2 * L) • (x - c)) - (G y + (2 * L) • (y - c))‖ ≤
      (3 * L) * ‖x - y‖ := by
  have heq : (G x + (2 * L) • (x - c)) - (G y + (2 * L) • (y - c)) =
      (G x - G y) + (2 * L) • (x - y) := by module
  rw [heq]
  constructor
  · rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have hi := (abs_le.mp (abs_real_inner_le_norm (G x - G y) (x - y))).1
    have hh := mul_le_mul_of_nonneg_right hl (norm_nonneg (x - y))
    nlinarith only [hi, hh]
  · have hh := norm_add_le (G x - G y) ((2 * L) • (x - y))
    rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * L)] at hh
    nlinarith only [hh, hl]

omit [InnerProductSpace ℝ F] in
lemma zero_sensitivity {G : E → F → E} {L : ℝ} (hL : 0 < L)
    (u v : E) (x y : F) (hu : G u x = 0) (hv : G v y = 0)
    (hm : L * ‖u - v‖ ^ 2 ≤ ⟪G u x - G v x, u - v⟫)
    (hl : ‖G v x - G v y‖ ≤ L * ‖x - y‖) :
    ‖u - v‖ ≤ ‖x - y‖ := by
  have heq : G u x - G v x = -(G v x - G v y) := by rw [hu, hv]; simp
  have hn : ‖G u x - G v x‖ ≤ L * ‖x - y‖ := by
    rw [heq, norm_neg]
    exact hl
  have hh := (real_inner_le_norm (G u x - G v x) (u - v)).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  have hd : ‖u - v‖ ^ 2 ≤ ‖x - y‖ * ‖u - v‖ := by
    apply (mul_le_mul_iff_right₀ hL).mp
    nlinarith only [hm, hh]
  by_contra h
  have hlt : ‖x - y‖ < ‖u - v‖ := lt_of_not_ge h
  have hp : 0 < ‖u - v‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  nlinarith

omit [InnerProductSpace ℝ F] in
lemma proximal_zero_map [CompleteSpace E] {G : E → F → E} {L : ℝ} (hL : 0 < L)
    (c : E) (hx : ∀ x u v, ‖G u x - G v x‖ ≤ L * ‖u - v‖)
    (hy : ∀ u x y, ‖G u x - G u y‖ ≤ L * ‖x - y‖) :
    ∃ U : F → E, (∀ y, G (U y) y + (2 * L) • (U y - c) = 0) ∧
      ∀ x y, ‖U x - U y‖ ≤ ‖x - y‖ := by
  have hex (y : F) : ∃ u, G u y + (2 * L) • (u - c) = 0 := by
    apply RecursiveEnvelopeGeometry.exists_zero (μ := L) (M := 3 * L) hL (by linarith)
    · intro u v
      exact (proximal_primal_bounds (G := fun u => G u y) hL.le c u v (hx y u v)).1
    · intro u v
      exact (proximal_primal_bounds (G := fun u => G u y) hL.le c u v (hx y u v)).2
  choose U hU using hex
  refine ⟨U, hU, ?_⟩
  intro x y
  apply zero_sensitivity (G := fun u y => G u y + (2 * L) • (u - c))
    hL (U x) (U y) x y (hU x) (hU y)
  · exact (proximal_primal_bounds (G := fun u => G u x) hL.le c (U x) (U y) (hx x (U x) (U y))).1
  · have heq : (G (U y) x + (2 * L) • (U y - c)) -
        (G (U y) y + (2 * L) • (U y - c)) = G (U y) x - G (U y) y := by abel
    rw [heq]
    exact hy (U y) x y

omit [InnerProductSpace ℝ E] in
lemma reference_refresh_energy {m B R : ℝ} (hm : 0 < m)
    (hscale : m * R ^ 2 = B) (reference target optimum : E)
    (hnew : ‖reference - target‖ ≤ R / 16)
    (hmove : ‖target - optimum‖ ≤ 5 * R / 8) :
    m * ‖reference - optimum‖ ^ 2 ≤ B / 2 := by
  have hn : ‖reference - optimum‖ ≤ 11 * R / 16 :=
    (norm_sub_le_norm_sub_add_norm_sub reference target optimum).trans (by linarith)
  have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 2) hm.le
  have hB : 0 ≤ B := by rw [← hscale]; positivity
  nlinarith only [hs, hscale, hB]

lemma monotone_step_sq {G : E → E} {L α η : ℝ} (hη : 0 ≤ η)
    (x y : E) (hm : α * ‖x - y‖ ^ 2 ≤ ⟪G x - G y, x - y⟫)
    (hl : ‖G x - G y‖ ≤ L * ‖x - y‖) :
    ‖(x - η • G x) - (y - η • G y)‖ ^ 2 ≤
      (1 - 2 * η * α + η ^ 2 * L ^ 2) * ‖x - y‖ ^ 2 := by
  have hs : ‖G x - G y‖ ^ 2 ≤ L ^ 2 * ‖x - y‖ ^ 2 := by
    simpa [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hl 2
  have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2 * η by positivity)
  rw [real_inner_comm] at hm'
  have hs' := mul_le_mul_of_nonneg_left hs (sq_nonneg η)
  rw [show (x - η • G x) - (y - η • G y) = (x - y) - η • (G x - G y) by module,
    norm_sub_sq_real, norm_smul, Real.norm_of_nonneg hη, inner_smul_right]
  nlinarith

lemma fast_step_contraction {G : E → E} {L : ℝ} (hL : 0 < L)
    (x y : E) (hm : L / 4 * ‖x - y‖ ^ 2 ≤ ⟪G x - G y, x - y⟫)
    (hl : ‖G x - G y‖ ≤ L * ‖x - y‖) :
    ‖(x - (1 / (4 * L)) • G x) - (y - (1 / (4 * L)) • G y)‖ ≤
      (31 / 32 : ℝ) * ‖x - y‖ := by
  have h := monotone_step_sq (by positivity : 0 ≤ 1 / (4 * L)) x y hm hl
  have hc : 1 - 2 * (1 / (4 * L)) * (L / 4) + (1 / (4 * L)) ^ 2 * L ^ 2 =
      (15 / 16 : ℝ) := by field_simp; ring
  rw [hc] at h
  have hn := norm_nonneg ((x - (1 / (4 * L)) • G x) - (y - (1 / (4 * L)) • G y))
  have hd := norm_nonneg (x - y)
  nlinarith [sq_nonneg (‖(x - (1 / (4 * L)) • G x) -
    (y - (1 / (4 * L)) • G y)‖ - (31 / 32 : ℝ) * ‖x - y‖)]

lemma fast_orbit_distance {G : E → E} {L : ℝ} (hL : 0 < L)
    (hm : ∀ x y, L / 4 * ‖x - y‖ ^ 2 ≤ ⟪G x - G y, x - y⟫)
    (hl : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (u x : E) (hu : G u = 0) (n : ℕ) :
    let T := fun z => z - (1 / (4 * L)) • G z
    ‖T^[n] x - u‖ ≤ (31 / 32 : ℝ) ^ n * ‖x - u‖ := by
  intro T
  have hT : LipschitzWith (31 / 32 : NNReal) T :=
    LipschitzWith.of_dist_le_mul (fun a b => by
      simpa [dist_eq_norm, T] using fast_step_contraction hL a b (hm a b) (hl a b))
  have hfixed : T u = u := by simp [T, hu]
  have h := (hT.iterate n).dist_le_mul x u
  simpa [dist_eq_norm, Function.iterate_fixed hfixed n] using h

omit [InnerProductSpace ℝ F] in
lemma fast_orbit_dual_bias {G : E → E} {H : E → F} {L : ℝ} (hL : 0 < L)
    (hm : ∀ x y, L / 4 * ‖x - y‖ ^ 2 ≤ ⟪G x - G y, x - y⟫)
    (hl : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hH : ∀ x y, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (u x : E) (hu : G u = 0) (n : ℕ) :
    let T := fun z => z - (1 / (4 * L)) • G z
    ‖H (T^[n] x) - H u‖ ≤ L * (31 / 32 : ℝ) ^ n * ‖x - u‖ := by
  intro T
  have h := mul_le_mul_of_nonneg_left (fast_orbit_distance hL hm hl u x hu n) hL.le
  exact (hH (T^[n] x) u).trans (by simpa only [mul_assoc] using h)

lemma dual_antimonotone {f : E → ℝ} {g : E → E} {μ : ℝ}
    (hsc : ∀ x y, f y ≤ f x + ⟪g x, y - x⟫ - μ / 2 * ‖y - x‖ ^ 2)
    (x y : E) : μ * ‖x - y‖ ^ 2 ≤ ⟪-g x - -g y, x - y⟫ := by
  have hx := hsc x y
  have hy := hsc y x
  have he : ⟪g x, y - x⟫ = -⟪g x, x - y⟫ := by
    rw [← inner_neg_right, neg_sub]
  rw [he, norm_sub_rev] at hx
  simp only [inner_sub_left, inner_neg_left]
  linarith

lemma dual_attainment [CompleteSpace E] {f : E → ℝ} {g : E → E} {L μ : ℝ}
    (hμ : 0 < μ) (hμL : μ ≤ L)
    (hl : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (hsc : ∀ x y, f y ≤ f x + ⟪g x, y - x⟫ - μ / 2 * ‖y - x‖ ^ 2) :
    ∃ u, g u = 0 ∧ ∀ x, f x ≤ f u := by
  obtain ⟨u, hu⟩ := RecursiveEnvelopeGeometry.exists_zero (G := fun x => -g x) hμ hμL
    (dual_antimonotone hsc) (fun x y => by
      rw [show -g x - -g y = -(g x - g y) by abel, norm_neg]
      exact hl x y)
  have hg : g u = 0 := neg_eq_zero.mp hu
  refine ⟨u, hg, fun x => ?_⟩
  have h := hsc u x
  rw [hg, inner_zero_left] at h
  nlinarith [mul_nonneg hμ.le (sq_nonneg ‖x - u‖)]

lemma dual_pl_bound {f : E → ℝ} {g : E → E} {μ : ℝ} (hμ : 0 < μ)
    (hsc : ∀ x y, f y ≤ f x + ⟪g x, y - x⟫ - μ / 2 * ‖y - x‖ ^ 2)
    (x y : E) : 2 * μ * (f y - f x) ≤ ‖g x‖ ^ 2 := by
  have h := hsc x y
  have hi := real_inner_le_norm (g x) (y - x)
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 2 * μ by positivity)
  have hm' := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2 * μ by positivity)
  nlinarith [sq_nonneg (μ * ‖y - x‖ - ‖g x‖)]

lemma minimax_value_hyp [CompleteSpace E] [CompleteSpace F]
    {f : E → F → ℝ} {gx : E × F → E} {gy : E × F → F} {L μ : ℝ}
    (hμ : 0 < μ) (hμL : μ ≤ L)
    (hgx : ∀ x y, HasGradientAt (fun x' => f x' y) (gx (x, y)) x)
    (hgy : ∀ x y, HasGradientAt (fun y' => f x y') (gy (x, y)) y)
    (hl : ∀ z z' : E × F, ‖gx z - gx z'‖ ^ 2 + ‖gy z - gy z'‖ ^ 2 ≤
      L ^ 2 * (‖z.1 - z'.1‖ ^ 2 + ‖z.2 - z'.2‖ ^ 2))
    (hsc : ∀ x y y', f x y' ≤ f x y + ⟪gy (x, y), y' - y⟫ - μ / 2 * ‖y' - y‖ ^ 2) :
    OracleTemplate.PLMinimax.Hyp f (fun x y => gx (x, y)) (fun x y => gy (x, y)) L μ := by
  have hL : 0 < L := lt_of_lt_of_le hμ hμL
  have hsplit (z z' : E × F) :
      ‖gx z - gx z'‖ ≤ L * (‖z.1 - z'.1‖ + ‖z.2 - z'.2‖) ∧
      ‖gy z - gy z'‖ ≤ L * (‖z.1 - z'.1‖ + ‖z.2 - z'.2‖) := by
    have hd : ‖z.1 - z'.1‖ ^ 2 + ‖z.2 - z'.2‖ ^ 2 ≤
        (‖z.1 - z'.1‖ + ‖z.2 - z'.2‖) ^ 2 := by
      nlinarith [mul_nonneg (norm_nonneg (z.1 - z'.1)) (norm_nonneg (z.2 - z'.2))]
    have hh := (hl z z').trans (mul_le_mul_of_nonneg_left hd (sq_nonneg L))
    rw [← mul_pow] at hh
    have hb : 0 ≤ L * (‖z.1 - z'.1‖ + ‖z.2 - z'.2‖) := by positivity
    constructor
    · nlinarith [sq_nonneg ‖gy z - gy z'‖, norm_nonneg (gx z - gx z')]
    · nlinarith [sq_nonneg ‖gx z - gx z'‖, norm_nonneg (gy z - gy z')]
  refine ⟨hL, hμ, hμL, hgx, hgy, ?_, ?_, ?_, ?_⟩
  · intro x x' y y'
    exact (hsplit (x, y) (x', y')).1
  · intro x x' y y'
    exact (hsplit (x, y) (x', y')).2
  · intro x y y'
    exact dual_pl_bound hμ (hsc x) y y'
  · intro x
    obtain ⟨y, _, hy⟩ := dual_attainment hμ hμL
      (fun y y' => by simpa using (hsplit (x, y) (x, y')).2) (hsc x)
    exact ⟨y, hy⟩

omit [InnerProductSpace ℝ F] in
lemma saddle_shift_energy {L μ : ℝ} (hL : 0 ≤ L) (hμ : 0 ≤ μ)
    (du dc : E) (dv : F)
    (h : L * ‖du‖ ^ 2 + μ * ‖dv‖ ^ 2 ≤ 2 * L * ⟪dc, du⟫) :
    L * ‖du‖ ^ 2 + μ * ‖dv‖ ^ 2 ≤ 4 * L * ‖dc‖ ^ 2 := by
  have hi := real_inner_le_norm dc du
  have hm := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2 * L by positivity)
  have hs := mul_nonneg hL (sq_nonneg (‖du‖ - 2 * ‖dc‖))
  have hv := mul_nonneg hμ (sq_nonneg ‖dv‖)
  nlinarith

omit [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] in
lemma gap_controls_energy {g : E → F → ℝ} {u us : E} {v vs : F}
    {α μ η : ℝ}
    (hu : g us vs + α / 2 * ‖u - us‖ ^ 2 ≤ g u vs)
    (hv : g us v ≤ g us vs - μ / 2 * ‖v - vs‖ ^ 2)
    (hgap : g u vs - g us v ≤ η) :
    α * ‖u - us‖ ^ 2 + μ * ‖v - vs‖ ^ 2 ≤ 2 * η := by
  linarith

lemma warm_start_energy {L μ η D : ℝ} (hL : 0 ≤ L) (hμ : 0 ≤ μ)
    (u us ut : E) (v vs vt : F)
    (hold : L * ‖u - us‖ ^ 2 + μ * ‖v - vs‖ ^ 2 ≤ 2 * η)
    (hshift : L * ‖us - ut‖ ^ 2 + μ * ‖vs - vt‖ ^ 2 ≤ 4 * L * D) :
    L * ‖u - ut‖ ^ 2 + μ * ‖v - vt‖ ^ 2 ≤ 4 * η + 8 * L * D := by
  have hx := AuxiliaryInner.norm_add_sq_le (u - us) (us - ut)
  have hy := AuxiliaryInner.norm_add_sq_le (v - vs) (vs - vt)
  simp only [sub_add_sub_cancel] at hx hy
  have hx' := mul_le_mul_of_nonneg_left hx hL
  have hy' := mul_le_mul_of_nonneg_left hy hμ
  linarith

lemma fine_gradient_transfer {L a b c : ℝ} (hL : 0 ≤ L)
    (g residual displacement error : E)
    (hid : g = residual + (2 * L) • displacement + (2 * L) • error)
    (hr : ‖residual‖ ≤ a) (hd : ‖displacement‖ ≤ b) (he : ‖error‖ ≤ c) :
    ‖g‖ ≤ a + 2 * L * b + 2 * L * c := by
  rw [hid]
  calc
    _ ≤ ‖residual‖ + ‖(2 * L) • displacement‖ + ‖(2 * L) • error‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖residual‖ + 2 * L * ‖displacement‖ + 2 * L * ‖error‖ := by
      simp [norm_smul, Real.norm_of_nonneg (show 0 ≤ 2 * L by positivity)]
    _ ≤ _ := by gcongr

lemma refresh_halving_geometry {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {m B gap : ℝ} (hm : 0 < m) (hB : 0 < B)
    (v z u : F) (ref next : E) (U : F → E)
    (hU : ∀ x y, ‖U x - U y‖ ≤ ‖x - y‖)
    (hen : gap + m / 2 * ‖z - u‖ ^ 2 ≤ 25 * B / 128)
    (hsc : m * ‖v - u‖ ^ 2 ≤ 2 * gap)
    (href : m * ‖ref - U u‖ ^ 2 ≤ B)
    (hnew : ‖next - U v‖ ≤ Real.sqrt (B / m) / 16) :
    ‖ref - U v‖ ≤ 13 * Real.sqrt (B / m) / 8 ∧
      m * ‖next - U u‖ ^ 2 ≤ B / 2 ∧
      gap + m / 2 * ‖v - u‖ ^ 2 ≤ B / 2 := by
  let R := Real.sqrt (B / m)
  have hR : 0 < R := Real.sqrt_pos.mpr (div_pos hB hm)
  have hR2 : m * R ^ 2 = B := by
    dsimp [R]
    rw [Real.sq_sqrt (div_pos hB hm).le]
    field_simp
  have hg : gap ≤ 25 * B / 128 := by nlinarith [mul_nonneg hm.le (sq_nonneg ‖z - u‖)]
  have hv : ‖v - u‖ ≤ 5 * R / 8 := by
    have hsq : ‖v - u‖ ^ 2 ≤ (5 * R / 8) ^ 2 := by
      apply (mul_le_mul_iff_right₀ hm).mp
      nlinarith only [hsc, hg, hR2]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq
  have hr : ‖ref - U u‖ ≤ R := by
    apply (sq_le_sq₀ (norm_nonneg _) hR.le).mp
    apply (mul_le_mul_iff_right₀ hm).mp
    nlinarith only [href, hR2]
  have hmove : ‖U v - U u‖ ≤ 5 * R / 8 := (hU v u).trans hv
  refine ⟨?_, ?_, ?_⟩
  · have hh := norm_sub_le_norm_sub_add_norm_sub ref (U u) (U v)
    rw [norm_sub_rev (U u) (U v)] at hh
    change ‖ref - U v‖ ≤ 13 * R / 8
    linarith
  · have hn := (norm_sub_le_norm_sub_add_norm_sub next (U v) (U u)).trans (add_le_add hnew hmove)
    have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 2) hm.le
    nlinarith only [hs, hR2, hB]
  · nlinarith only [hsc, hg, hB]

open OracleTemplate.PLMinimax OracleTemplate.WeaklyConvexHeavyTailed

lemma proximal_dual_strong_concave {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ : ℝ}
    (H : Hyp f gx gy L μ)
    (hsc : ∀ x y y', f x y' ≤ f x y + ⟪gy x y, y' - y⟫ - μ / 2 * ‖y' - y‖ ^ 2)
    (c : E) (y y' : F) :
    dual f L c y' ≤ dual f L c y + ⟪gy (innerPrimal f L c y) y, y' - y⟫ - μ / 2 * ‖y' - y‖ ^ 2 := by
  have hm := weakProx_min H.hL
    (continuous_iff_continuousAt.mpr (fun x => (H.hgx x y').continuousAt)) (H.slice_weak y') c
    (Set.mem_univ (innerPrimal f L c y))
  change dual f L c y' ≤ f (innerPrimal f L c y) y' + L * ‖innerPrimal f L c y - c‖ ^ 2 at hm
  have hh := hsc (innerPrimal f L c y) y y'
  change dual f L c y' ≤ (f (innerPrimal f L c y) y + L * ‖innerPrimal f L c y - c‖ ^ 2) + _ - _
  linarith only [hm, hh]

lemma proximal_dual_attainment {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ : ℝ}
    (H : Hyp f gx gy L μ)
    (hsc : ∀ x y y', f x y' ≤ f x y + ⟪gy x y, y' - y⟫ - μ / 2 * ‖y' - y‖ ^ 2)
    (c : E) : ∃ u, gy (innerPrimal f L c u) u = 0 ∧ ∀ y, dual f L c y ≤ dual f L c u := by
  exact dual_attainment H.hμ (show μ ≤ 2 * L by linarith [H.hμL, H.hL])
    (H.dual_gradient_lipschitz c) (proximal_dual_strong_concave H hsc c)

end LongTails.Proofs.HeavyTailSaddleGeometry
