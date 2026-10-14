import LongTails.Proofs.HiddenConvexGeometry
import LongTails.Proofs.GdConvex

open Set Metric InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.LocalHiddenConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

structure LocalModel (F H : E → ℝ) (c : E → E) (J : E → E →L[ℝ] E) (U : Set E)
    (x0 : E) (R μ LJ : ℝ) : Prop where
  eq : ∀ x ∈ ball x0 (3 * R), F x = H (c x)
  openU : IsOpen U
  convexH : ConvexOn ℝ U H
  diffH : ∀ u ∈ U, DifferentiableAt ℝ H u
  local_c : ∀ x ∈ closedBall x0 (2 * R), c x ∈ U ∧ HasFDerivAt c (J x) x ∧
    ∀ v, μ * ‖v‖ ≤ ‖J x v‖
  lipJ : ∀ x ∈ closedBall x0 (2 * R), ∀ y ∈ closedBall x0 (2 * R),
    ‖J x - J y‖ ≤ LJ * ‖x - y‖

section model

variable {F H : E → ℝ} {c : E → E} {J : E → E →L[ℝ] E} {U : Set E} {x0 : E} {R μ LJ : ℝ}

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma closedBall_two_subset (hR : 0 < R) : closedBall x0 (2 * R) ⊆ ball x0 (3 * R) :=
  closedBall_subset_ball (by linarith)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma norm_sub_le_four {x0 a b : E} {R : ℝ} (ha : a ∈ closedBall x0 (2 * R))
    (hb : b ∈ closedBall x0 (2 * R)) : ‖a - b‖ ≤ 4 * R := by
  rw [mem_closedBall, dist_eq_norm] at ha hb
  calc ‖a - b‖ = ‖(a - x0) - (b - x0)‖ := by congr 1; abel
    _ ≤ ‖a - x0‖ + ‖b - x0‖ := norm_sub_le _ _
    _ ≤ 4 * R := by linarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma norm_sub_le_three {x0 a u : E} {R : ℝ} (ha : a ∈ closedBall x0 (2 * R))
    (hu : u ∈ closedBall x0 R) : ‖u - a‖ ≤ 3 * R := by
  rw [mem_closedBall, dist_eq_norm] at ha hu
  calc ‖u - a‖ = ‖(u - x0) - (a - x0)‖ := by congr 1; abel
    _ ≤ ‖u - x0‖ + ‖a - x0‖ := norm_sub_le _ _
    _ ≤ 3 * R := by linarith

omit [CompleteSpace E] in
lemma LocalModel.preimage [FiniteDimensional ℝ E] (hm : LocalModel F H c J U x0 R μ LJ)
    (hμ : 0 < μ) {y : E} (hy : y ∈ closedBall x0 (2 * R)) (b : E) : ∃ v, J y v = b :=
  exists_preimage hμ (hm.local_c y hy).2.2 b

lemma LocalModel.support [FiniteDimensional ℝ E] (hm : LocalModel F H c J U x0 R μ LJ)
    (hR : 0 < R) (hμ : 0 < μ) (hF : ∀ x, HasGradientAt F (gradient F x) x) {y w : E}
    (hy : y ∈ closedBall x0 (2 * R)) (hw : w ∈ closedBall x0 (2 * R)) :
    F y + ⟪gradient F y, w - y⟫ + ⟪gradient F y, corr c J y w⟫ ≤ F w :=
  hidden_support isOpen_ball (closedBall_two_subset hR hy) (closedBall_two_subset hR hw) hm.eq
    hm.convexH (hm.local_c y hy).1 (hm.local_c w hw).1 (hm.local_c y hy).2.1
    (hm.diffH _ (hm.local_c y hy).1) (hF y) (hm.preimage hμ hy _)

omit [CompleteSpace E] in
lemma LocalModel.taylor (hm : LocalModel F H c J U x0 R μ LJ) (hLJ : 0 ≤ LJ) {a b : E}
    (ha : a ∈ closedBall x0 (2 * R)) (hb : b ∈ closedBall x0 (2 * R)) :
    ‖c b - c a - J a (b - a)‖ ≤ LJ * ‖b - a‖ ^ 2 :=
  taylor_bound hLJ (convex_closedBall x0 (2 * R)) (fun x hx => (hm.local_c x hx).2.1) hm.lipJ ha hb

omit [CompleteSpace E] in
lemma LocalModel.corr_le [FiniteDimensional ℝ E] (hm : LocalModel F H c J U x0 R μ LJ)
    (hμ : 0 < μ) (hLJ : 0 ≤ LJ) {y w : E} (hy : y ∈ closedBall x0 (2 * R))
    (hw : w ∈ closedBall x0 (2 * R)) : ‖corr c J y w‖ ≤ LJ / μ * ‖w - y‖ ^ 2 := by
  have h := corr_norm (hm.preimage hμ hy _) (hm.local_c y hy).2.2 (hm.taylor hLJ hy hw)
  rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
  linarith

omit [CompleteSpace E] in
lemma LocalModel.corr_lip [FiniteDimensional ℝ E] (hm : LocalModel F H c J U x0 R μ LJ)
    (hμ : 0 < μ) (hLJ : 0 ≤ LJ) {y y' w : E} (hy : y ∈ closedBall x0 (2 * R))
    (hy' : y' ∈ closedBall x0 (2 * R)) :
    ‖corr c J y w - corr c J y' w‖ ≤
      LJ / μ * ‖y - y'‖ * (‖y - y'‖ + ‖w - y‖ + ‖corr c J y' w‖) := by
  have h := corr_lipschitz (hm.preimage hμ hy (c w - c y)) (hm.preimage hμ hy' (c w - c y'))
    (hm.local_c y hy).2.2 (hm.taylor hLJ hy' hy) (hm.lipJ y hy y' hy')
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hμ]
  linarith

end model

lemma amgm_quarter {D t s a : ℝ} (hD : 0 < D) :
    a * s * t ≤ 2 * a ^ 2 / D * s ^ 2 + D / 8 * t ^ 2 := by
  have h : 2 * a ^ 2 / D * s ^ 2 + D / 8 * t ^ 2 - a * s * t = (D * t - 4 * a * s) ^ 2 / (8 * D) := by
    field_simp
    ring
  have : 0 ≤ (D * t - 4 * a * s) ^ 2 / (8 * D) := by positivity
  linarith

lemma amgm_sixteenth {D t m : ℝ} (hD : 0 ≤ D) :
    D * t * m ≤ D / 16 * t ^ 2 + 4 * D * m ^ 2 := by
  have h := mul_nonneg hD (sq_nonneg (t / 4 - 2 * m))
  nlinarith

lemma coef_tau (k : ℝ) (hk : 0 ≤ k) : (k + 1) * (k + 2) / 4 * (2 / (k + 2)) = (k + 1) / 2 := by
  have : k + 2 ≠ 0 := by positivity
  field_simp
  ring

lemma coef_tau_sq (k : ℝ) (hk : 0 ≤ k) : (k + 1) * (k + 2) / 4 * (2 / (k + 2)) ^ 2 ≤ 1 := by
  have h2 : 0 < k + 2 := by positivity
  rw [div_pow, ← mul_div_assoc, div_le_one (by positivity)]
  nlinarith

lemma coef_Aa_tau (k : ℝ) (hk : 0 ≤ k) :
    k * (k + 1) / 4 / ((k + 1) / 2) * (2 / (k + 2)) ^ 2 ≤ 2 / (k + 2) := by
  have h2 : 0 < k + 2 := by positivity
  have h1 : 0 < k + 1 := by positivity
  have e : k * (k + 1) / 4 / ((k + 1) / 2) * (2 / (k + 2)) ^ 2 = 2 / (k + 2) * (k / (k + 2)) := by
    field_simp
    ring
  rw [e]
  have : k / (k + 2) ≤ 1 := by rw [div_le_one h2]; linarith
  calc 2 / (k + 2) * (k / (k + 2)) ≤ 2 / (k + 2) * 1 := mul_le_mul_of_nonneg_left this (by positivity)
    _ = 2 / (k + 2) := mul_one _

omit [CompleteSpace E] in
lemma mixPoint_eq (k : ℕ) (x z : E) :
    mixPoint k x z = x + (2 / ((k : ℝ) + 2)) • (z - x) := by
  unfold mixPoint
  have hk : (k : ℝ) + 2 ≠ 0 := by positivity
  rw [smul_sub]
  have : (k : ℝ) / ((k : ℝ) + 2) = 1 - 2 / ((k : ℝ) + 2) := by field_simp; ring
  rw [this, sub_smul, one_smul]
  abel

omit [CompleteSpace E] in
lemma mixPoint_succ_eq (k : ℕ) (x z : E) :
    mixPoint (k + 1) x z = x + (2 / ((k : ℝ) + 3)) • (z - x) := by
  rw [mixPoint_eq]
  congr 3
  push_cast
  ring

omit [CompleteSpace E] in
lemma mix_identity (k : ℕ) (x z z' u : E) :
    (((k : ℝ) + 1) * ((k : ℝ) + 2) / 4) • (mixPoint k x z' - mixPoint k x z) -
      ((k : ℝ) * ((k : ℝ) + 1) / 4) • (x - mixPoint k x z) -
      (((k : ℝ) + 1) / 2) • (u - mixPoint k x z) = (((k : ℝ) + 1) / 2) • (z' - u) := by
  unfold mixPoint
  have hk : (k : ℝ) + 2 ≠ 0 := by positivity
  match_scalars <;> field_simp <;> ring

omit [CompleteSpace E] in
lemma mix_diff (k : ℕ) (x z z' : E) :
    mixPoint k x z' - mixPoint k x z = (2 / ((k : ℝ) + 2)) • (z' - z) := by
  rw [mixPoint_eq, mixPoint_eq]
  module

omit [CompleteSpace E] in
lemma mix_self_diff (k : ℕ) (x z : E) :
    x - mixPoint k x z = (2 / ((k : ℝ) + 2)) • (x - z) := by
  rw [mixPoint_eq]
  module

omit [CompleteSpace E] in
lemma mixPoint_mem {x0 x z : E} {r : ℝ} (k : ℕ) (hx : x ∈ closedBall x0 r)
    (hz : z ∈ closedBall x0 r) : mixPoint k x z ∈ closedBall x0 r := by
  rw [mixPoint_eq]
  have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  exact (convex_closedBall x0 r).add_smul_sub_mem hx hz
    ⟨by positivity, by rw [div_le_one hk]; linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]⟩

variable [FiniteDimensional ℝ E]

set_option maxHeartbeats 4000000 in
lemma step_bound {F H : E → ℝ} {c : E → E} {J : E → E →L[ℝ] E} {U : Set E}
    {x0 u x z g : E} {R μ LJ L D : ℝ} (k : ℕ)
    (hm : LocalModel F H c J U x0 R μ LJ) (hR : 0 < R) (hμ : 0 < μ) (hLJ : 0 ≤ LJ)
    (hreg : 32 * LJ * R ≤ μ) (hL : 0 ≤ L) (hD : 4 * L ≤ D) (hDpos : 0 < D)
    (hF : ∀ x, HasGradientAt F (gradient F x) x)
    (hlip : ∀ x y, ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖)
    (hu : u ∈ closedBall x0 R) (hx : x ∈ closedBall x0 (2 * R))
    (hz : z ∈ closedBall x0 (2 * R))
    {a A A' τ τ' M : ℝ} (ha : a = ((k : ℝ) + 1) / 2) (hA : A = (k : ℝ) * ((k : ℝ) + 1) / 4)
    (hA' : A' = ((k : ℝ) + 1) * ((k : ℝ) + 2) / 4) (hτ : τ = 2 / ((k : ℝ) + 2))
    (hτ' : τ' = 2 / ((k : ℝ) + 3)) (hM : M = LJ / μ)
    {y w z' x' y' : E} (hy : y = mixPoint k x z) (hw : w = z - (a / D) • g)
    (hz' : z' = ballProj x0 (2 * R) w) (hx' : x' = mixPoint k x z')
    (hy' : y' = mixPoint (k + 1) x' z') :
    A' * (F x' - F u) + D / 2 * ‖z' - u‖ ^ 2 - D * ⟪z' - u, corr c J y' u⟫ ≤
      A * (F x - F u) + D / 2 * ‖z - u‖ ^ 2 - D * ⟪z - u, corr c J y u⟫ -
      a * ⟪g - gradient F y, z - u⟫ + a * ⟪g - gradient F y, corr c J y u⟫ +
      A * ⟪g - gradient F y, corr c J y x⟫ + 2 * a ^ 2 / D * ‖g - gradient F y‖ ^ 2 +
      (96 * D * M * R ^ 3 * τ' + 3328 * D * M ^ 2 * R ^ 4 * τ ^ 2) := by
  obtain ⟨gr, hgr⟩ : ∃ v, v = gradient F y := ⟨_, rfl⟩
  obtain ⟨ξ, hξ⟩ : ∃ v, v = g - gr := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ v, v = corr c J y u := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ v, v = corr c J y x := ⟨_, rfl⟩
  obtain ⟨q', hq'⟩ : ∃ v, v = corr c J y' u := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ v, v = w - z' := ⟨_, rfl⟩
  obtain ⟨Δ, hΔ⟩ : ∃ v, v = z' - z := ⟨_, rfl⟩
  rw [← hgr, ← hξ, ← hq, ← hp, ← hq']
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hapos : 0 < a := by rw [ha]; positivity
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hA'0 : 0 ≤ A' := by rw [hA']; positivity
  have hτpos : 0 < τ := by rw [hτ]; positivity
  have hτ1 : τ ≤ 1 := by rw [hτ, div_le_one hk2]; linarith
  have hτ'pos : 0 < τ' := by rw [hτ']; positivity
  have hM0 : 0 ≤ M := by rw [hM]; exact div_nonneg hLJ hμ.le
  have hMR : M * R ≤ 1 / 32 := by
    rw [hM, div_mul_eq_mul_div, div_le_div_iff₀ hμ (by norm_num)]
    linarith
  have hAa0 : 0 ≤ A / a := div_nonneg hA0 hapos.le
  have huB : u ∈ closedBall x0 (2 * R) := closedBall_subset_closedBall (by linarith) hu
  have hyB : y ∈ closedBall x0 (2 * R) := hy ▸ mixPoint_mem k hx hz
  have hz'B : z' ∈ closedBall x0 (2 * R) := hz' ▸ ballProj_mem x0 w (by positivity)
  have hx'B : x' ∈ closedBall x0 (2 * R) := hx' ▸ mixPoint_mem k hx hz'B
  have hy'B : y' ∈ closedBall x0 (2 * R) := hy' ▸ mixPoint_mem (k + 1) hx'B hz'B
  have hxy' : x' - y = τ • Δ := by rw [hx', hy, mix_diff, hτ, hΔ]
  have hxmy : x - y = τ • (x - z) := by rw [hy, mix_self_diff, hτ]
  have hdy : y' - y = τ • Δ + τ' • (z' - x') := by
    rw [hy', mixPoint_succ_eq, ← hτ', ← hxy']
    abel
  -- combination of smoothness and the two hidden-convex supports
  have hS := Gradient.smooth_upper_bound hF hlip y x'
  have hC1 := hm.support hR hμ hF hyB huB
  have hC2 := hm.support hR hμ hF hyB hx
  rw [← hgr] at hS
  rw [← hgr, ← hq] at hC1
  rw [← hgr, ← hp] at hC2
  have hcin : A' * ⟪gr, x' - y⟫ - A * ⟪gr, x - y⟫ - a * ⟪gr, u - y⟫ = a * ⟪gr, z' - u⟫ := by
    have h := congrArg (fun v => ⟪gr, v⟫) (mix_identity k x z z' u)
    simp only [inner_sub_right, inner_smul_right] at h
    rw [← hy, ← hx'] at h
    rw [hA', hA, ha]
    simp only [inner_sub_right]
    linear_combination h
  have hnxy : ‖x' - y‖ ^ 2 = τ ^ 2 * ‖Δ‖ ^ 2 := by
    rw [hxy', norm_smul, Real.norm_eq_abs, abs_of_pos hτpos, mul_pow]
  have hA'τ : A' * τ ^ 2 ≤ 1 := by rw [hA', hτ]; exact coef_tau_sq k hk0
  have hsmooth : A' * (L / 2 * ‖x' - y‖ ^ 2) ≤ D / 8 * ‖Δ‖ ^ 2 := by
    rw [hnxy]
    have h1 := mul_le_mul_of_nonneg_right hA'τ (mul_nonneg hL (sq_nonneg ‖Δ‖))
    have h2 : L * ‖Δ‖ ^ 2 ≤ D / 4 * ‖Δ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    nlinarith
  have hAsum : A' = A + a := by rw [hA', hA, ha]; ring
  have hcomb : A' * (F x' - F u) ≤
      A * (F x - F u) + a * ⟪gr, z' - u⟫ - A * ⟪gr, p⟫ - a * ⟪gr, q⟫ + D / 8 * ‖Δ‖ ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hS hA'0
    have h2 := mul_le_mul_of_nonneg_left hC2 hA0
    have h3 := mul_le_mul_of_nonneg_left hC1 hapos.le
    rw [hAsum] at h1 hsmooth hcin ⊢
    nlinarith
  -- substitution of the stochastic dual step
  have hag : a • g = -(D • Δ) - D • n := by
    rw [hΔ, hn, hw]
    have e : a = D * (a / D) := by field_simp
    conv_lhs => rw [e]
    rw [← smul_smul]
    module
  have hsub (v : E) : a * ⟪gr, v⟫ = -(D * ⟪Δ, v⟫) - D * ⟪n, v⟫ - a * ⟪ξ, v⟫ := by
    have hg : gr = g - ξ := by rw [hξ]; abel
    have e : a * ⟪g, v⟫ = ⟪a • g, v⟫ := by rw [inner_smul_left]; simp
    rw [hg, inner_sub_left, mul_sub, e, hag, inner_sub_left, inner_neg_left, inner_smul_left,
      inner_smul_left]
    simp only [RCLike.conj_to_real]
  have hsub_p : A * ⟪gr, p⟫ = -(A / a * (D * ⟪Δ, p⟫)) - A / a * (D * ⟪n, p⟫) - A * ⟪ξ, p⟫ := by
    have h := hsub p
    have e : A * ⟪gr, p⟫ = A / a * (a * ⟪gr, p⟫) := by field_simp
    rw [e, h]
    field_simp
  have h3pt : -(D * ⟪Δ, z' - u⟫) = D / 2 * ‖z - u‖ ^ 2 - D / 2 * ‖z' - u‖ ^ 2 - D / 2 * ‖Δ‖ ^ 2 := by
    have e : z' - u = (z - u) + Δ := by rw [hΔ]; abel
    rw [e, norm_add_sq_real, inner_add_right, real_inner_self_eq_norm_sq, real_inner_comm Δ]
    ring
  have hqsplit : D * ⟪Δ, q⟫ = D * ⟪z' - u, q⟫ - D * ⟪z - u, q⟫ := by
    rw [← mul_sub, ← inner_sub_left, hΔ]
    congr 2
    abel
  have hξsplit : ⟪ξ, z' - u⟫ = ⟪ξ, z - u⟫ + ⟪ξ, Δ⟫ := by
    rw [← inner_add_right, hΔ]
    congr 1
    abel
  -- normal cone group
  have hmargin : R * ‖n‖ ≤ ⟪n, z' - u⟫ := by
    have h := ballProj_margin x0 w u (r := 2 * R) (by positivity)
      (by rw [mem_closedBall, dist_eq_norm] at hu; linarith)
    rw [show 2 * R / 2 = R by ring, ← hz', ← hn] at h
    exact h
  have hqbound : ∀ v ∈ closedBall x0 (2 * R), ‖corr c J v u‖ ≤ 9 * R / 32 := by
    intro v hv
    have h := hm.corr_le hμ hLJ hv huB
    have h3 := norm_sub_le_three hv hu
    have h9 : ‖u - v‖ ^ 2 ≤ 9 * R ^ 2 := by
      calc ‖u - v‖ ^ 2 ≤ (3 * R) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
        _ = 9 * R ^ 2 := by ring
    calc ‖corr c J v u‖ ≤ LJ / μ * ‖u - v‖ ^ 2 := h
      _ = M * ‖u - v‖ ^ 2 := by rw [hM]
      _ ≤ M * (9 * R ^ 2) := mul_le_mul_of_nonneg_left h9 hM0
      _ = 9 * R * (M * R) := by ring
      _ ≤ 9 * R * (1 / 32) := mul_le_mul_of_nonneg_left hMR (by positivity)
      _ = 9 * R / 32 := by ring
  have hqn : ‖q‖ ≤ 9 * R / 32 := hq ▸ hqbound y hyB
  have hq'n : ‖q'‖ ≤ 9 * R / 32 := hq' ▸ hqbound y' hy'B
  have hpn : A / a * ‖p‖ ≤ 16 * M * R ^ 2 * τ := by
    have h := hm.corr_le hμ hLJ hyB hx
    rw [← hp, ← hM] at h
    have h4 := norm_sub_le_four hx hz
    have hxy2 : ‖x - y‖ ^ 2 ≤ τ ^ 2 * (16 * R ^ 2) := by
      rw [hxmy, norm_smul, Real.norm_eq_abs, abs_of_pos hτpos, mul_pow]
      have h16 : ‖x - z‖ ^ 2 ≤ 16 * R ^ 2 := by
        calc ‖x - z‖ ^ 2 ≤ (4 * R) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h4 2
          _ = 16 * R ^ 2 := by ring
      exact mul_le_mul_of_nonneg_left h16 (sq_nonneg τ)
    have hAaτ : A / a * τ ^ 2 ≤ τ := by rw [hA, ha, hτ]; exact coef_Aa_tau k hk0
    calc A / a * ‖p‖ ≤ A / a * (M * (τ ^ 2 * (16 * R ^ 2))) :=
          mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left hxy2 hM0)) hAa0
      _ = (A / a * τ ^ 2) * (16 * M * R ^ 2) := by ring
      _ ≤ τ * (16 * M * R ^ 2) := mul_le_mul_of_nonneg_right hAaτ (by positivity)
      _ = 16 * M * R ^ 2 * τ := by ring
  have hpn2 : A / a * ‖p‖ ≤ R / 2 := by
    calc A / a * ‖p‖ ≤ 16 * M * R ^ 2 * τ := hpn
      _ ≤ 16 * M * R ^ 2 * 1 := mul_le_mul_of_nonneg_left hτ1 (by positivity)
      _ = 16 * R * (M * R) := by ring
      _ ≤ 16 * R * (1 / 32) := mul_le_mul_of_nonneg_left hMR (by positivity)
      _ = R / 2 := by ring
  have hnormal : D * ⟪n, q⟫ + A / a * (D * ⟪n, p⟫) - D * ⟪n, z' - u⟫ ≤ 0 := by
    have e1 := real_inner_le_norm n q
    have e2 := mul_le_mul_of_nonneg_left (real_inner_le_norm n p) hAa0
    have hRn : 0 ≤ R * ‖n‖ := by positivity
    have g1 : ‖n‖ * ‖q‖ ≤ 9 / 32 * (R * ‖n‖) := by
      calc ‖n‖ * ‖q‖ ≤ ‖n‖ * (9 * R / 32) := mul_le_mul_of_nonneg_left hqn (norm_nonneg n)
        _ = 9 / 32 * (R * ‖n‖) := by ring
    have g2 : A / a * ⟪n, p⟫ ≤ 1 / 2 * (R * ‖n‖) := by
      calc A / a * ⟪n, p⟫ ≤ A / a * (‖n‖ * ‖p‖) := e2
        _ = ‖n‖ * (A / a * ‖p‖) := by ring
        _ ≤ ‖n‖ * (R / 2) := mul_le_mul_of_nonneg_left hpn2 (norm_nonneg n)
        _ = 1 / 2 * (R * ‖n‖) := by ring
    have hsum : ⟪n, q⟫ + A / a * ⟪n, p⟫ - ⟪n, z' - u⟫ ≤ 0 := by linarith
    have h := mul_le_mul_of_nonneg_left hsum hDpos.le
    have e : D * (⟪n, q⟫ + A / a * ⟪n, p⟫ - ⟪n, z' - u⟫) =
      D * ⟪n, q⟫ + A / a * (D * ⟪n, p⟫) - D * ⟪n, z' - u⟫ := by ring
    rw [e, mul_zero] at h
    exact h
  -- Δ group
  have hξΔ : -(a * ⟪ξ, Δ⟫) ≤ 2 * a ^ 2 / D * ‖ξ‖ ^ 2 + D / 8 * ‖Δ‖ ^ 2 := by
    have h1 : -⟪ξ, Δ⟫ ≤ ‖ξ‖ * ‖Δ‖ := by
      have := abs_real_inner_le_norm ξ Δ
      linarith [neg_abs_le ⟪ξ, Δ⟫]
    have h2 := amgm_quarter (a := a) (s := ‖ξ‖) (t := ‖Δ‖) hDpos
    have h3 := mul_le_mul_of_nonneg_left h1 hapos.le
    linarith [show a * (‖ξ‖ * ‖Δ‖) = a * ‖ξ‖ * ‖Δ‖ by ring]
  have hpΔ : A / a * (D * ⟪Δ, p⟫) ≤ D / 16 * ‖Δ‖ ^ 2 + 1024 * D * M ^ 2 * R ^ 4 * τ ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left (real_inner_le_norm Δ p) (mul_nonneg hAa0 hDpos.le)
    have h3 : D * ‖Δ‖ * (A / a * ‖p‖) ≤ D * ‖Δ‖ * (16 * M * R ^ 2 * τ) :=
      mul_le_mul_of_nonneg_left hpn (by positivity)
    have h4 := amgm_sixteenth (t := ‖Δ‖) (m := 16 * M * R ^ 2 * τ) hDpos.le
    have e1 : A / a * D * (‖Δ‖ * ‖p‖) = D * ‖Δ‖ * (A / a * ‖p‖) := by ring
    have e2 : A / a * D * ⟪Δ, p⟫ = A / a * (D * ⟪Δ, p⟫) := by ring
    have e3 : 4 * D * (16 * M * R ^ 2 * τ) ^ 2 = 1024 * D * M ^ 2 * R ^ 4 * τ ^ 2 := by ring
    linarith
  have hqq' : ‖q - q'‖ ≤ 8 * M * R * ‖y - y'‖ := by
    have h := hm.corr_lip hμ hLJ (w := u) hyB hy'B
    rw [← hq, ← hq', ← hM] at h
    have h4 := norm_sub_le_four hyB hy'B
    have h3 := norm_sub_le_three hyB hu
    have hb : ‖y - y'‖ + ‖u - y‖ + ‖q'‖ ≤ 8 * R := by linarith
    calc ‖q - q'‖ ≤ M * ‖y - y'‖ * (‖y - y'‖ + ‖u - y‖ + ‖q'‖) := h
      _ ≤ M * ‖y - y'‖ * (8 * R) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 8 * M * R * ‖y - y'‖ := by ring
  have hdyn : ‖y - y'‖ ≤ τ * ‖Δ‖ + τ' * (4 * R) := by
    rw [norm_sub_rev, hdy]
    calc ‖τ • Δ + τ' • (z' - x')‖ ≤ ‖τ • Δ‖ + ‖τ' • (z' - x')‖ := norm_add_le _ _
      _ = τ * ‖Δ‖ + τ' * ‖z' - x'‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hτpos,
          abs_of_pos hτ'pos]
      _ ≤ τ * ‖Δ‖ + τ' * (4 * R) := by
        have := norm_sub_le_four hz'B hx'B
        have := mul_le_mul_of_nonneg_left this hτ'pos.le
        linarith
  have habel : D * ⟪z' - u, q⟫ - D * ⟪z' - u, q'⟫ ≤
      D / 16 * ‖Δ‖ ^ 2 + 2304 * D * M ^ 2 * R ^ 4 * τ ^ 2 + 96 * D * M * R ^ 3 * τ' := by
    have h1 : ⟪z' - u, q⟫ - ⟪z' - u, q'⟫ ≤ ‖z' - u‖ * ‖q - q'‖ := by
      rw [← inner_sub_right]
      exact real_inner_le_norm _ _
    have h3 : ‖z' - u‖ ≤ 3 * R := by rw [norm_sub_rev]; exact norm_sub_le_three hz'B hu
    have h2 : ‖z' - u‖ * ‖q - q'‖ ≤ 3 * R * (8 * M * R * (τ * ‖Δ‖ + τ' * (4 * R))) :=
      mul_le_mul h3 (hqq'.trans (mul_le_mul_of_nonneg_left hdyn (by positivity)))
        (norm_nonneg _) (by positivity)
    have h4 := amgm_sixteenth (t := ‖Δ‖) (m := 24 * M * R ^ 2 * τ) hDpos.le
    have h5 := mul_le_mul_of_nonneg_left (h1.trans h2) hDpos.le
    have e1 : D * (3 * R * (8 * M * R * (τ * ‖Δ‖ + τ' * (4 * R)))) =
        D * ‖Δ‖ * (24 * M * R ^ 2 * τ) + 96 * D * M * R ^ 3 * τ' := by ring
    have e2 : 4 * D * (24 * M * R ^ 2 * τ) ^ 2 = 2304 * D * M ^ 2 * R ^ 4 * τ ^ 2 := by ring
    have e3 : D * (⟪z' - u, q⟫ - ⟪z' - u, q'⟫) = D * ⟪z' - u, q⟫ - D * ⟪z' - u, q'⟫ := by ring
    linarith
  -- assemble
  have hsz := hsub (z' - u)
  have hsq := hsub q
  rw [hξsplit] at hsz
  have hsz' : a * ⟪gr, z' - u⟫ =
      -(D * ⟪Δ, z' - u⟫) - D * ⟪n, z' - u⟫ - a * ⟪ξ, z - u⟫ - a * ⟪ξ, Δ⟫ := by
    rw [hsz]; ring
  have hDΔ : 0 ≤ D / 8 * ‖Δ‖ ^ 2 := by positivity
  linarith [hcomb, hsz', hsq, hsub_p, h3pt, hqsplit, hnormal, hξΔ, hpΔ, habel, hDΔ]

end OracleTemplate.LocalHiddenConvex
