import LongTails.Proofs.CachedJacobianHalpern
import LongTails.Proofs.NearZeroSumProjection
import LongTails.Proofs.MatrixPolarGeometry
import LongTails.Algorithms.CachedJacobian
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Convex

open scoped RealInnerProductSpace Topology
open Set Filter

namespace LongTails.Proofs.CachedJacobianGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma derivative_monotone_on_differences {X : Set E} {F : E → E} {s x y : E}
    (hX : Convex ℝ X) (hs : s ∈ X) (hx : x ∈ X) (hy : y ∈ X)
    (hF : DifferentiableAt ℝ F s)
    (hmono : ∀ u ∈ X, ∀ v ∈ X, 0 ≤ ⟪F u - F v, u - v⟫) :
    0 ≤ ⟪fderiv ℝ F s (x - y), x - y⟫ := by
  let g : ℝ → ℝ := fun t =>
    ⟪F (s + t • (x - s)) - F (s + t • (y - s)), x - y⟫
  have hdx : HasDerivAt (fun t : ℝ => F (s + t • (x - s)))
      (fderiv ℝ F s (x - s)) 0 := by
    have hf : HasFDerivAt F (fderiv ℝ F s) (s + (0 : ℝ) • (x - s)) := by simpa using hF.hasFDerivAt
    simpa [Function.comp_def] using hf.comp_hasDerivAt 0
      (((hasDerivAt_id (0 : ℝ)).smul_const (x - s)).const_add s)
  have hdy : HasDerivAt (fun t : ℝ => F (s + t • (y - s)))
      (fderiv ℝ F s (y - s)) 0 := by
    have hf : HasFDerivAt F (fderiv ℝ F s) (s + (0 : ℝ) • (y - s)) := by simpa using hF.hasFDerivAt
    simpa [Function.comp_def] using hf.comp_hasDerivAt 0
      (((hasDerivAt_id (0 : ℝ)).smul_const (y - s)).const_add s)
  have hd : HasDerivAt g ⟪fderiv ℝ F s (x - y), x - y⟫ 0 := by
    simpa [g, ← map_sub, sub_sub_sub_cancel_right] using
      (hdx.sub hdy).inner ℝ (hasDerivAt_const (0 : ℝ) (x - y))
  have hg : ∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ g t := by
    intro t ht
    have h := hmono _ (hX.add_smul_sub_mem hs hx ⟨ht.1.le, ht.2⟩)
      _ (hX.add_smul_sub_mem hs hy ⟨ht.1.le, ht.2⟩)
    have he : (s + t • (x - s)) - (s + t • (y - s)) = t • (x - y) := by module
    rw [he, real_inner_smul_right] at h
    exact nonneg_of_mul_nonneg_right h ht.1
  apply ge_of_tendsto hd.tendsto_slope_zero_right
  have hlt : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin, hlt] with t ht ht₁
  simp only [zero_add, g, zero_smul, add_zero, sub_self, inner_zero_left, sub_zero,
    smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr (le_of_lt ht)) (hg t ⟨ht, ht₁.le⟩)

lemma stale_taylor_bound {X : Set E} {F : E → E} {u v s : E} {L : ℝ}
    (hX : Convex ℝ X) (hu : u ∈ X) (hv : v ∈ X) (hs : s ∈ X)
    (hL : 0 ≤ L) (hF : ∀ x ∈ X, DifferentiableAt ℝ F x)
    (hJ : ∀ x ∈ X, ∀ y ∈ X,
      ‖fderiv ℝ F x - fderiv ℝ F y‖ ≤ L * ‖x - y‖) :
    ‖F v - F u - fderiv ℝ F s (v - u)‖ ≤
      L * (‖u - s‖ + ‖v - u‖) * ‖v - u‖ := by
  let B := fderiv ℝ F s
  have hsub : segment ℝ u v ⊆ X := hX.segment_subset hu hv
  have hd (z : E) (hz : z ∈ segment ℝ u v) :
      HasFDerivWithinAt (fun w => F w - B w) (fderiv ℝ F z - B)
        (segment ℝ u v) z :=
    ((hF z (hsub hz)).hasFDerivAt.sub B.hasFDerivAt).hasFDerivWithinAt
  have hb (z : E) (hz : z ∈ segment ℝ u v) :
      ‖fderiv ℝ F z - B‖ ≤ L * (‖u - s‖ + ‖v - u‖) := by
    have hzdist := segment_subset_closedBall_left u v hz
    have hzu : ‖z - u‖ ≤ ‖v - u‖ := by
      simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hzdist
    have htri : ‖z - s‖ ≤ ‖u - s‖ + ‖v - u‖ := by
      calc
        ‖z - s‖ ≤ ‖z - u‖ + ‖u - s‖ := norm_sub_le_norm_sub_add_norm_sub z u s
        _ ≤ ‖u - s‖ + ‖v - u‖ := by linarith
    exact (hJ z (hsub hz) s hs).trans (mul_le_mul_of_nonneg_left htri hL)
  have h := (convex_segment u v).norm_image_sub_le_of_norm_hasFDerivWithin_le hd hb
    (left_mem_segment ℝ u v) (right_mem_segment ℝ u v)
  convert h using 1
  congr 1
  simp only [map_sub]
  module

lemma regularized_vi_exists {X : Set E} {F : E → E} {M μ : ℝ} (center : E)
    (hX : IsCompact X) (hc : Convex ℝ X) (hne : X.Nonempty)
    (hM : 0 ≤ M) (hμ : 0 < μ)
    (hmono : ∀ u ∈ X, ∀ v ∈ X, 0 ≤ ⟪F u - F v, u - v⟫)
    (hlip : ∀ u ∈ X, ∀ v ∈ X, ‖F u - F v‖ ≤ M * ‖u - v‖) :
    ∃ y ∈ X, ∀ z ∈ X, 0 ≤ ⟪F y + μ • (y - center), z - y⟫ := by
  let P := LongTails.Algorithms.MatrixPolar.closestPoint X
  have hP : OracleTemplate.ConstrainedMonotone.Proj X P :=
    ⟨fun u => (LongTails.Algorithms.MatrixPolar.closestPoint_spec hX hne u).1,
      fun u z hz => LongTails.Algorithms.MatrixPolar.closestPoint_variational hX hne hc u hz⟩
  let G : E → E := fun u => F u + μ • (u - center)
  have he (u v : E) : G u - G v = F u - F v + μ • (u - v) := by
    dsimp [G]
    module
  have hgm : ∀ u ∈ X, ∀ v ∈ X, μ * ‖u - v‖ ^ 2 ≤ ⟪G u - G v, u - v⟫ := by
    intro u hu v hv
    rw [he, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    linarith [hmono u hu v hv]
  have hgl : ∀ u ∈ X, ∀ v ∈ X, ‖G u - G v‖ ≤ (M + μ) * ‖u - v‖ := by
    intro u hu v hv
    rw [he]
    calc
      _ ≤ ‖F u - F v‖ + ‖μ • (u - v)‖ := norm_add_le _ _
      _ ≤ M * ‖u - v‖ + μ * ‖u - v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμ]
        exact add_le_add (hlip u hu v hv) le_rfl
      _ = _ := by ring
  obtain ⟨y, hy, hn⟩ := OracleTemplate.NearZeroSum.strongly_monotone_vi_exists
    hX.isComplete hne hP hμ (show μ ≤ M + μ by linarith) hgm hgl
  refine ⟨y, hy, fun z hz => ?_⟩
  have h := hn z hz
  simpa only [OracleTemplate.ConstrainedMonotone.Normal, inner_neg_left, neg_nonpos, G] using h

lemma affine_vi_exists {X : Set E} {B : E →L[ℝ] E} (b : E) {μ : ℝ}
    (hX : IsCompact X) (hc : Convex ℝ X) (hne : X.Nonempty) (hμ : 0 < μ)
    (hB : ∀ u ∈ X, ∀ v ∈ X, 0 ≤ ⟪B (u - v), u - v⟫) :
    ∃ y ∈ X, ∀ z ∈ X, 0 ≤ ⟪b + B y + μ • y, z - y⟫ := by
  have hm : ∀ u ∈ X, ∀ v ∈ X, 0 ≤ ⟪(b + B u) - (b + B v), u - v⟫ := by
    intro u hu v hv
    simpa [← map_sub] using hB u hu v hv
  have hl : ∀ u ∈ X, ∀ v ∈ X, ‖(b + B u) - (b + B v)‖ ≤ ‖B‖ * ‖u - v‖ := by
    intro u _ v _
    simpa [← map_sub] using B.le_opNorm (u - v)
  simpa using regularized_vi_exists (F := fun u => b + B u) (0 : E)
    hX hc hne (norm_nonneg B) hμ hm hl

lemma chord_error {X : Set E} {F : E → E} {B : E →L[ℝ] E}
    {u v y center : E} {η : ℝ} (hη : 0 < η)
    (hv : v ∈ X) (hy : y ∈ X)
    (hB : ∀ x z, x ∈ X → z ∈ X → 0 ≤ ⟪B (x - z), x - z⟫)
    (hvvi : ∀ z ∈ X, 0 ≤ ⟪F u + B (v - u) + η⁻¹ • (v - center), z - v⟫)
    (hyvi : ∀ z ∈ X, 0 ≤ ⟪F y + η⁻¹ • (y - center), z - y⟫) :
    ‖v - y‖ ≤ η * ‖F y - F u - B (y - u)‖ := by
  let b := F u - B u - η⁻¹ • center
  let e := F y - F u - B (y - u)
  have he₁ : b + B v + η⁻¹ • v = F u + B (v - u) + η⁻¹ • (v - center) := by
    dsimp [b]
    simp only [map_sub, smul_sub]
    module
  have he₂ : b + B y + η⁻¹ • y + e = F y + η⁻¹ • (y - center) := by
    dsimp [b, e]
    simp only [map_sub, smul_sub]
    module
  have h := CachedJacobianHalpern.affine_vi_error (b := b) (e := e) (μ := η⁻¹) hv hy hB
    (by simpa only [he₁] using hvvi) (by simpa only [he₂] using hyvi)
  have hh := mul_le_mul_of_nonneg_left h hη.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hη.ne', one_mul] using hh

lemma chord_contraction {X : Set E} {F : E → E} {u v y s center : E} {η L R r : ℝ}
    (hX : Convex ℝ X) (hu : u ∈ X) (hv : v ∈ X) (hy : y ∈ X) (hs : s ∈ X)
    (hη : 0 < η) (hL : 0 ≤ L)
    (hF : ∀ x ∈ X, DifferentiableAt ℝ F x)
    (hmono : ∀ x ∈ X, ∀ z ∈ X, 0 ≤ ⟪F x - F z, x - z⟫)
    (hJ : ∀ x ∈ X, ∀ z ∈ X,
      ‖fderiv ℝ F x - fderiv ℝ F z‖ ≤ L * ‖x - z‖)
    (hcache : ‖u - s‖ ≤ R) (hroot : ‖u - y‖ ≤ r)
    (hsmall₁ : η * L * R ≤ 1 / 16) (hsmall₂ : η * L * r ≤ 1 / 64)
    (hvvi : ∀ z ∈ X, 0 ≤
      ⟪F u + fderiv ℝ F s (v - u) + η⁻¹ • (v - center), z - v⟫)
    (hyvi : ∀ z ∈ X, 0 ≤ ⟪F y + η⁻¹ • (y - center), z - y⟫) :
    ‖v - y‖ ≤ ‖u - y‖ / 4 := by
  have he := chord_error hη hv hy
    (fun x z hx hz => derivative_monotone_on_differences hX hs hx hz (hF s hs) hmono)
    hvvi hyvi
  have ht := stale_taylor_bound hX hu hy hs hL hF hJ
  rw [norm_sub_rev y u] at ht
  have hb : ‖F y - F u - fderiv ℝ F s (y - u)‖ ≤
      L * (R + r) * ‖u - y‖ := by
    apply ht.trans
    gcongr
  have hcoef : η * L * (R + r) ≤ 1 / 4 := by nlinarith
  calc
    ‖v - y‖ ≤ η * ‖F y - F u - fderiv ℝ F s (y - u)‖ := he
    _ ≤ η * (L * (R + r) * ‖u - y‖) := mul_le_mul_of_nonneg_left hb hη.le
    _ = (η * L * (R + r)) * ‖u - y‖ := by ring
    _ ≤ (1 / 4 : ℝ) * ‖u - y‖ := mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
    _ = _ := by ring

lemma field_lipschitz {X : Set E} {F : E → E} {s : E} {L D : ℝ}
    (hX : Convex ℝ X) (hs : s ∈ X) (hL : 0 ≤ L)
    (hF : ∀ x ∈ X, DifferentiableAt ℝ F x)
    (hJ : ∀ x ∈ X, ∀ z ∈ X,
      ‖fderiv ℝ F x - fderiv ℝ F z‖ ≤ L * ‖x - z‖)
    (hD : ∀ x ∈ X, ‖x - s‖ ≤ D) {u v : E} (hu : u ∈ X) (hv : v ∈ X) :
    ‖F u - F v‖ ≤ (‖fderiv ℝ F s‖ + L * D) * ‖u - v‖ := by
  apply hX.norm_image_sub_le_of_norm_fderiv_le hF _ hv hu
  intro x hx
  have hnorm := norm_le_norm_sub_add (fderiv ℝ F x) (fderiv ℝ F s)
  have hbound := (hJ x hx s hs).trans (mul_le_mul_of_nonneg_left (hD x hx) hL)
  linarith

lemma regularized_vi_error {X : Set E} {F : E → E} {u y center e : E} {μ : ℝ}
    (hu : u ∈ X) (hy : y ∈ X)
    (hmono : ∀ x ∈ X, ∀ z ∈ X, 0 ≤ ⟪F x - F z, x - z⟫)
    (huvi : ∀ z ∈ X, 0 ≤ ⟪F u + μ • (u - center) - e, z - u⟫)
    (hyvi : ∀ z ∈ X, 0 ≤ ⟪F y + μ • (y - center), z - y⟫) :
    μ * ‖u - y‖ ≤ ‖e‖ := by
  have h₁ := huvi y hy
  have h₂ := hyvi u hu
  have hm := hmono u hu y hy
  have heq : ⟪F u + μ • (u - center) - e, y - u⟫ +
      ⟪F y + μ • (y - center), u - y⟫ =
      -⟪F u - F y, u - y⟫ - μ * ‖u - y‖ ^ 2 + ⟪e, u - y⟫ := by
    simp only [inner_add_left, inner_sub_left, inner_sub_right, real_inner_smul_left,
      norm_sub_sq_real, real_inner_self_eq_norm_sq]
    rw [real_inner_comm y u]
    ring
  have hcs := real_inner_le_norm e (u - y)
  by_cases hz : ‖u - y‖ = 0
  · simp [hz]
  · have hp : 0 < ‖u - y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

lemma chord_certificate {X : Set E} {F : E → E} {u v y s : E} {η L R r : ℝ}
    (hX : Convex ℝ X) (hu : u ∈ X) (hv : v ∈ X) (hs : s ∈ X)
    (hη : 0 < η) (hL : 0 ≤ L)
    (hF : ∀ x ∈ X, DifferentiableAt ℝ F x)
    (hJ : ∀ x ∈ X, ∀ z ∈ X,
      ‖fderiv ℝ F x - fderiv ℝ F z‖ ≤ L * ‖x - z‖)
    (hcache : ‖u - s‖ ≤ R) (hroot : ‖u - y‖ ≤ r)
    (hsmall₁ : η * L * R ≤ 1 / 16) (hsmall₂ : η * L * r ≤ 1 / 64)
    (hcontract : ‖v - y‖ ≤ ‖u - y‖ / 4) :
    η * ‖F v - F u - fderiv ℝ F s (v - u)‖ ≤ ‖u - y‖ / 4 := by
  have hd : ‖v - u‖ ≤ (5 / 4 : ℝ) * ‖u - y‖ := by
    have h := norm_sub_le_norm_sub_add_norm_sub v y u
    rw [norm_sub_rev y u] at h
    linarith
  have hηL : 0 ≤ η * L := mul_nonneg hη.le hL
  have hdr : ‖v - u‖ ≤ (5 / 4 : ℝ) * r := hd.trans (by gcongr)
  have hdsmall : η * L * ‖v - u‖ ≤ 5 / 256 := by
    have h := mul_le_mul_of_nonneg_left hdr hηL
    nlinarith
  have hb : η * L * (‖u - s‖ + ‖v - u‖) ≤ 1 / 8 := by
    have h := mul_le_mul_of_nonneg_left hcache hηL
    nlinarith
  have ht := stale_taylor_bound hX hu hv hs hL hF hJ
  calc
    η * ‖F v - F u - fderiv ℝ F s (v - u)‖ ≤
        η * (L * (‖u - s‖ + ‖v - u‖) * ‖v - u‖) := mul_le_mul_of_nonneg_left ht hη.le
    _ = (η * L * (‖u - s‖ + ‖v - u‖)) * ‖v - u‖ := by ring
    _ ≤ (1 / 8 : ℝ) * ‖v - u‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ ≤ ‖u - y‖ / 4 := by nlinarith [norm_nonneg (u - y)]

end LongTails.Proofs.CachedJacobianGeometry
