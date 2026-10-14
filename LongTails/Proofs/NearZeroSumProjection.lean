import LongTails.Proofs.ConstrainedAnchoredStep
import Mathlib.Topology.MetricSpace.Contracting

open scoped RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace OracleTemplate.NearZeroSum

open ConstrainedMonotone (Proj Normal)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma projection_nonexpansive {C : Set E} {P : E → E} (hP : Proj C P) (u v : E) :
    ‖P u - P v‖ ≤ ‖u - v‖ := by
  have h₁ := hP.var u (P v) (hP.mem v)
  have h₂ := hP.var v (P u) (hP.mem u)
  have heq : ⟪u - v, P u - P v⟫ - ‖P u - P v‖ ^ 2 =
      -⟪u - P u, P v - P u⟫ - ⟪v - P v, P u - P v⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    ring
  have hcs := real_inner_le_norm (u - v) (P u - P v)
  nlinarith [norm_nonneg (u - v), norm_nonneg (P u - P v)]

lemma projection_fixed_of_normal {C : Set E} {P : E → E} (hP : Proj C P)
    {x n : E} (hx : x ∈ C) (hn : Normal C x n) {γ : ℝ} (hγ : 0 ≤ γ) :
    P (x + γ • n) = x := by
  set p := P (x + γ • n)
  have h₁ := hP.var (x + γ • n) x hx
  have h₂ := hn p (hP.mem (x + γ • n))
  change ⟪x + γ • n - p, x - p⟫ ≤ 0 at h₁
  have heq : ⟪x + γ • n - p, x - p⟫ = ‖p - x‖ ^ 2 - γ * ⟪n, p - x⟫ := by
    have hp : x + γ • n - p = -(p - x) + γ • n := by module
    rw [hp, show x - p = -(p - x) by module]
    simp only [inner_add_left, inner_neg_left, inner_neg_right, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    ring
  rw [heq] at h₁
  have h₃ := mul_nonpos_of_nonneg_of_nonpos hγ h₂
  have hz : ‖p - x‖ = 0 := by nlinarith [sq_nonneg ‖p - x‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

lemma forward_normal {C : Set E} {P : E → E} (hP : Proj C P)
    (F : E → E) {L : ℝ} (hL : 0 < L) (u : E) :
    Normal C (P (u - (1 / L) • F u))
      (L • (u - P (u - (1 / L) • F u)) - F u) := by
  have h := hP.normal (u - (1 / L) • F u) (show 0 < 1 / L by positivity)
  have heq : (1 / L)⁻¹ • (u - (1 / L) • F u - P (u - (1 / L) • F u)) =
      L • (u - P (u - (1 / L) • F u)) - F u := by
    simp only [one_div, inv_inv, smul_sub, smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
    module
  rwa [heq] at h

lemma forward_residual_bound {F : E → E} {L D : ℝ} (hL : 0 ≤ L) {u v : E}
    (hlip : ‖F v - F u‖ ≤ L * ‖v - u‖) (hD : ‖v - u‖ ≤ D) :
    ‖F v + (L • (u - v) - F u)‖ ≤ 2 * L * D := by
  have heq : F v + (L • (u - v) - F u) = (F v - F u) + L • (u - v) := by abel
  rw [heq]
  have h := norm_add_le (F v - F u) (L • (u - v))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hL, norm_sub_rev u v] at h
  have hd := mul_le_mul_of_nonneg_left hD hL
  linarith

lemma projected_forward_contraction {C : Set E} {P A : E → E} {ρ L : ℝ}
    (hP : Proj C P) (hρ : 0 < ρ) (hL : ρ ≤ L)
    (hmono : ∀ u ∈ C, ∀ v ∈ C, ρ * ‖u - v‖ ^ 2 ≤ ⟪A u - A v, u - v⟫)
    (hlip : ∀ u ∈ C, ∀ v ∈ C, ‖A u - A v‖ ≤ L * ‖u - v‖)
    {u v : E} (hu : u ∈ C) (hv : v ∈ C) :
    ‖P (u - (ρ / L ^ 2) • A u) - P (v - (ρ / L ^ 2) • A v)‖ ≤
      (1 - ρ ^ 2 / (2 * L ^ 2)) * ‖u - v‖ := by
  have hLp : 0 < L := hρ.trans_le hL
  have hτ : 0 < ρ / L ^ 2 := by positivity
  have hp := projection_nonexpansive hP (u - (ρ / L ^ 2) • A u) (v - (ρ / L ^ 2) • A v)
  have he : (u - (ρ / L ^ 2) • A u) - (v - (ρ / L ^ 2) • A v) =
      (u - v) - (ρ / L ^ 2) • (A u - A v) := by module
  rw [he] at hp
  have heq : ‖(u - v) - (ρ / L ^ 2) • (A u - A v)‖ ^ 2 =
      ‖u - v‖ ^ 2 - 2 * (ρ / L ^ 2) * ⟪A u - A v, u - v⟫ +
        (ρ / L ^ 2) ^ 2 * ‖A u - A v‖ ^ 2 := by
    rw [norm_sub_sq_real]
    simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hτ, mul_pow]
    rw [real_inner_comm (u - v) (A u - A v)]
    ring
  have hm := mul_le_mul_of_nonneg_left (hmono u hu v hv) (show 0 ≤ 2 * (ρ / L ^ 2) by positivity)
  have hl := mul_self_le_mul_self (norm_nonneg _) (hlip u hu v hv)
  have hl₂ := mul_le_mul_of_nonneg_left hl (sq_nonneg (ρ / L ^ 2))
  have hcoef : 1 - 2 * (ρ / L ^ 2) * ρ + (ρ / L ^ 2) ^ 2 * L ^ 2 = 1 - ρ ^ 2 / L ^ 2 := by
    field_simp
    ring
  have hs : ‖(u - v) - (ρ / L ^ 2) • (A u - A v)‖ ^ 2 ≤
      (1 - ρ ^ 2 / L ^ 2) * ‖u - v‖ ^ 2 := by
    rw [← hcoef]
    nlinarith
  have hq : 0 ≤ 1 - ρ ^ 2 / (2 * L ^ 2) := by
    have hh := mul_self_le_mul_self hρ.le hL
    have : ρ ^ 2 / (2 * L ^ 2) ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith)
    linarith
  have hcoeff : 1 - ρ ^ 2 / L ^ 2 ≤ (1 - ρ ^ 2 / (2 * L ^ 2)) ^ 2 := by
    have hh : ρ ^ 2 / L ^ 2 = 2 * (ρ ^ 2 / (2 * L ^ 2)) := by ring
    rw [hh]
    nlinarith [sq_nonneg (ρ ^ 2 / (2 * L ^ 2))]
  have hh := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg ‖u - v‖)
  have hnorm : ‖(u - v) - (ρ / L ^ 2) • (A u - A v)‖ ≤
      (1 - ρ ^ 2 / (2 * L ^ 2)) * ‖u - v‖ := by
    nlinarith [norm_nonneg ((u - v) - (ρ / L ^ 2) • (A u - A v)),
      mul_nonneg hq (norm_nonneg (u - v))]
  exact hp.trans hnorm

lemma strongly_monotone_vi_exists {C : Set E} {P A : E → E} {ρ L : ℝ}
    (hC : IsComplete C) (hne : C.Nonempty) (hP : Proj C P) (hρ : 0 < ρ) (hL : ρ ≤ L)
    (hmono : ∀ u ∈ C, ∀ v ∈ C, ρ * ‖u - v‖ ^ 2 ≤ ⟪A u - A v, u - v⟫)
    (hlip : ∀ u ∈ C, ∀ v ∈ C, ‖A u - A v‖ ≤ L * ‖u - v‖) :
    ∃ s ∈ C, Normal C s (-A s) := by
  have hLp : 0 < L := hρ.trans_le hL
  let q := 1 - ρ ^ 2 / (2 * L ^ 2)
  have hq : 0 ≤ q := by
    have hh := mul_self_le_mul_self hρ.le hL
    have : ρ ^ 2 / (2 * L ^ 2) ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith)
    dsimp [q]; linarith
  have hq₁ : q < 1 := by
    have : 0 < ρ ^ 2 / (2 * L ^ 2) := by positivity
    dsimp [q]
    linarith
  let T : C → C := fun u => ⟨P (u - (ρ / L ^ 2) • A u), hP.mem _⟩
  have hT : ContractingWith ⟨q, hq⟩ T := by
    refine ⟨hq₁, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
    simp only [Subtype.dist_eq, dist_eq_norm]
    convert projected_forward_contraction hP hρ hL hmono hlip u.property v.property using 1
    norm_cast
  let : CompleteSpace C := hC.completeSpace_coe
  obtain ⟨u0, hu0⟩ := hne
  obtain ⟨s, hs, -⟩ := hT.exists_fixedPoint ⟨u0, hu0⟩ (edist_ne_top _ _)
  have hfix : P ((s : E) - (ρ / L ^ 2) • A s) = s := congrArg Subtype.val hs
  refine ⟨s, s.property, ?_⟩
  intro v hv
  have h := hP.var ((s : E) - (ρ / L ^ 2) • A s) v hv
  rw [hfix] at h
  have he : (s : E) - (ρ / L ^ 2) • A s - s = (ρ / L ^ 2) • (-A s) := by module
  rw [he, real_inner_smul_left] at h
  have hτ : 0 < ρ / L ^ 2 := by positivity
  nlinarith

end OracleTemplate.NearZeroSum
