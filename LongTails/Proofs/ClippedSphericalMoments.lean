import LongTails.Proofs.WeakGradientSegments
import LongTails.Proofs.ScalarClippedMoments
import LongTails.Proofs.ScalarMomentConcentration

open MeasureTheory Set Metric
open scoped RealInnerProductSpace ContDiff

namespace LongTails.Proofs.ClippedSphericalMoments

open OracleTemplate.ZerothOrder LongTails.Proofs.DirectionalSphericalMoments
  LongTails.Proofs.WeightedSphericalMoments

variable {d : ℕ} [NeZero d]
local notation "H" => EuclideanSpace ℝ (Fin d)
local notation "S" => sphere (0 : H) 1
local notation "Q" => (sphereLaw H : Measure S)

lemma unit_sphere_direction_even_moment (i : Fin d) (v : H) (hv : ‖v‖ = 1) (k : ℕ) :
    (d : ℝ) ^ k * (∫ u : S, ⟪(u : H), v⟫ ^ (2 * k) ∂Q) ≤
      2 ^ k * (k.factorial : ℝ) := by
  let e : H := EuclideanSpace.single i 1
  let R := Submodule.reflection (ℝ ∙ (e - v))ᗮ
  have hRv : R e = v := Submodule.reflection_sub (by simp [e, hv])
  let f := fun u : S => ⟪(u : H), v⟫ ^ (2 * k)
  have he : (fun u : S => f (sphereRotate R u)) = fun u : S => (u : H) i ^ (2 * k) := by
    funext u
    dsimp [f, sphereRotate]
    rw [← hRv, R.inner_map_map]
    simp [e, PiLp.inner_apply]
  have heq := (sphereLaw_rotate H R).integral_comp (sphere_rotation_embedding R) f
  rw [he] at heq
  change (d : ℝ) ^ k * (∫ u, f u ∂Q) ≤ _
  rw [← heq]
  exact sphere_even_moment_bound i k

lemma sphere_direction_even_moment (v : H) (k : ℕ) :
    Integrable (fun u : S => ⟪(u : H), v⟫ ^ (2 * k)) Q ∧
      (d : ℝ) ^ k * (∫ u : S, ⟪(u : H), v⟫ ^ (2 * k) ∂Q) ≤
        2 ^ k * (k.factorial : ℝ) * ‖v‖ ^ (2 * k) := by
  have hc : Continuous (fun u : S => ⟪(u : H), v⟫ ^ (2 * k)) := by fun_prop
  refine ⟨hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _), ?_⟩
  let i : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  obtain ⟨w, hw, hv⟩ := unit_direction_representation i v
  have h := unit_sphere_direction_even_moment i w hw k
  have he : (fun u : S => ⟪(u : H), v⟫ ^ (2 * k)) =
      fun u : S => ‖v‖ ^ (2 * k) * ⟪(u : H), w⟫ ^ (2 * k) := by
    funext u
    conv_lhs => rw [hv, real_inner_smul_right, mul_pow]
  rw [he, integral_const_mul]
  have hh := mul_le_mul_of_nonneg_right h (pow_nonneg (norm_nonneg v) (2 * k))
  nlinarith only [hh]

lemma clipped_moment_rescaling {D A W K B h τ : ℝ} (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hB : 0 ≤ B) (hτ : 0 ≤ τ) (k : ℕ)
    (ha : D ^ (k + 2) * A ≤ 5 * K * B)
    (hw : D ^ (k + 1) * W ≤ K) :
    D ^ (2 * (k + 1)) * (τ ^ (2 * k) * (2 * A + 2 * h ^ 2 * W)) ≤
      12 * K * (B + D * h ^ 2) * (D * τ ^ 2) ^ k := by
  have hA : D ^ (2 * (k + 1)) * A ≤ 5 * K * B * D ^ k := by
    convert mul_le_mul_of_nonneg_right ha (pow_nonneg hD k) using 1; ring
  have hW : D ^ (2 * (k + 1)) * W ≤ K * D ^ (k + 1) := by
    convert mul_le_mul_of_nonneg_right hw (pow_nonneg hD (k + 1)) using 1; ring
  calc
    D ^ (2 * (k + 1)) * (τ ^ (2 * k) * (2 * A + 2 * h ^ 2 * W)) =
        τ ^ (2 * k) * (2 * (D ^ (2 * (k + 1)) * A) + 2 * h ^ 2 * (D ^ (2 * (k + 1)) * W)) := by ring
    _ ≤ τ ^ (2 * k) * (2 * (5 * K * B * D ^ k) + 2 * h ^ 2 * (K * D ^ (k + 1))) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hτ _)
      exact add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num))
        (mul_le_mul_of_nonneg_left hW (by positivity))
    _ ≤ τ ^ (2 * k) * (12 * K * (B + D * h ^ 2) * D ^ k) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hτ _)
      rw [show D ^ (k + 1) = D ^ k * D by ring]
      nlinarith [mul_nonneg (mul_nonneg hK hB) (pow_nonneg hD k),
        mul_nonneg (mul_nonneg (mul_nonneg hK hD) (sq_nonneg h)) (pow_nonneg hD k)]
    _ = 12 * K * (B + D * h ^ 2) * (D * τ ^ 2) ^ k := by ring

lemma clipped_direction_even_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {a c : S × Ω → ℝ} {τ B h : ℝ}
    (ha : Measurable a) (hc : Measurable c) (hτ : 0 ≤ τ) (hB : 0 ≤ B)
    (hcb : ∀ z, |c z| ≤ h) (v : H) (k : ℕ)
    (hai : Integrable (fun z : S × Ω => a z ^ 2 * ⟪(z.1 : H), v⟫ ^ (2 * (k + 1))) ((Q).prod P))
    (hab : (d : ℝ) ^ (k + 2) * (∫ z : S × Ω, a z ^ 2 * ⟪(z.1 : H), v⟫ ^ (2 * (k + 1)) ∂(Q).prod P) ≤
      5 * 8 ^ (k + 1) * ((k + 1).factorial : ℝ) * B * ‖v‖ ^ (2 * (k + 1))) :
    Integrable (fun z : S × Ω =>
      |(d : ℝ) * OracleTemplate.clip τ (a z + c z) * ⟪(z.1 : H), v⟫| ^ (2 * (k + 1))) ((Q).prod P) ∧
      (∫ z : S × Ω, |(d : ℝ) * OracleTemplate.clip τ (a z + c z) * ⟪(z.1 : H), v⟫| ^ (2 * (k + 1)) ∂(Q).prod P) ≤
        12 * 8 ^ (k + 1) * ((k + 1).factorial : ℝ) * (B + d * h ^ 2) *
          ((d : ℝ) * τ ^ 2) ^ k * ‖v‖ ^ (2 * (k + 1)) := by
  let w := fun z : S × Ω => ⟪(z.1 : H), v⟫
  have hw : Measurable w := by
    have hcont : Continuous (fun u : S => ⟪(u : H), v⟫) := by fun_prop
    exact hcont.measurable.comp measurable_fst
  have he (z : S × Ω) : |w z| ^ (2 * (k + 1)) = w z ^ (2 * (k + 1)) := by
    simp only [pow_mul, sq_abs]
  have hs := sphere_direction_even_moment v (k + 1)
  have hwi : Integrable (fun z : S × Ω => w z ^ (2 * (k + 1))) ((Q).prod P) := hs.1.comp_fst P
  have hweight : (d : ℝ) ^ (k + 1) * (∫ z : S × Ω, w z ^ (2 * (k + 1)) ∂(Q).prod P) ≤
      8 ^ (k + 1) * ((k + 1).factorial : ℝ) * ‖v‖ ^ (2 * (k + 1)) := by
    have heq : (∫ z : S × Ω, w z ^ (2 * (k + 1)) ∂(Q).prod P) =
        ∫ u : S, ⟪(u : H), v⟫ ^ (2 * (k + 1)) ∂Q := by
      rw [integral_prod _ hwi]
      simp [w]
    rw [heq]
    apply hs.2.trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _)
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    exact pow_le_pow_left₀ (by norm_num) (by norm_num : (2 : ℝ) ≤ 8) (k + 1)
  have hCa := ScalarClippedMoments.scalar_clipped_perturbed_moment hτ ha hc hw hcb k
    (by simpa only [he] using hai) (by simpa only [he] using hwi)
  simp only [he] at hCa
  let K := 8 ^ (k + 1) * ((k + 1).factorial : ℝ) * ‖v‖ ^ (2 * (k + 1))
  have hres := clipped_moment_rescaling (h := h) (Nat.cast_nonneg d) (show 0 ≤ K by dsimp [K]; positivity)
    hB hτ k (show (d : ℝ) ^ (k + 2) * (∫ z, a z ^ 2 * w z ^ (2 * (k + 1)) ∂(Q).prod P) ≤
      5 * K * B by dsimp [K, w]; nlinarith only [hab]) hweight
  have hscale : (fun z : S × Ω =>
      |(d : ℝ) * OracleTemplate.clip τ (a z + c z) * ⟪(z.1 : H), v⟫| ^ (2 * (k + 1))) =
      fun z : S × Ω => (d : ℝ) ^ (2 * (k + 1)) *
        |OracleTemplate.clip τ (a z + c z) * w z| ^ (2 * (k + 1)) := by
    funext z
    rw [mul_assoc, abs_mul, mul_pow, abs_of_nonneg (Nat.cast_nonneg d)]
  rw [hscale]
  refine ⟨hCa.1.const_mul _, ?_⟩
  rw [integral_const_mul]
  have hh := (mul_le_mul_of_nonneg_left hCa.2 (pow_nonneg (Nat.cast_nonneg d) (2 * (k + 1)))).trans hres
  dsimp [K] at hh
  nlinarith only [hh]

lemma clipped_direction_centered_mgf {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {a c : S × Ω → ℝ} {τ B h θ : ℝ}
    (ha : Measurable a) (hc : Measurable c) (hτ : 0 ≤ τ) (hB : 0 ≤ B)
    (hcb : ∀ z, |c z| ≤ h) (v : H)
    (hm : ∀ k : ℕ,
      Integrable (fun z : S × Ω => a z ^ 2 * ⟪(z.1 : H), v⟫ ^ (2 * (k + 1))) ((Q).prod P) ∧
      (d : ℝ) ^ (k + 2) * (∫ z : S × Ω, a z ^ 2 * ⟪(z.1 : H), v⟫ ^ (2 * (k + 1)) ∂(Q).prod P) ≤
        5 * 8 ^ (k + 1) * ((k + 1).factorial : ℝ) * B * ‖v‖ ^ (2 * (k + 1)))
    (hsmall : 256 * |θ| * (Real.sqrt d * τ * ‖v‖) < 1) :
    let X := fun z : S × Ω => (d : ℝ) * OracleTemplate.clip τ (a z + c z) * ⟪(z.1 : H), v⟫
    Integrable (fun z => Real.exp (θ * (X z - ∫ w, X w ∂(Q).prod P))) ((Q).prod P) ∧
      (∫ z, Real.exp (θ * (X z - ∫ w, X w ∂(Q).prod P)) ∂(Q).prod P) ≤
        Real.exp (131072 * ((B + d * h ^ 2) * ‖v‖ ^ 2) * θ ^ 2 /
          (1 - 256 * |θ| * (Real.sqrt d * τ * ‖v‖))) := by
  let X := fun z : S × Ω => (d : ℝ) * OracleTemplate.clip τ (a z + c z) * ⟪(z.1 : H), v⟫
  have hinner : Measurable (fun z : S × Ω => ⟪(z.1 : H), v⟫) := by
    have hh : Continuous (fun u : S => ⟪(u : H), v⟫) := by fun_prop
    exact hh.measurable.comp measurable_fst
  have hX : Measurable X := (((OracleTemplate.measurable_clip τ).comp (ha.add hc)).const_mul _).mul hinner
  have hbound (z : S × Ω) : |X z| ≤ (d : ℝ) * τ * ‖v‖ := by
    have hu : ‖(z.1 : H)‖ = 1 := by simpa only [mem_sphere_iff_norm, sub_zero] using z.1.property
    have hi : |⟪(z.1 : H), v⟫| ≤ ‖v‖ := by simpa only [hu, one_mul] using abs_real_inner_le_norm (z.1 : H) v
    have ht : |OracleTemplate.clip τ (a z + c z)| ≤ τ := by
      simpa only [Real.norm_eq_abs] using OracleTemplate.norm_clip_le hτ (a z + c z)
    dsimp [X]
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg d)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg d)) hi
      (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg d) hτ)
  have hs : (Real.sqrt (d : ℝ)) ^ 2 = (d : ℝ) := Real.sq_sqrt (Nat.cast_nonneg d)
  apply ScalarMomentConcentration.bounded_centered_mgf_bernstein hX hbound (by positivity)
    (by positivity) hsmall
  intro k
  have hh := clipped_direction_even_moment ha hc hτ hB hcb v k (hm k).1 (hm k).2
  refine ⟨hh.1, hh.2.trans_eq ?_⟩
  simp only [mul_pow, pow_mul, hs]
  ring

lemma weak_clipped_direction_even_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : H × Ω → ℝ} {G : H × Ω → H}
    {C U : Set H} (hC : IsCompact C) (hUC : U ⊆ C)
    (hFm : Measurable F) (hG : Measurable G)
    (hF : ∀ᵐ ξ ∂P, ContinuousOn (fun z => F (z, ξ)) C ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    (x : H) {γ B τ h : ℝ} (hγ : 0 < γ) (hB : 0 ≤ B) (hτ : 0 ≤ τ)
    (hU : ball x γ ⊆ U) (hCU : closedBall x γ ⊆ C)
    (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B)
    {c : S × Ω → ℝ} (hc : Measurable c) (hcb : ∀ z, |c z| ≤ h) (v : H) (k : ℕ) :
    let a := fun z : S × Ω =>
      (F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)
    Integrable (fun z : S × Ω =>
      |(d : ℝ) * OracleTemplate.clip τ (a z + c z) * ⟪(z.1 : H), v⟫| ^ (2 * (k + 1))) ((Q).prod P) ∧
      (∫ z : S × Ω, |(d : ℝ) * OracleTemplate.clip τ (a z + c z) * ⟪(z.1 : H), v⟫| ^ (2 * (k + 1)) ∂(Q).prod P) ≤
        12 * 8 ^ (k + 1) * ((k + 1).factorial : ℝ) * (B + d * h ^ 2) *
          ((d : ℝ) * τ ^ 2) ^ k * ‖v‖ ^ (2 * (k + 1)) := by
  let a := fun z : S × Ω =>
    (F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)
  have ha : Measurable a := by
    have hp : Continuous (fun u : S => x + γ • (u : H)) := by fun_prop
    have hn : Continuous (fun u : S => x - γ • (u : H)) := by fun_prop
    exact ((hFm.comp ((hp.measurable.comp measurable_fst).prodMk measurable_snd)).sub
      (hFm.comp ((hn.measurable.comp measurable_fst).prodMk measurable_snd))).div_const _
  have hbase := WeakGradientSegments.weak_spherical_directional_moment
    hC hUC hFm hG hF x hγ hB hU hCU hi hb v (k + 1)
  exact clipped_direction_even_moment ha hc hτ hB hcb v k hbase.1 hbase.2

lemma weak_clipped_direction_centered_mgf {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : H × Ω → ℝ} {G : H × Ω → H}
    {C U : Set H} (hC : IsCompact C) (hUC : U ⊆ C)
    (hFm : Measurable F) (hG : Measurable G)
    (hF : ∀ᵐ ξ ∂P, ContinuousOn (fun z => F (z, ξ)) C ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    (x : H) {γ B τ h θ : ℝ} (hγ : 0 < γ) (hB : 0 ≤ B) (hτ : 0 ≤ τ)
    (hU : ball x γ ⊆ U) (hCU : closedBall x γ ⊆ C)
    (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B)
    {c : S × Ω → ℝ} (hc : Measurable c) (hcb : ∀ z, |c z| ≤ h) (v : H)
    (hsmall : 256 * |θ| * (Real.sqrt d * τ * ‖v‖) < 1) :
    let a := fun z : S × Ω =>
      (F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)
    let X := fun z : S × Ω => (d : ℝ) * OracleTemplate.clip τ (a z + c z) * ⟪(z.1 : H), v⟫
    Integrable (fun z => Real.exp (θ * (X z - ∫ w, X w ∂(Q).prod P))) ((Q).prod P) ∧
      (∫ z, Real.exp (θ * (X z - ∫ w, X w ∂(Q).prod P)) ∂(Q).prod P) ≤
        Real.exp (131072 * ((B + d * h ^ 2) * ‖v‖ ^ 2) * θ ^ 2 /
          (1 - 256 * |θ| * (Real.sqrt d * τ * ‖v‖))) := by
  let a := fun z : S × Ω =>
    (F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)
  have ha : Measurable a := by
    have hp : Continuous (fun u : S => x + γ • (u : H)) := by fun_prop
    have hn : Continuous (fun u : S => x - γ • (u : H)) := by fun_prop
    exact ((hFm.comp ((hp.measurable.comp measurable_fst).prodMk measurable_snd)).sub
      (hFm.comp ((hn.measurable.comp measurable_fst).prodMk measurable_snd))).div_const _
  exact clipped_direction_centered_mgf ha hc hτ hB hcb v
    (fun k => WeakGradientSegments.weak_spherical_directional_moment
      hC hUC hFm hG hF x hγ hB hU hCU hi hb v (k + 1)) hsmall

end LongTails.Proofs.ClippedSphericalMoments
