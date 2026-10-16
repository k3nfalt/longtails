import LongTails.Proofs.SamCycle

open InnerProductSpace
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SamCycle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma scaled_certificate (U : Space →ₗᵢ[ℝ] E) {L ρ μ t : ℝ}
    (hμ : 0 ≤ μ) (hμb : μ ≤ 1/100) (ht : 0 ≤ t) (htb : t ≤ 1/10) (i j : Fin 5) :
    ‖(L*ρ) • U (grad μ t j) - (L*ρ) • U (grad μ t i)‖^2 +
      (L*μ)*L*‖ρ • U (point μ t j) - ρ • U (point μ t i)‖^2 -
      2*(L*μ)*⟪(L*ρ) • U (grad μ t j) - (L*ρ) • U (grad μ t i),
        ρ • U (point μ t j) - ρ • U (point μ t i)⟫ ≤
      2*(L-L*μ)*(L*ρ^2*value μ t j - L*ρ^2*value μ t i -
        ⟪(L*ρ) • U (grad μ t i), ρ • U (point μ t j) - ρ • U (point μ t i)⟫) := by
  simp only [← smul_sub, ← map_sub, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    U.norm_map, real_inner_smul_left, inner_smul_right, U.inner_map_map]
  have h := mul_le_mul_of_nonneg_left (certificate hμ hμb ht htb i j)
    (mul_nonneg (sq_nonneg L) (sq_nonneg ρ))
  convert h using 1 <;> ring

lemma exists_scaled_model (U : Space →ₗᵢ[ℝ] E) {L ρ μ t : ℝ}
    (hL : 0 < L) (hμ : 0 < μ) (hμb : μ ≤ 1/100) (ht : 0 < t) (htb : t ≤ 1/10) :
    ∃ f : E → ℝ,
      (∀ a, HasGradientAt f (gradient f a) a) ∧
      (∀ a b, f a + ⟪gradient f a, b-a⟫ + (L*μ)/2*‖b-a‖^2 ≤ f b) ∧
      (∀ a b, ‖gradient f a-gradient f b‖ ≤ L*‖a-b‖) ∧
      (∀ i, f (ρ • U (point μ t i)) = L*ρ^2*value μ t i ∧
        gradient f (ρ • U (point μ t i)) = (L*ρ) • U (grad μ t i)) ∧
      f 0 = 0 ∧ IsMinOn f Set.univ 0 := by
  have hmL : L*μ < L := by nlinarith
  obtain ⟨f, G, hf, hc, hl, hi⟩ := SmoothInterpolation.strong_interpolation
    (mul_pos hL hμ).le hmL (fun i => ρ • U (point μ t i))
    (fun i => (L*ρ) • U (grad μ t i)) (fun i => L*ρ^2*value μ t i)
    (scaled_certificate U hμ.le hμb ht.le htb)
  have hg : ∀ a, gradient f a = G a := fun a => (hf a).gradient
  have h0 := hi 0
  norm_num [point, grad, value] at h0
  refine ⟨f, ?_, ?_, ?_, ?_, h0.1, ?_⟩
  · simpa only [hg] using hf
  · simpa only [hg] using hc
  · simpa only [hg] using hl
  · simpa only [hg] using hi
  · intro a _
    change f 0 ≤ f a
    have h := hc 0 a
    rw [h0.1, h0.2, inner_zero_left, sub_zero] at h
    have hn : 0 ≤ (L*μ)/2*‖a‖^2 := by positivity
    linarith [h0.1]

omit [CompleteSpace E] in
lemma scaled_perturbation (U : Space →ₗᵢ[ℝ] E) {L ρ : ℝ}
    (hL : 0 < L) (hρ : 0 < ρ) (x g : Space) :
    ρ • U x + (ρ / ‖(L*ρ) • U g‖) • ((L*ρ) • U g) =
      ρ • U (x + (1/‖g‖) • g) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hL hρ), U.norm_map,
    map_add, map_smul, smul_add, smul_smul, smul_smul]
  congr 1
  congr 1
  by_cases hg : ‖g‖ = 0
  · simp [hg]
  · field_simp

lemma scaled_step (U : Space →ₗᵢ[ℝ] E) {L ρ s : ℝ}
    (hL : 0 < L) (hρ : 0 < ρ) (x g y h z : Space) {f : E → ℝ}
    (hg : gradient f (ρ • U x) = (L*ρ) • U g)
    (hh : gradient f (ρ • U y) = (L*ρ) • U h)
    (hp : x + (1/‖g‖) • g = y) (hu : x - s • h = z) :
    LongTails.Algorithms.NormalizedSam.step (gradient f) (s/L) ρ (ρ • U x) = ρ • U z := by
  unfold LongTails.Algorithms.NormalizedSam.step
  rw [hg, scaled_perturbation U hL hρ, hp, hh, ← hu, map_sub, map_smul,
    smul_sub, smul_smul, smul_smul]
  congr 1
  congr 1
  field_simp

lemma scaled_steps (U : Space →ₗᵢ[ℝ] E) {L ρ μ t : ℝ}
    (hL : 0 < L) (hρ : 0 < ρ) (hμ : 0 < μ) (ht : 0 < t) {f : E → ℝ}
    (hg : ∀ i, gradient f (ρ • U (point μ t i)) = (L*ρ) • U (grad μ t i)) :
    LongTails.Algorithms.NormalizedSam.step (gradient f) (μ*t/L) ρ (ρ • U (point μ t 1)) =
      ρ • U (point μ t 2) ∧
    LongTails.Algorithms.NormalizedSam.step (gradient f) (μ*t/L) ρ (ρ • U (point μ t 2)) =
      ρ • U (point μ t 1) := by
  constructor
  · apply scaled_step U hL hρ _ _ _ _ _ (hg 1) (hg 3) (perturbation_plus hμ ht)
    norm_num [point, grad, pair_smul, pair_sub]
    congr 1
    ring
  · apply scaled_step U hL hρ _ _ _ _ _ (hg 2) (hg 4) (perturbation_minus hμ ht)
    norm_num [point, grad, pair_smul, pair_sub]
    congr 1
    ring

lemma scaled_output_in_cycle (U : Space →ₗᵢ[ℝ] E) {L ρ μ t : ℝ}
    (hL : 0 < L) (hρ : 0 < ρ) (hμ : 0 < μ) (ht : 0 < t) {f : E → ℝ}
    (hg : ∀ i, gradient f (ρ • U (point μ t i)) = (L*ρ) • U (grad μ t i)) (T : ℕ) :
    LongTails.Algorithms.NormalizedSam.output (gradient f) (μ*t/L) ρ (ρ • U (point μ t 1)) T =
      ρ • U (point μ t 1) ∨
    LongTails.Algorithms.NormalizedSam.output (gradient f) (μ*t/L) ρ (ρ • U (point μ t 1)) T =
      ρ • U (point μ t 2) := by
  obtain ⟨h1, h2⟩ := scaled_steps U hL hρ hμ ht hg
  unfold LongTails.Algorithms.NormalizedSam.output
  induction T with
  | zero => exact Or.inl rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h
    · rw [h, h1]
      exact Or.inr rfl
    · rw [h, h2]
      exact Or.inl rfl

lemma scaled_average_gap (U : Space →ₗᵢ[ℝ] E) {L ρ μ t a b : ℝ}
    (hL : 0 ≤ L) (hμ : 0 ≤ μ) (hab : a+b=1) {f : E → ℝ}
    (hc : ∀ x y, f x + ⟪gradient f x, y-x⟫ + (L*μ)/2*‖y-x‖^2 ≤ f y)
    (hg0 : gradient f 0 = 0) :
    9*L*μ*ρ^2*t^2/80000 ≤
      f (a • (ρ • U (point μ t 1)) + b • (ρ • U (point μ t 2))) - f 0 := by
  let z : Space := a • point μ t 1 + b • point μ t 2
  have hz : z 0 = 3*t/200 := by
    change a*(3*t/200)+b*(3*t/200)=3*t/200
    calc
      _ = (a+b)*(3*t/200) := by ring
      _ = _ := by rw [hab, one_mul]
  have he : a • (ρ • U (point μ t 1)) + b • (ρ • U (point μ t 2)) = ρ • U z := by
    simp only [z, map_add, map_smul, smul_add]
    module
  rw [he]
  have h := hc 0 (ρ • U z)
  rw [hg0, inner_zero_left, sub_zero, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    U.norm_map] at h
  have hn := mul_le_mul_of_nonneg_left (norm_sq_coordinate z)
    (by positivity : 0 ≤ L*μ/2*ρ^2)
  rw [hz] at hn
  nlinarith


lemma exists_scaled_orbit (U : Space →ₗᵢ[ℝ] E) {L ρ μ t : ℝ}
    (hL : 0 < L) (hρ : 0 < ρ) (hμ : 0 < μ) (hμb : μ ≤ 1/100)
    (ht : 0 < t) (htb : t ≤ 1/10) :
    ∃ f : E → ℝ,
      (∀ a, HasGradientAt f (gradient f a) a) ∧
      (∀ a b, f a + ⟪gradient f a, b-a⟫ + (L*μ)/2*‖b-a‖^2 ≤ f b) ∧
      (∀ a b, ‖gradient f a-gradient f b‖ ≤ L*‖a-b‖) ∧
      IsMinOn f Set.univ 0 ∧
      (∀ T, f (LongTails.Algorithms.NormalizedSam.output (gradient f) (μ*t/L) ρ
        (ρ • U (point μ t 1)) T) - f 0 = L*ρ^2*μ*t^2/5000) ∧
      LongTails.Algorithms.NormalizedSam.step (gradient f) (μ*t/L) ρ (ρ • U (point μ t 1)) = ρ • U (point μ t 2) ∧
      LongTails.Algorithms.NormalizedSam.step (gradient f) (μ*t/L) ρ (ρ • U (point μ t 2)) = ρ • U (point μ t 1) ∧
      (∀ a b : ℝ, a+b=1 → 9*L*μ*ρ^2*t^2/80000 ≤
        f (a • (ρ • U (point μ t 1)) + b • (ρ • U (point μ t 2))) - f 0) := by
  obtain ⟨f, hf, hc, hl, hi, h0, hmin⟩ := exists_scaled_model U hL hμ hμb ht htb
  refine ⟨f, hf, hc, hl, hmin, ?_, (scaled_steps U hL hρ hμ ht (fun i => (hi i).2)).1,
    (scaled_steps U hL hρ hμ ht (fun i => (hi i).2)).2, ?_⟩
  · intro T
    rcases scaled_output_in_cycle U hL hρ hμ ht (fun i => (hi i).2) T with h | h
    · rw [h, (hi 1).1, h0]
      norm_num [value]
      ring
    · rw [h, (hi 2).1, h0]
      norm_num [value]
      ring
  · intro a b hab
    have hg0 := (hi 0).2
    norm_num [point, grad] at hg0
    exact scaled_average_gap U hL.le hμ.le hab hc hg0

lemma exists_residual (U : Space →ₗᵢ[ℝ] E) {L ρ μ η : ℝ}
    (hL : 0 < L) (hρ : 0 < ρ) (hμ : 0 < μ) (hμb : μ ≤ L/100)
    (hη : 0 < η) (hηb : η ≤ μ/(10*L^2)) :
    ∃ (f : E → ℝ) (x0 x1 : E),
      (∀ a, HasGradientAt f (gradient f a) a) ∧
      (∀ a b, f a + ⟪gradient f a, b-a⟫ + μ/2*‖b-a‖^2 ≤ f b) ∧
      (∀ a b, ‖gradient f a-gradient f b‖ ≤ L*‖a-b‖) ∧
      IsMinOn f Set.univ 0 ∧
      (∀ T, f (LongTails.Algorithms.NormalizedSam.output (gradient f) η ρ x0 T) - f 0 =
        η^2*L^4*ρ^2/(5000*μ)) ∧
      LongTails.Algorithms.NormalizedSam.step (gradient f) η ρ x0 = x1 ∧
      LongTails.Algorithms.NormalizedSam.step (gradient f) η ρ x1 = x0 ∧
      (∀ a b : ℝ, a+b=1 → 9*η^2*L^4*ρ^2/(80000*μ) ≤ f (a • x0 + b • x1)-f 0) := by
  have hm : 0 < μ/L := div_pos hμ hL
  have hmb : μ/L ≤ 1/100 := (div_le_iff₀ hL).mpr (by linarith)
  have ht : 0 < η*L^2/μ := by positivity
  have htb : η*L^2/μ ≤ 1/10 := by
    apply (div_le_iff₀ hμ).mpr
    have h := (le_div_iff₀ (by positivity : 0 < 10*L^2)).mp hηb
    nlinarith
  obtain ⟨f, hf, hc, hl, hmin, ho, h01, h10, havg⟩ := exists_scaled_orbit U hL hρ hm hmb ht htb
  have hscale : L*(μ/L)=μ := by field_simp
  have hstep : (μ/L)*(η*L^2/μ)/L=η := by field_simp
  have hgap : L*ρ^2*(μ/L)*(η*L^2/μ)^2/5000=η^2*L^4*ρ^2/(5000*μ) := by
    field_simp
  have havgeq : 9*L*(μ/L)*ρ^2*(η*L^2/μ)^2/80000=9*η^2*L^4*ρ^2/(80000*μ) := by field_simp
  refine ⟨f, ρ • U (point (μ/L) (η*L^2/μ) 1), ρ • U (point (μ/L) (η*L^2/μ) 2),
    hf, ?_, hl, hmin, ?_, ?_, ?_, ?_⟩
  · simpa only [hscale] using hc
  · simpa only [hstep, hgap] using ho
  · simpa only [hstep] using h01
  · simpa only [hstep] using h10
  · simpa only [havgeq] using havg


end LongTails.Proofs.SamCycle
