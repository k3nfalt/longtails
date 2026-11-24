import LongTails.Proofs.NcConcaveInstance

open scoped BigOperators

namespace LongTails.Proofs.NcConcaveConcavity

open LongTails.Proofs.SmoothConvexFiniteGeometry LongTails.Proofs.NcConcaveScalars
open LongTails.Proofs.NcConcaveHuber LongTails.Proofs.NcConcaveBlock LongTails.Proofs.NcConcaveGadgets
open LongTails.Proofs.NcConcaveInstance

variable {m : ℕ}

lemma ramp_mono : Monotone ramp := by
  intro x y h
  simp only [ramp]
  split_ifs <;> nlinarith

lemma ramp_convex : ConvexOn ℝ Set.univ ramp := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  set z := a * x + b * y with hzdef
  have h1 := (ramp_model z x).1
  have h2 := (ramp_model z y).1
  have hz : a * (x - z) + b * (y - z) = 0 := by
    rw [hzdef]; linear_combination (-(a * x + b * y)) * hab
  have key : a * (ramp x - ramp z - rampSlope z * (x - z)) + b * (ramp y - ramp z - rampSlope z * (y - z)) =
      a * ramp x + b * ramp y - ramp z := by
    linear_combination (-ramp z) * hab - rampSlope z * hz
  linarith [mul_nonneg ha h1, mul_nonneg hb h2]

lemma comp_mono_convex {g h : ℝ → ℝ} (hg : ConvexOn ℝ Set.univ g) (hgm : Monotone g)
    (hh : ConvexOn ℝ Set.univ h) : ConvexOn ℝ Set.univ (fun t => g (h t)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have h1 := hh.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  have h2 := hg.2 (Set.mem_univ (h x)) (Set.mem_univ (h y)) ha hb hab
  exact (hgm h1).trans h2

lemma convex_comp_linear {ι : Type*} {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ)
    (L : (ι → ℝ) → ℝ) (hL : ∀ v w (a b : ℝ), L (a • v + b • w) = a * L v + b * L w) :
    ConvexOn ℝ Set.univ (fun v => φ (L v)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have := hφ.2 (Set.mem_univ (L x)) (Set.mem_univ (L y)) ha hb hab
  simp only [smul_eq_mul] at this ⊢
  rw [hL]; exact this

lemma zeta_sq_eq {θ : ℝ} (hθ : 0 < θ) (t : ℝ) :
    zeta θ t ^ 2 = θ ^ 2 * (rampR θ t ^ 2 + rampL θ t ^ 2) := by
  have hp : rampR θ t * rampL θ t = 0 := by
    rcases le_total t θ with h | h
    · rw [rampR_eq_zero hθ h, zero_mul]
    · rw [rampL_eq_zero hθ (by linarith), mul_zero]
  simp only [zeta]; nlinarith [hp]

lemma zeta_sq_convex {θ : ℝ} (hθ : 0 < θ) : ConvexOn ℝ Set.univ (fun t => zeta θ t ^ 2) := by
  have h1 : ConvexOn ℝ Set.univ (fun t => rampR θ t ^ 2) :=
    (rampR_convex θ hθ).pow (fun x _ => rampR_nonneg θ x) 2
  have h2 : ConvexOn ℝ Set.univ (fun t => rampL θ t ^ 2) :=
    (rampL_convex θ hθ).pow (fun x _ => rampL_nonneg θ x) 2
  have h := (h1.add h2).smul (sq_nonneg θ)
  have e : (fun t => zeta θ t ^ 2) = fun t => θ ^ 2 • ((fun t => rampR θ t ^ 2) + (fun t => rampL θ t ^ 2)) t := by
    funext t; simp [zeta_sq_eq hθ]
  rw [e]; exact h

lemma huber_zeta_eq {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) (t : ℝ) :
    huber c (zeta θ t) = c ^ 2 * (ramp (θ * rampR θ t / c) + ramp (θ * rampL θ t / c)) := by
  have hr0 : ramp 0 = 0 := by simp [ramp]
  simp only [huber]
  rcases le_total t θ with h | h
  · rw [rampR_eq_zero hθ h]
    simp only [zeta, rampR_eq_zero hθ h, zero_sub, mul_zero, zero_div, hr0, zero_add]
    have hl := rampL_nonneg θ t
    have hneg : -(θ * -rampL θ t) / c = θ * rampL θ t / c := by ring
    have hpos : θ * -rampL θ t / c ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by nlinarith) hc.le
    rw [hneg, show ramp (θ * -rampL θ t / c) = 0 by unfold ramp; rw [ite_eq_left hpos]]
    ring
  · rw [rampL_eq_zero hθ (by linarith)]
    simp only [zeta, rampL_eq_zero hθ (by linarith : -θ ≤ t), sub_zero, mul_zero, zero_div, hr0, add_zero]
    have hl := rampR_nonneg θ t
    have hpos : -(θ * rampR θ t) / c ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by nlinarith) hc.le
    rw [show ramp (-(θ * rampR θ t) / c) = 0 by unfold ramp; rw [ite_eq_left hpos]]
    ring

lemma huber_zeta_convex {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) :
    ConvexOn ℝ Set.univ (fun t => huber c (zeta θ t)) := by
  have hR : ConvexOn ℝ Set.univ (fun t => θ * rampR θ t / c) := by
    have := (rampR_convex θ hθ).smul (by positivity : (0 : ℝ) ≤ θ / c)
    convert this using 1; funext t; simp; ring
  have hL : ConvexOn ℝ Set.univ (fun t => θ * rampL θ t / c) := by
    have := (rampL_convex θ hθ).smul (by positivity : (0 : ℝ) ≤ θ / c)
    convert this using 1; funext t; simp; ring
  have h := ((comp_mono_convex ramp_convex ramp_mono hR).add
    (comp_mono_convex ramp_convex ramp_mono hL)).smul (sq_nonneg c)
  have e : (fun t => huber c (zeta θ t)) = fun t => c ^ 2 • ((fun t => ramp (θ * rampR θ t / c)) +
      (fun t => ramp (θ * rampL θ t / c))) t := by
    funext t; simp [huber_zeta_eq hc hθ]
  rw [e]; exact h

lemma convexOn_finset_sum {ι E : Type*} [AddCommGroup E] [Module ℝ E] (s : Finset ι)
    (f : ι → E → ℝ) (h : ∀ i ∈ s, ConvexOn ℝ Set.univ (f i)) :
    ConvexOn ℝ Set.univ (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set E)))
  | insert k s hk ih =>
    have e : (fun x => ∑ i ∈ insert k s, f i x) = f k + fun x => ∑ i ∈ s, f i x := by
      funext x; simp [Finset.sum_insert hk]
    rw [e]
    exact (h k (by simp)).add (ih fun i hi => h i (by simp [hi]))

lemma concave_linear1 (k : ℝ) : ConcaveOn ℝ Set.univ (fun t : ℝ => k * t) := by
  refine ⟨convex_univ, fun x _ y _ a b _ _ _ => ?_⟩
  simp only [smul_eq_mul]; nlinarith [le_refl (k * (a * x + b * y))]

lemma concave_coord {ι : Type*} {φ : ℝ → ℝ} (hφ : ConcaveOn ℝ Set.univ φ) (i : ι) :
    ConcaveOn ℝ Set.univ (fun v : ι → ℝ => φ (v i)) := by
  have h := convex_comp_linear hφ.neg (fun v : ι → ℝ => v i) (fun v w a b => by simp)
  have := h.neg
  convert this using 1; funext v; simp

theorem robB_concave {θ τ : ℝ} (hθ : 0 < θ) (hτ : 0 < τ) (a b : ℝ) :
    ConcaveOn ℝ Set.univ (fun y : Fin (m + 1) → ℝ => robB θ τ a b y) := by
  have hα := alpha_pos m
  have p1 : ConcaveOn ℝ Set.univ (fun y : Fin (m + 1) → ℝ => -(alpha m ^ 2 / 2) * zeta θ (y 0) ^ 2) := by
    have := (convex_comp_linear (zeta_sq_convex hθ) (fun y : Fin (m + 1) → ℝ => y 0)
      (fun v w a b => by simp)).smul (by positivity : (0 : ℝ) ≤ alpha m ^ 2 / 2)
    have h := this.neg
    convert h using 1; funext y; simp
  have p2 : ConcaveOn ℝ Set.univ (fun y : Fin (m + 1) → ℝ =>
      -∑ k : Fin m, huber τ (zeta (2 * θ) (y k.castSucc - y k.succ))) := by
    have hs := convexOn_finset_sum (Finset.univ : Finset (Fin m))
      (fun k (y : Fin (m + 1) → ℝ) => huber τ (zeta (2 * θ) (y k.castSucc - y k.succ)))
      (fun k _ => convex_comp_linear (huber_zeta_convex hτ (by linarith : (0 : ℝ) < 2 * θ))
        (fun y : Fin (m + 1) → ℝ => y k.castSucc - y k.succ) (fun v w a b => by simp; ring))
    exact hs.neg
  have hca : |alpha m * (a - zeta θ a)| ≤ 2 * alpha m * θ := by
    rw [abs_mul, abs_of_pos hα, abs_sub_comm]
    have := zeta_sub_le (θ := θ) (t := a) hθ
    nlinarith
  have hcb : |-(alpha m / 2) * (b - zeta θ b)| ≤ 2 * alpha m * θ := by
    rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < alpha m / 2), abs_sub_comm]
    have := zeta_sub_le (θ := θ) (t := b) hθ
    nlinarith
  have r0 : ConcaveOn ℝ Set.univ (fun t : ℝ => alpha m * zeta θ a * t +
      (alpha m * (a - zeta θ a) * zeta θ t - 2 * alpha m * θ * omega θ t)) :=
    (concave_linear1 _).add (repair_concave hθ hca)
  have rl : ConcaveOn ℝ Set.univ (fun t : ℝ => -(alpha m / 2) * zeta θ b * t +
      (-(alpha m / 2) * (b - zeta θ b) * zeta θ t - 2 * alpha m * θ * omega θ t)) :=
    (concave_linear1 _).add (repair_concave hθ hcb)
  have hsum := ((p1.add p2).add (concave_coord r0 0)).add (concave_coord rl (Fin.last m))
  have hc := hsum.add (concaveOn_const (-(alpha m ^ 2 * m * zeta θ b ^ 2 / 8)) convex_univ)
  convert hc using 1
  funext y
  simp only [robB, beta, Pi.add_apply]
  ring

end LongTails.Proofs.NcConcaveConcavity
