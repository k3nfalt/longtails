import LongTails.Proofs.ScalarInterval

namespace OracleTemplate.BoundedScalarConvex

open ScalarStopLoss

noncomputable def profile (F : ℝ → ℝ) (b v h H z : ℝ) : ℝ :=
  max 0 (F (b+h*z)-v)/(h*H)

lemma profile_nonneg {F : ℝ → ℝ} {b v h H z : ℝ} (hh : 0 < h) (hH : 0 < H) :
    0 ≤ profile F b v h H z := div_nonneg (le_max_left _ _) (by positivity)

lemma profile_zero {F : ℝ → ℝ} {b v h H : ℝ} (hb : F b ≤ v) :
    profile F b v h H 0 = 0 := by
  simp [profile, max_eq_left (sub_nonpos.mpr hb)]

lemma profile_convex {F : ℝ → ℝ} {b v h H : ℝ}
    (hF : ConvexOn ℝ Set.univ F) (hh : 0 < h) (hH : 0 < H) :
    ConvexOn ℝ Set.univ (profile F b v h H) := by
  have hp := positive_part_convex hF v
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a c ha hc hac
  have hconv := hp.2 (Set.mem_univ (b+h*x)) (Set.mem_univ (b+h*y)) ha hc hac
  simp only [smul_eq_mul] at hconv ⊢
  have he : a*(b+h*x)+c*(b+h*y)=b+h*(a*x+c*y) := by
    calc
      _ = (a+c)*b+h*(a*x+c*y) := by ring
      _ = _ := by rw [hac]; ring
  rw [he] at hconv
  unfold profile
  have hd := (div_le_div_iff_of_pos_right (mul_pos hh hH)).mpr hconv
  convert hd using 1
  ring

lemma profile_lipschitz {F : ℝ → ℝ} {b v h H : ℝ}
    (hh : 0 < h) (hH : 0 < H)
    (hF : ∀ x y, |F x-F y| ≤ H*|x-y|) (x y : ℝ) :
    |profile F b v h H x-profile F b v h H y| ≤ |x-y| := by
  have hm := abs_max_sub_max_le_max (0 : ℝ) (F (b+h*x)-v) 0 (F (b+h*y)-v)
  simp only [sub_self, abs_zero, sub_sub_sub_cancel_right] at hm
  rw [max_eq_right (abs_nonneg (F (b+h*x)-F (b+h*y)))] at hm
  have hf := hF (b+h*x) (b+h*y)
  have he : b+h*x-(b+h*y)=h*(x-y) := by ring
  rw [he, abs_mul, abs_of_pos hh] at hf
  unfold profile
  rw [← sub_div, abs_div, abs_of_pos (mul_pos hh hH)]
  apply (div_le_iff₀ (mul_pos hh hH)).mpr
  nlinarith [hm.trans hf]

lemma profile_monotone {F : ℝ → ℝ} {b v h H : ℝ}
    (hF : ConvexOn ℝ Set.univ F) (hh : 0 < h) (hH : 0 < H) (hb : F b ≤ v) :
    MonotoneOn (profile F b v h H) (Set.Ici 0) := by
  apply convex_monotone_right_of_min (profile_convex hF hh hH)
  intro x
  rw [profile_zero hb]
  exact profile_nonneg hh hH

lemma profile_grid_bounds {F : ℝ → ℝ} {b v h H : ℝ}
    (hF : ConvexOn ℝ Set.univ F) (hh : 0 < h) (hH : 0 < H) (hb : F b ≤ v)
    (hL : ∀ x y, |F x-F y| ≤ H*|x-y|) (j : ℕ) :
    0 ≤ profile F b v h H (j+1)-profile F b v h H j ∧
      profile F b v h H (j+1)-profile F b v h H j ≤ 1 := by
  constructor
  · apply sub_nonneg.mpr
    exact profile_monotone hF hh hH hb (show (j : ℝ) ∈ Set.Ici 0 by change 0 ≤ (j : ℝ); positivity)
      (show (j : ℝ)+1 ∈ Set.Ici 0 by change 0 ≤ (j : ℝ)+1; positivity) (by linarith)
  · have hl := profile_lipschitz (b := b) (v := v) hh hH hL ((j : ℝ)+1) j
    norm_num at hl
    exact (le_abs_self _).trans hl

lemma profile_grid_mono {F : ℝ → ℝ} {b v h H : ℝ}
    (hF : ConvexOn ℝ Set.univ F) (hh : 0 < h) (hH : 0 < H) :
    Monotone (fun j : ℕ => profile F b v h H (j+1)-profile F b v h H j) := by
  apply monotone_nat_of_le_succ
  intro j
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
    grid_slope_mono (profile_convex (b := b) (v := v) hF hh hH) (j : ℝ)

lemma profile_two {F : ℝ → ℝ} {b v h H : ℝ} (hh : 0 < h) (hH : 0 < H)
    (hb : F b ≤ v) (hL : ∀ x y, |F x-F y| ≤ H*|x-y|) :
    profile F b v h H 2 ≤ 2 := by
  have ht := profile_lipschitz (b := b) (v := v) hh hH hL 2 0
  rw [profile_zero hb] at ht
  norm_num at ht
  exact (le_abs_self _).trans ht

lemma profile_secant_support {F : ℝ → ℝ} {b v h H x g : ℝ}
    (hF : ConvexOn ℝ Set.univ F) (hh : 0 < h) (hH : 0 < H)
    (hv : v ≤ F x) (hg : ∀ y, F x+g*(y-x) ≤ F y)
    (j : ℕ) (hj : b+h*((j : ℝ)+1) ≤ x) :
    profile F b v h H (j+1)-profile F b v h H j ≤ g/H := by
  have hs := ordered_secant_support (positive_part_convex hF v)
    (show b+h*(j : ℝ) < b+h*((j : ℝ)+1) by nlinarith) hj
    (positive_part_support hv hg)
  unfold profile
  rw [← sub_div]
  apply (div_le_iff₀ (mul_pos hh hH)).mpr
  have he : g/H*(h*H)=g*h := by field_simp
  rw [he]
  nlinarith

lemma profile_at_excursion {F : ℝ → ℝ} {b v h H x : ℝ}
    (hh : 0 < h) (hb : F b ≤ v) :
    profile F b v h H (max 0 (x-b)/h) =
      if x ≤ b then 0 else max 0 (F x-v)/(h*H) := by
  by_cases hx : x ≤ b
  · rw [ite_eq_left hx, max_eq_left (sub_nonpos.mpr hx)]
    simpa using (profile_zero (h := h) (H := H) hb)
  · rw [ite_eq_right hx, max_eq_right (by linarith : 0 ≤ x-b)]
    unfold profile
    have he : b+h*((x-b)/h)=x := by field_simp; ring
    rw [he]

lemma rightEndpoint_strict {F : ℝ → ℝ} {l u v x : ℝ} (h : l ≤ u)
    (hx : x ∈ Set.Icc l u) (hb : rightEndpoint F l u v < x) : v < F x := by
  by_contra hn
  exact (not_le_of_gt hb) (le_rightEndpoint h hx (le_of_not_gt hn))

lemma positive_part_nonexpansive (x y : ℝ) : |max 0 x-max 0 y| ≤ |x-y| := by
  have h := abs_max_sub_max_le_max (0 : ℝ) x 0 y
  simpa [max_eq_right (abs_nonneg (x-y))] using h

lemma project_step_distance {l u x η H Y : ℝ} (hx : x ∈ Set.Icc l u)
    (hη : 0 ≤ η) (hY : |Y| ≤ H) : |project l u (x-η*Y)-x| ≤ η*H := by
  have hd := project_distance hx (x-η*Y)
  have he : x-η*Y-x= -(η*Y) := by ring
  rw [he, abs_neg, abs_mul, abs_of_nonneg hη] at hd
  exact hd.trans (mul_le_mul_of_nonneg_left hY hη)

lemma excursion_step_distance {l u b x η H Y : ℝ} (hx : x ∈ Set.Icc l u)
    (hη : 0 < η) (hH : 0 < H) (hY : |Y| ≤ H) :
    |max 0 (project l u (x-η*Y)-b)/(η*H)-max 0 (x-b)/(η*H)| ≤ 1 := by
  have hd := project_step_distance hx hη.le hY
  have hm := positive_part_nonexpansive (project l u (x-η*Y)-b) (x-b)
  rw [sub_sub_sub_cancel_right] at hm
  rw [← sub_div, abs_div, abs_of_pos (mul_pos hη hH)]
  exact (div_le_one (mul_pos hη hH)).mpr (hm.trans hd)

lemma excursion_threshold {b x h a : ℝ} (hh : 0 < h) (ha : 0 < a)
    (hz : a ≤ max 0 (x-b)/h) : b+h*a ≤ x := by
  have ht := (le_div_iff₀ hh).mp hz
  have hx : 0 ≤ x-b := by
    by_contra hn
    rw [max_eq_left (le_of_lt (lt_of_not_ge hn))] at ht
    nlinarith
  rw [max_eq_right hx] at ht
  nlinarith

lemma excursion_step_drift {l u b x η H Y : ℝ} (_hx : x ∈ Set.Icc l u)
    (hb : b ∈ Set.Icc l u) (hη : 0 < η) (hH : 0 < H) (hY : |Y| ≤ H)
    (hz : 1 ≤ max 0 (x-b)/(η*H)) :
    max 0 (project l u (x-η*Y)-b)/(η*H)-max 0 (x-b)/(η*H) ≤ -Y/H := by
  have hh := mul_pos hη hH
  have hxb : η*H ≤ x-b := by
    have hp := (le_div_iff₀ hh).mp hz
    have hxpos : 0 ≤ x-b := by
      by_contra hn
      rw [max_eq_left (le_of_lt (lt_of_not_ge hn))] at hp
      linarith
    rw [max_eq_right hxpos] at hp
    simpa using hp
  have hYhi := (abs_le.mp hY).2
  have hlo : b ≤ x-η*Y := by nlinarith
  have hl : l ≤ min u (x-η*Y) := le_min (hb.1.trans hb.2) (hb.1.trans hlo)
  have hpb : b ≤ project l u (x-η*Y) := by
    unfold project
    exact le_max_of_le_right (le_min hb.2 hlo)
  have hpu : project l u (x-η*Y) ≤ x-η*Y := by
    unfold project
    rw [max_eq_right hl]
    exact min_le_right _ _
  rw [max_eq_right (sub_nonneg.mpr hpb), max_eq_right (by linarith : 0 ≤ x-b), ← sub_div]
  apply (div_le_iff₀ hh).mpr
  have he : -Y/H*(η*H)= -η*Y := by field_simp
  rw [he]
  linarith

end OracleTemplate.BoundedScalarConvex
