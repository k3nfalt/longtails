import LongTails.Proofs.ScalarStopLoss
import Mathlib.Analysis.Convex.Slope

namespace OracleTemplate.ScalarStopLoss

lemma convex_monotone_right_of_min {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (hmin : ∀ x, f 0 ≤ f x) : MonotoneOn f (Set.Ici 0) := by
  intro x hx y hy hxy
  by_cases hx0 : x = 0
  · simpa [hx0] using hmin y
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · rfl
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hs := (convexOn_iff_slope_mono_adjacent.mp hf).2
      (Set.mem_univ (0 : ℝ)) (Set.mem_univ y) hxpos hlt
    have hn : 0 ≤ (f x-f 0)/(x-0) := div_nonneg (sub_nonneg.mpr (hmin x)) (by linarith)
    have hnum := (le_div_iff₀ (sub_pos.mpr hlt)).mp (hn.trans hs)
    linarith

lemma ordered_secant_support {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    {a b x g : ℝ} (hab : a < b) (hbx : b ≤ x)
    (hsub : ∀ y, f x+g*(y-x) ≤ f y) : f b-f a ≤ g*(b-a) := by
  rcases lt_or_eq_of_le hbx with hlt | rfl
  · have hs := (convexOn_iff_slope_mono_adjacent.mp hf).2
      (Set.mem_univ a) (Set.mem_univ x) hab hlt
    have hg : (f x-f b)/(x-b) ≤ g := by
      apply (div_le_iff₀ (sub_pos.mpr hlt)).mpr
      have h := hsub b
      nlinarith
    exact (div_le_iff₀ (sub_pos.mpr hab)).mp (hs.trans hg)
  · have h := hsub a
    nlinarith

lemma positive_part_convex {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (v : ℝ) :
    ConvexOn ℝ Set.univ (fun x => max 0 (f x-v)) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hc := hf.2 hx hy ha hb hab
  simp only [smul_eq_mul] at hc ⊢
  have h1 := mul_le_mul_of_nonneg_left (le_max_right 0 (f x-v)) ha
  have h2 := mul_le_mul_of_nonneg_left (le_max_right 0 (f y-v)) hb
  have he : a*v+b*v = v := by rw [← add_mul, hab, one_mul]
  apply max_le
  · positivity
  · nlinarith

lemma positive_part_support {f : ℝ → ℝ} {v x g : ℝ} (hv : v ≤ f x)
    (hsub : ∀ y, f x+g*(y-x) ≤ f y) (y : ℝ) :
    max 0 (f x-v)+g*(y-x) ≤ max 0 (f y-v) := by
  rw [max_eq_right (sub_nonneg.mpr hv)]
  have hs := hsub y
  have hm := le_max_right 0 (f y-v)
  linarith

noncomputable def polygon (d : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0, x => d 0 * max 0 (x-2)
  | n+1, x => polygon d n x + (d (n+1)-d n)*max 0 (x-(n+3))

lemma polygon_sum (d : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    polygon d n x = d 0*max 0 (x-2) +
      ∑ j ∈ Finset.range n, (d (j+1)-d j)*max 0 (x-(j+3)) := by
  induction n with
  | zero => simp [polygon]
  | succ n ih => rw [polygon, ih, Finset.sum_range_succ]; ring

lemma polygon_envelope_bound (d H : ℕ → ℝ) (N : ℕ)
    (hd : ∀ n, 0 ≤ d n) (hu : ∀ n, d n ≤ 1) (hmono : Monotone d)
    (hH : ∀ k, 2 ≤ k → H k ≤ envelope d N k) :
    d 2*H 2 + (∑ j ∈ Finset.range N, (d (j+3)-d (j+2))*H (j+3)) ≤ 4 := by
  have hsum : (∑ j ∈ Finset.range N, (d (j+3)-d (j+2))*H (j+3)) ≤
      ∑ j ∈ Finset.range N, (d (j+3)-d (j+2))*envelope d N (j+3) := by
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left (hH (j+3) (by omega))
    exact sub_nonneg.mpr (hmono (by omega : j+2 ≤ j+3))
  have hbase := mul_le_mul_of_nonneg_left (hH 2 le_rfl) (hd 2)
  have hbound : d 2*envelope d N 2 +
      (∑ j ∈ Finset.range N, (d (j+3)-d (j+2))*envelope d N (j+3)) ≤ 4 := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using envelope_objective d hd hu N
  linarith

lemma polygon_above (d : ℕ → ℝ) (n : ℕ) (x : ℝ) (hx : (n : ℝ)+2 ≤ x) :
    polygon d n x = (∑ j ∈ Finset.range n, d j)+d n*(x-(n+2)) := by
  induction n with
  | zero => simp [polygon, max_eq_right (by linarith : 0 ≤ x-2)]
  | succ n ih =>
    have hx' : (n : ℝ)+2 ≤ x := by norm_num at hx ⊢; linarith
    rw [polygon, ih hx', Finset.sum_range_succ]
    rw [max_eq_right (by norm_num at hx ⊢; linarith : 0 ≤ x-((n : ℝ)+3))]
    push_cast
    ring

lemma convex_unit_chord {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    {a x : ℝ} (hlo : a ≤ x) (hhi : x ≤ a+1) :
    f x ≤ f a+(f (a+1)-f a)*(x-a) := by
  have h := hf.2 (show a ∈ Set.univ from Set.mem_univ _)
    (show a+1 ∈ Set.univ from Set.mem_univ _)
    (show 0 ≤ a+1-x by linarith) (show 0 ≤ x-a by linarith)
    (show (a+1-x)+(x-a)=1 by ring)
  simp only [smul_eq_mul] at h
  have he : (a+1-x)*a+(x-a)*(a+1)=x := by ring
  rw [he] at h
  nlinarith

lemma grid_slope_mono {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (a : ℝ) :
    f (a+1)-f a ≤ f (a+2)-f (a+1) := by
  have hm := hf.2 (show a ∈ Set.univ from Set.mem_univ _)
    (show a+2 ∈ Set.univ from Set.mem_univ _)
    (show (0 : ℝ) ≤ 1/2 by norm_num) (show (0 : ℝ) ≤ 1/2 by norm_num)
    (show (1/2 : ℝ)+1/2=1 by norm_num)
  simp only [smul_eq_mul] at hm
  have he : (1/2 : ℝ)*a+1/2*(a+2)=a+1 := by ring
  rw [he] at hm
  linarith

lemma shifted_grid_sum (f : ℝ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n, (f (j+3)-f (j+2)) = f (n+2)-f 2 := by
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, add_assoc,
    show (1 : ℝ)+2=3 by norm_num] using
    (Finset.sum_range_sub (fun j : ℕ => f (j+2)) n)

lemma polygon_majorizes {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (hm : MonotoneOn f (Set.Ici 0)) (n : ℕ) (x : ℝ) (hx0 : 0 ≤ x)
    (hx : x ≤ (n : ℝ)+3) :
    f x-f 2 ≤ polygon (fun j => f (j+3)-f (j+2)) n x := by
  induction n with
  | zero =>
    by_cases h : x ≤ 2
    · have hf2 := hm hx0 (by norm_num : (0 : ℝ) ≤ 2) h
      have hz : max 0 (x-2) = 0 := max_eq_left (by linarith)
      simp only [polygon, Nat.cast_zero, zero_add, hz, mul_zero]
      linarith
    · have hc := convex_unit_chord hf (a := 2) (x := x) (by linarith) (by norm_num at hx ⊢; exact hx)
      norm_num at hc
      simp only [polygon, Nat.cast_zero, zero_add]
      rw [max_eq_right (by linarith : 0 ≤ x-2)]
      linarith
  | succ n ih =>
    by_cases h : x ≤ (n : ℝ)+3
    · have hc := ih h
      have hs := grid_slope_mono hf ((n : ℝ)+2)
      simp only [polygon, Nat.cast_add, Nat.cast_one]
      have he : f (↑n+1+3)-f (↑n+1+2) - (f (↑n+3)-f (↑n+2)) ≥ 0 := by
        ring_nf at hs ⊢
        linarith
      exact hc.trans (by nlinarith [mul_nonneg he (le_max_left 0 (x-(↑n+3)))])
    · have hlo : (n : ℝ)+3 ≤ x := by linarith
      have hhi : x ≤ ((n : ℝ)+3)+1 := by norm_num at hx ⊢; linarith
      have hc := convex_unit_chord hf hlo hhi
      rw [polygon_above _ (n+1) x (by push_cast; linarith), shifted_grid_sum]
      push_cast
      ring_nf at hc ⊢
      linarith

end OracleTemplate.ScalarStopLoss
