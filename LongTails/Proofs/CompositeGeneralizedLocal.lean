import LongTails.Setups.CompositeGeneralizedSmooth
import LongTails.Proofs.GdConvex
import LongTails.Proofs.NearestSetLocal

open Set Filter
open scoped RealInnerProductSpace Topology

namespace OracleTemplate.CompositeGeneralized

open LongTails.Setups.CompositeGeneralizedSmooth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def SymmetricSmooth (g : E → E) (L0 L1 : ℝ) : Prop :=
  ∀ x y M, (∀ θ ∈ Icc (0 : ℝ) 1, ‖g (x + θ • (y - x))‖ ≤ M) →
    ‖g x - g y‖ ≤ (L0 + L1 * M) * ‖x - y‖

omit [CompleteSpace E] in
lemma segment_gradient_bound {g : E → E} {L0 L1 : ℝ} (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1)
    (hg : Continuous g) (hs : SymmetricSmooth g L0 L1) (x w : E)
    (hr : L1 * ‖w - x‖ ≤ 1 / 2) :
    ‖g w‖ ≤ 2 * (‖g x‖ + L0 * ‖w - x‖) := by
  set r := ‖w - x‖
  have hcont : ContinuousOn (fun t : ℝ => ‖g (x + t • (w - x))‖) (Icc 0 1) :=
    (by fun_prop : Continuous fun t : ℝ => ‖g (x + t • (w - x))‖).continuousOn
  obtain ⟨t0, ht0, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 zero_le_one) hcont
  set S := ‖g (x + t0 • (w - x))‖
  have hS : ∀ θ ∈ Icc (0 : ℝ) 1, ‖g (x + θ • (x + t0 • (w - x) - x))‖ ≤ S := by
    intro θ hθ
    have hmem : θ * t0 ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg hθ.1 ht0.1, by nlinarith [hθ.1, hθ.2, ht0.1, ht0.2]⟩
    have h := hmax hmem
    simp only [mem_ofPred_eq] at h
    have he : x + θ • (x + t0 • (w - x) - x) = x + (θ * t0) • (w - x) := by
      rw [add_sub_cancel_left, smul_smul]
    rw [he]
    exact h
  have h := hs x (x + t0 • (w - x)) S hS
  have hd : ‖x - (x + t0 • (w - x))‖ ≤ r := by
    rw [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht0.2
  have hS0 : 0 ≤ S := norm_nonneg _
  have hdiff : S ≤ ‖g x‖ + (L0 + L1 * S) * r := by
    have h1 : S ≤ ‖g x‖ + ‖g x - g (x + t0 • (w - x))‖ := by
      have := norm_sub_norm_le (g (x + t0 • (w - x))) (g x)
      rw [norm_sub_rev] at this
      linarith
    have h2 : (L0 + L1 * S) * ‖x - (x + t0 • (w - x))‖ ≤ (L0 + L1 * S) * r :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    linarith
  have hw : ‖g w‖ ≤ S := by
    have h1 := hmax (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)
    simp only [mem_ofPred_eq, one_smul, add_sub_cancel] at h1
    exact h1
  have hr0 : 0 ≤ r := norm_nonneg _
  nlinarith

omit [CompleteSpace E] in
lemma ball_lipschitz {g : E → E} {L0 L1 : ℝ} (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1)
    (hg : Continuous g) (hs : SymmetricSmooth g L0 L1) {x u v : E} {r : ℝ}
    (hr : L1 * r ≤ 1 / 2) (hu : ‖u - x‖ ≤ r) (hv : ‖v - x‖ ≤ r) :
    ‖g u - g v‖ ≤ 2 * (L0 + L1 * ‖g x‖) * ‖u - v‖ := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hu
  have hpt : ∀ θ ∈ Icc (0 : ℝ) 1, ‖g (u + θ • (v - u))‖ ≤ 2 * (‖g x‖ + L0 * r) := by
    intro θ hθ
    have hdist : ‖u + θ • (v - u) - x‖ ≤ r := by
      have he : u + θ • (v - u) - x = (1 - θ) • (u - x) + θ • (v - x) := by module
      rw [he]
      calc ‖(1 - θ) • (u - x) + θ • (v - x)‖ ≤ ‖(1 - θ) • (u - x)‖ + ‖θ • (v - x)‖ :=
            norm_add_le _ _
        _ = (1 - θ) * ‖u - x‖ + θ * ‖v - x‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (sub_nonneg.mpr hθ.2), abs_of_nonneg hθ.1]
        _ ≤ (1 - θ) * r + θ * r := by
            gcongr
            · exact sub_nonneg.mpr hθ.2
            · exact hθ.1
        _ = r := by ring
    have h := segment_gradient_bound hL0 hL1 hg hs x (u + θ • (v - u))
      (le_trans (mul_le_mul_of_nonneg_left hdist hL1) hr)
    have h2 : L0 * ‖u + θ • (v - u) - x‖ ≤ L0 * r := mul_le_mul_of_nonneg_left hdist hL0
    linarith
  have h := hs u v _ hpt
  have hc : L0 + L1 * (2 * (‖g x‖ + L0 * r)) ≤ 2 * (L0 + L1 * ‖g x‖) := by
    nlinarith [mul_le_mul_of_nonneg_left hr hL0]
  exact h.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

lemma ball_upper {f : E → ℝ} {g : E → E} {L0 L1 : ℝ} (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g) (hs : SymmetricSmooth g L0 L1)
    {x u v : E} {r : ℝ} (hr : L1 * r ≤ 1 / 2) (hu : ‖u - x‖ ≤ r) (hv : ‖v - x‖ ≤ r) :
    f v ≤ f u + ⟪g u, v - u⟫ + (L0 + L1 * ‖g x‖) * ‖v - u‖ ^ 2 := by
  have h := NearestSet.segment_upper_bound (L := 2 * (L0 + L1 * ‖g x‖)) hf u v (by
    intro t ht
    have hpt : ‖u + t • (v - u) - x‖ ≤ r := by
      have he : u + t • (v - u) - x = (1 - t) • (u - x) + t • (v - x) := by module
      rw [he]
      calc ‖(1 - t) • (u - x) + t • (v - x)‖ ≤ ‖(1 - t) • (u - x)‖ + ‖t • (v - x)‖ :=
            norm_add_le _ _
        _ = (1 - t) * ‖u - x‖ + t * ‖v - x‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (sub_nonneg.mpr ht.2.le), abs_of_nonneg ht.1]
        _ ≤ (1 - t) * r + t * r := by
            gcongr
            · exact sub_nonneg.mpr ht.2.le
            · exact ht.1
        _ = r := by ring
    have h := ball_lipschitz hL0 hL1 hg hs hr hpt hu
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at h
    linarith)
  linarith

lemma shifted_cocoercive {f : E → ℝ} {g : E → E} {L0 L1 : ℝ} (hL0 : 0 < L0) (hL1 : 0 ≤ L1)
    (hc : ConvexOn ℝ univ f) (hf : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hs : SymmetricSmooth g L0 L1) (xs x : E) :
    ‖g x - g xs‖ ^ 2 ≤ 8 * (L0 + L1 * ‖g x‖ + L1 * ‖g x - g xs‖) *
      (f x - f xs - ⟪g xs, x - xs⟫) := by
  set γ := ‖g x - g xs‖
  set M := L0 + L1 * ‖g x‖
  have hM : 0 < M := by positivity
  set t := 1 / (4 * (M + L1 * γ))
  have hden : 0 < M + L1 * γ := by positivity
  have ht : 0 < t := by positivity
  set w := x - t • (g x - g xs)
  have hwx : ‖w - x‖ = t * γ := by
    simp only [w, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    rfl
  have htg : L1 * (t * γ) ≤ 1 / 2 := by
    have h1 : L1 * γ * t ≤ (M + L1 * γ) * t := by nlinarith
    have h2 : (M + L1 * γ) * t = 1 / 4 := by
      simp only [t]; field_simp
    nlinarith
  have hup := ball_upper hL0.le hL1 hf hg hs (x := x) (u := x) (v := w) htg
    (by simp; positivity) (le_of_eq hwx)
  have hlow := Gradient.convex_support hc hf xs w
  have hwx' : w - x = -(t • (g x - g xs)) := by simp [w]
  have e1 : ⟪g x, w - x⟫ = -(t * ⟪g x, g x - g xs⟫) := by
    rw [hwx', inner_neg_right, inner_smul_right]
  rw [e1, hwx] at hup
  have hin : ⟪g xs, w - xs⟫ = ⟪g xs, x - xs⟫ - t * ⟪g xs, g x - g xs⟫ := by
    simp only [w]
    rw [show x - t • (g x - g xs) - xs = (x - xs) - t • (g x - g xs) by abel,
      inner_sub_right, inner_smul_right]
  have hsq : ⟪g x, g x - g xs⟫ - ⟪g xs, g x - g xs⟫ = γ ^ 2 := by
    rw [← inner_sub_left, real_inner_self_eq_norm_sq]
  have hMt : M * t ≤ 1 / 4 := by
    have h2 : (M + L1 * γ) * t = 1 / 4 := by simp only [t]; field_simp
    nlinarith [mul_nonneg hL1 (norm_nonneg (g x - g xs))]
  have key : t * γ ^ 2 * (3 / 4) ≤ f x - f xs - ⟪g xs, x - xs⟫ := by
    have h3 : M * (t * γ) ^ 2 ≤ t * γ ^ 2 / 4 := by
      have := mul_le_mul_of_nonneg_right hMt (show 0 ≤ t * γ ^ 2 by positivity)
      nlinarith
    rw [hin] at hlow
    nlinarith
  have h2 : t * (4 * (M + L1 * γ)) = 1 := by simp only [t]; field_simp
  have hfinal : γ ^ 2 = t * γ ^ 2 * (4 * (M + L1 * γ)) := by
    calc γ ^ 2 = γ ^ 2 * (t * (4 * (M + L1 * γ))) := by rw [h2, mul_one]
      _ = t * γ ^ 2 * (4 * (M + L1 * γ)) := by ring
  rw [hfinal]
  have h4 : 0 ≤ 4 * (M + L1 * γ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left key h4]

lemma optimality {f ψ : E → ℝ} {g : E → E} {Q : Set E} (hc : ConvexOn ℝ univ f)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hQ : Convex ℝ Q) (hψ : ConvexOn ℝ Q ψ) {xs : E} (hxs : xs ∈ Q)
    (hmin : IsMinOn (fun x => f x + ψ x) Q xs) {u : E} (hu : u ∈ Q) :
    ψ xs - ψ u ≤ ⟪g xs, u - xs⟫ := by
  set d := u - xs
  have hbound : ∀ t ∈ Ioo (0 : ℝ) 1, ψ xs - ψ u ≤ ⟪g (xs + t • d), d⟫ := by
    intro t ht
    have hpt : (1 - t) • xs + t • u = xs + t • d := by
      simp only [d, smul_sub]
      module
    have hmem : xs + t • d ∈ Q := by
      rw [← hpt]
      exact hQ hxs hu (sub_nonneg.mpr ht.2.le) ht.1.le (by ring)
    have hm := hmin hmem
    simp only [mem_ofPred_eq] at hm
    have hψt : ψ (xs + t • d) ≤ (1 - t) * ψ xs + t * ψ u := by
      rw [← hpt]
      simpa [smul_eq_mul] using hψ.2 hxs hu (sub_nonneg.mpr ht.2.le) ht.1.le (by ring)
    have hsupp := Gradient.convex_support hc hf (xs + t • d) xs
    have he : xs - (xs + t • d) = -(t • d) := by abel
    rw [he, inner_neg_right, inner_smul_right] at hsupp
    have hmul : t * (ψ xs - ψ u) ≤ t * ⟪g (xs + t • d), d⟫ := by nlinarith
    exact le_of_mul_le_mul_left hmul ht.1
  have hcont : Continuous (fun t : ℝ => ⟪g (xs + t • d), d⟫) := by fun_prop
  have h0 := hcont.tendsto 0
  simp only [zero_smul, add_zero] at h0
  refine ge_of_tendsto (h0.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))) ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht using hbound t ht

omit [CompleteSpace E] in
lemma norm_mix_sq (t : ℝ) (A B : E) :
    ‖(1 - t) • A + t • B‖ ^ 2 =
      (1 - t) * ‖A‖ ^ 2 + t * ‖B‖ ^ 2 - t * (1 - t) * ‖A - B‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul, inner_smul_left,
    inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
  simp only [conj_trivial]
  ring

omit [CompleteSpace E] in
lemma prox_three_point {ψ : E → ℝ} {Q : Set E} (hQ : Convex ℝ Q) (hψ : ConvexOn ℝ Q ψ)
    {a : ℝ} (ha : 0 < a) {z v p : E} (hp : p ∈ Q)
    (hmin : IsMinOn (fun u => ‖u - z‖ ^ 2 / (2 * a) + ⟪v, u - z⟫ + ψ u) Q p)
    {u : E} (hu : u ∈ Q) :
    a * (⟪v, p - u⟫ + ψ p - ψ u) ≤
      ‖z - u‖ ^ 2 / 2 - ‖p - u‖ ^ 2 / 2 - ‖p - z‖ ^ 2 / 2 := by
  set P := fun u => ‖u - z‖ ^ 2 / (2 * a) + ⟪v, u - z⟫ + ψ u
  set c := ‖u - p‖ ^ 2 / (2 * a)
  have hgap : ∀ t ∈ Ioo (0 : ℝ) 1, (1 - t) * c ≤ P u - P p := by
    intro t ht
    have hmem : (1 - t) • p + t • u ∈ Q :=
      hQ hp hu (sub_nonneg.mpr ht.2.le) ht.1.le (by ring)
    have hm := hmin hmem
    simp only [mem_ofPred_eq] at hm
    have hψt := hψ.2 hp hu (sub_nonneg.mpr ht.2.le) ht.1.le (by ring : 1 - t + t = 1)
    simp only [smul_eq_mul] at hψt
    have hn : ‖(1 - t) • p + t • u - z‖ ^ 2 =
        (1 - t) * ‖p - z‖ ^ 2 + t * ‖u - z‖ ^ 2 - t * (1 - t) * ‖u - p‖ ^ 2 := by
      have he : (1 - t) • p + t • u - z = (1 - t) • (p - z) + t • (u - z) := by module
      rw [he, norm_mix_sq, show p - z - (u - z) = -(u - p) by abel, norm_neg]
    have hi : ⟪v, (1 - t) • p + t • u - z⟫ = (1 - t) * ⟪v, p - z⟫ + t * ⟪v, u - z⟫ := by
      have he : (1 - t) • p + t • u - z = (1 - t) • (p - z) + t • (u - z) := by module
      rw [he, inner_add_right, inner_smul_right, inner_smul_right]
    simp only [P, c] at hm ⊢
    rw [hn, hi] at hm
    have h2a : 0 < 2 * a := by positivity
    have key : t * ((1 - t) * (‖u - p‖ ^ 2 / (2 * a))) ≤
        t * (‖u - z‖ ^ 2 / (2 * a) + ⟪v, u - z⟫ + ψ u -
          (‖p - z‖ ^ 2 / (2 * a) + ⟪v, p - z⟫ + ψ p)) := by
      have e : ((1 - t) * ‖p - z‖ ^ 2 + t * ‖u - z‖ ^ 2 - t * (1 - t) * ‖u - p‖ ^ 2) / (2 * a) =
          (1 - t) * (‖p - z‖ ^ 2 / (2 * a)) + t * (‖u - z‖ ^ 2 / (2 * a)) -
            t * (1 - t) * (‖u - p‖ ^ 2 / (2 * a)) := by ring
      rw [e] at hm
      nlinarith
    exact le_of_mul_le_mul_left key ht.1
  have hlim : c ≤ P u - P p := by
    have hcont : Continuous (fun t : ℝ => (1 - t) * c) := by fun_prop
    have h0 := hcont.tendsto 0
    simp only [sub_zero, one_mul] at h0
    refine le_of_tendsto (h0.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))) ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht using hgap t ht
  simp only [P, c] at hlim
  have hi : ⟪v, u - z⟫ - ⟪v, p - z⟫ = -⟪v, p - u⟫ := by
    rw [← inner_sub_right, ← inner_neg_right]
    congr 1
    abel
  have hm := mul_le_mul_of_nonneg_left hlim ha.le
  have e1 : a * (‖u - p‖ ^ 2 / (2 * a)) = ‖u - p‖ ^ 2 / 2 := by field_simp
  have e2 : a * (‖u - z‖ ^ 2 / (2 * a) + ⟪v, u - z⟫ + ψ u -
      (‖p - z‖ ^ 2 / (2 * a) + ⟪v, p - z⟫ + ψ p)) =
      ‖u - z‖ ^ 2 / 2 - ‖p - z‖ ^ 2 / 2 + a * (⟪v, u - z⟫ - ⟪v, p - z⟫ + ψ u - ψ p) := by
    field_simp
    ring
  rw [e1, e2, hi, norm_sub_rev u p, norm_sub_rev u z] at hm
  linarith

omit [CompleteSpace E] in
lemma prox_distance {ψ : E → ℝ} {Q : Set E} (hQ : Convex ℝ Q) (hψ : ConvexOn ℝ Q ψ)
    {a : ℝ} (ha : 0 < a) {z v p xs gs : E} (hp : p ∈ Q) (hxs : xs ∈ Q)
    (hmin : IsMinOn (fun u => ‖u - z‖ ^ 2 / (2 * a) + ⟪v, u - z⟫ + ψ u) Q p)
    (hopt : ψ xs - ψ p ≤ ⟪gs, p - xs⟫) :
    ‖p - xs‖ ≤ ‖z - xs‖ + 2 * a * ‖v - gs‖ := by
  have h := prox_three_point hQ hψ ha hp hmin hxs
  have hcs : -⟪v - gs, p - xs⟫ ≤ ‖v - gs‖ * ‖p - xs‖ := by
    have := real_inner_le_norm (-(v - gs)) (p - xs)
    rwa [inner_neg_left, norm_neg] at this
  have hi : ⟪v, p - xs⟫ = ⟪v - gs, p - xs⟫ + ⟪gs, p - xs⟫ := by
    rw [inner_sub_left]; ring
  rw [hi] at h
  set T := ‖p - xs‖
  set S := ‖z - xs‖
  set B := a * ‖v - gs‖
  have hT : 0 ≤ T := norm_nonneg _
  have hS : 0 ≤ S := norm_nonneg _
  have hB : 0 ≤ B := by positivity
  have hq : T ^ 2 ≤ S ^ 2 + 2 * B * T := by
    have h1 : a * (-⟪v - gs, p - xs⟫) ≤ a * (‖v - gs‖ * T) := mul_le_mul_of_nonneg_left hcs ha.le
    have h2 : a * (ψ xs - ψ p) ≤ a * ⟪gs, p - xs⟫ := mul_le_mul_of_nonneg_left hopt ha.le
    nlinarith [sq_nonneg ‖p - z‖]
  nlinarith [sq_nonneg (T - S - 2 * B)]

end OracleTemplate.CompositeGeneralized
