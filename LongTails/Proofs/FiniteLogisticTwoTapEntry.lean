import LongTails.Proofs.FiniteLogisticTwoTapCoordinates
import LongTails.Proofs.TwoTapGaussianBounds
import LongTails.Proofs.FiniteLogisticPerceptronCrossing

open scoped RealInnerProductSpace
open LongTails.Setups.FiniteLogisticTwoTap
open LongTails.Setups.TwoSampleQuadraticPerceptron (ones)
open LongTails.Proofs.FiniteLogisticTwoTapSpectrum
open LongTails.Proofs.FiniteLogisticTwoTapCoordinates
open LongTails.Proofs.TwoTapGaussianBounds
open LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding (norm_ones)

namespace LongTails.Proofs.FiniteLogisticTwoTapEntry

lemma pair_coordinate {d : ℕ} (a b : Fin 2 ⊕ Fin d) (hab : a ≠ b) (τ : ℝ) (hτ : τ^2=1)
    (w : Weights d) : |(w a + τ*w b) / Real.sqrt 2| ≤ ‖w‖ := by
  let v : Weights d := EuclideanSpace.single a 1 + τ • EuclideanSpace.single b 1
  have hform (z : Weights d) : ⟪v,z⟫ = z a + τ*z b := by
    simp [v, inner_add_left, real_inner_smul_left, EuclideanSpace.inner_single_left]
  have hnorm := hform v
  rw [real_inner_self_eq_norm_sq] at hnorm
  conv_rhs at hnorm => simp [v, hab, Ne.symm hab]
  have hn : ‖v‖ = Real.sqrt 2 := by
    nlinarith [norm_nonneg v, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  have h := abs_real_inner_le_norm v w
  rw [hform, hn] at h
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _), div_le_iff₀ (by positivity)]
  linarith

noncomputable def centeredPair {d : ℕ} (i : Fin d) : Weights d :=
  (2/(d:ℝ)) • liftReadout (ones d) - EuclideanSpace.single (.inr i) 1 -
    EuclideanSpace.single (.inr (finRotate d i)) 1

lemma center_inner {d : ℕ} (i : Fin d) (w : Weights d) :
    ⟪centeredPair i,w⟫ = 2 * readSum w / d - (w (.inr i) + w (.inr (finRotate d i))) := by
  simp [centeredPair, inner_sub_left, real_inner_smul_left, inner_background,
    EuclideanSpace.inner_single_left]
  ring

lemma u_bound {d : ℕ} (hd : 2 < d) (i : Fin d) (hi : finRotate d i ≠ i) (w : Weights d) :
    |(coords i w).u| ≤ ‖w‖ := by
  have hD : (2 : ℝ) < d := by exact_mod_cast hd
  have hd₀ : 0 < (d : ℝ) := by linarith
  have he : 0 < 1 - 2/(d : ℝ) := sub_pos.mpr ((div_lt_one hd₀).mpr hD)
  have hsum : readSum (centeredPair i) = 0 := by
    simp [readSum, centeredPair, liftReadout, ones, Finset.sum_sub_distrib]
    field_simp
    norm_num
  have hnorm := center_inner i (centeredPair i)
  rw [real_inner_self_eq_norm_sq, hsum] at hnorm
  conv_rhs at hnorm => simp [centeredPair, liftReadout, ones, -finRotate_apply, hi, Ne.symm hi]
  have hs : ‖centeredPair i‖ = Real.sqrt 2 * Real.sqrt (1-2/(d:ℝ)) := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt he.le]
    linarith
  have h := abs_real_inner_le_norm (centeredPair i) w
  rw [center_inner, hs] at h
  dsimp only [coords]
  rw [abs_div, abs_of_pos (by positivity : 0 < Real.sqrt 2 * Real.sqrt (1-2/(d:ℝ))),
    div_le_iff₀ (by positivity)]
  linarith

lemma coordinate_bounds {d : ℕ} (hd : 2 < d) (i : Fin d) (hi : finRotate d i ≠ i)
    (w : Weights d) : let z := coords i w
    |z.p| ≤ ‖w‖ ∧ |z.q| ≤ ‖w‖ ∧ |z.u| ≤ ‖w‖ ∧ |z.r| ≤ ‖w‖ ∧ |z.v| ≤ ‖w‖ := by
  have h01 : (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin d) ≠ .inl 1 := fun h => (by decide : (0 : Fin 2) ≠ 1) (Sum.inl.inj h)
  have hji : (Sum.inr (finRotate d i) : Fin 2 ⊕ Fin d) ≠ .inr i := fun h => hi (Sum.inr.inj h)
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  refine ⟨?_, ?_, u_bound hd i hi w, ?_, ?_⟩
  · simpa [coords] using pair_coordinate _ _ h01 1 (by norm_num) w
  · have h := abs_real_inner_le_norm (liftReadout (ones d)) w
    rw [inner_background, norm_lift, norm_ones] at h
    dsimp only [coords]
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _), div_le_iff₀ (Real.sqrt_pos.mpr hd₀)]
    linarith
  · simpa [coords, sub_eq_add_neg] using pair_coordinate _ _ h01 (-1) (by norm_num) w
  · simpa [coords, sub_eq_add_neg] using pair_coordinate _ _ hji (-1) (by norm_num) w

lemma coord_sub {d : ℕ} (i : Fin d) (x y : Weights d) :
    let a := coords i x
    let b := coords i y
    coords i (x-y) = ⟨a.p-b.p,a.q-b.q,a.u-b.u,a.r-b.r,a.v-b.v⟩ := by
  simp [coords, readSum, Finset.sum_sub_distrib]
  and_intros <;> ring

lemma coord_smul {d : ℕ} (i : Fin d) (s : ℝ) (x : Weights d) :
    let a := coords i x
    coords i (s • x) = ⟨s*a.p,s*a.q,s*a.u,s*a.r,s*a.v⟩ := by
  simp [coords, readSum, ← Finset.mul_sum]
  and_intros <;> ring

lemma growing_coords {d : ℕ} (hd : 2 < d) (i : Fin d) (hi : finRotate d i ≠ i)
    (x : Weights d) :
    let p := ⟪mode i 1,x⟫ / Real.sqrt 2
    let r := ⟪mode i (-1),x⟫ / Real.sqrt 2
    coords i (growingPart i x) =
      ⟨p, -(Real.sqrt 2/Real.sqrt d)*p, Real.sqrt (1-2/(d:ℝ))*p, r,r⟩ := by
  have hD : (2 : ℝ) < d := by exact_mod_cast hd
  have hd₀ : (0 : ℝ) < d := by linarith
  have he := sub_pos.mpr ((div_lt_one hd₀).mpr hD)
  have hs := Real.sq_sqrt he.le
  have hf := Real.sq_sqrt (show 0 ≤ (2:ℝ) by norm_num)
  dsimp only
  rw [growingPart_explicit i hi, mode_inner, mode_inner]
  simp [coords, readSum, Finset.sum_add_distrib, -finRotate_apply, hi, Ne.symm hi]
  generalize hz : Real.sqrt (1-2/(d:ℝ)) = B at hs ⊢
  have hb : B ≠ 0 := hz ▸ (Real.sqrt_pos.mpr he).ne'
  have hb' : (d:ℝ)*B^2 = d-2 := by rw [hs]; field_simp
  and_intros <;> field_simp [hb, hd₀.ne', (Real.sqrt_pos.mpr hd₀).ne'] <;> ring_nf
  grind

lemma aligned_entry {d : ℕ} (hd : 2 < d) (i : Fin d) (hi : finRotate d i ≠ i)
    (w x : Weights d) (M e : ℝ)
    (herr : ‖x-M • growingPart i w‖ ≤ e)
    (hP : 0 < M * (⟪mode i 1,w⟫ / Real.sqrt 2))
    (he : e ≤ (1/Real.sqrt d)*(M * (⟪mode i 1,w⟫ / Real.sqrt 2))/20)
    (hS : e < |M*(⟪mode i (-1),w⟫ / Real.sqrt 2)|) :
    let z := coords i x
    let a := min (19/20 : ℝ) (4*(1/Real.sqrt d))
    0 < z.p+z.q ∧ z.q ≤ 0 ∧ -a*z.p ≤ z.q ∧ z.p/2 ≤ z.u ∧ z.u ≤ 50*(z.p+z.q) ∧
      0 < z.r*z.v ∧ M*(⟪mode i 1,w⟫ / Real.sqrt 2)-e ≤ z.p := by
  let P := M*(⟪mode i 1,w⟫ / Real.sqrt 2)
  let S := M*(⟪mode i (-1),w⟫ / Real.sqrt 2)
  let k := 1/Real.sqrt d
  let B := Real.sqrt (1-2/(d:ℝ))
  have hD : (3:ℝ) ≤ d := by exact_mod_cast (by omega : 3 ≤ d)
  have hd₀ : (0:ℝ) < d := by linarith
  have hsd := Real.sq_sqrt hd₀.le
  have hk : 0 < k := by dsimp [k]; positivity
  have hk₂ : 3*k^2 ≤ 1 := by
    dsimp [k]
    rw [div_pow, one_pow, hsd, div_eq_inv_mul]
    field_simp
    linarith
  have hinside : 0 < 1-2/(d:ℝ) := sub_pos.mpr ((div_lt_one hd₀).mpr (by linarith))
  have hB : 0 < B := Real.sqrt_pos.mpr hinside
  have hB₂ : B^2 = 1-2*k^2 := by
    dsimp [B,k]
    rw [Real.sq_sqrt hinside.le, div_pow, one_pow, hsd]
    ring
  have H := coordinate_bounds hd i hi (x-M • growingPart i w)
  rw [coord_sub, coord_smul, growing_coords hd i hi] at H
  obtain ⟨hp,hq,hu,hr,hv⟩ := H
  have ep : |(coords i x).p-P| ≤ e := hp.trans herr
  have eq : |(coords i x).q+Real.sqrt 2*k*P| ≤ e := by
    convert hq.trans herr using 2
    dsimp [P,k]
    ring
  have eu : |(coords i x).u-B*P| ≤ e := by
    convert hu.trans herr using 2
    dsimp [P,B]
    ring
  obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := FiniteLogisticPerceptronCrossing.enters_cone hk hk₂ hB hB₂ hP he ep eq eu
  refine ⟨h₁,h₂,h₃,h₄,h₅,?_,by linarith [(abs_le.mp ep).1]⟩
  have er : |(coords i x).r-S| ≤ e := hr.trans herr
  have ev : |(coords i x).v-S| ≤ e := hv.trans herr
  change e < |S| at hS
  rcases le_total 0 S with h|h
  · rw [abs_of_nonneg h] at hS
    exact mul_pos (by linarith [(abs_le.mp er).1]) (by linarith [(abs_le.mp ev).1])
  · rw [abs_of_nonpos h] at hS
    exact mul_pos_of_neg_of_neg (by linarith [(abs_le.mp er).2]) (by linarith [(abs_le.mp ev).2])

end LongTails.Proofs.FiniteLogisticTwoTapEntry
