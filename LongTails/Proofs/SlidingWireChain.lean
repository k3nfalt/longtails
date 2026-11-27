import LongTails.Proofs.FrontierChainGeometry
import LongTails.Proofs.SmoothConvexFiniteGeometry
import LongTails.Proofs.SlidingLowerChain

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.SlidingWireChain

open SmoothConvexFiniteGeometry FrontierChainProfiles FrontierChain FrontierChainGeometry
open SlidingLowerChain (Point)

noncomputable def sp (δ t : ℝ) : ℝ := ramp (t - δ) + ramp (-t - δ)

noncomputable def spS (δ t : ℝ) : ℝ := rampSlope (t - δ) - rampSlope (-t - δ)

lemma sp_hasDerivAt (δ t : ℝ) : HasDerivAt (sp δ) (spS δ t) t := by
  have h := (QuasarHardProfiles.ramp_affine_hasDerivAt 1 (-δ) t).add
    (QuasarHardProfiles.ramp_affine_hasDerivAt (-1) (-δ) t)
  convert h using 1
  · funext x
    simp only [sp]
    congr 1 <;> congr 1 <;> ring
  · simp only [spS]
    rw [show 1 * t + -δ = t - δ by ring, show -1 * t + -δ = -t - δ by ring]
    ring

lemma sp_flat {δ t : ℝ} (h : |t| ≤ δ) : sp δ t = 0 ∧ spS δ t = 0 := by
  have h1 : t - δ ≤ 0 := by linarith [(abs_le.mp h).2]
  have h2 : -t - δ ≤ 0 := by linarith [(abs_le.mp h).1]
  refine ⟨?_, ?_⟩
  · unfold sp
    rw [QuasarHardProfiles.ramp_of_nonpos h1, QuasarHardProfiles.ramp_of_nonpos h2]
    ring
  · unfold spS
    rw [QuasarHardProfiles.rampSlope_of_nonpos h1, QuasarHardProfiles.rampSlope_of_nonpos h2]
    ring

lemma spS_abs (δ t : ℝ) : |spS δ t| ≤ 1 := by
  unfold spS
  have := rampSlope_nonneg (t - δ)
  have := rampSlope_le_one (t - δ)
  have := rampSlope_nonneg (-t - δ)
  have := rampSlope_le_one (-t - δ)
  rw [abs_le]; constructor <;> linarith

lemma sp_model (δ x y : ℝ) :
    0 ≤ sp δ y - sp δ x - spS δ x * (y - x) ∧ sp δ y - sp δ x - spS δ x * (y - x) ≤ (y - x) ^ 2 := by
  have h1 := ramp_model (x - δ) (y - δ)
  have h2 := ramp_model (-x - δ) (-y - δ)
  have e1 : (y - δ) - (x - δ) = y - x := by ring
  have e2 : (-y - δ) - (-x - δ) = -(y - x) := by ring
  rw [e1] at h1
  rw [e2] at h2
  simp only [sp, spS]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

lemma sp_nonneg (δ t : ℝ) : 0 ≤ sp δ t := by
  unfold sp
  linarith [QuasarHardProfiles.ramp_nonneg (t - δ), QuasarHardProfiles.ramp_nonneg (-t - δ)]

lemma spS_lipschitz (δ s t : ℝ) : |spS δ s - spS δ t| ≤ 2 * |s - t| := by
  have h1 := rampSlope_lipschitz (s - δ) (t - δ)
  have h2 := rampSlope_lipschitz (-s - δ) (-t - δ)
  have e1 : (s - δ) - (t - δ) = s - t := by ring
  have e2 : (-s - δ) - (-t - δ) = -(s - t) := by ring
  rw [e1] at h1
  rw [e2, abs_neg] at h2
  unfold spS
  calc _ = |(rampSlope (s - δ) - rampSlope (t - δ)) -
        (rampSlope (-s - δ) - rampSlope (-t - δ))| := by ring_nf
    _ ≤ _ := abs_sub _ _
    _ ≤ _ := by linarith

lemma spS_upper {δ t : ℝ} (hδ : 0 ≤ δ) (h : spS δ t < 1) : t ≤ δ + spS δ t := by
  unfold spS at h ⊢
  rcases le_or_gt t δ with ht | ht
  · rw [QuasarHardProfiles.rampSlope_of_nonpos (by linarith : t - δ ≤ 0), zero_sub]
    rcases le_or_gt (-t - δ) 0 with h3 | h3
    · rw [QuasarHardProfiles.rampSlope_of_nonpos h3]; linarith
    · have : rampSlope (-t - δ) ≤ -t - δ := by
        unfold rampSlope; exact min_le_of_right_le (max_le h3.le le_rfl)
      linarith
  · rw [QuasarHardProfiles.rampSlope_of_nonpos (by linarith : -t - δ ≤ 0), sub_zero] at h ⊢
    rcases le_or_gt (t - δ) 1 with h4 | h4
    · rw [QuasarHardProfiles.rampSlope_of_mid (by linarith) h4]; linarith
    · rw [QuasarHardProfiles.rampSlope_of_ge h4.le] at h; linarith

lemma spS_lower {δ t : ℝ} (hδ : 0 ≤ δ) (h : -1 < spS δ t) : spS δ t - δ ≤ t := by
  have hs : spS δ (-t) = -spS δ t := by unfold spS; ring_nf
  have h' : spS δ (-t) < 1 := by rw [hs]; linarith
  have := spS_upper hδ h'
  rw [hs] at this
  linarith

def phase (r k : ℕ) : ℕ := k % (r ^ 2 + 2)

noncomputable def cA (r k : ℕ) : ℝ :=
  if phase r k = 0 then -7 else if phase r k = r ^ 2 then (r : ℝ) else (r : ℝ) ^ 2

noncomputable def cB (r k : ℕ) : ℝ :=
  if phase r k = 0 then (r : ℝ) else if phase r k = r ^ 2 then -7 / 2 else -((r : ℝ) ^ 2)

noncomputable def stretch (r k : ℕ) (s t : ℝ) : ℝ := cA r k * s + cB r k * t

noncomputable def link (r : ℕ) (δ : ℝ) (k : ℕ) (s t : ℝ) : ℝ :=
  if phase r k = r ^ 2 + 1 then edge s t else sp δ (stretch r k s t)

noncomputable def linkL (r : ℕ) (δ : ℝ) (k : ℕ) (s t : ℝ) : ℝ :=
  if phase r k = r ^ 2 + 1 then edgeLeft s t else cA r k * spS δ (stretch r k s t)

noncomputable def linkR (r : ℕ) (δ : ℝ) (k : ℕ) (s t : ℝ) : ℝ :=
  if phase r k = r ^ 2 + 1 then edgeRight s t else cB r k * spS δ (stretch r k s t)

variable {d : ℕ}

noncomputable def lfield (r : ℕ) (δ : ℝ) (k : ℕ) (i j : Fin d) (u : Point d) : Point d :=
  linkL r δ k (u i) (u j) • EuclideanSpace.single i (1 : ℝ) +
    linkR r δ k (u i) (u j) • EuclideanSpace.single j (1 : ℝ)

lemma link_gradient (r : ℕ) (δ : ℝ) (k : ℕ) (i j : Fin d) (u : Point d) :
    HasGradientAt (fun v : Point d => link r δ k (v i) (v j)) (lfield r δ k i j u) u := by
  by_cases hg : phase r k = r ^ 2 + 1
  · have h := edge_gradient i j u
    simp only [link, linkL, linkR, lfield, hg, ite_true]
    simpa [edgeField] using h
  · set v : Point d := cA r k • EuclideanSpace.single i (1 : ℝ) +
      cB r k • EuclideanSpace.single j (1 : ℝ) with hv
    have hLy : ∀ y : Point d, innerSL ℝ v y = stretch r k (y i) (y j) := by
      intro y
      rw [innerSL_apply_apply, hv, inner_add_left, inner_smul_left, inner_smul_left,
        EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left]
      simp only [conj_trivial, map_one, one_mul, stretch]
    have h := SlidingLowerChain.comp_linear_gradient (innerSL ℝ v) v u (fun y => innerSL_apply_apply (𝕜 := ℝ) v y)
      (sp_hasDerivAt δ (innerSL ℝ v u))
    simp only [link, linkL, linkR, lfield, hg, ite_false]
    have hf : (fun y : Point d => sp δ (stretch r k (y i) (y j))) =
        fun y => sp δ (innerSL ℝ v y) := funext fun y => by rw [hLy]
    rw [hf]
    rw [hLy u] at h
    convert h using 1
    rw [hv, smul_add, smul_smul, smul_smul]
    congr 1 <;> congr 1 <;> ring

noncomputable def obj (r : ℕ) (δ : ℝ) {k : ℕ} (π : Fin (k + 1) ↪ Fin d) (u : Point d) : ℝ :=
  -potential (u (π 0)) + ∑ i : Fin k, link r δ i.val (u (π i.castSucc)) (u (π i.succ))

noncomputable def field (r : ℕ) (δ : ℝ) {k : ℕ} (π : Fin (k + 1) ↪ Fin d) (u : Point d) :
    Point d :=
  -(potentialSlope (u (π 0)) • EuclideanSpace.single (π 0) (1 : ℝ)) +
    ∑ i : Fin k, lfield r δ i.val (π i.castSucc) (π i.succ) u

lemma obj_gradient (r : ℕ) (δ : ℝ) {k : ℕ} (π : Fin (k + 1) ↪ Fin d) (u : Point d) :
    HasGradientAt (obj r δ π) (field r δ π u) u := by
  have hs := HasFDerivAt.sum (u := Finset.univ)
    (fun (i : Fin k) _ => (link_gradient r δ i.val (π i.castSucc) (π i.succ) u).hasFDerivAt)
  have hp := (coordinate_gradient (π 0) u (potential_deriv (u (π 0)))).hasFDerivAt.neg
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hp.add hs using 1
  · ext y
    simp [obj]
  · simp [field]

lemma field_inner (r : ℕ) (δ : ℝ) {k : ℕ} (π : Fin (k + 1) ↪ Fin d) (u v : Point d) :
    ⟪field r δ π u, v⟫ = -potentialSlope (u (π 0)) * v (π 0) +
      ∑ i : Fin k, (linkL r δ i.val (u (π i.castSucc)) (u (π i.succ)) * v (π i.castSucc) +
        linkR r δ i.val (u (π i.castSucc)) (u (π i.succ)) * v (π i.succ)) := by
  unfold field lfield
  rw [inner_add_left, sum_inner]
  simp [inner_add_left, inner_smul_left, EuclideanSpace.inner_single_left]

lemma field_decomposition (r : ℕ) (δ : ℝ) {k : ℕ} (π : Fin (k + 1) ↪ Fin d) (u : Point d) :
    field r δ π u = -(potentialSlope (u (π 0)) • EuclideanSpace.single (π 0) (1 : ℝ)) +
      scatter (Fin.castSuccEmb.trans π)
        (fun i => linkL r δ i.val (u (π i.castSucc)) (u (π i.succ))) +
      scatter ((Fin.succEmb k).trans π)
        (fun i => linkR r δ i.val (u (π i.castSucc)) (u (π i.succ))) := by
  simp [field, scatter, lfield, Finset.sum_add_distrib, add_assoc]

lemma coef_bounds (r k : ℕ) : |cA r k| ≤ (r : ℝ) ^ 2 + 7 ∧ |cB r k| ≤ (r : ℝ) ^ 2 + 7 := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hr2 : (r : ℝ) ≤ (r : ℝ) ^ 2 + 7 := by nlinarith
  have hr3 : (0 : ℝ) ≤ (r : ℝ) ^ 2 := by positivity
  unfold cA cB
  constructor
  · split_ifs
    · rw [abs_of_neg (by norm_num)]; linarith
    · rw [abs_of_nonneg hr]; linarith
    · rw [abs_of_nonneg hr3]; linarith
  · split_ifs
    · rw [abs_of_nonneg hr]; linarith
    · rw [abs_of_neg (by norm_num)]; linarith
    · rw [abs_neg, abs_of_nonneg hr3]; linarith

lemma linkL_lipschitz (r : ℕ) (δ : ℝ) (k : ℕ) (s t s' t' : ℝ) :
    |linkL r δ k s t - linkL r δ k s' t'| ≤ (2 * ((r : ℝ) ^ 2 + 7) ^ 2 + 256) * (|s - s'| + |t - t'|) := by
  have hc := coef_bounds r k
  have hP : 0 ≤ 2 * ((r : ℝ) ^ 2 + 7) ^ 2 := by positivity
  unfold linkL
  split_ifs
  · have := edgeLeft_lipschitz s t s' t'
    have h0 : 0 ≤ |s - s'| + |t - t'| := by positivity
    nlinarith
  · rw [← mul_sub, abs_mul]
    have h1 := spS_lipschitz δ (stretch r k s t) (stretch r k s' t')
    have h2 : |stretch r k s t - stretch r k s' t'| ≤ ((r : ℝ) ^ 2 + 7) * (|s - s'| + |t - t'|) := by
      unfold stretch
      have e : cA r k * s + cB r k * t - (cA r k * s' + cB r k * t') =
          cA r k * (s - s') + cB r k * (t - t') := by ring
      rw [e]
      calc _ ≤ |cA r k * (s - s')| + |cB r k * (t - t')| := abs_add_le _ _
        _ = |cA r k| * |s - s'| + |cB r k| * |t - t'| := by rw [abs_mul, abs_mul]
        _ ≤ ((r : ℝ) ^ 2 + 7) * |s - s'| + ((r : ℝ) ^ 2 + 7) * |t - t'| := by
            gcongr
            · exact hc.1
            · exact hc.2
        _ = _ := by ring
    have h0 : 0 ≤ |s - s'| + |t - t'| := by positivity
    have hA := abs_nonneg (cA r k)
    calc |cA r k| * |spS δ (stretch r k s t) - spS δ (stretch r k s' t')|
        ≤ ((r : ℝ) ^ 2 + 7) * (2 * (((r : ℝ) ^ 2 + 7) * (|s - s'| + |t - t'|))) := by
          apply mul_le_mul hc.1 (h1.trans (by linarith)) (abs_nonneg _) (by positivity)
      _ ≤ _ := by nlinarith

lemma linkR_lipschitz (r : ℕ) (δ : ℝ) (k : ℕ) (s t s' t' : ℝ) :
    |linkR r δ k s t - linkR r δ k s' t'| ≤ (2 * ((r : ℝ) ^ 2 + 7) ^ 2 + 256) * (|s - s'| + |t - t'|) := by
  have hc := coef_bounds r k
  have hP : 0 ≤ 2 * ((r : ℝ) ^ 2 + 7) ^ 2 := by positivity
  unfold linkR
  split_ifs
  · have := edgeRight_lipschitz s t s' t'
    have h0 : 0 ≤ |s - s'| + |t - t'| := by positivity
    nlinarith
  · rw [← mul_sub, abs_mul]
    have h1 := spS_lipschitz δ (stretch r k s t) (stretch r k s' t')
    have h2 : |stretch r k s t - stretch r k s' t'| ≤ ((r : ℝ) ^ 2 + 7) * (|s - s'| + |t - t'|) := by
      unfold stretch
      have e : cA r k * s + cB r k * t - (cA r k * s' + cB r k * t') =
          cA r k * (s - s') + cB r k * (t - t') := by ring
      rw [e]
      calc _ ≤ |cA r k * (s - s')| + |cB r k * (t - t')| := abs_add_le _ _
        _ = |cA r k| * |s - s'| + |cB r k| * |t - t'| := by rw [abs_mul, abs_mul]
        _ ≤ ((r : ℝ) ^ 2 + 7) * |s - s'| + ((r : ℝ) ^ 2 + 7) * |t - t'| := by
            gcongr
            · exact hc.1
            · exact hc.2
        _ = _ := by ring
    have h0 : 0 ≤ |s - s'| + |t - t'| := by positivity
    calc |cB r k| * |spS δ (stretch r k s t) - spS δ (stretch r k s' t')|
        ≤ ((r : ℝ) ^ 2 + 7) * (2 * (((r : ℝ) ^ 2 + 7) * (|s - s'| + |t - t'|))) := by
          apply mul_le_mul hc.2 (h1.trans (by linarith)) (abs_nonneg _) (by positivity)
      _ ≤ _ := by nlinarith

lemma field_lipschitz (r : ℕ) (δ : ℝ) {k : ℕ} (π : Fin (k + 1) ↪ Fin d) (x y : Point d) :
    ‖field r δ π x - field r δ π y‖ ≤ (8 * ((r : ℝ) ^ 2 + 7) ^ 2 + 1026) * ‖x - y‖ := by
  set C := 2 * ((r : ℝ) ^ 2 + 7) ^ 2 + 256 with hC
  have hC0 : 0 ≤ C := by positivity
  let α := Fin.castSuccEmb.trans π
  let β := (Fin.succEmb k).trans π
  have hl := scatter_increment α α β
    (fun i => linkL r δ i.val (x (π i.castSucc)) (x (π i.succ)))
    (fun i => linkL r δ i.val (y (π i.castSucc)) (y (π i.succ))) (x - y) hC0 (fun i => by
      simpa [α, β] using linkL_lipschitz r δ i.val (x (π i.castSucc)) (x (π i.succ))
        (y (π i.castSucc)) (y (π i.succ)))
  have hr := scatter_increment β α β
    (fun i => linkR r δ i.val (x (π i.castSucc)) (x (π i.succ)))
    (fun i => linkR r δ i.val (y (π i.castSucc)) (y (π i.succ))) (x - y) hC0 (fun i => by
      simpa [α, β] using linkR_lipschitz r δ i.val (x (π i.castSucc)) (x (π i.succ))
        (y (π i.castSucc)) (y (π i.succ)))
  have hs : ‖-(potentialSlope (x (π 0)) • EuclideanSpace.single (π 0) (1 : ℝ)) -
      -(potentialSlope (y (π 0)) • EuclideanSpace.single (π 0) (1 : ℝ))‖ ≤ 2 * ‖x - y‖ := by
    have he : -(potentialSlope (x (π 0)) • EuclideanSpace.single (π 0) (1 : ℝ)) -
        -(potentialSlope (y (π 0)) • EuclideanSpace.single (π 0) (1 : ℝ)) =
        -(potentialSlope (x (π 0)) - potentialSlope (y (π 0))) •
          EuclideanSpace.single (π 0) (1 : ℝ) := by module
    rw [he]
    simp only [norm_smul, norm_neg, PiLp.norm_single, norm_one, mul_one,
      Real.norm_eq_abs]
    have hc : |x (π 0) - y (π 0)| ≤ ‖x - y‖ := by
      simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x - y) (π 0)
    have hp := potentialSlope_lipschitz (x (π 0)) (y (π 0))
    linarith
  rw [field_decomposition, field_decomposition]
  have hadd (a b c a' b' c' : Point d) :
      ‖a + b + c - (a' + b' + c')‖ ≤ ‖a - a'‖ + ‖b - b'‖ + ‖c - c'‖ := by
    rw [show a + b + c - (a' + b' + c') = (a - a') + (b - b') + (c - c') by abel]
    exact norm_add₃_le
  refine (hadd _ _ _ _ _ _).trans ?_
  have hxy := norm_nonneg (x - y)
  nlinarith

end LongTails.Proofs.SlidingWireChain
