import LongTails.Proofs.AbcChainMask
import LongTails.Proofs.SmoothConvexFiniteGeometry
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.AbcHardFunction

open LongTails.Proofs.AbcChainProfiles LongTails.Proofs.AbcChain
open LongTails.Proofs.AbcChainProperties LongTails.Proofs.AbcChainMask
open LongTails.Proofs.SmoothConvexFiniteGeometry
open LongTails.Proofs.FiniteSumNondualLowerComponents

variable {d n : ℕ}

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable def width (n : ℕ) : ℝ := 256 * (n + 1)

noncomputable def radius (n : ℕ) : ℝ := 2048 * (n + 1)

lemma width_pos (n : ℕ) : 0 < width n := by unfold width; positivity

lemma radius_pos (n : ℕ) : 0 < radius n := by unfold radius; positivity

noncomputable def wallFn (n : ℕ) (w : Space d) : ℝ := (‖w‖ ^ 2 - radius n ^ 2) / radius n

noncomputable def wallGrad (n : ℕ) (w : Space d) : Space d := (2 / radius n) • w

noncomputable def sel (π : Fin (n + 1) ↪ Fin d) : Space d →L[ℝ] Chain n := coordinateMap π

noncomputable def hardValue (π : Fin (n + 1) ↪ Fin d) (w : Space d) : ℝ :=
  smoothMax (width n) (chain (sel π w)) (wallFn n w)

noncomputable def hardGrad (π : Fin (n + 1) ↪ Fin d) (w : Space d) : Space d :=
  weight (width n) (chain (sel π w)) (wallFn n w) • (sel π).adjoint (field (sel π w)) +
    (1 - weight (width n) (chain (sel π w)) (wallFn n w)) • wallGrad n w

noncomputable def knownGrad (π : Fin (n + 1) ↪ Fin d) (m : ℕ) (w : Space d) : Space d :=
  weight (width n) (chain (trunc m (sel π w))) (wallFn n w) •
      (sel π).adjoint (knownField m (sel π w)) +
    (1 - weight (width n) (chain (trunc m (sel π w))) (wallFn n w)) • wallGrad n w

lemma sel_apply (π : Fin (n + 1) ↪ Fin d) (w : Space d) (i : Fin (n + 1)) :
    sel π w i = w (π i) := rfl

lemma sel_norm (π : Fin (n + 1) ↪ Fin d) (w : Space d) : ‖sel π w‖ ≤ ‖w‖ :=
  coordinateMap_norm π w

lemma sel_opNorm (π : Fin (n + 1) ↪ Fin d) : ‖sel π‖ ≤ 1 :=
  (sel π).opNorm_le_bound zero_le_one (fun w => by rw [one_mul]; exact sel_norm π w)

lemma adjoint_apply (π : Fin (n + 1) ↪ Fin d) (v : Chain n) (j : Fin d) :
    (sel π).adjoint v j = ∑ k : Fin (n + 1), if π k = j then v k else 0 := by
  classical
  have h := ContinuousLinearMap.adjoint_inner_left (sel π) (EuclideanSpace.single j (1 : ℝ)) v
  have hl : ⟪(sel π).adjoint v, EuclideanSpace.single j (1 : ℝ)⟫ = (sel π).adjoint v j := by
    simp [EuclideanSpace.inner_single_right]
  have hr : ⟪v, sel π (EuclideanSpace.single j (1 : ℝ))⟫ =
      ∑ k : Fin (n + 1), if π k = j then v k else 0 := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, sel_apply]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : π k = j
    · simp [hk]
    · simp [hk]
  rw [← hl, ← hr]
  exact h

lemma adjoint_apply_emb (π : Fin (n + 1) ↪ Fin d) (v : Chain n) (k : Fin (n + 1)) :
    (sel π).adjoint v (π k) = v k := by
  classical
  rw [adjoint_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    rw [ite_eq_right (fun h => hb (π.injective h))]
  · simp

lemma sel_adjoint (π : Fin (n + 1) ↪ Fin d) (v : Chain n) : sel π ((sel π).adjoint v) = v := by
  ext k
  rw [sel_apply, adjoint_apply_emb]

lemma adjoint_norm (π : Fin (n + 1) ↪ Fin d) (v : Chain n) : ‖(sel π).adjoint v‖ ≤ ‖v‖ := by
  have h := (sel π).adjoint.le_opNorm v
  rw [ContinuousLinearMap.adjoint.norm_map] at h
  exact h.trans (mul_le_of_le_one_left (norm_nonneg _) (sel_opNorm π))

lemma adjoint_congr (π ρ : Fin (n + 1) ↪ Fin d) (v : Chain n) (m : ℕ)
    (hv : ∀ k : Fin (n + 1), m ≤ k.val → v k = 0)
    (h : ∀ k : Fin (n + 1), k.val < m → π k = ρ k) :
    (sel π).adjoint v = (sel ρ).adjoint v := by
  ext j
  rw [adjoint_apply, adjoint_apply]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k.val < m
  · rw [h k hk]
  · rw [hv k (by omega)]
    simp

lemma wall_hasGradientAt (n : ℕ) (w : Space d) :
    HasGradientAt (wallFn n) (wallGrad n w) w := by
  have hR := radius_pos n
  have hfun : wallFn (d := d) n = fun z => 1 / radius n * ‖z‖ ^ 2 - radius n := by
    funext z
    unfold wallFn
    field_simp
  rw [hfun, hasGradientAt_iff_hasFDerivAt]
  convert ((hasStrictFDerivAt_norm_sq w).hasFDerivAt.const_mul (1 / radius n)).sub_const
    (radius n) using 1
  ext v
  simp only [wallGrad, InnerProductSpace.toDual_apply_apply, smul_apply, smul_eq_mul,
    innerSL_apply_apply, real_inner_smul_left, nsmul_eq_mul, Nat.cast_ofNat]
  ring

lemma chainSel_hasGradientAt (π : Fin (n + 1) ↪ Fin d) (w : Space d) :
    HasGradientAt (fun z => chain (sel π z)) ((sel π).adjoint (field (sel π w))) w := by
  have hd := (chain_hasGradientAt (sel π w)).hasFDerivAt.comp w (sel π).hasFDerivAt
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hd using 1
  · rfl
  · ext v
    exact (sel π).adjoint_inner_left v (field (sel π w))

lemma hardValue_hasGradientAt (π : Fin (n + 1) ↪ Fin d) (w : Space d) :
    HasGradientAt (hardValue π) (hardGrad π w) w :=
  smoothMax_gradient (width n) (width_pos n) (fun z => chain (sel π z)) (wallFn n) w _ _
    (chainSel_hasGradientAt π w) (wall_hasGradientAt n w)

lemma field_norm (u : Chain n) : ‖field u‖ ≤ 27 * Real.sqrt (n + 1) := by
  have h := field_norm_sq u
  have hs : (27 * Real.sqrt (n + 1)) ^ 2 = 729 * (n + 1) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  have hpos : 0 ≤ 27 * Real.sqrt (n + 1) := by positivity
  nlinarith [norm_nonneg (field u)]

lemma sqrt_le_self_succ (n : ℕ) : Real.sqrt (n + 1) ≤ n + 1 := by
  have h1 : (1 : ℝ) ≤ n + 1 := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  calc Real.sqrt (n + 1) ≤ Real.sqrt (((n : ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = n + 1 := Real.sqrt_sq (by positivity)

lemma chainSel_value_lipschitz (π : Fin (n + 1) ↪ Fin d) (x y : Space d) :
    |chain (sel π x) - chain (sel π y)| ≤ 27 * Real.sqrt (n + 1) * ‖x - y‖ := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set (Space d))).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun z => chain (sel π z))
    (fun z _ => (chainSel_hasGradientAt π z).hasFDerivAt.hasFDerivWithinAt)
    (fun z _ => by
      rw [(InnerProductSpace.toDual ℝ (Space d)).norm_map]
      exact (adjoint_norm π _).trans (field_norm _)) (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using h

lemma wall_value_lipschitz (n : ℕ) (B : ℝ) (x y : Space d) (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) :
    |wallFn n x - wallFn n y| ≤ 2 * B / radius n * ‖x - y‖ := by
  have hR := radius_pos n
  have h1 : |‖x‖ - ‖y‖| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
  have h2 : 0 ≤ ‖x‖ + ‖y‖ := by positivity
  have hsq : |‖x‖ ^ 2 - ‖y‖ ^ 2| ≤ 2 * B * ‖x - y‖ := by
    have e : ‖x‖ ^ 2 - ‖y‖ ^ 2 = (‖x‖ - ‖y‖) * (‖x‖ + ‖y‖) := by ring
    rw [e, abs_mul, abs_of_nonneg h2]
    have := mul_le_mul h1 (by linarith : ‖x‖ + ‖y‖ ≤ 2 * B) h2 (norm_nonneg _)
    linarith
  have e2 : wallFn n x - wallFn n y = (‖x‖ ^ 2 - ‖y‖ ^ 2) / radius n := by unfold wallFn; ring
  rw [e2, abs_div, abs_of_pos hR, div_le_iff₀ hR]
  have : 2 * B / radius n * ‖x - y‖ * radius n = 2 * B * ‖x - y‖ := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hR.ne']
  linarith

lemma wallGrad_norm (n : ℕ) (w : Space d) : ‖wallGrad n w‖ = 2 * ‖w‖ / radius n := by
  rw [wallGrad, norm_smul, Real.norm_of_nonneg (by have := radius_pos n; positivity)]
  ring

lemma wallGrad_lipschitz (n : ℕ) (x y : Space d) :
    ‖wallGrad n x - wallGrad n y‖ ≤ 2 / radius n * ‖x - y‖ := by
  rw [wallGrad, wallGrad, ← smul_sub, norm_smul,
    Real.norm_of_nonneg (by have := radius_pos n; positivity)]

lemma weight_one_inside (π : Fin (n + 1) ↪ Fin d) (m : ℕ) (w : Space d)
    (hw : ‖w‖ ≤ radius n / 2) :
    weight (width n) (chain (trunc m (sel π w))) (wallFn n w) = 1 ∧
      weight (width n) (chain (sel π w)) (wallFn n w) = 1 ∧
      smoothMax (width n) (chain (sel π w)) (wallFn n w) = chain (sel π w) := by
  have hR := radius_pos n
  have hwall : wallFn n w ≤ -(3 / 4) * radius n := by
    unfold wallFn
    rw [div_le_iff₀ hR]
    have := pow_le_pow_left₀ (norm_nonneg w) hw 2
    nlinarith
  have hc1 := chain_ge (trunc m (sel π w))
  have hc2 := chain_ge (sel π w)
  have hgap (c : ℝ) (hc : -3 * ((n : ℝ) + 1) ≤ c) : width n / 2 ≤ c - wallFn n w := by
    unfold width; unfold radius at hwall; nlinarith
  exact ⟨(smoothMax_eq_left _ _ _ (width_pos n) (hgap _ hc1)).2,
    (smoothMax_eq_left _ _ _ (width_pos n) (hgap _ hc2)).2,
    (smoothMax_eq_left _ _ _ (width_pos n) (hgap _ hc2)).1⟩

lemma weight_zero_outside (π : Fin (n + 1) ↪ Fin d) (m : ℕ) (w : Space d)
    (hw : 2 * radius n ≤ ‖w‖) :
    weight (width n) (chain (trunc m (sel π w))) (wallFn n w) = 0 ∧
      weight (width n) (chain (sel π w)) (wallFn n w) = 0 ∧
      smoothMax (width n) (chain (sel π w)) (wallFn n w) = wallFn n w := by
  have hR := radius_pos n
  have hwall : 3 * radius n ≤ wallFn n w := by
    unfold wallFn
    rw [le_div_iff₀ hR]
    have := pow_le_pow_left₀ (by positivity) hw 2
    nlinarith
  have hc1 := chain_le (trunc m (sel π w))
  have hc2 := chain_le (sel π w)
  have hgap (c : ℝ) (hc : c ≤ 3 * ((n : ℝ) + 1)) : c - wallFn n w ≤ -(width n / 2) := by
    unfold width; unfold radius at hwall; nlinarith
  exact ⟨(smoothMax_eq_right _ _ _ (width_pos n) (hgap _ hc1)).2,
    (smoothMax_eq_right _ _ _ (width_pos n) (hgap _ hc2)).2,
    (smoothMax_eq_right _ _ _ (width_pos n) (hgap _ hc2)).1⟩

lemma hardGrad_outside (π : Fin (n + 1) ↪ Fin d) (w : Space d) (hw : 2 * radius n ≤ ‖w‖) :
    hardGrad π w = wallGrad n w := by
  rw [hardGrad, (weight_zero_outside π 0 w hw).2.1]
  simp

lemma knownGrad_outside (π : Fin (n + 1) ↪ Fin d) (m : ℕ) (w : Space d)
    (hw : 2 * radius n ≤ ‖w‖) : knownGrad π m w = wallGrad n w := by
  rw [knownGrad, (weight_zero_outside π m w hw).1]
  simp

lemma knownGrad_full (π : Fin (n + 1) ↪ Fin d) (m : ℕ) (w : Space d) (hm : n + 1 ≤ m) :
    knownGrad π m w = hardGrad π w := by
  rw [knownGrad, hardGrad, trunc_full m _ hm, knownField_full m _ hm]

lemma knownGrad_prefix (π ρ : Fin (n + 1) ↪ Fin d) (m : ℕ) (w : Space d)
    (h : ∀ k : Fin (n + 1), k.val < m → π k = ρ k) :
    knownGrad π m w = knownGrad ρ m w := by
  have hs : ∀ i : Fin (n + 1), i.val < m → sel π w i = sel ρ w i := by
    intro i hi; rw [sel_apply, sel_apply, h i hi]
  have ht : trunc m (sel π w) = trunc m (sel ρ w) := trunc_congr m _ _ hs
  have hk : knownField m (sel π w) = knownField m (sel ρ w) := knownField_congr m _ _ hs
  by_cases hm : n + 1 ≤ m
  · have hπ : π = ρ := Function.Embedding.ext (fun k => h k (by have := k.isLt; omega))
    rw [hπ]
  · have hsupp : ∀ k : Fin (n + 1), m ≤ k.val → knownField m (sel ρ w) k = 0 := by
      intro k hk'
      rw [knownField_apply, ite_eq_right (by omega)]
    rw [knownGrad, knownGrad, ht, hk, adjoint_congr π ρ _ m hsupp h]

lemma hardValue_ge (π : Fin (n + 1) ↪ Fin d) (w : Space d) :
    chain (sel π w) ≤ hardValue π w :=
  (le_max_left _ _).trans (smoothMax_ge _ _ _ (width_pos n))

lemma hardValue_lower (π : Fin (n + 1) ↪ Fin d) (w : Space d) :
    -3 * ((n : ℝ) + 1) ≤ hardValue π w :=
  (chain_ge _).trans (hardValue_ge π w)

noncomputable def hardMinimizer (π : Fin (n + 1) ↪ Fin d) : Space d :=
  (sel π).adjoint (twoPoint (n := n))

lemma hardMinimizer_norm (π : Fin (n + 1) ↪ Fin d) :
    ‖hardMinimizer π‖ ≤ 2 * Real.sqrt (n + 1) := by
  have h := adjoint_norm π (twoPoint (n := n))
  have hs := twoPoint_norm_sq (n := n)
  have hb : ‖(twoPoint (n := n))‖ ≤ 2 * Real.sqrt (n + 1) := by
    have hq : (2 * Real.sqrt (n + 1)) ^ 2 = 4 * (n + 1) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
    nlinarith [norm_nonneg (twoPoint (n := n)), Real.sqrt_nonneg ((n : ℝ) + 1)]
  exact h.trans hb

lemma hardValue_minimizer (π : Fin (n + 1) ↪ Fin d) :
    hardValue π (hardMinimizer π) = -3 * ((n : ℝ) + 1) := by
  have hn := hardMinimizer_norm π
  have hs := sqrt_le_self_succ n
  have hw : ‖hardMinimizer π‖ ≤ radius n / 2 := by unfold radius; nlinarith
  rw [hardValue, (weight_one_inside π 0 _ hw).2.2, hardMinimizer, sel_adjoint, chain_twoPoint]

lemma hardValue_zero (π : Fin (n + 1) ↪ Fin d) : hardValue π 0 = -3 / 2 := by
  have hw : ‖(0 : Space d)‖ ≤ radius n / 2 := by
    rw [norm_zero]; have := radius_pos n; linarith
  rw [hardValue, (weight_one_inside π 0 _ hw).2.2, map_zero, chain_zero]

end LongTails.Proofs.AbcHardFunction
