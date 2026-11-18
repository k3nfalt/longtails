import LongTails.Proofs.RelativeHessianLocalized

namespace LongTails.Proofs.RelativeHessianOracle

open scoped RealInnerProductSpace BigOperators Topology
open RelativeHessianArctan RelativeHessianGate RelativeHessianGeometry RelativeHessianLocalized

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

abbrev Reply (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := ℝ × E × (E →L[ℝ] E)
noncomputable def jet (f : E → ℝ) (x : E) : Reply E := (f x, gradient f x, fderiv ℝ (gradient f) x)
noncomputable def rawPrefix {m : ℕ} (v : Fin (m + 1) → E) (r : ℕ) (x : E) : ℝ :=
  -RidgeJets.value profile (v 0) x +
    ∑ i : Fin m, if i.val < r then edge (v i.castSucc) (v i.succ) x else 0
noncomputable def prefixFunction {m : ℕ} (v : Fin (m + 1) → E) (r : ℕ) (x : E) : ℝ :=
  RelativeHessianCutoffSpatial.value (radius m) x * rawPrefix v r x +
    FullGeneralizedSmoothZeroQuery.quadratic coefficient 0 x

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma rawPrefix_smooth {m : ℕ} (v : Fin (m + 1) → E) (r : ℕ) : ContDiff ℝ 3 (rawPrefix v r) := by
  apply (RidgeJets.smooth profile_contDiff _).neg.add
  apply ContDiff.sum
  intro i _
  by_cases hi : i.val < r
  · simpa only [ite_eq_left hi] using edge_smooth (v i.castSucc) (v i.succ)
  · simpa only [ite_eq_right hi] using (contDiff_const : ContDiff ℝ 3 (fun _ : E => (0 : ℝ)))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma partial_smooth {m : ℕ} (v : Fin (m + 1) → E) (r : ℕ) : ContDiff ℝ 3 (prefixFunction v r) :=
  ((RelativeHessianCutoffSpatial.smooth _).mul (rawPrefix_smooth v r)).add
    (RelativeHessianGuard.quadratic_smooth _)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma edge_flat (a b x : E) (hx : |⟪a, x⟫| ≤ 1 / 10) : edge a b x = 0 := by
  have h := abs_le.mp hx
  rw [edge_eq]
  simp [RelativeHessianChain.link, (gate_flat h.2).1,
    (gate_flat (show -⟪a, x⟫ ≤ 1 / 10 by linarith)).1]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma eventually_rawPrefix {m : ℕ} (v : Fin (m + 1) → E) (r : ℕ) (x : E)
    (hx : ∀ i : Fin m, r ≤ i.val → |⟪v i.castSucc, x⟫| < 1 / 10) :
    chain v =ᶠ[𝓝 x] rawPrefix v r := by
  classical
  have hi (i : Fin m) : ∀ᶠ y in 𝓝 x, r ≤ i.val → |⟪v i.castSucc, y⟫| < 1 / 10 := by
    by_cases h : r ≤ i.val
    · have he := ((innerSL ℝ (v i.castSucc)).continuous.abs).continuousAt.eventually
        (gt_mem_nhds (hx i h))
      exact he.mono (fun _ hh _ => hh)
    · exact Filter.Eventually.of_forall (fun _ hh => (h hh).elim)
  have he : ∀ᶠ y in 𝓝 x, ∀ i : Fin m, r ≤ i.val → |⟪v i.castSucc, y⟫| < 1 / 10 :=
    Filter.eventually_all.mpr hi
  filter_upwards [he] with y hy
  unfold chain rawPrefix
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · rfl
  · exact edge_flat _ _ _ (hy i (by omega)).le

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma eventually_partial {m : ℕ} (v : Fin (m + 1) → E) (r : ℕ) (x : E)
    (hx : ∀ i : Fin m, r ≤ i.val → |⟪v i.castSucc, x⟫| < 1 / 10) :
    RelativeHessianLocalized.value v =ᶠ[𝓝 x] prefixFunction v r := by
  filter_upwards [eventually_rawPrefix v r x hx] with y hy
  simp only [RelativeHessianLocalized.value, perturbation, prefixFunction, hy]

omit [FiniteDimensional ℝ E] in
lemma jet_prequery {m : ℕ} (v : Fin (m + 1) → E) (r : ℕ) (x : E)
    (hx : ∀ i : Fin m, r ≤ i.val → |⟪v i.castSucc, x⟫| < 1 / 10) :
    jet (RelativeHessianLocalized.value v) x = jet (prefixFunction v r) x := by
  obtain ⟨hf, hg, hH, _⟩ := ThirdOrderAffineCalculus.local_jets_eq (eventually_partial v r x hx)
  simp only [jet, hf, hg, hH]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma partial_prefix {m : ℕ} (v w : Fin (m + 1) → E) (r : ℕ)
    (hv : ∀ j, j.val < r + 1 → v j = w j) : prefixFunction v r = prefixFunction w r := by
  funext x
  unfold prefixFunction rawPrefix
  rw [hv 0 (by simp)]
  congr 2
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with hi
  · rw [hv i.castSucc (by simpa using Nat.lt_succ_of_lt hi), hv i.succ (by simpa using hi)]
  · rfl

lemma cutoff_jet_outside {R : ℝ} (hR : 0 < R) {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (a : ℝ) (x : E) (hx : 2 * R ≤ ‖x‖) :
    jet (fun y => RelativeHessianCutoffSpatial.value R y * f y +
      FullGeneralizedSmoothZeroQuery.quadratic a 0 y) x =
      jet (FullGeneralizedSmoothZeroQuery.quadratic a 0) x := by
  obtain ⟨hc, hg, hH, _⟩ := RelativeHessianCutoffSpatial.outside_jets hR x hx
  have hp := (RelativeHessianCutoffSpatial.smooth R).mul hf
  have hgp : gradient (fun y => RelativeHessianCutoffSpatial.value R y * f y) x = 0 := by
    rw [ProductCompositionJets.product_gradient (RelativeHessianCutoffSpatial.smooth R) hf]
    simp [hc, hg]
  have hHp : fderiv ℝ (gradient (fun y => RelativeHessianCutoffSpatial.value R y * f y)) x = 0 := by
    ext u
    rw [ProductCompositionJets.product_hessian_apply (RelativeHessianCutoffSpatial.smooth R) hf]
    simp [hc, hg, hH]
  have hgt : gradient (fun y => RelativeHessianCutoffSpatial.value R y * f y +
      FullGeneralizedSmoothZeroQuery.quadratic a 0 y) x =
      gradient (FullGeneralizedSmoothZeroQuery.quadratic a 0) x := by
    have h := ThirdOrderAffineCalculus.combination_gradient hp (RelativeHessianGuard.quadratic_smooth a) 1 1 x
    simpa only [one_mul, one_smul, hgp, zero_add] using h
  have hHt : fderiv ℝ (gradient (fun y => RelativeHessianCutoffSpatial.value R y * f y +
      FullGeneralizedSmoothZeroQuery.quadratic a 0 y)) x =
      fderiv ℝ (gradient (FullGeneralizedSmoothZeroQuery.quadratic a 0)) x := by
    have h := ThirdOrderAffineCalculus.combination_hessian hp (RelativeHessianGuard.quadratic_smooth a) 1 1 x
    simpa only [one_mul, one_smul, hHp, zero_add] using h
  simp only [jet, hc, zero_mul, zero_add, hgt, hHt]

lemma full_jet_outside {m : ℕ} (v : Fin (m + 1) → E) (x : E) (hx : 2 * radius m ≤ ‖x‖) :
    jet (RelativeHessianLocalized.value v) x =
      jet (FullGeneralizedSmoothZeroQuery.quadratic coefficient 0) x :=
  cutoff_jet_outside (radius_pos m) (chain_smooth v) coefficient x hx

lemma partial_jet_outside {m : ℕ} (v : Fin (m + 1) → E) (r : ℕ)
    (x : E) (hx : 2 * radius m ≤ ‖x‖) :
    jet (prefixFunction v r) x = jet (FullGeneralizedSmoothZeroQuery.quadratic coefficient 0) x :=
  cutoff_jet_outside (radius_pos m) (rawPrefix_smooth v r) coefficient x hx

lemma jet_prequery_bounded {m : ℕ} (v : Fin (m + 1) → E) (r : ℕ) (x : E)
    (hx : ‖x‖ ≤ 2 * radius m → ∀ i : Fin m, r ≤ i.val → |⟪v i.castSucc, x⟫| < 1 / 10) :
    jet (RelativeHessianLocalized.value v) x = jet (prefixFunction v r) x := by
  by_cases hn : ‖x‖ ≤ 2 * radius m
  · exact jet_prequery v r x (hx hn)
  · rw [full_jet_outside v x (le_of_not_ge hn), partial_jet_outside v r x (le_of_not_ge hn)]

end LongTails.Proofs.RelativeHessianOracle
