import LongTails.Proofs.ThirdOrderMaskedOracle

open scoped BigOperators RealInnerProductSpace Topology

namespace LongTails.Proofs.MeanSquaredPLMask

open LongTails.Proofs.ThirdOrderMaskedOracle
open LongTails.Proofs.RelativeHessianSimulation (axes axes_inner axes_orthonormal)
open LongTails.Proofs.RelativeHessianOracle (prefixFunction rawPrefix partial_smooth)
open LongTails.Proofs.RelativeHessianLocalized (radius radius_pos)
open LongTails.Proofs.RelativeHessianGeometry (edge edge_smooth edge_eq)

noncomputable def cut (t : ℝ) : ℝ := min 1 (max 0 (2 - 40 * |t|))

lemma cut_bounds (t : ℝ) : 0 ≤ cut t ∧ cut t ≤ 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

lemma cut_zero {t : ℝ} (h : 1 / 20 ≤ |t|) : cut t = 0 := by
  simp [cut, max_eq_left (by linarith : 2 - 40 * |t| ≤ 0)]

lemma cut_one {t : ℝ} (h : |t| ≤ 1 / 40) : cut t = 1 := by
  apply min_eq_left
  exact (show 1 ≤ 2 - 40 * |t| by linarith).trans (le_max_right _ _)

lemma cut_lipschitz (x y : ℝ) : |cut x - cut y| ≤ 40 * |x - y| := by
  have h1 := abs_max_sub_max_le_max (0 : ℝ) (2 - 40 * |x|) 0 (2 - 40 * |y|)
  have h2 := abs_min_sub_min_le_max (1 : ℝ) (max 0 (2 - 40 * |x|)) 1 (max 0 (2 - 40 * |y|))
  simp only [sub_self, abs_zero] at h1 h2
  rw [max_eq_right (abs_nonneg ((2 - 40 * |x|) - (2 - 40 * |y|)))] at h1
  rw [max_eq_right (abs_nonneg (max 0 (2 - 40 * |x|) - max 0 (2 - 40 * |y|)))] at h2
  have h3 : |(2 - 40 * |x|) - (2 - 40 * |y|)| = 40 * |(|x| - |y|)| := by
    rw [show (2 - 40 * |x|) - (2 - 40 * |y|) = -40 * (|x| - |y|) by ring, abs_mul]
    norm_num
  have h4 := abs_abs_sub_abs_le_abs_sub x y
  dsimp [cut]
  rw [h3] at h1
  linarith

variable {d n : ℕ}

noncomputable def maskUpTo (R : ℕ) (π : Fin (n + 1) ↪ Fin d) (w : Space d) (s : ℕ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun i : Fin (n + 1) => if s ≤ i.val ∧ i.val < R then cut (w (π i)) else 1)

lemma maskUpTo_bounds (R : ℕ) (π : Fin (n + 1) ↪ Fin d) (w : Space d) (s : ℕ) :
    0 ≤ maskUpTo R π w s ∧ maskUpTo R π w s ≤ 1 := by
  classical
  constructor
  · apply Finset.le_inf'
    intro i _
    split_ifs
    · exact (cut_bounds _).1
    · norm_num
  · have h := Finset.inf'_le
      (fun i : Fin (n + 1) => if s ≤ i.val ∧ i.val < R then cut (w (π i)) else 1)
      (Finset.mem_univ (0 : Fin (n + 1)))
    apply h.trans
    split_ifs
    · exact (cut_bounds _).2
    · exact le_rfl

lemma maskUpTo_zero (R : ℕ) (π : Fin (n + 1) ↪ Fin d) (w : Space d) (s : ℕ) (i : Fin (n + 1))
    (hs : s ≤ i.val) (hR : i.val < R) (hi : 1 / 20 ≤ |w (π i)|) : maskUpTo R π w s = 0 := by
  apply le_antisymm _ (maskUpTo_bounds R π w s).1
  have h := Finset.inf'_le
    (fun i : Fin (n + 1) => if s ≤ i.val ∧ i.val < R then cut (w (π i)) else 1)
    (Finset.mem_univ i)
  simpa only [maskUpTo, ite_eq_left (And.intro hs hR), cut_zero hi] using h

lemma maskUpTo_one (R : ℕ) (π : Fin (n + 1) ↪ Fin d) (w : Space d) (s : ℕ)
    (h : ∀ i : Fin (n + 1), s ≤ i.val → i.val < R → |w (π i)| ≤ 1 / 40) :
    maskUpTo R π w s = 1 := by
  apply le_antisymm (maskUpTo_bounds R π w s).2
  apply Finset.le_inf'
  intro i _
  split_ifs with hi
  · rw [cut_one (h i hi.1 hi.2)]
  · exact le_rfl

lemma maskUpTo_lipschitz (R : ℕ) (π : Fin (n + 1) ↪ Fin d) (x y : Space d) (s : ℕ) :
    |maskUpTo R π x s - maskUpTo R π y s| ≤ 40 * ‖x - y‖ := by
  classical
  have hdir (x y : Space d) : maskUpTo R π x s ≤ maskUpTo R π y s + 40 * ‖x - y‖ := by
    obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (fun i : Fin (n + 1) => if s ≤ i.val ∧ i.val < R then cut (y (π i)) else 1)
    have hx := Finset.inf'_le
      (fun i : Fin (n + 1) => if s ≤ i.val ∧ i.val < R then cut (x (π i)) else 1) hi
    change maskUpTo R π y s = _ at he
    rw [he]
    apply hx.trans
    split_ifs
    · have hc := cut_lipschitz (x (π i)) (y (π i))
      have hn : |x (π i) - y (π i)| ≤ ‖x - y‖ := by
        simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x - y) (π i)
      have hs := le_abs_self (cut (x (π i)) - cut (y (π i)))
      linarith
    · have hn := norm_nonneg (x - y)
      linarith
  have hxy := hdir x y
  have hyx := hdir y x
  rw [norm_sub_rev y x] at hyx
  rw [abs_le]
  constructor <;> linarith

lemma maskUpTo_prefix (R : ℕ) (π ρ : Fin (n + 1) ↪ Fin d) (w : Space d) (s : ℕ)
    (h : ∀ k : Fin (n + 1), k.val < R → π k = ρ k) : maskUpTo R π w s = maskUpTo R ρ w s := by
  unfold maskUpTo
  congr 1
  funext i
  by_cases hi : s ≤ i.val ∧ i.val < R
  · rw [ite_eq_left hi, ite_eq_left hi, h i hi.2]
  · rw [ite_eq_right hi, ite_eq_right hi]

lemma maskUpTo_congr_small (R R' : ℕ) (π : Fin (n + 1) ↪ Fin d) (w : Space d) (s : ℕ)
    (h : ∀ i : Fin (n + 1), min R R' ≤ i.val → |w (π i)| ≤ 1 / 40) :
    maskUpTo R π w s = maskUpTo R' π w s := by
  unfold maskUpTo
  congr 1
  funext i
  by_cases hi : i.val < min R R'
  · have h1 : i.val < R := lt_of_lt_of_le hi (min_le_left _ _)
    have h2 : i.val < R' := lt_of_lt_of_le hi (min_le_right _ _)
    simp only [h1, h2, and_true]
  · have hc := cut_one (h i (not_lt.mp hi))
    split_ifs <;> simp [hc]

noncomputable def block (π : Fin (n + 1) ↪ Fin d) (s : ℕ) (w : Space d) : Space d :=
  partGrad π s w - partGrad π (s - 1) w

lemma block_bound (π : Fin (n + 1) ↪ Fin d) (s : ℕ) (w : Space d) : ‖block π s w‖ ≤ 2 ^ 51 :=
  secret_bound π s w

lemma block_prefix (π ρ : Fin (n + 1) ↪ Fin d) (s : ℕ) (w : Space d)
    (h : ∀ k : Fin (n + 1), k.val < s + 1 → π k = ρ k) : block π s w = block ρ s w := by
  unfold block
  rw [partGrad_prefix π ρ s w h, partGrad_prefix π ρ (s - 1) w (fun k hk => h k (by omega))]

lemma block_outside (π : Fin (n + 1) ↪ Fin d) (s : ℕ) (w : Space d)
    (hw : 2 * radius n ≤ ‖w‖) : block π s w = 0 := by
  unfold block
  rw [partGrad_outside π s w hw, partGrad_outside π (s - 1) w hw, sub_self]

lemma rawPrefix_step_eq {m : ℕ} (v : Fin (m + 1) → Space d) (s : ℕ) (y : Space d)
    (hy : ∀ i : Fin m, i.val + 1 = s → |⟪v i.castSucc, y⟫| ≤ 1 / 10) :
    rawPrefix v s y = rawPrefix v (s - 1) y := by
  unfold rawPrefix
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases h1 : i.val < s - 1
  · have h2 : i.val < s := by omega
    rw [ite_eq_left h1, ite_eq_left h2]
  · rw [ite_eq_right h1]
    by_cases h2 : i.val < s
    · rw [ite_eq_left h2]
      exact LongTails.Proofs.RelativeHessianOracle.edge_flat _ _ _ (hy i (by omega))
    · rw [ite_eq_right h2]

lemma prefix_step_eventually {m : ℕ} (v : Fin (m + 1) → Space d) (s : ℕ) (x : Space d)
    (hx : ∀ i : Fin m, i.val + 1 = s → |⟪v i.castSucc, x⟫| < 1 / 10) :
    prefixFunction v s =ᶠ[𝓝 x] prefixFunction v (s - 1) := by
  classical
  have hi (i : Fin m) : ∀ᶠ y in 𝓝 x, i.val + 1 = s → |⟪v i.castSucc, y⟫| < 1 / 10 := by
    by_cases h : i.val + 1 = s
    · have he := ((innerSL ℝ (v i.castSucc)).continuous.abs).continuousAt.eventually
        (gt_mem_nhds (hx i h))
      exact he.mono (fun _ hh _ => hh)
    · exact Filter.Eventually.of_forall (fun _ hh => (h hh).elim)
  have he : ∀ᶠ y in 𝓝 x, ∀ i : Fin m, i.val + 1 = s → |⟪v i.castSucc, y⟫| < 1 / 10 :=
    Filter.eventually_all.mpr hi
  filter_upwards [he] with y hy
  simp only [prefixFunction, rawPrefix_step_eq v s y (fun i h => (hy i h).le)]

lemma block_flat (π : Fin (n + 1) ↪ Fin d) (s : ℕ) (w : Space d)
    (h : ∀ i : Fin (n + 1), i.val + 1 = s → |w (π i)| < 1 / 10) : block π s w = 0 := by
  have hev := prefix_step_eventually (axes π) s w (fun i hi => by
    rw [axes_inner]
    exact h i.castSucc (by simpa using hi))
  have hg := (LongTails.Proofs.ThirdOrderAffineCalculus.local_jets_eq hev).2.1
  unfold block partGrad
  rw [hg, sub_self]

lemma block_small (π : Fin (n + 1) ↪ Fin d) (r s : ℕ) (w : Space d) (hs : r + 1 ≤ s)
    (h : ∀ i : Fin (n + 1), r ≤ i.val → |w (π i)| ≤ 1 / 40) : block π s w = 0 := by
  apply block_flat
  intro i hi
  have := h i (by omega)
  linarith

lemma rawPrefix_step_hessian {m : ℕ} (v : Fin (m + 1) → Space d) (hn : ∀ i, ‖v i‖ ≤ 1)
    (s : ℕ) :
    ∃ e : Space d → ℝ, ContDiff ℝ 3 e ∧ (∀ x, |e x| ≤ 4) ∧ (∀ x, ‖gradient e x‖ ≤ 2 ^ 50) ∧
      (∀ x, ‖fderiv ℝ (gradient e) x‖ ≤ 2 ^ 51) ∧
      ∀ x, rawPrefix v s x = rawPrefix v (s - 1) x + e x := by
  have hzero : ∃ e : Space d → ℝ, ContDiff ℝ 3 e ∧ (∀ x, |e x| ≤ 4) ∧
      (∀ x, ‖gradient e x‖ ≤ 2 ^ 50) ∧ (∀ x, ‖fderiv ℝ (gradient e) x‖ ≤ 2 ^ 51) ∧
      ∀ x, e x = 0 := by
    have hg : gradient (fun _ : Space d => (0 : ℝ)) = fun _ => 0 := by
      funext x
      have h : HasGradientAt (fun _ : Space d => (0 : ℝ)) (0 : Space d) x := by
        rw [hasGradientAt_iff_hasFDerivAt]
        simpa using hasFDerivAt_const (0 : ℝ) x
      exact h.gradient
    refine ⟨fun _ => 0, contDiff_const, fun x => by norm_num, fun x => ?_, fun x => ?_,
      fun x => rfl⟩
    · rw [hg, norm_zero]
      positivity
    · rw [hg]
      simp
  rcases Nat.eq_zero_or_pos s with hs | hs
  · obtain ⟨e, h1, h2, h3, h4, h5⟩ := hzero
    refine ⟨e, h1, h2, h3, h4, fun x => ?_⟩
    subst hs
    simp [h5 x]
  · obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    by_cases hk : k < m
    · refine ⟨edge (v (⟨k, hk⟩ : Fin m).castSucc) (v (⟨k, hk⟩ : Fin m).succ), edge_smooth _ _,
        fun x => ?_, fun x => (RelativeHessianChainBounds.edge_bounds _ _ x (hn _) (hn _)).1,
        fun x => (RelativeHessianChainBounds.edge_bounds _ _ x (hn _) (hn _)).2, fun x => ?_⟩
      · rw [edge_eq, abs_le]
        have := RelativeHessianChain.link_bounds ⟪v (⟨k, hk⟩ : Fin m).castSucc, x⟫
          ⟪v (⟨k, hk⟩ : Fin m).succ, x⟫
        constructor <;> linarith [Real.pi_lt_four, this.1, this.2]
      · unfold rawPrefix
        rw [add_assoc]
        congr 1
        have hsplit : ∀ i : Fin m,
            (if i.val < k + 1 then edge (v i.castSucc) (v i.succ) x else 0) =
            (if i.val < k then edge (v i.castSucc) (v i.succ) x else 0) +
              (if i = (⟨k, hk⟩ : Fin m) then edge (v i.castSucc) (v i.succ) x else 0) := by
          intro i
          by_cases h1 : i.val < k
          · have h2 : i ≠ (⟨k, hk⟩ : Fin m) := fun h => by rw [h] at h1; simp at h1
            simp [h1, h2, Nat.lt_succ_of_lt h1]
          · by_cases h2 : i = (⟨k, hk⟩ : Fin m)
            · subst h2; simp
            · have h3 : ¬ i.val < k + 1 := by
                intro h
                exact h2 (Fin.ext (by simp; omega))
              simp [h1, h2, h3]
        simp_rw [hsplit]
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (⟨k, hk⟩ : Fin m)]
        simp
    · obtain ⟨e, h1, h2, h3, h4, h5⟩ := hzero
      refine ⟨e, h1, h2, h3, h4, fun x => ?_⟩
      rw [h5 x, add_zero]
      unfold rawPrefix
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      have hi := i.isLt
      rw [ite_eq_left (by omega), ite_eq_left (by omega)]

lemma block_lipschitz (π : Fin (n + 1) ↪ Fin d) (s : ℕ) (x y : Space d) :
    ‖block π s x - block π s y‖ ≤ 2 ^ 54 * ‖x - y‖ := by
  have hv := axes_orthonormal π
  obtain ⟨e, he, hval, hgrad, hhess, hstep⟩ :=
    rawPrefix_step_hessian (axes π) (fun i => (hv.norm_eq_one i).le) s
  have hcs := RelativeHessianCutoffSpatial.smooth (E := Space d) (radius n)
  have hD : ContDiff ℝ 3 (fun z => RelativeHessianCutoffSpatial.value (radius n) z * e z) :=
    hcs.mul he
  have hfun : prefixFunction (axes π) s = fun z => 1 * prefixFunction (axes π) (s - 1) z +
      1 * (RelativeHessianCutoffSpatial.value (radius n) z * e z) := by
    funext z
    unfold prefixFunction
    rw [hstep z]
    ring
  have hblock : ∀ w, block π s w =
      gradient (fun z => RelativeHessianCutoffSpatial.value (radius n) z * e z) w := by
    intro w
    have hg := ThirdOrderAffineCalculus.combination_gradient (partial_smooth (axes π) (s - 1))
      hD 1 1 w
    unfold block partGrad
    rw [hfun, hg, one_smul, one_smul, add_sub_cancel_left]
  have hH : ∀ z, ‖fderiv ℝ (gradient (fun z =>
      RelativeHessianCutoffSpatial.value (radius n) z * e z)) z‖ ≤ 2 ^ 54 := by
    intro z
    obtain ⟨hc0, hc1, hc2, -, -⟩ := ThirdOrderChainLipschitz.cutoff_small (E := Space d) n z
    have hN : (1 : ℝ) / (n + 1 : ℕ) ≤ 1 := by
      rw [div_le_one (by exact_mod_cast Nat.succ_pos n)]
      exact_mod_cast Nat.succ_pos n
    have hp := ThirdOrderJetDifference.product_hessian_norm hcs he z
    have t1 : |RelativeHessianCutoffSpatial.value (radius n) z| * ‖fderiv ℝ (gradient e) z‖ ≤
        1 * 2 ^ 51 := mul_le_mul hc0 (hhess z) (norm_nonneg _) (by norm_num)
    have t2 : 2 * ‖gradient (RelativeHessianCutoffSpatial.value (radius n)) z‖ *
        ‖gradient e z‖ ≤ 2 * 1 * 2 ^ 50 :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hc1.trans hN) (by norm_num)) (hgrad z)
        (norm_nonneg _) (by norm_num)
    have t3 : |e z| * ‖fderiv ℝ (gradient (RelativeHessianCutoffSpatial.value (radius n))) z‖ ≤
        4 * 1 := mul_le_mul (hval z) (hc2.trans hN) (norm_nonneg _) (by norm_num)
    refine hp.trans ?_
    have hnum : (1 : ℝ) * 2 ^ 51 + 2 * 1 * 2 ^ 50 + 4 * 1 ≤ 2 ^ 54 := by norm_num
    linarith
  rw [hblock x, hblock y]
  exact ThirdOrderJetDifference.lipschitz_of_bound
    (LongTails.Proofs.GradientDependentLocal.derivative_chain hD).2.1 hH x y

end LongTails.Proofs.MeanSquaredPLMask
