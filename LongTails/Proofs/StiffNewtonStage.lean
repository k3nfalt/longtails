import LongTails.Proofs.MonotoneTensorBounds

open scoped RealInnerProductSpace

namespace LongTails.Proofs.StiffNewtonStage

open LongTails.Proofs.MonotoneTensorBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : E → E} {L : ℝ}

noncomputable def nq (F : E → E) (b : ℝ) (x u : E) : ℝ := ‖u‖ ^ 2 + b * ⟪fderiv ℝ F x u, u⟫

noncomputable def resid (F : E → E) (b : ℝ) (v z : E) : E := b • F z + z - v

noncomputable def op (F : E → E) (b : ℝ) (z : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E + b • fderiv ℝ F z

noncomputable def newton (F : E → E) (b : ℝ) (v z : E) : E :=
  z - Function.invFun (op F b z) (resid F b v z)

lemma op_inner (b : ℝ) (z u : E) :
    ⟪op F b z u, u⟫ = nq F b z u := by
  simp only [op, nq, add_apply, ContinuousLinearMap.id_apply,
    smul_apply, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq]

lemma _root_.LongTails.Proofs.MonotoneTensorBounds.Regular.nq_ge (h : Regular F L) {b : ℝ} (hb : 0 ≤ b) (z u : E) : ‖u‖ ^ 2 ≤ nq F b z u := by
  unfold nq; nlinarith [mul_nonneg hb (h.psd z u)]

lemma _root_.LongTails.Proofs.MonotoneTensorBounds.Regular.nq_nonneg (h : Regular F L) {b : ℝ} (hb : 0 ≤ b) (z u : E) : 0 ≤ nq F b z u :=
  (sq_nonneg _).trans (h.nq_ge hb z u)

lemma _root_.LongTails.Proofs.MonotoneTensorBounds.Regular.op_surjective [FiniteDimensional ℝ E] (h : Regular F L) {b : ℝ} (hb : 0 ≤ b)
    (z : E) : Function.Surjective (op F b z) := by
  have := LongTails.Proofs.FrozenJacobianSplitting.op_surjective (fderiv ℝ F z) (h.psd z)
    (β := 1) (τ := b) one_pos hb
  simpa [op, one_smul] using this

lemma _root_.LongTails.Proofs.MonotoneTensorBounds.Regular.op_invFun [FiniteDimensional ℝ E] (h : Regular F L) {b : ℝ} (hb : 0 ≤ b)
    (z r : E) : op F b z (Function.invFun (op F b z) r) = r :=
  Function.invFun_eq (h.op_surjective hb z r)

lemma _root_.LongTails.Proofs.MonotoneTensorBounds.Regular.sn_scaled (h : Regular F L) (b : ℝ) (z u : E) :
    b * sn F z u ^ 2 ≤ nq F b z u := by
  rw [h.sn_sq]; unfold nq; nlinarith [sq_nonneg ‖u‖]

lemma _root_.LongTails.Proofs.MonotoneTensorBounds.Regular.newton_identity [FiniteDimensional ℝ E] (h : Regular F L) {b : ℝ} (hb : 0 ≤ b)
    {v zs z : E} (hzs : resid F b v zs = 0) :
    op F b z (newton F b v z - zs) =
      b • (F zs - F z - fderiv ℝ F z (zs - z)) := by
  have hinv := h.op_invFun hb z (resid F b v z)
  have hsplit : newton F b v z - zs = (z - zs) - Function.invFun (op F b z) (resid F b v z) := by
    unfold newton; abel
  rw [hsplit, map_sub, hinv]
  have hr : resid F b v z = resid F b v z - resid F b v zs := by rw [hzs, sub_zero]
  rw [hr]
  simp only [op, resid, add_apply, ContinuousLinearMap.id_apply,
    smul_apply, map_sub, smul_sub]
  abel

lemma _root_.LongTails.Proofs.MonotoneTensorBounds.Regular.newton_error [FiniteDimensional ℝ E] (h : Regular F L) {b : ℝ} (hb : 0 ≤ b)
    {v zs z : E} (hzs : resid F b v zs = 0) :
    Real.sqrt (nq F b z (newton F b v z - zs)) ≤
      Real.sqrt (b * L) * ‖z - zs‖ ^ 2 +
        2 * Real.sqrt (b * L) * ‖z - zs‖ * Real.sqrt (nq F b z (z - zs)) +
          b * L * ‖z - zs‖ ^ 3 := by
  set e := z - zs
  set e1 := newton F b v z - zs
  set B := fderiv ℝ (fderiv ℝ F) z
  set X := Real.sqrt (nq F b z e1)
  set Y := Real.sqrt (nq F b z e)
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hXsq : X ^ 2 = nq F b z e1 := Real.sq_sqrt (h.nq_nonneg hb z e1)
  have hYsq : Y ^ 2 = nq F b z e := Real.sq_sqrt (h.nq_nonneg hb z e)
  have hT := h.taylor z zs
  have hzse : zs - z = -e := by simp [e]
  rw [hzse, norm_neg] at hT
  set T := F zs - F z - fderiv ℝ F z (-e) - (1 / 2 : ℝ) • B (-e) (-e)
  have hid := h.newton_identity hb (z := z) hzs
  rw [hzse] at hid
  have hBee : B (-e) (-e) = B e e := by simp
  have hrel : F zs - F z - fderiv ℝ F z (-e) = (1 / 2 : ℝ) • B e e + T := by
    simp only [T, hBee]; abel
  rw [hrel] at hid
  have hnq : nq F b z e1 = (b / 2) * ⟪e1, B e e⟫ + b * ⟪T, e1⟫ := by
    rw [← op_inner (F := F) b z e1, hid, real_inner_smul_left, inner_add_left,
      real_inner_smul_left, real_inner_comm (B e e) e1]
    ring
  have htb := h.tensor_bound z e1 e e
  have hTe : |⟪T, e1⟫| ≤ L * ‖e‖ ^ 3 * ‖e1‖ :=
    (abs_real_inner_le_norm _ _).trans (by gcongr)
  have he1 : ‖e1‖ ≤ X := by
    rw [← Real.sqrt_sq (norm_nonneg e1)]; exact Real.sqrt_le_sqrt (h.nq_ge hb z e1)
  have hs1 : Real.sqrt b * sn F z e1 ≤ X := by
    rw [← Real.sqrt_sq (sn_nonneg z e1), ← Real.sqrt_mul hb]
    exact Real.sqrt_le_sqrt (h.sn_scaled b z e1)
  have hs : Real.sqrt b * sn F z e ≤ Y := by
    rw [← Real.sqrt_sq (sn_nonneg z e), ← Real.sqrt_mul hb]
    exact Real.sqrt_le_sqrt (h.sn_scaled b z e)
  have hbL : Real.sqrt (b * L) = Real.sqrt b * Real.sqrt L := Real.sqrt_mul hb L
  have hsb := Real.sqrt_nonneg b
  have hsL := Real.sqrt_nonneg L
  have hsq : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb
  have key : X ^ 2 ≤ X * (Real.sqrt (b * L) * ‖e‖ ^ 2 +
      2 * Real.sqrt (b * L) * ‖e‖ * Y + b * L * ‖e‖ ^ 3) := by
    rw [hXsq, hnq]
    have h1 : (b / 2) * ⟪e1, B e e⟫ ≤ (b / 2) * (2 * Real.sqrt L *
        (sn F z e1 * ‖e‖ * ‖e‖ + ‖e1‖ * sn F z e * ‖e‖ + ‖e1‖ * ‖e‖ * sn F z e)) :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans htb) (by positivity)
    have h2 : b * ⟪T, e1⟫ ≤ b * (L * ‖e‖ ^ 3 * ‖e1‖) :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans hTe) hb
    have h3 : (b / 2) * (2 * Real.sqrt L *
        (sn F z e1 * ‖e‖ * ‖e‖ + ‖e1‖ * sn F z e * ‖e‖ + ‖e1‖ * ‖e‖ * sn F z e)) =
        Real.sqrt L * Real.sqrt b * ((Real.sqrt b * sn F z e1) * ‖e‖ ^ 2 +
          2 * ‖e1‖ * (Real.sqrt b * sn F z e) * ‖e‖) := by
      calc (b / 2) * (2 * Real.sqrt L *
            (sn F z e1 * ‖e‖ * ‖e‖ + ‖e1‖ * sn F z e * ‖e‖ + ‖e1‖ * ‖e‖ * sn F z e))
          = Real.sqrt L * b * (sn F z e1 * ‖e‖ ^ 2 + 2 * ‖e1‖ * sn F z e * ‖e‖) := by ring
        _ = _ := by conv_lhs => rw [← hsq]
                    ring
    rw [h3] at h1
    have hn := norm_nonneg e
    have h4 : Real.sqrt L * Real.sqrt b * ((Real.sqrt b * sn F z e1) * ‖e‖ ^ 2 +
        2 * ‖e1‖ * (Real.sqrt b * sn F z e) * ‖e‖) ≤
        Real.sqrt L * Real.sqrt b * (X * ‖e‖ ^ 2 + 2 * X * Y * ‖e‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have := mul_le_mul he1 hs (mul_nonneg hsb (sn_nonneg z e)) hX0
      nlinarith [mul_le_mul_of_nonneg_right hs1 (sq_nonneg ‖e‖), mul_nonneg hn hn]
    have h5 : b * (L * ‖e‖ ^ 3 * ‖e1‖) ≤ b * (L * ‖e‖ ^ 3 * X) := by
      apply mul_le_mul_of_nonneg_left _ hb
      exact mul_le_mul_of_nonneg_left he1 (mul_nonneg h.nonneg (pow_nonneg (norm_nonneg e) 3))
    rw [hbL]
    nlinarith [h1, h2, h4, h5]
  rcases eq_or_lt_of_le hX0 with h0 | hpos
  · rw [← h0]; have := h.nonneg; positivity
  · nlinarith [key]

lemma _root_.LongTails.Proofs.MonotoneTensorBounds.Regular.compare (h : Regular F L) {b : ℝ} (hb : 0 ≤ b) (x x' u : E)
    (hδ : 6 * b * L * ‖x' - x‖ ^ 2 ≤ 1) :
    nq F b x' u ≤ 2 * nq F b x u ∧ nq F b x u ≤ 2 * nq F b x' u := by
  set δ := x' - x
  have ht := h.jac_taylor x x'
  set Er := fderiv ℝ F x' - fderiv ℝ F x - fderiv ℝ (fderiv ℝ F) x δ
  have hEr : |⟪Er u, u⟫| ≤ L * ‖δ‖ ^ 2 * ‖u‖ ^ 2 := by
    calc |⟪Er u, u⟫| ≤ ‖Er u‖ * ‖u‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖Er‖ * ‖u‖ * ‖u‖ := by gcongr; exact Er.le_opNorm u
      _ ≤ L * ‖δ‖ ^ 2 * ‖u‖ * ‖u‖ := by gcongr
      _ = L * ‖δ‖ ^ 2 * ‖u‖ ^ 2 := by ring
  have htau := h.tau_bound x δ u (τ := 2) two_pos
  have hdec : ⟪fderiv ℝ F x' u, u⟫ =
      ⟪fderiv ℝ F x u, u⟫ + ⟪fderiv ℝ (fderiv ℝ F) x δ u, u⟫ + ⟪Er u, u⟫ := by
    have : fderiv ℝ F x' = fderiv ℝ F x + fderiv ℝ (fderiv ℝ F) x δ + Er := by
      simp only [Er]; abel
    rw [this]
    simp only [add_apply, inner_add_left]
  have hpsd := h.psd x u
  have hpsd' := h.psd x' u
  rw [abs_le] at hEr htau
  have hb6 : b * (L * ‖δ‖ ^ 2) ≤ 1 / 6 := by nlinarith
  have hu := sq_nonneg ‖u‖
  unfold nq
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hb6 hu, mul_nonneg hb hpsd]
  · nlinarith [mul_le_mul_of_nonneg_right hb6 hu, mul_nonneg hb hpsd', mul_nonneg hb hpsd]

lemma nq_neg (b : ℝ) (x u : E) : nq F b x (-u) = nq F b x u := by
  simp [nq]

lemma _root_.LongTails.Proofs.MonotoneTensorBounds.Regular.nq_add_le (h : Regular F L) {b : ℝ} (hb : 0 ≤ b) (x u v : E) :
    nq F b x (u + v) ≤ 2 * nq F b x u + 2 * nq F b x v := by
  have hpar := LongTails.Proofs.MonotoneTensorBounds.parallelogram_form (fderiv ℝ F x) u v
  have hn : ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
    have := norm_add_sq_real u v
    have := norm_sub_sq_real u v
    linarith
  have h0 := h.nq_nonneg hb x (u - v)
  unfold nq at h0 ⊢
  nlinarith

lemma _root_.LongTails.Proofs.MonotoneTensorBounds.Regular.nq_mono (h : Regular F L) {b b' : ℝ} (hbb : b ≤ b')
    (hb' : b' ≤ 2 * b) (x u : E) : nq F b x u ≤ nq F b' x u ∧ nq F b' x u ≤ 2 * nq F b x u := by
  have hp := h.psd x u
  unfold nq
  constructor
  · nlinarith
  · nlinarith [sq_nonneg ‖u‖]

lemma _root_.LongTails.Proofs.MonotoneTensorBounds.Regular.newton_quarter [FiniteDimensional ℝ E] (h : Regular F L) {b : ℝ} (hb : 0 ≤ b)
    {v zs y : E} (hzs : resid F b v zs = 0)
    (hsmall : 169 * b * L * nq F b zs (y - zs) ≤ 1) :
    nq F b zs (newton F b v y - zs) ≤ nq F b zs (y - zs) / 4 := by
  set e := y - zs
  set m2 := nq F b zs e
  have hm2 : 0 ≤ m2 := h.nq_nonneg hb zs e
  have he2 : ‖e‖ ^ 2 ≤ m2 := h.nq_ge hb zs e
  have hL := h.nonneg
  have hbL : 0 ≤ b * L := mul_nonneg hb hL
  have hcmp : 6 * b * L * ‖y - zs‖ ^ 2 ≤ 1 := by nlinarith
  have hcmp' : 6 * b * L * ‖zs - y‖ ^ 2 ≤ 1 := by rwa [norm_sub_rev]
  have hY : nq F b y e ≤ 2 * m2 := (h.compare hb zs y e hcmp).1
  have hE := h.newton_error hb (z := y) hzs
  set e1 := newton F b v y - zs
  have hback : nq F b zs e1 ≤ 2 * nq F b y e1 := (h.compare hb y zs e1 hcmp').1
  set t := Real.sqrt (b * L)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = b * L := Real.sq_sqrt hbL
  set m := Real.sqrt m2
  have hm0 : 0 ≤ m := Real.sqrt_nonneg _
  have hmsq : m ^ 2 = m2 := Real.sq_sqrt hm2
  have hen : ‖e‖ ≤ m := by rw [← Real.sqrt_sq (norm_nonneg e)]; exact Real.sqrt_le_sqrt he2
  set Y := Real.sqrt (nq F b y e)
  have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
  have hYsq : Y ^ 2 = nq F b y e := Real.sq_sqrt (h.nq_nonneg hb y e)
  have hYm : Y ≤ 3 / 2 * m := by
    have : Y ^ 2 ≤ (3 / 2 * m) ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ hY0 (by positivity) (by norm_num)).mp this
  have htm : t * m ≤ 1 / 13 := by
    have : (t * m) ^ 2 ≤ (1 / 13) ^ 2 := by rw [mul_pow, ht2, hmsq]; nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num)).mp this
  have hn0 := norm_nonneg e
  have hS : t * ‖e‖ ^ 2 + 2 * t * ‖e‖ * Y + b * L * ‖e‖ ^ 3 ≤ 41 / 10 * t * m ^ 2 := by
    rw [← ht2]
    have h1 : t * ‖e‖ ^ 2 ≤ t * m ^ 2 := by gcongr
    have h2 : 2 * t * ‖e‖ * Y ≤ 2 * t * m * (3 / 2 * m) := by gcongr
    have h3 : t ^ 2 * ‖e‖ ^ 3 ≤ t ^ 2 * m ^ 3 := by gcongr
    have h4 : t ^ 2 * m ^ 3 ≤ t * m ^ 2 * (1 / 13) := by
      have : t ^ 2 * m ^ 3 = (t * m) * (t * m ^ 2) := by ring
      rw [this]; nlinarith [mul_nonneg ht0 (sq_nonneg m)]
    nlinarith
  have hX0 := Real.sqrt_nonneg (nq F b y e1)
  have hX := hE.trans hS
  have hXsq : nq F b y e1 ≤ (41 / 10 * t * m ^ 2) ^ 2 := by
    rw [← Real.sq_sqrt (h.nq_nonneg hb y e1)]
    exact pow_le_pow_left₀ hX0 hX 2
  have hfin : (41 / 10 * t * m ^ 2) ^ 2 = 1681 / 100 * (t * m) ^ 2 * m2 := by rw [← hmsq]; ring
  rw [hfin] at hXsq
  have htm2 : (t * m) ^ 2 ≤ 1 / 169 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right htm2 hm2]

end LongTails.Proofs.StiffNewtonStage
