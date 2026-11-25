import LongTails.Proofs.NcPlCut

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.NcPlInstance

open LongTails.Proofs.AbcChainProfiles LongTails.Proofs.NcPlCalc
open LongTails.Proofs.NcPlBlockSmooth LongTails.Proofs.NcPlChain
open LongTails.Proofs.NcPlChainPL LongTails.Proofs.NcPlFlat LongTails.Proofs.NcPlCut
open LongTails.Proofs.AbcChain (Chain)
open LongTails.Proofs.AbcHardFunction (Space sel sel_apply sel_norm adjoint_norm)
open LongTails.Proofs.MintyChainGeometry (ball ball_norm_le ball_lipschitz ball_of_le)

structure Geo where
  m : ℕ
  n : ℕ
  k : ℕ
  r : ℕ → ℝ
  ρ : ℝ
  Bx : ℝ
  By : ℝ
  hk : k + 1 = (m + 1) * (n + 2)
  scales : Scales n r ρ
  hBx : 0 < Bx
  hBy : 0 < By
  hBxM : 2 ^ 40 * ((m : ℝ) + 1) ≤ Bx ^ 2
  hByM : 2 ^ 19 * ((m : ℝ) + 1) * ((n : ℝ) + 1) ≤ By ^ 2

section Seq

variable {k : ℕ}

noncomputable def seq (c : Chain k) (p : ℕ) : ℝ := if h : p < k + 1 then c ⟨p, h⟩ else 0

lemma seq_fin (c : Chain k) (p : Fin (k + 1)) : seq c p = c p := by
  unfold seq
  rw [dite_eq_left p.isLt]

lemma seq_lt (c : Chain k) {p : ℕ} (h : p < k + 1) : seq c p = c ⟨p, h⟩ := by
  unfold seq
  rw [dite_eq_left h]

lemma seq_of_ge (c : Chain k) {p : ℕ} (h : k + 1 ≤ p) : seq c p = 0 := by
  unfold seq
  rw [dite_eq_right (by omega)]

lemma sum_seq_sq (a b : Chain k) :
    ∑ p ∈ Finset.range (k + 1), (seq a p - seq b p) ^ 2 = ‖a - b‖ ^ 2 := by
  rw [Finset.sum_range, norm_sub_sq_eq]
  apply Finset.sum_congr rfl
  intro p _
  rw [seq_fin, seq_fin]

end Seq

section Base

variable {d : ℕ}

noncomputable def base (lam ρ : ℝ) (y : Space d) : ℝ := ∑ j, hb lam ρ (y j)

noncomputable def baseGrad (lam ρ : ℝ) (y : Space d) : Space d :=
  WithLp.toLp 2 (fun j => dhb lam ρ (y j))

lemma base_hasGradientAt {lam : ℝ} (hlam : 0 ≤ lam) (ρ : ℝ) (y : Space d) :
    HasGradientAt (base lam ρ) (baseGrad lam ρ y) y := by
  refine hasGradientAt_of_model (base lam ρ) (fun y j => dhb lam ρ (y j)) (lam / 2 + 1 / 2) ?_ y
  intro a b
  unfold base
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  exact hb_model hlam ρ (a j) (b j)

lemma base_le_zero {lam : ℝ} (hlam : 0 ≤ lam) (ρ : ℝ) (y : Space d) : base lam ρ y ≤ 0 :=
  Finset.sum_nonpos fun j _ => hb_le_zero hlam ρ (y j)

lemma base_zero (lam : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) : base lam ρ (0 : Space d) = 0 := by
  unfold base
  apply Finset.sum_eq_zero
  intro j _
  exact hb_zero lam hρ

lemma baseGrad_zero (lam : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) : baseGrad lam ρ (0 : Space d) = 0 := by
  unfold baseGrad
  ext j
  exact dhb_zero lam hρ

lemma baseGrad_lip {lam : ℝ} (hlam : 0 ≤ lam) (ρ : ℝ) (y y' : Space d) :
    ‖baseGrad lam ρ y - baseGrad lam ρ y'‖ ≤ (lam + 1) * ‖y - y'‖ := by
  apply norm_le_of_sq_le _ (mul_nonneg (by linarith) (norm_nonneg _))
  rw [mul_pow, norm_sub_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have h := dhb_lip hlam ρ (y j) (y' j)
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs, mul_pow, sq_abs] at h2
  exact h2

lemma base_eq (lam ρ : ℝ) (y : Space d) :
    base lam ρ y = -(lam / 2 * ‖y‖ ^ 2) - ∑ j, pos (-y j - ρ / 2) ^ 2 / 2 := by
  unfold base
  rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [hb_eq]
  ring

lemma baseGrad_inner (lam : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) (y : Space d) :
    ⟪baseGrad lam ρ y, y⟫ ≤ -(lam * ‖y‖ ^ 2) - ∑ j, pos (-y j - ρ / 2) ^ 2 := by
  unfold baseGrad
  rw [inner_toLp, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro j _
  exact dhb_mul_self lam hρ (y j)

end Base

section Defs

variable (G : Geo) {d : ℕ} (π : Fin (G.k + 1) ↪ Fin d)

noncomputable def chA (x : Space d) : Chain G.k := cutv G.Bx x • sel π x

noncomputable def vA (x y : Space d) : Chain G.k :=
  WithLp.toLp 2 (fun p : Fin (G.k + 1) =>
    gA G.m G.n G.r (seq (chA G π x)) (seq (sel π y)) (cutv G.By y) p)

noncomputable def vB (x y : Space d) : Chain G.k :=
  WithLp.toLp 2 (fun p : Fin (G.k + 1) => gB G.n G.r (seq (chA G π x)) (seq (sel π y)) p)

noncomputable def rVal (x y : Space d) : ℝ := rF G.m G.n G.r (seq (chA G π x)) (seq (sel π y))

noncomputable def hardF (x y : Space d) : ℝ :=
  ‖x‖ ^ 2 / 32 + base (lamOf G.n) G.ρ y +
    theta G.m G.n G.r (seq (chA G π x)) (seq (sel π y)) (cutv G.By y)

noncomputable def hardGx (x y : Space d) : Space d :=
  (1 / 16 : ℝ) • x + cutv G.Bx x • (sel π).adjoint (vA G π x y) +
    ⟪vA G π x y, sel π x⟫ • cutGrad G.Bx x

noncomputable def hardGy (x y : Space d) : Space d :=
  baseGrad (lamOf G.n) G.ρ y + cutv G.By y • (sel π).adjoint (vB G π x y) +
    rVal G π x y • cutGrad G.By y

end Defs

section ChainSpace

variable (G : Geo)

lemma thetaA_hasGradientAt (b : ℕ → ℝ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (a : Chain G.k) :
    HasGradientAt (fun a : Chain G.k => theta G.m G.n G.r (seq a) b c)
      (WithLp.toLp 2 (fun p : Fin (G.k + 1) => gA G.m G.n G.r (seq a) b c p)) a := by
  refine hasGradientAt_of_model (fun a : Chain G.k => theta G.m G.n G.r (seq a) b c)
    (fun a p => gA G.m G.n G.r (seq a) b c p) (2 ^ 17) ?_ a
  intro a a'
  have h := theta_model_a (m := G.m) G.scales hc0 hc1 (seq a) (seq a') b
  rw [← G.hk, Finset.sum_range, Finset.sum_range] at h
  simp only [seq_fin] at h
  exact h

lemma rB_hasGradientAt (a : ℕ → ℝ) (b : Chain G.k) :
    HasGradientAt (fun b : Chain G.k => rF G.m G.n G.r a (seq b))
      (WithLp.toLp 2 (fun p : Fin (G.k + 1) => gB G.n G.r a (seq b) p)) b := by
  refine hasGradientAt_of_model (fun b : Chain G.k => rF G.m G.n G.r a (seq b))
    (fun b p => gB G.n G.r a (seq b) p) (104 / G.ρ ^ 2) ?_ b
  intro b b'
  have h := theta_model_b (m := G.m) G.scales a (seq b) (seq b') 1
  rw [← G.hk, Finset.sum_range, Finset.sum_range] at h
  simp only [seq_fin, theta, one_mul, abs_one, sub_sub_sub_cancel_right] at h
  exact h

end ChainSpace

section Gradients

variable (G : Geo) {d : ℕ} (π : Fin (G.k + 1) ↪ Fin d)

lemma normSq_hasGradientAt (x : Space d) :
    HasGradientAt (fun x : Space d => ‖x‖ ^ 2 / 32) ((1 / 16 : ℝ) • x) x := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (1 / 32 : ℝ)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  · funext z
    ring
  · ext v
    simp only [InnerProductSpace.toDual_apply_apply, smul_apply, smul_eq_mul,
      innerSL_apply_apply, real_inner_smul_left, nsmul_eq_mul, Nat.cast_ofNat]
    ring

lemma chainX_hasGradientAt (x y : Space d) :
    HasGradientAt
      (fun x : Space d => theta G.m G.n G.r (seq (chA G π x)) (seq (sel π y)) (cutv G.By y))
      (cutv G.Bx x • (sel π).adjoint (vA G π x y) + ⟪vA G π x y, sel π x⟫ • cutGrad G.Bx x) x := by
  have hth := (thetaA_hasGradientAt G (seq (sel π y)) (cutv_nonneg G.By y) (cutv_le_one G.By y)
    (chA G π x)).hasFDerivAt
  have hch : HasFDerivAt (fun x : Space d => cutv G.Bx x • sel π x)
      (cutv G.Bx x • (sel π : Space d →L[ℝ] Chain G.k) +
        (InnerProductSpace.toDual ℝ (Space d) (cutGrad G.Bx x)).smulRight (sel π x)) x :=
    (cutv_hasGradientAt (B := G.Bx) x).hasFDerivAt.smul (sel π).hasFDerivAt
  have hcomp := hth.comp x hch
  rw [hasGradientAt_iff_hasFDerivAt]
  refine HasFDerivAt.congr_fderiv hcomp ?_
  ext v
  have key : ⟪cutv G.Bx x • (sel π).adjoint (vA G π x y) +
      ⟪vA G π x y, sel π x⟫ • cutGrad G.Bx x, v⟫ =
      ⟪vA G π x y, cutv G.Bx x • sel π v + ⟪cutGrad G.Bx x, v⟫ • sel π x⟫ := by
    rw [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_right, ContinuousLinearMap.adjoint_inner_left]
    ring
  exact key.symm

theorem hardF_hasGradientAt_x (x y : Space d) :
    HasGradientAt (fun x => hardF G π x y) (hardGx G π x y) x := by
  have h1 := (normSq_hasGradientAt x).hasFDerivAt
  have h2 := (chainX_hasGradientAt G π x y).hasFDerivAt
  have h3 : HasFDerivAt (fun x : Space d => ‖x‖ ^ 2 / 32 + base (lamOf G.n) G.ρ y +
      theta G.m G.n G.r (seq (chA G π x)) (seq (sel π y)) (cutv G.By y))
      (InnerProductSpace.toDual ℝ (Space d) ((1 / 16 : ℝ) • x) +
        InnerProductSpace.toDual ℝ (Space d) (cutv G.Bx x • (sel π).adjoint (vA G π x y) +
          ⟪vA G π x y, sel π x⟫ • cutGrad G.Bx x)) x :=
    (h1.add_const (base (lamOf G.n) G.ρ y)).add h2
  rw [hasGradientAt_iff_hasFDerivAt]
  refine HasFDerivAt.congr_fderiv h3 ?_
  unfold hardGx
  rw [add_assoc]
  exact (map_add _ _ _).symm

lemma rY_hasGradientAt (a : ℕ → ℝ) (y : Space d) :
    HasGradientAt (fun y : Space d => rF G.m G.n G.r a (seq (sel π y)))
      ((sel π).adjoint (WithLp.toLp 2 (fun p : Fin (G.k + 1) =>
        gB G.n G.r a (seq (sel π y)) p))) y := by
  have hd := (rB_hasGradientAt G a (sel π y)).hasFDerivAt.comp y (sel π).hasFDerivAt
  rw [hasGradientAt_iff_hasFDerivAt]
  refine HasFDerivAt.congr_fderiv hd ?_
  ext v
  exact ((sel π).adjoint_inner_left v _).symm

theorem hardF_hasGradientAt_y (x y : Space d) :
    HasGradientAt (fun y => hardF G π x y) (hardGy G π x y) y := by
  have hb := (base_hasGradientAt (lamOf_pos G.n).le G.ρ y).hasFDerivAt
  have hc := (cutv_hasGradientAt (B := G.By) y).hasFDerivAt
  have hr := (rY_hasGradientAt G π (seq (chA G π x)) y).hasFDerivAt
  have hm : HasFDerivAt (fun y : Space d => cutv G.By y *
      rF G.m G.n G.r (seq (chA G π x)) (seq (sel π y)))
      (cutv G.By y • InnerProductSpace.toDual ℝ (Space d) ((sel π).adjoint (vB G π x y)) +
        rF G.m G.n G.r (seq (chA G π x)) (seq (sel π y)) •
          InnerProductSpace.toDual ℝ (Space d) (cutGrad G.By y)) y := hc.mul hr
  have h3 : HasFDerivAt (fun y : Space d => ‖x‖ ^ 2 / 32 + base (lamOf G.n) G.ρ y +
      (cutv G.By y * rF G.m G.n G.r (seq (chA G π x)) (seq (sel π y)) -
        cF G.m G.n (seq (chA G π x))))
      (InnerProductSpace.toDual ℝ (Space d) (baseGrad (lamOf G.n) G.ρ y) +
        (cutv G.By y • InnerProductSpace.toDual ℝ (Space d) ((sel π).adjoint (vB G π x y)) +
          rF G.m G.n G.r (seq (chA G π x)) (seq (sel π y)) •
            InnerProductSpace.toDual ℝ (Space d) (cutGrad G.By y))) y :=
    (hb.const_add (‖x‖ ^ 2 / 32)).add (hm.sub_const (cF G.m G.n (seq (chA G π x))))
  rw [hasGradientAt_iff_hasFDerivAt]
  refine HasFDerivAt.congr_fderiv h3 ?_
  ext v
  have key : ⟪hardGy G π x y, v⟫ = ⟪baseGrad (lamOf G.n) G.ρ y, v⟫ +
      (cutv G.By y * ⟪(sel π).adjoint (vB G π x y), v⟫ +
        rF G.m G.n G.r (seq (chA G π x)) (seq (sel π y)) * ⟪cutGrad G.By y, v⟫) := by
    unfold hardGy rVal
    rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    ring
  exact key.symm

end Gradients

end LongTails.Proofs.NcPlInstance
