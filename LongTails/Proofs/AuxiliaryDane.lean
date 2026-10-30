import LongTails.Proofs.AuxiliaryEval
import LongTails.Proofs.AuxiliaryInner
import LongTails.Proofs.NearZeroSumCalculus

namespace LongTails.Proofs.AuxiliaryDane

open scoped RealInnerProductSpace
open LongTails.Algorithms.AuxiliaryPlan LongTails.Algorithms.AuxiliarySimilarity
open LongTails.Algorithms.AuxiliaryPlan.TwoPlan LongTails.Proofs.AuxiliaryPlan.TwoPlan LongTails.Proofs.AuxiliaryEval
open LongTails.Proofs.AuxiliaryCertificates LongTails.Proofs.AuxiliaryInner

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section Defs

variable (t : Tuning) (ρ : ℝ)

noncomputable def tau : ℝ := t.α / (32 * ρ)

noncomputable def vartheta : ℝ := t.a * t.α ^ 3 / (192 * ρ * t.db)

end Defs

structure Hyp (t : Tuning) (f h : E → ℝ) (L δ ρ Δ : ℝ) : Prop where
  hf : ContDiff ℝ 2 f
  hh : Differentiable ℝ h
  hHess : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖
  hsim : ∀ x y, ‖(gradient f x - gradient h x) - (gradient f y - gradient h y)‖ ≤ δ * ‖x - y‖
  hLh : ∀ x y, ‖gradient h x - gradient h y‖ ≤ L * ‖x - y‖
  hL : 0 ≤ L
  hδ : 0 < δ
  hρ : 0 < ρ
  hα : 0 < t.α
  hδdb : δ ≤ t.db
  hαdb : t.α ≤ t.db
  hM : t.M = L + 2 * t.α + 4 * t.db
  ha : t.a ^ 2 * (4 * t.db) = t.α
  ha0 : 0 < t.a
  ha1 : t.a ≤ 1
  hη : t.η = t.α / (8 * ρ)
  hN : 2 ≤ t.N
  hJ : 1 ≤ t.J
  hCN : 2 * t.M * ((1 - 3 * t.db / t.M) ^ (t.N - 1) *
    ((4 * (L + δ) * Δ + 18 * tau t ρ ^ 2 * (t.M + δ) ^ 2) / (6 * t.db))) ≤
    (vartheta t ρ ^ 2 / (60 * t.M * tau t ρ)) ^ 2
  hCJ : 2 * t.M * ((3 / 5) ^ t.J * (t.M / 2 * (6 * tau t ρ) ^ 2) +
    5 / 2 * (vartheta t ρ ^ 2 / (60 * t.M * tau t ρ)) * (6 * tau t ρ)) ≤ vartheta t ρ ^ 2
  hε : 0 < t.ε
  hCT : 2 * vartheta t ρ ^ 2 + 8 * t.db * ((1 - t.a) ^ t.T * (t.α * tau t ρ ^ 2) +
    6 * vartheta t ρ * tau t ρ / t.a) ≤ t.ε ^ 2 / 4
  hCε : 2 * (t.α * tau t ρ ^ 2) ≤ t.ε ^ 2 / (16 * t.α)

variable {t : Tuning} {f h : E → ℝ} {L δ ρ Δ : ℝ}

lemma Hyp.db_pos (hyp : Hyp t f h L δ ρ Δ) : 0 < t.db := hyp.hα.trans_le hyp.hαdb

lemma Hyp.M_pos (hyp : Hyp t f h L δ ρ Δ) : 0 < t.M := by
  rw [hyp.hM]; have := hyp.db_pos; have := hyp.hα; linarith [hyp.hL]

lemma Hyp.tau_pos (hyp : Hyp t f h L δ ρ Δ) : 0 < tau t ρ := by
  unfold tau; have := hyp.hα; have := hyp.hρ; positivity

lemma Hyp.vartheta_nonneg (hyp : Hyp t f h L δ ρ Δ) : 0 ≤ vartheta t ρ := by
  unfold vartheta; have := hyp.hα; have := hyp.hρ; have := hyp.db_pos; have := hyp.ha0
  positivity

lemma Hyp.gradf (hyp : Hyp t f h L δ ρ Δ) (x : E) : HasGradientAt f (gradient f x) x :=
  ((hyp.hf.differentiable (by norm_num)) x).hasGradientAt

lemma Hyp.gradh (hyp : Hyp t f h L δ ρ Δ) (x : E) : HasGradientAt h (gradient h x) x :=
  (hyp.hh x).hasGradientAt

lemma quad_grad (c : ℝ) (p x : E) :
    HasGradientAt (fun z => c * ‖z - p‖ ^ 2) ((2 * c) • (x - p)) x := by
  have hq := hasGradientWithinAt_univ.mp
    (OracleTemplate.NearZeroSum.gradient_translated_quadratic (2 * c) p x Set.univ)
  have he : (fun u => 2 * c / 2 * ‖u - p‖ ^ 2) = fun z => c * ‖z - p‖ ^ 2 := by
    funext u; ring
  rwa [he] at hq

lemma grad_add {p q : E → ℝ} {gp gq x : E} (hp : HasGradientAt p gp x)
    (hq : HasGradientAt q gq x) : HasGradientAt (fun z => p z + q z) (gp + gq) x := by
  rw [hasGradientAt_iff_hasFDerivAt, map_add]
  exact (hasGradientAt_iff_hasFDerivAt.mp hp).add (hasGradientAt_iff_hasFDerivAt.mp hq)

lemma grad_sub {p q : E → ℝ} {gp gq x : E} (hp : HasGradientAt p gp x)
    (hq : HasGradientAt q gq x) : HasGradientAt (fun z => p z - q z) (gp - gq) x := by
  rw [hasGradientAt_iff_hasFDerivAt, map_sub]
  exact (hasGradientAt_iff_hasFDerivAt.mp hp).sub (hasGradientAt_iff_hasFDerivAt.mp hq)

lemma grad_sub_const {p : E → ℝ} {gp x : E} (hp : HasGradientAt p gp x) (c : ℝ) :
    HasGradientAt (fun z => p z - c) gp x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  exact (hasGradientAt_iff_hasFDerivAt.mp hp).sub_const c

lemma Hyp.phi_breg (hyp : Hyp t f h L δ ρ Δ) (u w : E) :
    |breg (fun x => f x - h x) (fun x => gradient f x - gradient h x) u w| ≤
      δ / 2 * ‖u - w‖ ^ 2 :=
  breg_abs_le (fun x => grad_sub (hyp.gradf x) (hyp.gradh x)) hyp.hsim u w

lemma Hyp.gradf_lip (hyp : Hyp t f h L δ ρ Δ) (x z : E) :
    ‖gradient f x - gradient f z‖ ≤ (L + δ) * ‖x - z‖ := by
  have he : gradient f x - gradient f z =
      (gradient h x - gradient h z) + ((gradient f x - gradient h x) - (gradient f z - gradient h z)) := by
    abel
  rw [he]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ L * ‖x - z‖ + δ * ‖x - z‖ := add_le_add (hyp.hLh x z) (hyp.hsim x z)
    _ = _ := by ring

section Records

variable (t : Tuning) (y v : E) (f h : E → ℝ)

noncomputable def Fo (f : E → ℝ) : E → ℝ × E := fun x => (f x, gradient f x)

noncomputable def tval (x : E) : ℝ := f x + t.α * ‖x - y‖ ^ 2 + t.db * ‖x - v‖ ^ 2

noncomputable def tgrad (x : E) : E := gradient f x + (2 * t.α) • (x - y) + (2 * t.db) • (x - v)

noncomputable def pval (x : E) : ℝ :=
  h x + t.α * ‖x - y‖ ^ 2 + t.db * ‖x - v‖ ^ 2 + t.db * ‖x‖ ^ 2

noncomputable def pgrad (x : E) : E :=
  gradient h x + (2 * t.α) • (x - y) + (2 * t.db) • (x - v) + (2 * t.db) • x

lemma tRec_eq (x : E) : tRec t y v x (Fo f x) = (x, tval t y v f x, tgrad t y v f x) := rfl

lemma psiRec_eq (x : E) : psiRec t y v x (Fo h x) = (x, pval t y v h x, pgrad t y v h x) := rfl

lemma recBreg_T (u w : E) :
    recBreg (tRec t y v u (Fo f u)) (tRec t y v w (Fo f w)) =
      breg f (gradient f) u w + (t.α + t.db) * ‖u - w‖ ^ 2 := by
  simp only [recBreg, tRec, Fo]
  exact breg_two_quad f (gradient f) t.α t.db y v u w

lemma recBreg_psi (u w : E) :
    recBreg (psiRec t y v u (Fo h u)) (psiRec t y v w (Fo h w)) =
      breg h (gradient h) u w + (t.α + t.db + t.db) * ‖u - w‖ ^ 2 := by
  simp only [recBreg, psiRec, Fo]
  exact breg_three_quad h (gradient h) t.α t.db t.db y v u w

lemma recBreg_g (u w : E) :
    recBreg (gRecY t y (Fo f) u) (gRecY t y (Fo f) w) =
      breg f (gradient f) u w + t.α * ‖u - w‖ ^ 2 := by
  simp only [recBreg, gRecY, Fo]
  exact breg_one_quad f (gradient f) t.α y u w

end Records

lemma breg_h_eq (u w : E) :
    breg h (gradient h) u w = breg f (gradient f) u w -
      breg (fun x => f x - h x) (fun x => gradient f x - gradient h x) u w := by
  rw [breg_sub_eq]; ring

lemma Hyp.T_le_psi (hyp : Hyp t f h L δ ρ Δ) (y v u w : E) :
    recBreg (tRec t y v u (Fo f u)) (tRec t y v w (Fo f w)) ≤
      recBreg (psiRec t y v u (Fo h u)) (psiRec t y v w (Fo h w)) := by
  rw [recBreg_T, recBreg_psi, breg_h_eq (f := f) (h := h)]
  exact AuxiliaryCertificates.T_le_psi rfl (by ring) (hyp.phi_breg u w) hyp.hδdb (sq_nonneg _) hyp.db_pos.le

lemma Hyp.cert_T (hyp : Hyp t f h L δ ρ Δ) (y v u w : E)
    (hfail : recBreg (tRec t y v u (Fo f u)) (tRec t y v w (Fo f w)) <
      2 / 5 * recBreg (psiRec t y v u (Fo h u)) (psiRec t y v w (Fo h w))) :
    breg f (gradient f) u w < -(t.α / 2) * ‖u - w‖ ^ 2 := by
  rw [recBreg_T, recBreg_psi, breg_h_eq (f := f) (h := h)] at hfail
  exact transfer_T rfl (by ring) (hyp.phi_breg u w) hyp.hδdb hyp.hα.le (sq_nonneg _) hfail

lemma Hyp.cert_psi (hyp : Hyp t f h L δ ρ Δ) (y v u w : E)
    (hfail : recBreg (psiRec t y v u (Fo h u)) (psiRec t y v w (Fo h w)) <
      3 * t.db / 2 * ‖u - w‖ ^ 2) :
    breg f (gradient f) u w < -(t.α / 2) * ‖u - w‖ ^ 2 := by
  rw [recBreg_psi, breg_h_eq (f := f) (h := h)] at hfail
  exact transfer_psi (by ring) (hyp.phi_breg u w) hyp.hδdb hyp.hα.le (sq_nonneg _) hfail

lemma cert_g (t : Tuning) (f : E → ℝ) (y u w : E)
    (hfail : recBreg (gRecY t y (Fo f) u) (gRecY t y (Fo f) w) < t.α / 2 * ‖u - w‖ ^ 2) :
    breg f (gradient f) u w < -(t.α / 2) * ‖u - w‖ ^ 2 := by
  rw [recBreg_g] at hfail
  exact transfer_g rfl hfail

omit [CompleteSpace E] in
lemma ne_of_breg_neg {q : E → ℝ} {dq : E → E} {c : ℝ} {u w : E}
    (hb : breg q dq u w < -c * ‖u - w‖ ^ 2) : u ≠ w := by
  rintro rfl
  simp [breg] at hb

lemma Hyp.pgrad_has (hyp : Hyp t f h L δ ρ Δ) (y v x : E) :
    HasGradientAt (pval t y v h) (pgrad t y v h x) x := by
  have h1 := quad_grad t.α y x
  have h2 := quad_grad t.db v x
  have h3 := quad_grad t.db 0 x
  simp only [sub_zero] at h3
  exact grad_add (grad_add (grad_add (hyp.gradh x) h1) h2) h3

lemma Hyp.pgrad_lip (hyp : Hyp t f h L δ ρ Δ) (y v a b : E) :
    ‖pgrad t y v h a - pgrad t y v h b‖ ≤ t.M * ‖a - b‖ := by
  have he : pgrad t y v h a - pgrad t y v h b =
      (gradient h a - gradient h b) + (2 * t.α + 4 * t.db) • (a - b) := by
    simp only [pgrad]; module
  rw [he, hyp.hM]
  have hc : 0 ≤ 2 * t.α + 4 * t.db := by have := hyp.hα; have := hyp.db_pos; positivity
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ L * ‖a - b‖ + (2 * t.α + 4 * t.db) * ‖a - b‖ := by
      gcongr
      · exact hyp.hLh a b
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    _ = _ := by ring

lemma Hyp.tgrad_has (hyp : Hyp t f h L δ ρ Δ) (y v x : E) :
    HasGradientAt (tval t y v f) (tgrad t y v f x) x :=
  grad_add (grad_add (hyp.gradf x) (quad_grad t.α y x)) (quad_grad t.db v x)

end LongTails.Proofs.AuxiliaryDane

namespace LongTails.Algorithms.AuxiliarySimilarity.Book

variable {E : Type}

lemma note_le_left (bk : Book E) (x : E) (fx : ℝ) : (bk.note x fx).best.2 ≤ bk.best.2 := by
  unfold Book.note
  split_ifs with h
  · exact h.le
  · exact le_rfl

lemma note_le_right (bk : Book E) (x : E) (fx : ℝ) : (bk.note x fx).best.2 ≤ fx := by
  unfold Book.note
  split_ifs with h
  · exact le_rfl
  · exact not_lt.mp h

@[simp] lemma note_cert (bk : Book E) (x : E) (fx : ℝ) : (bk.note x fx).cert = bk.cert := rfl

@[simp] lemma flag_best (bk : Book E) (c : Option (E × E)) : (bk.flag c).best = bk.best := rfl

lemma flag_some (bk : Book E) (c : Option (E × E)) {p : E × E} (h : bk.cert = some p) :
    (bk.flag c).cert = some p := by
  simp [Book.flag, h]

lemma flag_cases (bk : Book E) (c : Option (E × E)) {p : E × E} (h : (bk.flag c).cert = some p) :
    bk.cert = some p ∨ (bk.cert = none ∧ c = some p) := by
  unfold Book.flag at h
  cases hc : bk.cert with
  | none => simp only [hc] at h; exact Or.inr ⟨rfl, h⟩
  | some q => simp only [hc] at h; exact Or.inl (by rw [h])

lemma flag_none (bk : Book E) (c : Option (E × E)) (h : (bk.flag c).cert = none) :
    bk.cert = none ∧ c = none := by
  unfold Book.flag at h
  cases hc : bk.cert with
  | none => simp only [hc] at h; exact ⟨rfl, h⟩
  | some q => simp [hc] at h

lemma note_valid {f : E → ℝ} (bk : Book E) (hb : bk.best.2 = f bk.best.1) (x : E) :
    (bk.note x (f x)).best.2 = f (bk.note x (f x)).best.1 := by
  unfold Book.note
  split_ifs <;> simp [hb]

end LongTails.Algorithms.AuxiliarySimilarity.Book
