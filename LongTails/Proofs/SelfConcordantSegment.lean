import LongTails.Setups.SelfConcordantBFGS
import LongTails.Proofs.SelfConcordantCalculus
import LongTails.Proofs.BFGSLogPotential
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Matrix.PosDef

open Set Matrix

namespace LongTails.Proofs.SelfConcordantSegment

open LongTails.Setups.SelfConcordantBFGS LongTails.Proofs.SelfConcordantCalculus
open LongTails.Proofs.BFGSLogPotential LongTails.Proofs.BFGSMatrix

variable {d : ℕ}

lemma bilin_expand (H : Vec d →L[ℝ] Vec d →L[ℝ] ℝ) (v w : Vec d) :
    H v w = v ⬝ᵥ (hessMatrix H *ᵥ w) := by
  conv_lhs => rw [pi_eq_sum_univ' v, pi_eq_sum_univ' w]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
    smul_eq_mul, dotProduct, mulVec, hessMatrix, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma seg_deriv (x s : Vec d) (τ : ℝ) : HasDerivAt (fun τ : ℝ => x + τ • s) s τ := by
  simpa using ((hasDerivAt_id τ).smul_const s).const_add x

variable {D : Set (Vec d)} {f : Vec d → ℝ} {Df : Vec d → Vec d →L[ℝ] ℝ}
  {D2f : Vec d → Vec d →L[ℝ] Vec d →L[ℝ] ℝ}
  {D3f : Vec d → Vec d →L[ℝ] Vec d →L[ℝ] Vec d →L[ℝ] ℝ}

lemma deriv_f (hSC : SelfConcordantOn D f Df D2f D3f) {x s : Vec d} {τ : ℝ}
    (hτ : x + τ • s ∈ D) : HasDerivAt (fun τ : ℝ => f (x + τ • s)) (Df (x + τ • s) s) τ :=
  (hSC.1 _ hτ).comp_hasDerivAt τ (seg_deriv x s τ)

lemma deriv_Df (hSC : SelfConcordantOn D f Df D2f D3f) {x s : Vec d} {τ : ℝ}
    (hτ : x + τ • s ∈ D) (w : Vec d) :
    HasDerivAt (fun τ : ℝ => Df (x + τ • s) w) (D2f (x + τ • s) s w) τ := by
  have h := (hSC.2.1 _ hτ).comp_hasDerivAt τ (seg_deriv x s τ)
  have := h.clm_apply (hasDerivAt_const τ w)
  simpa using this

lemma deriv_D2f (hSC : SelfConcordantOn D f Df D2f D3f) {x s : Vec d} {τ : ℝ}
    (hτ : x + τ • s ∈ D) (v w : Vec d) :
    HasDerivAt (fun τ : ℝ => D2f (x + τ • s) v w) (D3f (x + τ • s) s v w) τ := by
  have h := HasFDerivAt.comp_hasDerivAt (l := D2f) (l' := D3f (x + τ • s)) τ
    (hSC.2.2.1 _ hτ) (seg_deriv x s τ)
  have h1 := h.clm_apply (hasDerivAt_const τ v)
  have h2 := h1.clm_apply (hasDerivAt_const τ w)
  simpa using h2

lemma restrict_SC1 (hSC : SelfConcordantOn D f Df D2f D3f) {x s : Vec d} {a b : ℝ}
    (hseg : ∀ τ ∈ Icc a b, x + τ • s ∈ D) (hs : s ≠ 0) :
    SC1 (fun τ => f (x + τ • s)) (fun τ => Df (x + τ • s) s) (fun τ => D2f (x + τ • s) s s)
      (fun τ => D3f (x + τ • s) s s s) a b where
  hφ := fun τ hτ => deriv_f hSC (hseg τ hτ)
  hφ1 := fun τ hτ => deriv_Df hSC (hseg τ hτ) s
  hψ := fun τ hτ => deriv_D2f hSC (hseg τ hτ) s s
  pos := fun τ hτ => hSC.2.2.2.1 _ (hseg τ hτ) s hs
  sc := fun τ hτ => hSC.2.2.2.2.1 _ (hseg τ hτ) s s

lemma restrict_comp (hSC : SelfConcordantOn D f Df D2f D3f) {x s : Vec d} {a b : ℝ}
    (hseg : ∀ τ ∈ Icc a b, x + τ • s ∈ D) {v : Vec d} (hv : v ≠ 0) :
    Comp (fun τ => D2f (x + τ • s) s s) (fun τ => D2f (x + τ • s) v v)
      (fun τ => D3f (x + τ • s) s v v) a b where
  hχ := fun τ hτ => deriv_D2f hSC (hseg τ hτ) v v
  pos := fun τ hτ => hSC.2.2.2.1 _ (hseg τ hτ) v hv
  bd := fun τ hτ => hSC.2.2.2.2.1 _ (hseg τ hτ) s v

lemma hess_symm (hSC : SelfConcordantOn D f Df D2f D3f) (hD : IsOpen D) {x : Vec d}
    (hx : x ∈ D) (v w : Vec d) : D2f x v w = D2f x w v := by
  have hev : ∀ᶠ y in nhds x, HasFDerivAt Df (D2f y) y :=
    Filter.eventually_of_mem (hD.mem_nhds hx) fun y hy => hSC.2.1 y hy
  have hev' : ∀ᶠ y in nhds x, HasFDerivAt f (Df y) y :=
    Filter.eventually_of_mem (hD.mem_nhds hx) fun y hy => hSC.1 y hy
  exact second_derivative_symmetric_of_eventually hev' (hSC.2.1 x hx) v w

lemma hessMatrix_posDef (hSC : SelfConcordantOn D f Df D2f D3f) (hD : IsOpen D) {x : Vec d}
    (hx : x ∈ D) : (hessMatrix (D2f x)).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v hv => ?_⟩
  · ext i j
    simp only [conjTranspose_apply, star_trivial, hessMatrix, Matrix.of_apply]
    exact hess_symm hSC hD hx _ _
  · simp only [star_trivial]
    rw [← bilin_expand]
    exact hSC.2.2.2.1 x hx v hv

noncomputable def segQ (D2f : Vec d → Vec d →L[ℝ] Vec d →L[ℝ] ℝ) (x s : Vec d) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => ∫ τ in (0 : ℝ)..1, D2f (x + τ • s) (Pi.single i 1) (Pi.single j 1)

lemma cont_D2f (hSC : SelfConcordantOn D f Df D2f D3f) {x s : Vec d}
    (hseg : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • s ∈ D) (v w : Vec d) :
    ContinuousOn (fun τ : ℝ => D2f (x + τ • s) v w) (Icc 0 1) :=
  fun τ hτ => (deriv_D2f hSC (hseg τ hτ) v w).continuousAt.continuousWithinAt

lemma segQ_quad (hSC : SelfConcordantOn D f Df D2f D3f) {x s : Vec d}
    (hseg : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • s ∈ D) (v w : Vec d) :
    v ⬝ᵥ (segQ D2f x s *ᵥ w) = ∫ τ in (0 : ℝ)..1, D2f (x + τ • s) v w := by
  have hint : ∀ i j, IntervalIntegrable
      (fun τ : ℝ => D2f (x + τ • s) (Pi.single i 1) (Pi.single j 1)) MeasureTheory.volume 0 1 :=
    fun i j => (cont_D2f hSC hseg _ _).intervalIntegrable_of_Icc zero_le_one
  have : ∀ τ : ℝ, D2f (x + τ • s) v w = ∑ i, ∑ j, v i * w j *
      D2f (x + τ • s) (Pi.single i 1) (Pi.single j 1) := fun τ => by
    rw [bilin_expand]
    simp only [dotProduct, mulVec, hessMatrix, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hint2 : ∀ i, IntervalIntegrable (fun τ : ℝ => ∑ j, v i * w j *
      D2f (x + τ • s) (Pi.single i 1) (Pi.single j 1)) MeasureTheory.volume 0 1 := fun i =>
    (continuousOn_finsetSum _ fun j _ => continuousOn_const.mul (cont_D2f hSC hseg _ _)
      ).intervalIntegrable_of_Icc zero_le_one
  simp_rw [this]
  rw [intervalIntegral.integral_finsetSum fun i _ => hint2 i]
  simp only [dotProduct, mulVec, segQ, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum fun j _ => (hint i j).const_mul (v i * w j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul]
  ring

def SegBound (D2f : Vec d → Vec d →L[ℝ] Vec d →L[ℝ] ℝ) (x s : Vec d) (a : ℝ) : Prop :=
  ∀ v : Vec d, ∀ τ ∈ Icc (0 : ℝ) 1, ∀ τ' ∈ Icc (0 : ℝ) 1,
    D2f (x + τ • s) v v ≤ Real.exp a * D2f (x + τ' • s) v v

lemma short_aux {r τ : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 / 2) (hτ : τ ∈ Icc (0 : ℝ) 1) :
    (1 / r) ^ 2 ≤ Real.exp (4 * r) * (1 / r - τ) ^ 2 := by
  have h1 : 1 + 2 * r ≤ Real.exp (2 * r) := by linarith [Real.add_one_le_exp (2 * r)]
  have hir : 2 ≤ 1 / r := by rw [le_div_iff₀ hr0]; linarith
  have hb : 1 / r - 1 ≤ 1 / r - τ := by linarith [hτ.2]
  have hc : 0 ≤ 1 / r - 1 := by linarith
  have hkey : 1 / r ≤ Real.exp (2 * r) * (1 / r - 1) := by
    have : 1 / r - 1 = (1 / r) * (1 - r) := by field_simp
    rw [this]
    have h2 : 1 ≤ (1 + 2 * r) * (1 - r) := by nlinarith
    have h3 : (1 + 2 * r) * (1 - r) ≤ Real.exp (2 * r) * (1 - r) :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    have hp : 0 < 1 / r := by positivity
    nlinarith
  have hkey2 : 1 / r ≤ Real.exp (2 * r) * (1 / r - τ) :=
    hkey.trans (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le)
  have hp : 0 ≤ 1 / r := by positivity
  have := pow_le_pow_left₀ hp hkey2 2
  rw [mul_pow, ← Real.exp_nat_mul] at this
  convert this using 2
  push_cast; ring_nf

lemma segBound_short (hSC : SelfConcordantOn D f Df D2f D3f) {x s : Vec d}
    (hseg : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • s ∈ D) (hs : s ≠ 0) (hr : √(D2f x s s) ≤ 1 / 2) :
    SegBound D2f x s (8 * √(D2f x s s)) := by
  have S := restrict_SC1 hSC hseg hs
  have hx0 : x + (0 : ℝ) • s = x := by simp
  have hψ0 : D2f (x + (0 : ℝ) • s) s s = D2f x s s := by rw [hx0]
  have hpos : 0 < D2f x s s := hSC.2.2.2.1 x (by simpa using hseg 0 ⟨le_rfl, zero_le_one⟩) s hs
  set r := √(D2f x s s) with hrdef
  have hr0 : 0 < r := Real.sqrt_pos.mpr hpos
  have hh0 : hinv (fun τ => D2f (x + τ • s) s s) 0 = 1 / r := by
    simp only [hinv]; rw [hψ0]
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have base : ∀ v : Vec d, ∀ τ ∈ Icc (0 : ℝ) 1,
      D2f (x + τ • s) v v ≤ Real.exp (4 * r) * D2f x v v ∧
      D2f x v v ≤ Real.exp (4 * r) * D2f (x + τ • s) v v := by
    intro v τ hτ
    by_cases hv : v = 0
    · subst hv; simp
    have C := restrict_comp hSC hseg hv
    have hlt : τ - 0 < hinv (fun τ => D2f (x + τ • s) s s) 0 := by
      rw [hh0]
      have : 2 ≤ 1 / r := by rw [le_div_iff₀ hr0]; linarith
      linarith [hτ.2]
    have hup := comp_short_up S C hτ hlt
    have hdn := comp_short_down S C hτ hlt
    simp only [sub_zero, hh0] at hup hdn
    rw [hx0] at hup hdn
    have haux := short_aux hr0 hr hτ
    have hχ0 : 0 < D2f x v v := by
      have := C.pos 0 h0mem; simpa using this
    have hχτ : 0 < D2f (x + τ • s) v v := C.pos τ hτ
    have hq : 0 < (1 / r - τ) ^ 2 := by
      have : 2 ≤ 1 / r := by rw [le_div_iff₀ hr0]; linarith
      have : 0 < 1 / r - τ := by linarith [hτ.2]
      positivity
    constructor
    · have h1 : D2f (x + τ • s) v v * (1 / r) ^ 2 ≤
          D2f (x + τ • s) v v * (Real.exp (4 * r) * (1 / r - τ) ^ 2) :=
        mul_le_mul_of_nonneg_left haux hχτ.le
      have h2 : D2f (x + τ • s) v v * (1 / r) ^ 2 ≤ Real.exp (4 * r) * D2f x v v * (1 / r) ^ 2 := by
        nlinarith [Real.exp_pos (4 * r)]
      have hp : 0 < (1 / r) ^ 2 := by positivity
      exact le_of_mul_le_mul_right h2 hp
    · have h2 : D2f x v v * (1 / r) ^ 2 ≤ Real.exp (4 * r) * D2f (x + τ • s) v v * (1 / r) ^ 2 := by
        have := mul_le_mul_of_nonneg_left haux hχ0.le
        nlinarith [Real.exp_pos (4 * r)]
      have hp : 0 < (1 / r) ^ 2 := by positivity
      exact le_of_mul_le_mul_right h2 hp
  intro v τ hτ τ' hτ'
  obtain ⟨h1, -⟩ := base v τ hτ
  obtain ⟨-, h2⟩ := base v τ' hτ'
  have he : Real.exp (8 * r) = Real.exp (4 * r) * Real.exp (4 * r) := by
    rw [← Real.exp_add]; ring_nf
  rw [he]
  calc D2f (x + τ • s) v v ≤ Real.exp (4 * r) * D2f x v v := h1
    _ ≤ Real.exp (4 * r) * (Real.exp (4 * r) * D2f (x + τ' • s) v v) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = Real.exp (4 * r) * Real.exp (4 * r) * D2f (x + τ' • s) v v := by ring

lemma le_exp_of_abs_log {a b L : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : |Real.log b - Real.log a| ≤ L) : a ≤ Real.exp L * b ∧ b ≤ Real.exp L * a := by
  rw [abs_le] at h
  constructor
  · calc a = Real.exp (Real.log a) := (Real.exp_log ha).symm
      _ ≤ Real.exp (L + Real.log b) := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp L * b := by rw [Real.exp_add, Real.exp_log hb]
  · calc b = Real.exp (Real.log b) := (Real.exp_log hb).symm
      _ ≤ Real.exp (L + Real.log a) := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp L * a := by rw [Real.exp_add, Real.exp_log ha]

lemma segBound_long (hSC : SelfConcordantOn D f Df D2f D3f) {x s : Vec d}
    (hseg : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • s ∈ D) (hs : s ≠ 0) {Δ : ℝ} (hΔ0 : 0 ≤ Δ)
    (hosc : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ τ' ∈ Icc (0 : ℝ) 1, f (x + τ • s) - f (x + τ' • s) ≤ Δ) :
    SegBound D2f x s (6 * Δ + 6) := by
  have S := restrict_SC1 hSC hseg hs
  intro v τ hτ τ' hτ'
  by_cases hv : v = 0
  · subst hv; simp
  have C := restrict_comp hSC hseg hv
  have key : ∀ p ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1, p ≤ q →
      |Real.log (D2f (x + q • s) v v) - Real.log (D2f (x + p • s) v v)| ≤ 6 * Δ + 6 := by
    intro p hp q hq hpq
    have hsub : Icc p q ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hp.1 hq.2
    exact osc_full (S.mono hsub) (C.mono hsub) hpq
      (fun u hu w hw => hosc u (hsub hu) w (hsub hw)) hΔ0
  rcases le_total τ τ' with h | h
  · exact (le_exp_of_abs_log (C.pos τ hτ) (C.pos τ' hτ') (key τ hτ τ' hτ' h)).1
  · exact (le_exp_of_abs_log (C.pos τ' hτ') (C.pos τ hτ) (key τ' hτ' τ hτ h)).2

lemma segQ_le (hSC : SelfConcordantOn D f Df D2f D3f) {x s : Vec d}
    (hseg : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • s ∈ D) {a : ℝ} (hb : SegBound D2f x s a)
    {τ' : ℝ} (hτ' : τ' ∈ Icc (0 : ℝ) 1) (v : Vec d) :
    v ⬝ᵥ (segQ D2f x s *ᵥ v) ≤ Real.exp a * D2f (x + τ' • s) v v := by
  rw [segQ_quad hSC hseg]
  have hint := (cont_D2f hSC hseg v v).intervalIntegrable_of_Icc (μ := MeasureTheory.volume)
    zero_le_one
  calc ∫ τ in (0 : ℝ)..1, D2f (x + τ • s) v v ≤
        ∫ _τ in (0 : ℝ)..1, Real.exp a * D2f (x + τ' • s) v v :=
        intervalIntegral.integral_mono_on zero_le_one hint
          (intervalIntegrable_const (μ := MeasureTheory.volume))
          (fun τ hτ => hb v τ hτ τ' hτ')
    _ = Real.exp a * D2f (x + τ' • s) v v := by simp

lemma le_segQ (hSC : SelfConcordantOn D f Df D2f D3f) {x s : Vec d}
    (hseg : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • s ∈ D) {a : ℝ} (hb : SegBound D2f x s a)
    {τ' : ℝ} (hτ' : τ' ∈ Icc (0 : ℝ) 1) (v : Vec d) :
    D2f (x + τ' • s) v v ≤ Real.exp a * (v ⬝ᵥ (segQ D2f x s *ᵥ v)) := by
  rw [segQ_quad hSC hseg]
  have hint := (cont_D2f hSC hseg v v).intervalIntegrable_of_Icc (μ := MeasureTheory.volume)
    zero_le_one
  have : ∫ _τ in (0 : ℝ)..1, D2f (x + τ' • s) v v ≤
      ∫ τ in (0 : ℝ)..1, Real.exp a * D2f (x + τ • s) v v :=
    intervalIntegral.integral_mono_on zero_le_one
      (intervalIntegrable_const (μ := MeasureTheory.volume))
      (hint.const_mul _) (fun τ hτ => hb v τ' hτ' τ hτ)
  simpa [intervalIntegral.integral_const_mul] using this

lemma segQ_posDef (hSC : SelfConcordantOn D f Df D2f D3f) (hD : IsOpen D) {x s : Vec d}
    (hseg : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • s ∈ D) {a : ℝ} (hb : SegBound D2f x s a) :
    (segQ D2f x s).PosDef := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v hv => ?_⟩
  · ext i j
    simp only [conjTranspose_apply, star_trivial, segQ, Matrix.of_apply]
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [uIcc_of_le zero_le_one] at hτ
    exact hess_symm hSC hD (hseg τ hτ) _ _
  · simp only [star_trivial]
    have h1 := le_segQ hSC hseg hb h0 v
    have h2 : 0 < D2f (x + (0 : ℝ) • s) v v := hSC.2.2.2.1 _ (hseg 0 h0) v hv
    have := Real.exp_pos a
    nlinarith

lemma segQ_mulVec (hSC : SelfConcordantOn D f Df D2f D3f) (hD : IsOpen D) {x s g g' : Vec d}
    (hseg : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • s ∈ D) (hg : ∀ w, Df x w = g ⬝ᵥ w)
    (hg' : ∀ w, Df (x + s) w = g' ⬝ᵥ w) : segQ D2f x s *ᵥ s = g' - g := by
  ext i
  have hq := segQ_quad hSC hseg (Pi.single i 1) s
  have hl : Pi.single i 1 ⬝ᵥ (segQ D2f x s *ᵥ s) = (segQ D2f x s *ᵥ s) i := by
    simp [dotProduct, Pi.single_apply]
  rw [← hl, hq]
  have hsym : ∀ τ ∈ uIcc (0 : ℝ) 1, D2f (x + τ • s) (Pi.single i 1) s =
      D2f (x + τ • s) s (Pi.single i 1) := fun τ hτ => by
    rw [uIcc_of_le zero_le_one] at hτ
    exact hess_symm hSC hD (hseg τ hτ) _ _
  rw [intervalIntegral.integral_congr hsym]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun τ : ℝ => Df (x + τ • s) (Pi.single i 1))
    (fun τ hτ => by
      rw [uIcc_of_le zero_le_one] at hτ
      exact deriv_Df hSC (hseg τ hτ) _)
    ((cont_D2f hSC hseg s (Pi.single i 1)).intervalIntegrable_of_Icc zero_le_one)]
  simp only [one_smul, zero_smul, add_zero, hg, hg', Pi.sub_apply]
  simp [dotProduct, Pi.single_apply]

lemma seg_mem (hconv : Convex ℝ D) {x y : Vec d} (hx : x ∈ D) (hy : y ∈ D) :
    ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • (y - x) ∈ D := fun τ hτ => by
  have := hconv.add_smul_sub_mem hx hy hτ
  simpa using this

lemma hinv_zero_eq {x s : Vec d} :
    hinv (fun τ => D2f (x + τ • s) s s) 0 = 1 / √(D2f x s s) := by
  simp [hinv]

lemma first_order (hSC : SelfConcordantOn D f Df D2f D3f) (hconv : Convex ℝ D) {x y : Vec d}
    (hx : x ∈ D) (hy : y ∈ D) : f x + Df x (y - x) ≤ f y := by
  by_cases hxy : y - x = 0
  · have : y = x := sub_eq_zero.mp hxy
    subst this; simp
  have S := restrict_SC1 hSC (seg_mem hconv hx hy) hxy
  have h := convex_tangent S ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simpa using h

lemma quad_eq {x : Vec d} (v : Vec d) :
    (D2f x) v v = v ⬝ᵥ (hessMatrix (D2f x) *ᵥ v) := bilin_expand _ v v

lemma gap_of_decrement (hSC : SelfConcordantOn D f Df D2f D3f) (hD : IsOpen D)
    (hconv : Convex ℝ D) {x y g : Vec d} (hx : x ∈ D) (hy : y ∈ D)
    (hg : ∀ w, Df x w = g ⬝ᵥ w) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlam : g ⬝ᵥ ((hessMatrix (D2f x))⁻¹ *ᵥ g) ≤ lam ^ 2) (hlam8 : lam ≤ 1 / 8) :
    f x - 2 * lam ^ 2 ≤ f y := by
  set u := y - x with hu
  by_cases hu0 : u = 0
  · have : y = x := by rw [← sub_eq_zero]; exact hu0
    subst this; nlinarith
  have hH := hessMatrix_posDef hSC hD hx
  have hseg := seg_mem hconv hx hy
  have S := restrict_SC1 hSC hseg hu0
  have hpos : 0 < D2f x u u := hSC.2.2.2.1 x hx u hu0
  set r := √(D2f x u u) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hpos
  have hrr : r ^ 2 = D2f x u u := Real.sq_sqrt hpos.le
  have hcs : (g ⬝ᵥ u) ^ 2 ≤ lam ^ 2 * r ^ 2 := by
    have h := cs_posDef hH ((hessMatrix (D2f x))⁻¹ *ᵥ g) u
    have e1 : ((hessMatrix (D2f x))⁻¹ *ᵥ g) ⬝ᵥ (hessMatrix (D2f x) *ᵥ u) = g ⬝ᵥ u := by
      rw [← symm_dot (posDef_symm hH), mulVec_inv_mulVec hH]
    have e2 : ((hessMatrix (D2f x))⁻¹ *ᵥ g) ⬝ᵥ (hessMatrix (D2f x) *ᵥ
        ((hessMatrix (D2f x))⁻¹ *ᵥ g)) = g ⬝ᵥ ((hessMatrix (D2f x))⁻¹ *ᵥ g) := by
      rw [mulVec_inv_mulVec hH, dotProduct_comm]
    rw [e1, e2, ← quad_eq u, ← hrr] at h
    have : 0 ≤ r ^ 2 := sq_nonneg r
    nlinarith
  have hgu : -(lam * r) ≤ g ⬝ᵥ u := by nlinarith [mul_nonneg hlam0 hr0.le]
  have hφ0 : (fun τ => f (x + τ • u)) 0 = f x := by simp
  have hφ10 : (fun τ => Df (x + τ • u) u) 0 = g ⬝ᵥ u := by simp [hg]
  have hh0 : hinv (fun τ => D2f (x + τ • u) u u) 0 = 1 / r := hinv_zero_eq
  have hlow : ∀ τ ∈ Icc (0 : ℝ) 1, 1 / (1 / r + τ) ^ 2 ≤ D2f (x + τ • u) u u := fun τ hτ => by
    have := hinv_lip_up S ⟨le_rfl, zero_le_one⟩ hτ hτ.1
    rw [hh0, sub_zero] at this
    exact psi_ge_of_hinv S hτ this
  rcases le_or_gt r 1 with hr1 | hr1
  · have hm : ∀ τ ∈ Icc (0 : ℝ) 1, r ^ 2 / 4 ≤ D2f (x + τ • u) u u := fun τ hτ => by
      refine le_trans ?_ (hlow τ hτ)
      have hir : 0 < 1 / r := by positivity
      have hp : 0 < 1 / r + τ := by linarith [hτ.1]
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      have : (1 / r + τ) * r ≤ 2 := by
        rw [add_mul, one_div, inv_mul_cancel₀ hr0.ne']; nlinarith [hτ.2]
      have h1 : 0 ≤ (1 / r + τ) * r := by positivity
      nlinarith
    have h := second_order_lower S zero_le_one hm
    simp only [sub_zero, one_pow, mul_one, one_smul, zero_smul, add_zero, hg] at h
    have : f x + -(lam * r) + r ^ 2 / 4 / 2 ≤ f y := by
      have hy' : x + u = y := by rw [hu]; abel
      rw [hy'] at h; linarith
    nlinarith [sq_nonneg (r - 4 * lam)]
  · set τ0 := 1 / r with hτ0
    have hτ0pos : 0 < τ0 := by positivity
    have hτ01 : τ0 ≤ 1 := by rw [hτ0, div_le_one hr0]; linarith
    have hτ0m : τ0 ∈ Icc (0 : ℝ) 1 := ⟨hτ0pos.le, hτ01⟩
    have S0 := S.mono (Icc_subset_Icc le_rfl hτ01)
    have hm : ∀ τ ∈ Icc (0 : ℝ) τ0, r ^ 2 / 4 ≤ D2f (x + τ • u) u u := fun τ hτ => by
      refine le_trans ?_ (hlow τ ⟨hτ.1, hτ.2.trans hτ01⟩)
      have hp : 0 < 1 / r + τ := by linarith [hτ.1]
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      have : (1 / r + τ) * r ≤ 2 := by
        have : τ * r ≤ 1 := by
          have := mul_le_mul_of_nonneg_right hτ.2 hr0.le
          rw [hτ0, one_div, inv_mul_cancel₀ hr0.ne'] at this; exact this
        rw [add_mul, one_div, inv_mul_cancel₀ hr0.ne']; linarith
      have h1 : 0 ≤ (1 / r + τ) * r := by positivity
      nlinarith
    have h := second_order_lower S0 hτ0pos.le hm
    simp only [sub_zero, zero_smul, add_zero, hg] at h
    have hgτ : (g ⬝ᵥ u) * τ0 ≥ -lam := by
      have : (g ⬝ᵥ u) * τ0 ≥ -(lam * r) * τ0 := mul_le_mul_of_nonneg_right hgu hτ0pos.le
      have e : -(lam * r) * τ0 = -lam := by rw [hτ0]; field_simp
      linarith
    have hsq : r ^ 2 / 4 / 2 * τ0 ^ 2 = 1 / 8 := by rw [hτ0]; field_simp; ring
    have hφτ0 : f x ≤ f (x + τ0 • u) := by nlinarith
    have t1 := convex_tangent S hτ0m ⟨zero_le_one, le_rfl⟩ hτ01
    have t2 := tangent_left S ⟨le_rfl, zero_le_one⟩ hτ0m hτ0pos.le
    simp only [zero_smul, add_zero, sub_zero, one_smul] at t1 t2
    have hslope : 0 ≤ Df (x + τ0 • u) u := by
      by_contra hneg
      push Not at hneg
      have : 0 < Df (x + τ0 • u) u * τ0 := by nlinarith
      nlinarith
    have hy' : x + u = y := by rw [hu]; abel
    rw [hy'] at t1
    nlinarith [mul_nonneg hslope (by linarith : (0 : ℝ) ≤ 1 - τ0)]

lemma upper_on_dikin (hSC : SelfConcordantOn D f Df D2f D3f) {x u : Vec d} {b : ℝ}
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (hseg : ∀ τ ∈ Icc (0 : ℝ) b, x + τ • u ∈ D) (hu : u ≠ 0)
    (hr : D2f x u u ≤ 1 / 4) :
    f (x + b • u) ≤ f x + b * Df x u + b ^ 2 / 2 := by
  have S := restrict_SC1 hSC hseg hu
  have hpos : 0 < D2f x u u := hSC.2.2.2.1 x (by simpa using hseg 0 ⟨le_rfl, hb⟩) u hu
  have hh0 : hinv (fun τ => D2f (x + τ • u) u u) 0 = 1 / √(D2f x u u) := hinv_zero_eq
  have hr2 : 2 ≤ 1 / √(D2f x u u) := by
    have hs : √(D2f x u u) ≤ 1 / 2 := by
      rw [show (1 / 2 : ℝ) = √(1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hr
    have hs0 : 0 < √(D2f x u u) := Real.sqrt_pos.mpr hpos
    rw [le_div_iff₀ hs0]; linarith
  have hM : ∀ τ ∈ Icc (0 : ℝ) b, D2f (x + τ • u) u u ≤ 1 := fun τ hτ => by
    have := hinv_lip_down S ⟨le_rfl, hb⟩ hτ hτ.1
    rw [hh0, sub_zero] at this
    have h1 : 1 ≤ hinv (fun τ => D2f (x + τ • u) u u) τ := by linarith [hτ.2]
    have := psi_le_of_hinv S hτ zero_lt_one h1
    simpa using this
  have h := second_order_upper S hb hM
  simp only [sub_zero, zero_smul, add_zero] at h
  linarith

lemma dikin (hSC : SelfConcordantOn D f Df D2f D3f) (hD : IsOpen D) {x u : Vec d}
    (hx : x ∈ D) (hr : D2f x u u ≤ 1 / 4) : x + u ∈ D := by
  by_cases hu : u = 0
  · subst hu; simpa using hx
  by_contra hout
  set T := {τ : ℝ | τ ∈ Icc (0 : ℝ) 1 ∧ x + τ • u ∉ D} with hT
  have hcontγ : Continuous (fun τ : ℝ => x + τ • u) := by fun_prop
  have hTc : IsClosed T := isClosed_Icc.inter (hD.isClosed_compl.preimage hcontγ)
  have h1T : (1 : ℝ) ∈ T := ⟨⟨zero_le_one, le_rfl⟩, by simpa using hout⟩
  have hTne : T.Nonempty := ⟨1, h1T⟩
  have hTbdd : BddBelow T := ⟨0, fun τ hτ => hτ.1.1⟩
  set τs := sInf T with hτs
  have hτsT : τs ∈ T := hTc.csInf_mem hTne hTbdd
  have hbefore : ∀ τ ∈ Icc (0 : ℝ) τs, τ < τs → x + τ • u ∈ D := fun τ hτ hlt => by
    by_contra hc
    have : τ ∈ T := ⟨⟨hτ.1, hτ.2.trans hτsT.1.2⟩, hc⟩
    have := csInf_le hTbdd this
    linarith
  have hτs0 : 0 < τs := by
    rcases hτsT.1.1.eq_or_lt with h | h
    · exfalso; apply hτsT.2; rw [← h]; simpa using hx
    · exact h
  set c := f x + |Df x u| + 1 with hc
  have hbound : ∀ τ ∈ Icc (0 : ℝ) τs, τ < τs → x + τ • u ∈ {y | y ∈ D ∧ f y ≤ c} := by
    intro τ hτ hlt
    refine ⟨hbefore τ hτ hlt, ?_⟩
    have hseg : ∀ σ ∈ Icc (0 : ℝ) τ, x + σ • u ∈ D := fun σ hσ =>
      hbefore σ ⟨hσ.1, hσ.2.trans hτ.2⟩ (lt_of_le_of_lt hσ.2 hlt)
    have hτ1 : τ ≤ 1 := hτ.2.trans hτsT.1.2
    have := upper_on_dikin hSC hτ.1 hτ1 hseg hu hr
    have h1 : τ * Df x u ≤ |Df x u| := by
      calc τ * Df x u ≤ τ * |Df x u| := mul_le_mul_of_nonneg_left (le_abs_self _) hτ.1
        _ ≤ 1 * |Df x u| := mul_le_mul_of_nonneg_right hτ1 (abs_nonneg _)
        _ = |Df x u| := one_mul _
    have h2 : τ ^ 2 / 2 ≤ 1 := by nlinarith [hτ.1]
    linarith
  have hlim : Filter.Tendsto (fun τ : ℝ => x + τ • u) (nhdsWithin τs (Iio τs))
      (nhds (x + τs • u)) := (hcontγ.tendsto τs).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ τ in nhdsWithin τs (Iio τs), x + τ • u ∈ {y | y ∈ D ∧ f y ≤ c} := by
    filter_upwards [Ioo_mem_nhdsLT hτs0] with τ hτ
    exact hbound τ ⟨hτ.1.le, hτ.2.le⟩ hτ.2
  have hmem := (hSC.2.2.2.2.2 c).mem_of_tendsto hlim hev
  exact hτsT.2 hmem.1

lemma decrement_bound (hSC : SelfConcordantOn D f Df D2f D3f) (hD : IsOpen D) {x g : Vec d}
    (hx : x ∈ D) (hg : ∀ w, Df x w = g ⬝ᵥ w) {Δ : ℝ} (hΔ : ∀ y ∈ D, f x - Δ ≤ f y) :
    g ⬝ᵥ ((hessMatrix (D2f x))⁻¹ *ᵥ g) ≤ (2 * Δ + 1) ^ 2 := by
  have hH := hessMatrix_posDef hSC hD hx
  set Λ := g ⬝ᵥ ((hessMatrix (D2f x))⁻¹ *ᵥ g) with hΛ
  have hΛ0 : 0 ≤ Λ := posDef_quad_nonneg hH.inv g
  rcases hΛ0.eq_or_lt with h0 | hpos
  · rw [← h0]
    have := hΔ x hx
    nlinarith
  set l := √Λ with hl
  have hl0 : 0 < l := Real.sqrt_pos.mpr hpos
  have hll : l ^ 2 = Λ := Real.sq_sqrt hpos.le
  set u := (-(1 / (2 * l))) • ((hessMatrix (D2f x))⁻¹ *ᵥ g) with hu
  have hHw : hessMatrix (D2f x) *ᵥ ((hessMatrix (D2f x))⁻¹ *ᵥ g) = g := mulVec_inv_mulVec hH g
  have hquad : D2f x u u = 1 / 4 := by
    rw [quad_eq, hu, mulVec_smul, hHw, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, dotProduct_comm, ← hΛ, ← hll]
    field_simp; ring
  have hlin : Df x u = -(l / 2) := by
    rw [hg, hu, dotProduct_smul, smul_eq_mul, ← hΛ, ← hll]
    field_simp
  have hu0 : u ≠ 0 := by
    intro h0
    have := hquad
    rw [h0] at this; simp at this
  have hmem := dikin hSC hD hx (le_of_eq hquad)
  have hseg : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • u ∈ D := fun τ hτ => by
    have h := dikin hSC hD hx (u := τ • u) (by
      simp only [map_smul, _root_.smul_apply, smul_eq_mul, hquad]
      nlinarith [hτ.1, hτ.2])
    exact h
  have hup := upper_on_dikin hSC zero_le_one le_rfl hseg hu0 (le_of_eq hquad)
  simp only [one_smul, one_mul, one_pow] at hup
  have := hΔ _ hmem
  rw [hlin] at hup
  have hl : l ≤ 2 * Δ + 1 := by linarith
  calc Λ = l ^ 2 := hll.symm
    _ ≤ (2 * Δ + 1) ^ 2 := pow_le_pow_left₀ hl0.le hl 2

end LongTails.Proofs.SelfConcordantSegment
