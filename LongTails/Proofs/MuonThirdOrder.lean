import LongTails.Proofs.MuonExecution
import LongTails.Setups.MuonThirdOrder
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.Muon

variable {m n : ℕ}

theorem hessian_diff_bound (f : Mat m n → ℝ) (s : ℝ)
    (hd3 : Differentiable ℝ (iteratedFDeriv ℝ 2 f))
    (h : ∀ W U V X, |iteratedFDeriv ℝ 3 f W ![U, V, X]| ≤ s * ‖U‖ * ‖V‖ * ‖X‖)
    (W D : Mat m n) (τ : ℝ) (hτ : 0 ≤ τ) :
    |fderiv ℝ (fderiv ℝ f) (W + τ • D) D D - fderiv ℝ (fderiv ℝ f) W D D| ≤ s * ‖D‖ ^ 3 * τ := by
  set G := iteratedFDeriv ℝ 2 f
  have hline : ∀ u : ℝ, HasDerivAt (fun u : ℝ => W + u • D) D u := fun u => by
    simpa using ((hasDerivAt_id u).smul_const D).const_add W
  have hg : ∀ u, HasDerivAt (fun u : ℝ => G (W + u • D) ![D, D])
      (iteratedFDeriv ℝ 3 f (W + u • D) ![D, D, D]) u := by
    intro u
    have hc := (hd3 (W + u • D)).hasFDerivAt.comp_hasDerivAt u (hline u)
    have he := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Mat m n) ℝ ![D, D]).hasFDerivAt.comp_hasDerivAt u hc
    have e : iteratedFDeriv ℝ 3 f (W + u • D) ![D, D, D] = fderiv ℝ G (W + u • D) D ![D, D] := by
      rw [iteratedFDeriv_succ_apply_left]
      rfl
    rw [e]
    exact he
  have hb := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun u : ℝ => G (W + u • D) ![D, D])
    (a := 0) (b := τ) (C := s * ‖D‖ ^ 3) (fun u _ => (hg u).hasDerivWithinAt)
    (fun u _ => by
      rw [Real.norm_eq_abs]
      have := h (W + u • D) D D D
      calc _ ≤ s * ‖D‖ * ‖D‖ * ‖D‖ := this
        _ = s * ‖D‖ ^ 3 := by ring) τ (Set.right_mem_Icc.2 hτ)
  simp only [zero_smul, add_zero, sub_zero, Real.norm_eq_abs] at hb
  have e2 : ∀ y, G y ![D, D] = fderiv ℝ (fderiv ℝ f) y D D := fun y => by
    rw [iteratedFDeriv_two_apply]
    rfl
  rw [e2, e2] at hb
  exact hb

theorem taylor_third (f : Mat m n → ℝ) (s : ℝ) (hd1 : Differentiable ℝ f)
    (hd2 : Differentiable ℝ (fderiv ℝ f)) (hd3 : Differentiable ℝ (iteratedFDeriv ℝ 2 f))
    (h : ∀ W U V X, |iteratedFDeriv ℝ 3 f W ![U, V, X]| ≤ s * ‖U‖ * ‖V‖ * ‖X‖) (W D : Mat m n) :
    f (W + D) ≤ f W + fderiv ℝ f W D + fderiv ℝ (fderiv ℝ f) W D D / 2 + s * ‖D‖ ^ 3 / 6 := by
  set F1 := fderiv ℝ f
  set F2 := fderiv ℝ F1
  set c := s * ‖D‖ ^ 3
  have hline : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => W + τ • D) D τ := fun τ => by
    simpa using ((hasDerivAt_id τ).smul_const D).const_add W
  have h1 : ∀ τ, HasDerivAt (fun τ : ℝ => f (W + τ • D)) (F1 (W + τ • D) D) τ := fun τ =>
    (hd1 (W + τ • D)).hasFDerivAt.comp_hasDerivAt τ (hline τ)
  have h2 : ∀ τ, HasDerivAt (fun τ : ℝ => F1 (W + τ • D) D) (F2 (W + τ • D) D D) τ := by
    intro τ
    have hc := (hd2 (W + τ • D)).hasFDerivAt.comp_hasDerivAt τ (hline τ)
    have := hc.clm_apply (hasDerivAt_const τ D)
    simpa using this
  let ψ : ℝ → ℝ := fun τ => F1 (W + τ • D) D - F1 W D - τ * F2 W D D - c * τ ^ 2 / 2
  have hψ : ∀ τ, HasDerivAt ψ (F2 (W + τ • D) D D - 1 * F2 W D D - c * (2 * τ) / 2) τ := by
    intro τ
    have := (((h2 τ).sub_const (F1 W D)).sub ((hasDerivAt_id τ).mul_const (F2 W D D))).sub
      (((hasDerivAt_pow 2 τ).const_mul c).div_const 2)
    convert this using 1
    · rfl
    · simp
  have hψle : ∀ τ ∈ Set.Icc (0 : ℝ) 1, F2 (W + τ • D) D D - 1 * F2 W D D - c * (2 * τ) / 2 ≤ 0 := by
    intro τ hτ
    have hl := hessian_diff_bound f s hd3 h W D τ hτ.1
    have : c * (2 * τ) / 2 = s * ‖D‖ ^ 3 * τ := by simp only [c]; ring
    linarith [le_abs_self (F2 (W + τ • D) D D - F2 W D D)]
  have hψanti : AntitoneOn ψ (Set.Icc 0 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
      (fun τ _ => (hψ τ).continuousAt.continuousWithinAt) (fun τ _ => (hψ τ).hasDerivWithinAt)
      (fun τ hτ => hψle τ (Set.Ioo_subset_Icc_self (by rwa [interior_Icc] at hτ)))
  have hψ0 : ψ 0 = 0 := by simp [ψ]
  let φ : ℝ → ℝ := fun τ => f (W + τ • D) - τ * F1 W D - τ ^ 2 / 2 * F2 W D D - c * τ ^ 3 / 6
  have hφ : ∀ τ, HasDerivAt φ (F1 (W + τ • D) D - 1 * F1 W D - (2 * τ) / 2 * F2 W D D - c * (3 * τ ^ 2) / 6) τ := by
    intro τ
    have := ((((h1 τ).sub ((hasDerivAt_id τ).mul_const (F1 W D))).sub
      (((hasDerivAt_pow 2 τ).div_const 2).mul_const (F2 W D D))).sub
      (((hasDerivAt_pow 3 τ).const_mul c).div_const 6))
    convert this using 1
    · rfl
    · simp
  have hφanti : AntitoneOn φ (Set.Icc 0 1) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
      (fun τ _ => (hφ τ).continuousAt.continuousWithinAt) (fun τ _ => (hφ τ).hasDerivWithinAt)
      (fun τ hτ => ?_)
    rw [interior_Icc] at hτ
    have hle := hψanti (Set.left_mem_Icc.2 zero_le_one) (Set.Ioo_subset_Icc_self hτ) hτ.1.le
    rw [hψ0] at hle
    have : F1 (W + τ • D) D - 1 * F1 W D - (2 * τ) / 2 * F2 W D D - c * (3 * τ ^ 2) / 6 = ψ τ := by
      simp only [ψ]; ring
    linarith
  have := hφanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  have e0 : φ 0 = f W := by simp [φ]
  have e1 : φ 1 = f (W + D) - F1 W D - F2 W D D / 2 - c / 6 := by simp only [φ, one_smul]; ring
  rw [e0, e1] at this
  simp only [c] at this
  linarith

theorem exists_le_of_average_le (T : ℕ) (hT : 1 ≤ T) (a : Fin T → ℝ) (ε : ℝ)
    (h : (1 / (T : ℝ)) * ∑ t, a t ≤ ε) : ∃ t, a t ≤ ε := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hne : (Finset.univ : Finset (Fin T)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hs : ∑ t, a t ≤ ∑ _t : Fin T, ε := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hTpos] at h
    linarith
  obtain ⟨t, -, ht⟩ := Finset.exists_le_of_sum_le hne hs
  exact ⟨t, ht⟩

theorem fderiv_eq_inner_gradient (f : Mat m n → ℝ) (W P : Mat m n) :
    fderiv ℝ f W P = ⟪gradient f W, P⟫ := by
  change fderiv ℝ f W P = (inner ℝ ((InnerProductSpace.toDual ℝ (Mat m n)).symm (fderiv ℝ f W)) (P))
  rw [InnerProductSpace.toDual_symm_apply]

theorem third_step (f : Mat m n → ℝ) (s η : ℝ) (hs : 0 ≤ s) (hη : 0 ≤ η)
    (hf : LongTails.Setups.MuonThirdOrder.ThirdDerivativeBounded s f) (W : Mat m n) :
    f (W - η • orthogonalize (gradient f W)) ≤ f W - η * nuclearNorm (gradient f W) +
      η ^ 2 * LongTails.Setups.MuonThirdOrder.hessianQuadratic f W / 2 +
      s * η ^ 3 * (((min m n : ℕ) : ℝ) * Real.sqrt ((min m n : ℕ) : ℝ)) / 6 := by
  obtain ⟨hd1, hd2, hd3, h⟩ := hf
  set P := orthogonalize (gradient f W)
  have ht := taylor_third f s hd1 hd2 hd3 h W (-(η • P))
  rw [← sub_eq_add_neg] at ht
  have e1 : fderiv ℝ f W (-(η • P)) = -(η * nuclearNorm (gradient f W)) := by
    rw [map_neg, map_smul, fderiv_eq_inner_gradient, inner_orthogonalize, smul_eq_mul]
  have e2 : fderiv ℝ (fderiv ℝ f) W (-(η • P)) (-(η • P)) =
      η ^ 2 * LongTails.Setups.MuonThirdOrder.hessianQuadratic f W := by
    have hq : LongTails.Setups.MuonThirdOrder.hessianQuadratic f W = fderiv ℝ (fderiv ℝ f) W P P := by
      change iteratedFDeriv ℝ 2 f W ![P, P] = _
      rw [iteratedFDeriv_two_apply]
      rfl
    rw [hq]
    simp
    ring
  have hP : ‖P‖ ≤ Real.sqrt ((min m n : ℕ) : ℝ) := by
    rw [Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg _)]; exact norm_orthogonalize_sq_le _
  have e3 : ‖-(η • P)‖ ^ 3 ≤ η ^ 3 * (((min m n : ℕ) : ℝ) * Real.sqrt ((min m n : ℕ) : ℝ)) := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη, mul_pow]
    have hr := Real.mul_self_sqrt (Nat.cast_nonneg (min m n) : (0:ℝ) ≤ ((min m n : ℕ) : ℝ))
    have h3 : ‖P‖ ^ 3 ≤ Real.sqrt ((min m n : ℕ) : ℝ) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hP 3
    have : Real.sqrt ((min m n : ℕ) : ℝ) ^ 3 = ((min m n : ℕ) : ℝ) * Real.sqrt ((min m n : ℕ) : ℝ) := by
      rw [pow_succ, sq, hr]
    rw [← this]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  rw [e1, e2] at ht
  nlinarith [mul_le_mul_of_nonneg_left e3 hs]

end OracleTemplate.Muon

namespace OracleTemplate.MuonThirdOrder

open Muon LongTails.Setups.MuonThirdOrder

theorem guarantee (p : Params) (hp : spec.valid p) (f : Mat p.m p.n → ℝ)
    (hf : ThirdDerivativeBounded p.s f) (hb : BddBelow (Set.range f)) :
    Guarantee p f (fun j : Fin (p.T + 1) => SimplifiedMuon.trajectory (publicInput p) (gradient f) j) := by
  obtain ⟨hm, hn, hs, hη, hT⟩ := hp
  set W : ℕ → Mat p.m p.n := fun t => SimplifiedMuon.trajectory (publicInput p) (gradient f) t
  set r : ℝ := ((min p.m p.n : ℕ) : ℝ)
  set T : ℝ := (p.T : ℝ)
  have hTpos : 0 < T := Nat.cast_pos.mpr (by omega)
  have hsucc : ∀ t, W (t + 1) = W t - p.η • orthogonalize (gradient f (W t)) := fun t =>
    Function.iterate_succ_apply' _ _ _
  have hW0 : W 0 = p.W0 := rfl
  set c : ℝ := p.s * p.η ^ 3 * (r * Real.sqrt r) / 6
  have hstep : ∀ t, p.η * nuclearNorm (gradient f (W t)) ≤ f (W t) - f (W (t + 1)) +
      p.η ^ 2 * hessianQuadratic f (W t) / 2 + c := by
    intro t
    have := third_step f p.s p.η hs hη.le hf (W t)
    rw [← hsucc] at this
    have hc : c = p.s * p.η ^ 3 * (((min p.m p.n : ℕ) : ℝ) * Real.sqrt ((min p.m p.n : ℕ) : ℝ)) / 6 := rfl
    linarith
  have hsum := Finset.sum_le_sum (fun t (_ : t ∈ Finset.range p.T) => hstep t)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_range_sub' (fun t => f (W t)), ← Finset.sum_div, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hsum
  set A := ∑ t ∈ Finset.range p.T, nuclearNorm (gradient f (W t))
  set H := ∑ t ∈ Finset.range p.T, hessianQuadratic f (W t)
  have hA : (1 / T) * ∑ t : Fin p.T, nuclearNorm (gradient f (W t.castSucc)) = (1 / T) * A := by
    simp only [Fin.val_castSucc, A]
    rw [Fin.sum_univ_eq_sum_range (fun t => nuclearNorm (gradient f (W t))) p.T]
  have hH : (1 / T) * ∑ t : Fin p.T, hessianQuadratic f (W t.castSucc) = (1 / T) * H := by
    simp only [Fin.val_castSucc, H]
    rw [Fin.sum_univ_eq_sum_range (fun t => hessianQuadratic f (W t)) p.T]
  have hmain : (1 / T) * A ≤ (f (W 0) - f (W p.T)) / (T * p.η) + p.η * ((1 / T) * H) / 2 +
      p.s * p.η ^ 2 * (r * Real.sqrt r) / 6 := by
    have e : (f (W 0) - f (W p.T)) / (T * p.η) + p.η * ((1 / T) * H) / 2 +
        p.s * p.η ^ 2 * (r * Real.sqrt r) / 6 =
        (f (W 0) - f (W p.T) + p.η ^ 2 * H / 2 + T * c) / (T * p.η) := by
      simp only [c]; field_simp; try ring
    rw [e, le_div_iff₀ (mul_pos hTpos hη)]
    have : 1 / T * A * (T * p.η) = p.η * A := by field_simp
    rw [this]
    linarith
  set Δ := f p.W0 - ⨅ W, f W
  have hgap : f (W 0) - f (W p.T) ≤ Δ := by
    have := ciInf_le hb (W p.T)
    rw [hW0]
    change f p.W0 - f (W p.T) ≤ f p.W0 - ⨅ W, f W
    linarith
  refine ⟨?_, ?_⟩
  · rw [hA, hH]
    exact hmain
  · intro hJ hηdef
    rw [hA]
    rw [hH] at hJ hηdef ⊢
    set J := (1 / T) * H
    have hΔ : 0 < Δ := by
      by_contra hc
      have : 2 * Δ / (J * T) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith [not_lt.mp hc]) (by positivity)
      rw [hηdef, Real.sqrt_eq_zero'.mpr this] at hη
      exact lt_irrefl _ hη
    have hη2 : p.η ^ 2 = 2 * Δ / (J * T) := by
      rw [hηdef, Real.sq_sqrt (by positivity)]
    have hk : p.η * J / 2 = Δ / (T * p.η) := by
      rw [eq_div_iff (by positivity)]
      have : p.η * J / 2 * (T * p.η) = p.η ^ 2 * J * T / 2 := by ring
      rw [this, hη2]; field_simp
    have hηJ : p.η * J = Real.sqrt (2 * J * Δ / T) := by
      rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
      have : p.η * J * (p.η * J) = p.η ^ 2 * J ^ 2 := by ring
      rw [this, hη2]; field_simp; try ring
    have hlast : p.s * p.η ^ 2 * (r * Real.sqrt r) / 6 = p.s * (r * Real.sqrt r) * Δ / (3 * J * T) := by
      rw [hη2]; field_simp; try ring
    have h1 : (f (W 0) - f (W p.T)) / (T * p.η) ≤ Δ / (T * p.η) :=
      div_le_div_of_nonneg_right hgap (by positivity)
    have hbound : (1 / T) * A ≤ Real.sqrt (2 * J * Δ / T) + p.s * (r * Real.sqrt r) * Δ / (3 * J * T) := by
      have : p.η * J / 2 + p.η * J / 2 = p.η * J := by ring
      linarith
    refine ⟨hbound, fun ε hε h8 h2 => ?_⟩
    have hq1 : Real.sqrt (2 * J * Δ / T) ≤ ε / 2 := by
      rw [Real.sqrt_le_left (by positivity), div_le_iff₀ hTpos]
      rw [div_le_iff₀ (by positivity)] at h8
      nlinarith
    have hq2 : p.s * (r * Real.sqrt r) * Δ / (3 * J * T) ≤ ε / 2 := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ (by positivity)] at h2
      nlinarith
    have havgε : (1 / T) * A ≤ ε := by linarith
    refine ⟨havgε, ?_⟩
    exact exists_le_of_average_le p.T hT (fun t => nuclearNorm (gradient f (W t.castSucc))) ε
      (hA.trans_le havgε)

end OracleTemplate.MuonThirdOrder
