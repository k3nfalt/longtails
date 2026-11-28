import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import LongTails.Proofs.BrightnessFirstFitForces

namespace LongTails.Proofs.BrightnessResolventTravel

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma solve_filter [FiniteDimensional ℝ E] (A C : E →ₗ[ℝ] E)
    (horth : ∀ w, ⟪A w,C w⟫ = 0) (hker : ∀ w, A w = 0 → C w = 0 → w = 0)
    (q p : ℝ) (hq : q ≠ 0) (hp : p ≠ 0) (u : E) :
    ∃ w, q • A w - p • C w = u := by
  let F := q • A - p • C
  suffices hinj : Function.Injective F from LinearMap.surjective_of_injective hinj u
  apply (LinearMap.ker_eq_bot.mp _)
  apply LinearMap.ker_eq_bot'.mpr
  intro w hw
  change q • A w - p • C w = 0 at hw
  have hn := norm_sub_sq_real (q • A w) (p • C w)
  rw [hw,norm_zero,zero_pow (by decide),real_inner_smul_left,real_inner_smul_right,horth,
    mul_zero,mul_zero,mul_zero,sub_zero] at hn
  have ha : q • A w = 0 := norm_eq_zero.mp (by nlinarith [sq_nonneg ‖p • C w‖])
  have hc : p • C w = 0 := by rw [ha,zero_sub,neg_eq_zero] at hw; exact hw
  exact hker w ((smul_eq_zero.mp ha).resolve_left hq) ((smul_eq_zero.mp hc).resolve_left hp)

lemma transported_margin (A C : E →ₗ[ℝ] E)
    (hskew : ∀ x y, ⟪A x,C y⟫ = -⟪C x,A y⟫) (q p : ℝ) (w z : E) :
    ⟪q • A w,q • A z + p • C z⟫ = q*⟪q • A w - p • C w,A z⟫ := by
  simp only [inner_add_right,inner_sub_left,real_inner_smul_left,real_inner_smul_right,hskew]
  ring

lemma norm_transport (u v a : E) (p : ℝ) (he : u + p • v = a) (ho : ⟪u,v⟫ = 0) :
    ‖u‖ ≤ ‖a‖ := by
  have H := norm_add_sq_real u (p • v)
  rw [he,real_inner_smul_right,ho,mul_zero,mul_zero,add_zero] at H
  nlinarith only [H,sq_nonneg ‖p • v‖,norm_nonneg u,norm_nonneg a]

lemma displacement (u v u' v' a : E) (p r : ℝ)
    (hp : u+p • v = a) (hr : u'+r • v' = a)
    (ho : ⟪u,v⟫ = 0) (ho' : ⟪u',v'⟫ = 0) (hskew : ⟪u,v'⟫ = -⟪v,u'⟫) :
    (p+r)*‖u-u'‖^2 = (p-r)*(‖u'‖^2-‖u‖^2) := by
  have eqA := congrArg (inner ℝ u) (hp.trans hr.symm)
  have eqB := congrArg (inner ℝ u') (hp.trans hr.symm)
  simp only [inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq,ho,ho',mul_zero,
    add_zero,real_inner_comm u' u,real_inner_comm u' v,hskew] at eqA eqB
  rw [norm_sub_sq_real, real_inner_comm u' u]
  linear_combination 2*p*eqA - 2*r*eqB

lemma step_travel (u v u' v' a : E) {p r : ℝ} (hr₀ : 0 < r) (hrp : r ≤ p)
    (hp : u+p • v = a) (hr : u'+r • v' = a)
    (ho : ⟪u,v⟫ = 0) (ho' : ⟪u',v'⟫ = 0) (hskew : ⟪u,v'⟫ = -⟪v,u'⟫) :
    ‖u-u'‖^2 ≤ (Real.log p-Real.log r)*(‖u'‖^2-‖u‖^2) := by
  have H := displacement u v u' v' a p r hp hr ho ho' hskew
  obtain he | hlt := eq_or_lt_of_le hrp
  · subst p
    simp only [sub_self,zero_mul] at H ⊢
    nlinarith only [H,hr₀,sq_nonneg ‖u-u'‖,mul_self_pos.mpr (show r ≠ 0 by positivity)]
  have hn : 0 ≤ ‖u'‖^2-‖u‖^2 := by
    by_contra! h
    linarith only [H,mul_neg_of_pos_of_neg (sub_pos.mpr hlt) h,
      mul_nonneg (add_nonneg (hr₀.le.trans hrp) hr₀.le) (sq_nonneg ‖u-u'‖)]
  have hp₀ := hr₀.trans hlt
  have hratio : 0 < r/p := div_pos hr₀ hp₀
  have hlog := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div hr₀.ne' hp₀.ne'] at hlog
  have he : (p-r)/p ≤ Real.log p-Real.log r := by
    rw [sub_div,div_self hp₀.ne']
    linarith
  apply le_trans _ (mul_le_mul_of_nonneg_right he hn)
  rw [div_mul_eq_mul_div,le_div_iff₀ hp₀]
  nlinarith only [H,mul_nonneg hr₀.le (sq_nonneg ‖u-u'‖)]

lemma total_travel (u v : ℕ → E) (p : ℕ → ℝ) (a : E) (N : ℕ)
    (ha : ‖a‖ ≤ 1) (hpos : ∀ k ≤ N, 0 < p k)
    (hm : ∀ k < N, p (k+1) ≤ p k) (he : ∀ k ≤ N, u k+p k • v k = a)
    (ho : ∀ k ≤ N, ⟪u k,v k⟫ = 0)
    (hskew : ∀ k < N, ⟪u k,v (k+1)⟫ = -⟪v k,u (k+1)⟫) :
    (∑ k ∈ Finset.range N, ‖u k-u (k+1)‖)^2 ≤ Real.log (p 0)-Real.log (p N) := by
  let l k := Real.log (p k)-Real.log (p (k+1))
  let z k := ‖u (k+1)‖^2-‖u k‖^2
  have hl (k : ℕ) (hk : k < N) : 0 ≤ l k :=
    sub_nonneg.mpr (Real.log_le_log (hpos _ (by omega)) (hm _ hk))
  have hz (k : ℕ) (hk : k < N) : 0 ≤ z k := by
    let j := k+1
    have H := displacement _ _ _ _ _ _ _ (he k (by omega)) (he j (by dsimp [j]; omega))
      (ho k (by omega)) (ho j (by dsimp [j]; omega)) (hskew k hk)
    rcases eq_or_lt_of_le (hm k hk) with h | h
    · rw [h,sub_self,zero_mul] at H
      have hzero : u k-u j = 0 := norm_eq_zero.mp (by
        have hn := (mul_eq_zero.mp H).resolve_left (by have := hpos k (by omega); positivity)
        exact (sq_eq_zero_iff.mp hn))
      simp [z,sub_eq_zero.mp hzero,j]
    · by_contra! hneg
      have bad := mul_neg_of_pos_of_neg (sub_pos.mpr h) hneg
      exact (not_lt_of_ge (mul_nonneg (add_nonneg (hpos k (by omega)).le
        (hpos j (by dsimp [j]; omega)).le) (sq_nonneg _))) (H.trans_lt bad)
  have hrow (k : ℕ) (hk : k < N) : ‖u k-u (k+1)‖ ≤ Real.sqrt (l k)*Real.sqrt (z k) := by
    have HH := step_travel _ _ _ _ _ (hpos (k+1) (by omega)) (hm _ hk) (he k (by omega))
      (he (k+1) (by omega)) (ho k (by omega)) (ho (k+1) (by omega)) (hskew k hk)
    change _ ≤ l k*z k at HH
    rw [← Real.sqrt_mul (hl k hk)]
    exact (Real.le_sqrt (norm_nonneg _) (mul_nonneg (hl k hk) (hz k hk))).mpr HH
  have Hsum := Finset.sum_le_sum (s := Finset.range N)
    (fun k hk => hrow k (Finset.mem_range.mp hk))
  have Hsq := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) Hsum 2
  have Hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N) (fun k => Real.sqrt (l k))
    (fun k => Real.sqrt (z k))
  have hls : (∑ k ∈ Finset.range N, (Real.sqrt (l k))^2) = Real.log (p 0)-Real.log (p N) := by
    calc
      _ = ∑ k ∈ Finset.range N, l k := Finset.sum_congr rfl
        (fun k hk => Real.sq_sqrt (hl _ (Finset.mem_range.mp hk)))
      _ = _ := Finset.sum_range_sub' (fun k => Real.log (p k)) _
  have hzs : (∑ k ∈ Finset.range N, (Real.sqrt (z k))^2) = ‖u N‖^2-‖u 0‖^2 := by
    calc
      _ = ∑ k ∈ Finset.range N, z k := Finset.sum_congr rfl
        (fun k hk => Real.sq_sqrt (hz _ (Finset.mem_range.mp hk)))
      _ = _ := Finset.sum_range_sub (fun k => ‖u k‖^2) _
  have hnon : 0 ≤ Real.log (p 0)-Real.log (p N) := hls ▸ Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hn := (norm_transport _ _ _ _ (he N le_rfl) (ho N le_rfl)).trans ha
  rw [hls,hzs] at Hcs
  have hbound : ‖u N‖^2-‖u 0‖^2 ≤ 1 := by
    nlinarith only [pow_le_pow_left₀ (norm_nonneg (u N)) hn 2,sq_nonneg ‖u 0‖]
  exact (Hsq.trans Hcs).trans (by simpa using mul_le_mul_of_nonneg_left hbound hnon)

end LongTails.Proofs.BrightnessResolventTravel

namespace LongTails.Proofs.BrightnessFilterTransport

open scoped RealInnerProductSpace

open LongTails.Setups.BrightnessScaledTwoTap
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features shift)
open LongTails.Proofs.BrightnessScaledForces (shiftMap)
open LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding
open LongTails.Proofs.BrightnessResolventTravel

lemma transport (p : Params) (x : Images p) (G : Geometry p x) (hQ : p.Q ≠ 0)
    (sign : ℝ) (hs : sign ≠ 0) (r : ℕ → ℝ) (N : ℕ)
    (hr : ∀ k, 0 < r k) (hm : ∀ k < N, r (k+1) ≤ r k) :
    ∃ u : ℕ → Features p.d, (∀ k, ‖u k‖ ≤ 1) ∧
      (∀ k i, |p.Q| * p.γ ≤ ⟪u k,p.Q • contrast (x i)+(sign*r k) • smooth (x i)⟫) ∧
      (∑ k ∈ Finset.range N, ‖u k-u (k+1)‖)^2 ≤ Real.log (r 0)-Real.log (r N) := by
  classical
  let A : Features p.d →ₗ[ℝ] Features p.d := LinearMap.id - shiftMap p.d
  let C : Features p.d →ₗ[ℝ] Features p.d := sign • (LinearMap.id + shiftMap p.d)
  have skew (a b : Features p.d) : ⟪A a,C b⟫ = -⟪C a,A b⟫ := by
    change ⟪a-shift a,sign • (b+shift b)⟫ = -⟪sign • (a+shift a),b-shift b⟫
    simp only [real_inner_smul_left,real_inner_smul_right,inner_sub_right,inner_sub_left,
      inner_add_left,inner_add_right,inner_shift_shift]
    ring
  have orth (a : Features p.d) : ⟪A a,C a⟫ = 0 := by
    have H := skew a a
    rw [real_inner_comm (A a) (C a)] at H
    linarith
  have ker (a : Features p.d) (h : A a = 0) (h' : C a = 0) : a = 0 := by
    change a-shift a = 0 at h
    change sign • (a+shift a) = 0 at h'
    have hsum := (smul_eq_zero.mp h').resolve_left hs
    rw [← sub_eq_zero.mp h,← two_smul ℝ] at hsum
    exact (smul_eq_zero.mp hsum).resolve_left (by norm_num)
  obtain ⟨v,hv,hmargin⟩ := G.2.2.2
  let a := if p.Q < 0 then -v else v
  have ha : ‖a‖ ≤ 1 := by dsimp [a]; split_ifs <;> simp [hv]
  have hmargin' (i : Fin p.n) : |p.Q| * p.γ ≤ p.Q*⟪a,contrast (x i)⟫ := by
    dsimp [a]
    split_ifs with h
    · rw [abs_of_neg h,inner_neg_left]
      nlinarith only [mul_le_mul_of_nonpos_left (hmargin i) h.le]
    · rw [abs_of_nonneg (le_of_not_gt h)]
      exact mul_le_mul_of_nonneg_left (hmargin i) (le_of_not_gt h)
  choose w hw using fun k => solve_filter A C orth ker p.Q (r k) hQ (hr k).ne' a
  let u k := p.Q • A (w k)
  let v' k := -C (w k)
  have he (k : ℕ) : u k+r k • v' k = a := by simpa [u,v',sub_eq_add_neg] using hw k
  have ho (k : ℕ) : ⟪u k,v' k⟫ = 0 := by simp [u,v',real_inner_smul_left,orth]
  refine ⟨u,fun k => (norm_transport _ _ _ _ (he k) (ho k)).trans ha,?_,?_⟩
  · intro k i
    apply (hmargin' i).trans
    have H := transported_margin A C skew p.Q (r k) (w k) ((Real.sqrt 2)⁻¹ • centered (x i))
    rw [hw k] at H
    have hA : A ((Real.sqrt 2)⁻¹ • centered (x i)) = contrast (x i) := map_smul A _ _
    have hC : C ((Real.sqrt 2)⁻¹ • centered (x i)) = sign • smooth (x i) := by
      rw [map_smul]
      change (Real.sqrt 2)⁻¹ • (sign • (centered (x i)+shift (centered (x i)))) =
        sign • ((Real.sqrt 2)⁻¹ • (centered (x i)+shift (centered (x i))))
      exact smul_comm _ _ _
    rw [hA,hC,smul_smul,mul_comm (r k) sign] at H
    exact H.ge
  · apply total_travel u v' r a N ha (fun k _ => hr k) hm (fun k _ => he k) (fun k _ => ho k)
    intro k _
    simp only [u,v',inner_neg_left,inner_neg_right,real_inner_smul_left,real_inner_smul_right,
      skew,mul_neg,neg_neg]

end LongTails.Proofs.BrightnessFilterTransport
