import LongTails.Proofs.BirchResourceChainScalars
import LongTails.Setups.BirchSgd

namespace LongTails.Proofs.BirchResourceChain

open Finset
open OracleTemplate.Rennala (Point)
open LongTails.Proofs.BirchResourceChainScalars

def coord {D : ℕ} (x : Point D) (i : ℕ) : ℝ :=
  if h : i < D then x ⟨i, h⟩ else 0

noncomputable def basis {D : ℕ} (i : Fin D) : Point D := EuclideanSpace.single i 1

noncomputable def link {D : ℕ} (x : Point D) (i : ℕ) : ℝ :=
  gate (-coord x i) * payoff (-coord x (i + 1)) -
    gate (coord x i) * payoff (coord x (i + 1))

noncomputable def objective {D : ℕ} (x : Point D) : ℝ :=
  -payoff (coord x 0) + ∑ i ∈ range (D - 1), link x i

noncomputable def leftSlope {D : ℕ} (x : Point D) (i : ℕ) : ℝ :=
  -(gateSlope (-coord x i) * payoff (-coord x (i + 1))) -
    gateSlope (coord x i) * payoff (coord x (i + 1))

noncomputable def rightSlope {D : ℕ} (x : Point D) (i : ℕ) : ℝ :=
  -(gate (-coord x i) * payoffSlope (-coord x (i + 1))) -
    gate (coord x i) * payoffSlope (coord x (i + 1))

lemma left_nonpos {D : ℕ} (x : Point D) (i : ℕ) : leftSlope x i ≤ 0 := by
  unfold leftSlope
  linarith only [mul_nonneg (gateSlope_range (-coord x i)).1 (payoff_range (-coord x (i + 1))).1,
    mul_nonneg (gateSlope_range (coord x i)).1 (payoff_range (coord x (i + 1))).1]

lemma right_nonpos {D : ℕ} (x : Point D) (i : ℕ) : rightSlope x i ≤ 0 := by
  unfold rightSlope
  linarith only [mul_nonneg (gate_range (-coord x i)).1 (payoffSlope_range (-coord x (i + 1))).1,
    mul_nonneg (gate_range (coord x i)).1 (payoffSlope_range (coord x (i + 1))).1]

lemma right_lb {D : ℕ} (x : Point D) (i : ℕ)
    (hprev : 1 ≤ |coord x i|) (hnext : |coord x (i + 1)| ≤ 1) :
    rightSlope x i ≤ -(1 / 16) := by
  unfold rightSlope
  have hnext' : |-coord x (i + 1)| ≤ 1 := by simpa only [abs_neg] using hnext
  by_cases h : 0 ≤ coord x i
  · rw [abs_of_nonneg h] at hprev
    have ha := mul_le_mul (gate_lb hprev) (payoffSlope_lb hnext) (by norm_num)
      (gate_range _).1
    have hb := mul_nonneg (gate_range (-coord x i)).1 (payoffSlope_range (-coord x (i + 1))).1
    linarith only [ha, hb]
  · rw [abs_of_neg (lt_of_not_ge h)] at hprev
    have ha := mul_le_mul (gate_lb hprev) (payoffSlope_lb hnext') (by norm_num)
      (gate_range _).1
    have hb := mul_nonneg (gate_range (coord x i)).1 (payoffSlope_range (coord x (i + 1))).1
    linarith only [ha, hb]

lemma coord_diff {D : ℕ} (i : ℕ) : Differentiable ℝ (fun x : Point D => coord x i) := by
  by_cases h : i < D
  · have he : (fun x : Point D => coord x i) = EuclideanSpace.proj ⟨i, h⟩ := by
      funext x
      exact dite_eq_left h
    rw [he]
    exact (EuclideanSpace.proj (⟨i, h⟩ : Fin D) : Point D →L[ℝ] ℝ).differentiable
  · have he : (fun x : Point D => coord x i) = fun _ => 0 := by
      funext x
      exact dite_eq_right h
    rw [he]
    exact differentiable_const _

lemma objective_diff (D : ℕ) : Differentiable ℝ (objective : Point D → ℝ) := by
  have hgate : Differentiable ℝ gate := fun x => (gate_deriv x).differentiableAt
  have hpayoff : Differentiable ℝ payoff := fun x => (payoff_deriv x).differentiableAt
  unfold objective
  refine ((hpayoff.comp (coord_diff 0)).neg).add ?_
  apply Differentiable.fun_sum
  intro i _
  exact ((hgate.comp (coord_diff i).neg).mul (hpayoff.comp (coord_diff (i + 1)).neg)).sub
    ((hgate.comp (coord_diff i)).mul (hpayoff.comp (coord_diff (i + 1))))

lemma link_range {D : ℕ} (x : Point D) (i : ℕ) : |link x i| ≤ 2 := by
  have hb (a b : ℝ) : 0 ≤ gate a * payoff b ∧ gate a * payoff b ≤ 2 := by
    refine ⟨mul_nonneg (gate_range a).1 (payoff_range b).1, ?_⟩
    have h := mul_le_mul (gate_range a).2 (payoff_range b).2 (payoff_range b).1
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  unfold link
  exact abs_le.mpr ⟨by linarith [(hb (-coord x i) (-coord x (i + 1))).1,
    (hb (coord x i) (coord x (i + 1))).2], by linarith [(hb (-coord x i) (-coord x (i + 1))).2,
    (hb (coord x i) (coord x (i + 1))).1]⟩

lemma gap {D : ℕ} (hD : 0 < D) (x : Point D) :
    objective (0 : Point D) - objective x ≤ 4 * D := by
  have hz (i : ℕ) : coord (0 : Point D) i = 0 := by
    unfold coord
    split <;> rfl
  have hf (i : ℕ) : link (0 : Point D) i = 0 := by simp [link, hz]
  have hs : -(2 * (D : ℝ)) ≤ ∑ i ∈ range (D - 1), link x i := by
    calc
      _ ≤ (-2 : ℝ) * ((D - 1 : ℕ) : ℝ) := by
        have h : ((D - 1 : ℕ) : ℝ) ≤ D := Nat.cast_le.mpr (Nat.sub_le _ _)
        linarith
      _ = ∑ _i ∈ range (D - 1), (-2 : ℝ) := by simp [mul_comm]
      _ ≤ _ := sum_le_sum (fun i _ => (abs_le.mp (link_range x i)).1)
  unfold objective
  simp only [hf, sum_const_zero, add_zero, hz, payoff, Real.arctan_zero]
  have hp := (payoff_range (coord x 0)).2
  unfold payoff at hp
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  linarith only [hs, hp, hD']

noncomputable def line {D : ℕ} (x : Point D) (i : Fin D) (t : ℝ) : Point D := x + t • basis i

def coefficient {D : ℕ} (i : Fin D) (j : ℕ) : ℝ := if j = i.val then 1 else 0

lemma line_zero {D : ℕ} (x : Point D) (i : Fin D) : line x i 0 = x := by
  simp [line]

lemma line_deriv {D : ℕ} (x : Point D) (i : Fin D) :
    HasDerivAt (line x i) (basis i) 0 := by
  convert (hasDerivAt_const (0 : ℝ) x).add
    ((hasDerivAt_id (0 : ℝ)).smul_const (basis i)) using 1 <;> first | rfl | simp

lemma coord_line {D : ℕ} (x : Point D) (i : Fin D) (j : ℕ) (t : ℝ) :
    coord (line x i t) j = coord x j + t * coefficient i j := by
  by_cases hj : j < D
  · by_cases he : j = i.val
    · subst j
      simp [coord, line, basis, coefficient, i.isLt]
    · have hne : i ≠ (⟨j, hj⟩ : Fin D) := fun h => he ((congrArg Fin.val h).symm)
      simp [coord, line, basis, coefficient, hj, he, hne]
  · have he : j ≠ i.val := by intro h; exact hj (h.symm ▸ i.isLt)
    simp [coord, hj, coefficient, he]

lemma coord_line_deriv {D : ℕ} (x : Point D) (i : Fin D) (j : ℕ) :
    HasDerivAt (fun t => coord (line x i t) j) (coefficient i j) 0 := by
  have h := (hasDerivAt_const (0 : ℝ) (coord x j)).add
    ((hasDerivAt_id (0 : ℝ)).mul_const (coefficient i j))
  convert h using 1
  · funext t
    exact coord_line x i j t
  · simp

lemma link_deriv {D : ℕ} (x : Point D) (i : Fin D) (j : ℕ) :
    HasDerivAt (fun t => link (line x i t) j)
      (coefficient i j * leftSlope x j + coefficient i (j + 1) * rightSlope x j) 0 := by
  have hleft := coord_line_deriv x i j
  have hright := coord_line_deriv x i (j + 1)
  have hgneg := (gate_deriv (-coord x j)).comp_of_eq (0 : ℝ)
    (show HasDerivAt (fun t => -coord (line x i t) j) (-coefficient i j) 0 from hleft.neg) (by rw [line_zero])
  have hgpos := (gate_deriv (coord x j)).comp_of_eq (0 : ℝ) hleft (by rw [line_zero])
  have hpneg := (payoff_deriv (-coord x (j + 1))).comp_of_eq (0 : ℝ)
    (show HasDerivAt (fun t => -coord (line x i t) (j + 1)) (-coefficient i (j + 1)) 0 from hright.neg) (by rw [line_zero])
  have hppos := (payoff_deriv (coord x (j + 1))).comp_of_eq (0 : ℝ) hright (by rw [line_zero])
  convert (hgneg.mul hpneg).sub (hgpos.mul hppos) using 1
  · rfl
  · simp only [line_zero, Function.comp_apply, leftSlope, rightSlope]
    ring

lemma gradient_coordinate {D : ℕ} (x : Point D) (i : Fin D) :
    gradient objective x i = -(coefficient i 0 * payoffSlope (coord x 0)) +
      ∑ j ∈ range (D - 1), (coefficient i j * leftSlope x j +
        coefficient i (j + 1) * rightSlope x j) := by
  let v := -(coefficient i 0 * payoffSlope (coord x 0)) +
    ∑ j ∈ range (D - 1), (coefficient i j * leftSlope x j + coefficient i (j + 1) * rightSlope x j)
  have hp := (payoff_deriv (coord x 0)).comp_of_eq (0 : ℝ) (coord_line_deriv x i 0) (by rw [line_zero])
  have hs := HasDerivAt.fun_sum (fun j (_ : j ∈ range (D - 1)) => link_deriv x i j)
  have hv : HasDerivAt (fun t => objective (line x i t)) v 0 := by
    convert hp.neg.add hs using 1
    · rfl
    · unfold v
      ring
  have hf := ((objective_diff D x).hasGradientAt).hasFDerivAt
  have hf' : HasFDerivAt objective (InnerProductSpace.toDual ℝ (Point D) (gradient objective x)) (line x i 0) := by
    rw [line_zero]
    exact hf
  have hd := hf'.comp_hasDerivAt (0 : ℝ) (line_deriv x i)
  have he := hd.deriv.symm.trans hv.deriv
  rw [InnerProductSpace.toDual_apply_apply] at he
  rw [basis, EuclideanSpace.inner_single_right, one_mul] at he
  exact he

def Supported {D : ℕ} (x : Point D) (k : ℕ) : Prop :=
  ∀ i : Fin D, k ≤ i.val → x i = 0

lemma coord_zero {D : ℕ} {x : Point D} {k : ℕ} (hx : Supported x k)
    (i : ℕ) (hi : k ≤ i) : coord x i = 0 := by
  unfold coord
  split
  next h => exact hx ⟨i, h⟩ hi
  next => rfl

lemma gradient_support {D : ℕ} {x : Point D} {k : ℕ} (hx : Supported x k) :
    Supported (gradient objective x) (k + 1) := by
  intro i hi
  rw [gradient_coordinate]
  have hc : coefficient i 0 = 0 := by
    unfold coefficient
    rw [ite_eq_right (by omega : 0 ≠ i.val)]
  rw [hc, zero_mul, neg_zero, zero_add]
  apply sum_eq_zero
  intro j _
  have hleft : coefficient i j * leftSlope x j = 0 := by
    by_cases he : j = i.val
    · have hz := coord_zero hx j (by omega)
      have hs : gateSlope 0 = 0 := gateSlope_nonpos le_rfl
      simp [leftSlope, hz, hs]
    · simp [coefficient, he]
  have hright : coefficient i (j + 1) * rightSlope x j = 0 := by
    by_cases he : j + 1 = i.val
    · have hz := coord_zero hx j (by omega)
      have hs : gate 0 = 0 := gate_nonpos le_rfl
      simp [rightSlope, hz, hs]
    · simp [coefficient, he]
  rw [hleft, hright, add_zero]

lemma coefficient_nonneg {D : ℕ} (i : Fin D) (j : ℕ) : 0 ≤ coefficient i j := by
  unfold coefficient
  split <;> norm_num

lemma term_nonpos {D : ℕ} (x : Point D) (i : Fin D) (j : ℕ) :
    coefficient i j * leftSlope x j + coefficient i (j + 1) * rightSlope x j ≤ 0 :=
  add_nonpos (mul_nonpos_of_nonneg_of_nonpos (coefficient_nonneg _ _) (left_nonpos _ _))
    (mul_nonpos_of_nonneg_of_nonpos (coefficient_nonneg _ _) (right_nonpos _ _))

lemma coordinate_large {D : ℕ} (x : Point D) (i : Fin D) (hi : |coord x i| ≤ 1)
    (hp : 0 < i.val → 1 ≤ |coord x (i.val - 1)|) :
    gradient objective x i ≤ -(1 / 16) := by
  rw [gradient_coordinate]
  by_cases hz : i.val = 0
  · have hc : coefficient i 0 = 1 := by simp [coefficient, hz]
    have hs := sum_nonpos (s := range (D - 1)) (fun j _ => term_nonpos x i j)
    have hpay : 1 / 2 ≤ payoffSlope (coord x 0) := payoffSlope_lb (by simpa [hz] using hi)
    rw [hc, one_mul]
    linarith only [hs, hpay]
  · let j := i.val - 1
    have hj : j ∈ range (D - 1) := by
      have hv := i.isLt
      exact mem_range.mpr (by dsimp [j]; omega)
    have he : j + 1 = i.val := by dsimp [j]; omega
    have hleft : coefficient i j = 0 := by unfold coefficient; rw [ite_eq_right (by omega)]
    have hright : coefficient i (j + 1) = 1 := by simp [coefficient, he]
    have hs : (∑ n ∈ range (D - 1), (coefficient i n * leftSlope x n +
        coefficient i (n + 1) * rightSlope x n)) ≤
        coefficient i j * leftSlope x j + coefficient i (j + 1) * rightSlope x j := by
      let v := fun n => coefficient i n * leftSlope x n + coefficient i (n + 1) * rightSlope x n
      have h := sum_nonpos (s := (range (D - 1)).erase j) (fun n _ => term_nonpos x i n)
      change (∑ n ∈ range (D - 1), v n) ≤ v j
      rw [← sum_erase_add _ v hj]
      exact add_le_of_nonpos_left h
    rw [hleft, hright, zero_mul, one_mul, zero_add] at hs
    have hr := right_lb x j (hp (Nat.pos_of_ne_zero hz)) (by rwa [he])
    have hfirst := mul_nonneg (coefficient_nonneg i 0) (payoffSlope_range (coord x 0)).1
    linarith only [hs, hr, hfirst]

lemma gradient_norm_lb {D : ℕ} {x : Point D} {k : ℕ} (hk : k < D) (hx : Supported x k) :
    (1 : ℝ) / 16 ≤ ‖gradient objective x‖ := by
  let ex : ∃ j, j < D ∧ |coord x j| < 1 :=
    ⟨k, hk, by rw [coord_zero hx k le_rfl, abs_zero]; norm_num⟩
  let j := Nat.find ex
  have hj := Nat.find_spec ex
  let i : Fin D := ⟨j, hj.1⟩
  have hprev : 0 < i.val → 1 ≤ |coord x (i.val - 1)| := by
    intro hi
    change 0 < j at hi
    have hjD : j < D := hj.1
    by_contra! hl
    have h := Nat.find_min ex (m := i.val - 1) (by change j - 1 < j; omega)
    exact h ⟨by change j - 1 < D; omega, hl⟩
  have hc := coordinate_large x i hj.2.le hprev
  have hnorm : ‖(gradient objective x) i‖ ≤ ‖gradient objective x‖ := PiLp.norm_apply_le _ _
  rw [Real.norm_eq_abs, abs_of_nonpos (hc.trans (by norm_num))] at hnorm
  linarith only [hc, hnorm]

end LongTails.Proofs.BirchResourceChain
