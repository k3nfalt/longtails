import LongTails.Proofs.BirchAveragingInstability
import LongTails.Proofs.BirchAveragingPaths
import Mathlib.Probability.Independence.InfinitePi
import LongTails.Proofs.BirchAveragingExecution
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open scoped BigOperators RealInnerProductSpace

namespace BirchNonIIDInstability

open OracleTemplate.Rennala (Point)

noncomputable def vec (a b : ℝ) : Point 2 := WithLp.toLp 2 ![a, b]

@[simp] theorem vec_zero (a b : ℝ) : vec a b 0 = a := rfl
@[simp] theorem vec_one (a b : ℝ) : vec a b 1 = b := rfl

theorem vec_eta (z : Point 2) : vec (z 0) (z 1) = z := by
  ext i
  fin_cases i <;> rfl

theorem inner_vec (a b : ℝ) (z : Point 2) : inner ℝ (vec a b) z = a * z 0 + b * z 1 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, vec, dotProduct, Fin.sum_univ_two]
  ring

theorem norm_sq_vec (a b : ℝ) : ‖vec a b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_two]

theorem norm_sq_coordinates (z : Point 2) : ‖z‖ ^ 2 = (z 0) ^ 2 + (z 1) ^ 2 := by
  rw [← vec_eta z, norm_sq_vec]
  rfl

theorem coordinate_abs_le_norm (z : Point 2) (i : Fin 2) : |z i| ≤ ‖z‖ := by
  have hn := norm_sq_coordinates z
  fin_cases i
  · change |z 0| ≤ ‖z‖
    nlinarith [sq_abs (z 0), abs_nonneg (z 0), norm_nonneg z, sq_nonneg (z 1)]
  · change |z 1| ≤ ‖z‖
    nlinarith [sq_abs (z 1), abs_nonneg (z 1), norm_nonneg z, sq_nonneg (z 0)]

theorem norm_vec_le_abs_sum (a b : ℝ) : ‖vec a b‖ ≤ |a| + |b| := by
  have hn := norm_sq_vec a b
  nlinarith [sq_abs a, sq_abs b, norm_nonneg (vec a b), abs_nonneg a, abs_nonneg b,
    mul_nonneg (abs_nonneg a) (abs_nonneg b)]

noncomputable abbrev coord (i : Fin 2) : Point 2 →L[ℝ] ℝ := EuclideanSpace.proj i

noncomputable def euclideanPotential (z : Point 2) : ℝ := potential (z 0) (z 1)

theorem hasGradientAt_euclideanPotential (z : Point 2) :
    HasGradientAt euclideanPotential (vec (horizontal (z 0) (z 1)) (vertical (z 0) (z 1))) z := by
  have hx := (coord 0).hasFDerivAt (x := z)
  have hy := (coord 1).hasFDerivAt (x := z)
  have ht := (hasDerivAt_tanhSlope_value (z 0)).comp_hasFDerivAt z hx
  have hl := ((Real.hasDerivAt_cosh (z 1)).log (ne_of_gt (Real.cosh_pos (z 1)))).comp_hasFDerivAt z hy
  have he := ((((hasDerivAt_id (z 1)).pow 2).neg).exp).comp_hasFDerivAt z hy
  have hbase := (((hx.pow 2).const_mul (1 / 2)).add (hx.const_mul (1 / 50))).add
    ((hy.pow 2).const_mul (1 / 2))
  have hc := (ht.mul ((hasFDerivAt_const (1 : ℝ) z).sub he)).const_mul (1 / 5)
  have hd := (hbase.sub (hl.const_mul 2)).sub hc
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hd using 1
  · funext v
    dsimp [euclideanPotential, potential, Function.comp_def, coord]
    ring
  · ext v
    rw [InnerProductSpace.toDual_apply_apply, inner_vec]
    simp [horizontal, vertical, coord, Real.tanh_eq_sinh_div_cosh]
    ring

theorem gradient_euclideanPotential (z : Point 2) :
    gradient euclideanPotential z = vec (horizontal (z 0) (z 1)) (vertical (z 0) (z 1)) :=
  (hasGradientAt_euclideanPotential z).gradient

end BirchNonIIDInstability

namespace BirchNonIIDInstability

theorem log_cosh_le_abs (y : ℝ) : Real.log (Real.cosh y) ≤ |y| := by
  have h1 := Real.exp_le_exp.mpr (le_abs_self y)
  have h2 := Real.exp_le_exp.mpr (neg_le_abs y)
  have hc : Real.cosh y ≤ Real.exp |y| := by
    rw [Real.cosh_eq]
    linarith
  have h := Real.log_le_log (Real.cosh_pos y) hc
  simpa only [Real.log_exp] using h

theorem potential_lower (x y : ℝ) : -(11001 / 5000 : ℝ) ≤ potential x y := by
  have he0 : 0 ≤ 1 - Real.exp (-y ^ 2) := by
    have h := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg y))
    linarith
  have he1 : 1 - Real.exp (-y ^ 2) ≤ 1 := by linarith [Real.exp_pos (-y ^ 2)]
  have hc := mul_le_mul (Real.tanh_lt_one x).le he1 he0 (by norm_num : (0 : ℝ) ≤ 1)
  have hl := log_cosh_le_abs y
  dsimp [potential]
  nlinarith [sq_nonneg (x + 1 / 50), sq_nonneg (|y| - 2), sq_abs y]

theorem potential_anchor (s : ℝ) : potential s 0 = s ^ 2 / 2 + s / 50 := by
  simp [potential]

theorem potential_anchor_gap {s : ℝ} (hs : s ∈ Set.Icc (4 / 25 : ℝ) (9 / 50)) :
    potential s 0 - (-(11001 / 5000 : ℝ)) ≤ 9 / 4 := by
  rw [potential_anchor]
  nlinarith [hs.1, hs.2]

theorem gaussian_square_bound (y : ℝ) : y ^ 2 * Real.exp (-y ^ 2) ≤ 1 := by
  have he := Real.add_one_le_exp (y ^ 2)
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-y ^ 2)).le
  have hp : Real.exp (y ^ 2) * Real.exp (-y ^ 2) = 1 := by
    rw [← Real.exp_add]
    simp
  nlinarith [Real.exp_pos (-y ^ 2)]

theorem gaussian_linear_bound (y : ℝ) : |y| * Real.exp (-y ^ 2) ≤ 1 := by
  have hs := gaussian_square_bound y
  have he : Real.exp (-y ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg y))
  have hm := mul_nonneg (sq_nonneg (|y| - 1)) (Real.exp_pos (-y ^ 2)).le
  nlinarith [sq_abs y]

end BirchNonIIDInstability

open scoped BigOperators RealInnerProductSpace

namespace BirchNonIIDInstability

open OracleTemplate.Rennala (Point)
open LongTails.Setups.BirchNonIID

noncomputable def perturbation (z : Point 2) : ℝ := Real.tanh (z 0) * Real.tanh (z 1)

theorem hasGradientAt_perturbation (z : Point 2) :
    HasGradientAt perturbation (vec (tanhSlope (z 0) * Real.tanh (z 1))
      (Real.tanh (z 0) * tanhSlope (z 1))) z := by
  have hx := (hasDerivAt_tanhSlope_value (z 0)).comp_hasFDerivAt z ((coord 0).hasFDerivAt (x := z))
  have hy := (hasDerivAt_tanhSlope_value (z 1)).comp_hasFDerivAt z ((coord 1).hasFDerivAt (x := z))
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hx.mul hy using 1
  · rfl
  · ext v
    rw [InnerProductSpace.toDual_apply_apply, inner_vec]
    simp [coord]
    ring

noncomputable def clientPotential (δ sign : ℝ) (z : Point 2) : ℝ :=
  euclideanPotential z + sign * δ * perturbation z

theorem hasGradientAt_clientPotential (δ sign : ℝ) (z : Point 2) :
    HasGradientAt (clientPotential δ sign)
      (vec (horizontal (z 0) (z 1) + sign * δ * tanhSlope (z 0) * Real.tanh (z 1))
        (vertical (z 0) (z 1) + sign * δ * Real.tanh (z 0) * tanhSlope (z 1))) z := by
  have hd := (hasGradientAt_euclideanPotential z).hasFDerivAt.add
    ((hasGradientAt_perturbation z).hasFDerivAt.const_mul (sign * δ))
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hd using 1
  · rfl
  · ext v
    simp [InnerProductSpace.toDual_apply_apply, inner_vec]
    ring

theorem gradient_clientPotential (δ sign : ℝ) (z : Point 2) :
    gradient (clientPotential δ sign) z =
      vec (horizontal (z 0) (z 1) + sign * δ * tanhSlope (z 0) * Real.tanh (z 1))
        (vertical (z 0) (z 1) + sign * δ * Real.tanh (z 0) * tanhSlope (z 1)) :=
  (hasGradientAt_clientPotential δ sign z).gradient

def clientSign (i : Fin 2) : ℝ := if i = 0 then 1 else -1

noncomputable def lowerInstance (δ : ℝ) : Instance 2 2 where
  localObjective i := clientPotential δ (clientSign i)
  lower := -(11001 / 5000)

theorem objective_lowerInstance (δ : ℝ) : objective (lowerInstance δ) = euclideanPotential := by
  funext z
  simp [objective, lowerInstance, clientSign, clientPotential, Fin.sum_univ_two]
  ring

theorem correctedDirection_lowerInstance (δ s x y : ℝ) (i : Fin 2) :
    correctedDirection (lowerInstance δ) i (vec s 0) (vec x y) =
      vec (directionX δ (clientSign i) x y) (directionY δ (clientSign i) s x y) := by
  unfold correctedDirection
  change gradient (clientPotential δ (clientSign i)) (vec x y) -
    gradient (clientPotential δ (clientSign i)) (vec s 0) +
    gradient (objective (lowerInstance δ)) (vec s 0) = _
  rw [objective_lowerInstance, gradient_clientPotential, gradient_clientPotential, gradient_euclideanPotential]
  ext j
  fin_cases j <;> norm_num [vec, directionX, directionY, horizontal, vertical, tanhSlope]
  ring

end BirchNonIIDInstability

namespace BirchNonIIDInstability

open OracleTemplate.Rennala (Point)
open LongTails.Setups.BirchNonIID

theorem abs_tanh_le_one (x : ℝ) : |Real.tanh x| ≤ 1 := by
  nlinarith [Real.tanh_sq_lt_one x, sq_abs (Real.tanh x), abs_nonneg (Real.tanh x)]

theorem abs_clientSign (i : Fin 2) : |clientSign i| = 1 := by
  fin_cases i <;> norm_num [clientSign]

theorem client_gradient_difference (δ : ℝ) (i : Fin 2) (z : Point 2) :
    gradient ((lowerInstance δ).localObjective i) z - gradient (objective (lowerInstance δ)) z =
      vec (clientSign i * δ * tanhSlope (z 0) * Real.tanh (z 1))
        (clientSign i * δ * Real.tanh (z 0) * tanhSlope (z 1)) := by
  rw [objective_lowerInstance, gradient_euclideanPotential]
  change gradient (clientPotential δ (clientSign i)) z - _ = _
  rw [gradient_clientPotential]
  ext j
  fin_cases j <;> simp [vec]

theorem firstOrderSimilarity_lowerInstance {δ : ℝ} (hδ : 0 ≤ δ) :
    FirstOrderSimilarity (lowerInstance δ) (2 * δ) := by
  intro i z
  rw [client_gradient_difference]
  have hx : |tanhSlope (z 0)| ≤ 1 := by
    rw [abs_of_pos (tanhSlope_pos _)]; exact tanhSlope_le_one _
  have hy : |tanhSlope (z 1)| ≤ 1 := by
    rw [abs_of_pos (tanhSlope_pos _)]; exact tanhSlope_le_one _
  have ha : |clientSign i * δ * tanhSlope (z 0) * Real.tanh (z 1)| ≤ δ := by
    have hp : |tanhSlope (z 0)| * |Real.tanh (z 1)| ≤ 1 := by
      nlinarith [abs_tanh_le_one (z 1), mul_nonneg (sub_nonneg.mpr hx) (abs_nonneg (Real.tanh (z 1)))]
    simpa [abs_mul, abs_clientSign, abs_of_nonneg hδ, mul_assoc] using
      mul_le_mul_of_nonneg_left hp hδ
  have hb : |clientSign i * δ * Real.tanh (z 0) * tanhSlope (z 1)| ≤ δ := by
    have hp : |Real.tanh (z 0)| * |tanhSlope (z 1)| ≤ 1 := by
      nlinarith [abs_tanh_le_one (z 0), mul_nonneg (sub_nonneg.mpr hy) (abs_nonneg (Real.tanh (z 0)))]
    simpa [abs_mul, abs_clientSign, abs_of_nonneg hδ, mul_assoc] using
      mul_le_mul_of_nonneg_left hp hδ
  have hn := norm_vec_le_abs_sum
    (clientSign i * δ * tanhSlope (z 0) * Real.tanh (z 1))
    (clientSign i * δ * Real.tanh (z 0) * tanhSlope (z 1))
  exact pow_le_pow_left₀ (norm_nonneg _) (by linarith : ‖vec
    (clientSign i * δ * tanhSlope (z 0) * Real.tanh (z 1))
    (clientSign i * δ * Real.tanh (z 0) * tanhSlope (z 1))‖ ≤ 2 * δ) 2

theorem localPath_lowerInstance (δ s : ℝ) (i : Fin 2) (k : ℕ) :
    localPath (lowerInstance δ) i (vec s 0) (1 / 100) k =
      vec (phasePath δ (clientSign i) s k).1 (phasePath δ (clientSign i) s k).2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [localPath, ih, correctedDirection_lowerInstance]
    ext j
    fin_cases j <;> simp [phasePath, phaseStep, vec, div_eq_mul_inv, mul_comm]

end BirchNonIIDInstability

open scoped BigOperators

namespace BirchNonIIDInstability

open LongTails.Setups.BirchNonIID

theorem euclidean_mean_fixedPoint {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 1000000) :
    ∃ s ∈ Set.Icc (4 / 25 : ℝ) (9 / 50),
      pointMean (fun i => localPath (lowerInstance δ) i (vec s 0) (1 / 100)
        (instabilityHorizon δ)) = vec s 0 ∧
      (81 / 2500 : ℝ) ≤ ‖gradient (objective (lowerInstance δ)) (vec s 0)‖ ^ 2 := by
  obtain ⟨s, hs, hf, hg⟩ := phasePath_mean_fixedPoint hδ0 hδ1
  refine ⟨s, hs, ?_, ?_⟩
  · have hx := congrArg Prod.fst hf
    have hy := congrArg Prod.snd hf
    dsimp only at hx hy
    simp only [pointMean, Fin.sum_univ_two, localPath_lowerInstance]
    ext j
    fin_cases j
    · norm_num [vec, clientSign]
      linarith [hx]
    · norm_num [vec, clientSign]
      linarith [hy]
  · simpa [objective_lowerInstance, gradient_euclideanPotential, norm_sq_vec] using hg

/-- Reusing the fixed anchor prevents progress for every number of communication rounds. -/
theorem euclidean_server_stagnation {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 1000000) :
    ∃ s ∈ Set.Icc (4 / 25 : ℝ) (9 / 50), ∀ r : ℕ,
      serverPath (lowerInstance δ) (vec s 0) (1 / 100) (instabilityHorizon δ) r = vec s 0 ∧
      (81 / 2500 : ℝ) ≤ ‖gradient (objective (lowerInstance δ))
        (serverPath (lowerInstance δ) (vec s 0) (1 / 100) (instabilityHorizon δ) r)‖ ^ 2 := by
  obtain ⟨s, hs, hf, hg⟩ := euclidean_mean_fixedPoint hδ0 hδ1
  refine ⟨s, hs, ?_⟩
  intro r
  have he : serverPath (lowerInstance δ) (vec s 0) (1 / 100) (instabilityHorizon δ) r = vec s 0 := by
    induction r with
    | zero => rfl
    | succ r ih => rw [serverPath, ih]; exact hf
  exact ⟨he, by rw [he]; exact hg⟩

end BirchNonIIDInstability

namespace BirchNonIIDInstability

open OracleTemplate.Rennala (Point)

noncomputable def matrix2 (a b c d : ℝ) : Point 2 →L[ℝ] Point 2 :=
  (a • coord 0 + b • coord 1).smulRight (vec 1 0) +
    (c • coord 0 + d • coord 1).smulRight (vec 0 1)

theorem matrix2_apply (a b c d : ℝ) (v : Point 2) :
    matrix2 a b c d v = vec (a * v 0 + b * v 1) (c * v 0 + d * v 1) := by
  ext i
  fin_cases i <;> simp [matrix2, coord, vec]

theorem matrix2_norm_le (a b c d : ℝ) :
    ‖matrix2 a b c d‖ ≤ |a| + |b| + |c| + |d| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [matrix2_apply]
  have h0 := coordinate_abs_le_norm v 0
  have h1 := coordinate_abs_le_norm v 1
  calc
    ‖vec (a * v 0 + b * v 1) (c * v 0 + d * v 1)‖ ≤
        |a * v 0 + b * v 1| + |c * v 0 + d * v 1| := norm_vec_le_abs_sum _ _
    _ ≤ (|a| * |v 0| + |b| * |v 1|) + (|c| * |v 0| + |d| * |v 1|) := by
      simpa only [abs_mul] using add_le_add (abs_add_le (a * v 0) (b * v 1))
        (abs_add_le (c * v 0) (d * v 1))
    _ ≤ (|a| + |b| + |c| + |d|) * ‖v‖ := by
      nlinarith [mul_le_mul_of_nonneg_left h0 (abs_nonneg a),
        mul_le_mul_of_nonneg_left h1 (abs_nonneg b),
        mul_le_mul_of_nonneg_left h0 (abs_nonneg c),
        mul_le_mul_of_nonneg_left h1 (abs_nonneg d)]

theorem hasFDerivAt_vec {f g : Point 2 → ℝ} {a b c d : ℝ} {z : Point 2}
    (hf : HasFDerivAt f (a • coord 0 + b • coord 1) z)
    (hg : HasFDerivAt g (c • coord 0 + d • coord 1) z) :
    HasFDerivAt (fun v => vec (f v) (g v)) (matrix2 a b c d) z := by
  convert (hf.smul_const (vec 1 0)).add (hg.smul_const (vec 0 1)) using 1
  · funext v
    ext i
    fin_cases i <;> simp [vec]
  · rfl

end BirchNonIIDInstability

namespace BirchNonIIDInstability

open OracleTemplate.Rennala (Point)

noncomputable def hxx (x y : ℝ) : ℝ :=
  1 + (2 / 5) * Real.tanh x * tanhSlope x * (1 - Real.exp (-y ^ 2))
noncomputable def hxy (x y : ℝ) : ℝ :=
  -(2 / 5) * tanhSlope x * y * Real.exp (-y ^ 2)
noncomputable def hyy (x y : ℝ) : ℝ :=
  1 - 2 * tanhSlope y - (2 / 5) * Real.tanh x * (1 - 2 * y ^ 2) * Real.exp (-y ^ 2)

theorem horizontal_fderiv (z : Point 2) :
    HasFDerivAt (fun v : Point 2 => horizontal (v 0) (v 1))
      (hxx (z 0) (z 1) • coord 0 + hxy (z 0) (z 1) • coord 1) z := by
  have hx := (coord 0).hasFDerivAt (x := z)
  have hy := (coord 1).hasFDerivAt (x := z)
  have hs := (hasDerivAt_tanhSlope (z 0)).comp_hasFDerivAt z hx
  have he := ((hy.pow 2).neg).exp
  have hd := (hx.add_const (1 / 50)).sub
    ((hs.mul ((hasFDerivAt_const (1 : ℝ) z).sub he)).const_mul (1 / 5))
  convert hd using 1
  · funext v
    dsimp [horizontal, coord]
    ring
  · ext v
    simp [hxx, hxy, coord]
    ring

theorem vertical_fderiv (z : Point 2) :
    HasFDerivAt (fun v : Point 2 => vertical (v 0) (v 1))
      (hxy (z 0) (z 1) • coord 0 + hyy (z 0) (z 1) • coord 1) z := by
  have hx := (coord 0).hasFDerivAt (x := z)
  have hy := (coord 1).hasFDerivAt (x := z)
  have ht := (hasDerivAt_tanhSlope_value (z 0)).comp_hasFDerivAt z hx
  have hu := (hasDerivAt_tanhSlope_value (z 1)).comp_hasFDerivAt z hy
  have he := ((hy.pow 2).neg).exp
  have hd := (hy.sub (hu.const_mul 2)).sub (((ht.mul hy).mul he).const_mul (2 / 5))
  convert hd using 1
  · funext v
    dsimp [vertical, coord]
    ring
  · ext v
    simp [hxy, hyy, coord]
    ring

theorem gradient_potential_fderiv (z : Point 2) :
    HasFDerivAt (gradient euclideanPotential)
      (matrix2 (hxx (z 0) (z 1)) (hxy (z 0) (z 1))
        (hxy (z 0) (z 1)) (hyy (z 0) (z 1))) z := by
  have he : gradient euclideanPotential =
      fun v => vec (horizontal (v 0) (v 1)) (vertical (v 0) (v 1)) :=
    funext gradient_euclideanPotential
  rw [he]
  exact hasFDerivAt_vec (horizontal_fderiv z) (vertical_fderiv z)

end BirchNonIIDInstability

namespace BirchNonIIDInstability

open OracleTemplate.Rennala (Point)

theorem abs_tanhSlope_le_one (x : ℝ) : |tanhSlope x| ≤ 1 := by
  rw [abs_of_pos (tanhSlope_pos x)]
  exact tanhSlope_le_one x

theorem abs_mul_le_one_of_bounds {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    |a * b| ≤ 1 := by
  rw [abs_mul]
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (abs_nonneg b)]

theorem abs_hxx_le (x y : ℝ) : |hxx x y| ≤ 7 / 5 := by
  have he : |1 - Real.exp (-y ^ 2)| ≤ 1 := by
    rw [abs_of_nonneg (by linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg y))])]
    linarith [Real.exp_pos (-y ^ 2)]
  have hp := abs_mul_le_one_of_bounds
    (abs_mul_le_one_of_bounds (abs_tanh_le_one x) (abs_tanhSlope_le_one x)) he
  have ht := abs_add_le (1 : ℝ)
    ((2 / 5) * Real.tanh x * tanhSlope x * (1 - Real.exp (-y ^ 2)))
  rw [hxx]
  simp only [abs_mul] at hp ht
  norm_num at ht
  nlinarith [hp]

theorem abs_hxy_le (x y : ℝ) : |hxy x y| ≤ 2 / 5 := by
  have hg := gaussian_linear_bound y
  have hs := abs_tanhSlope_le_one x
  have hm := mul_le_mul_of_nonneg_right hs
    (mul_nonneg (abs_nonneg y) (Real.exp_pos (-y ^ 2)).le)
  dsimp [hxy]
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  norm_num
  nlinarith [hm]

theorem abs_hyy_le (x y : ℝ) : |hyy x y| ≤ 21 / 5 := by
  have he : Real.exp (-y ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg y))
  have he0 := (Real.exp_pos (-y ^ 2)).le
  have hg := gaussian_square_bound y
  have ha : |1 - 2 * y ^ 2| ≤ 1 + 2 * y ^ 2 := by
    have hn : 0 ≤ 2 * y ^ 2 := by positivity
    have hh := abs_add_le (1 : ℝ) (-(2 * y ^ 2))
    rw [abs_neg, abs_of_nonneg hn, abs_one] at hh
    simpa only [sub_eq_add_neg] using hh
  have hp : |1 - 2 * y ^ 2| * Real.exp (-y ^ 2) ≤ 3 := by
    have hm := mul_le_mul_of_nonneg_right ha he0
    nlinarith
  have hb : |1 - 2 * tanhSlope y| ≤ 3 := by
    exact abs_le.mpr ⟨by linarith [tanhSlope_le_one y], by linarith [tanhSlope_pos y]⟩
  have ht := mul_le_mul_of_nonneg_right (abs_tanh_le_one x)
    (mul_nonneg (abs_nonneg (1 - 2 * y ^ 2)) he0)
  have hh := abs_add_le (1 - 2 * tanhSlope y)
    (-((2 / 5) * Real.tanh x * (1 - 2 * y ^ 2) * Real.exp (-y ^ 2)))
  dsimp [hyy]
  simp only [← sub_eq_add_neg, abs_neg, abs_mul, abs_of_pos (Real.exp_pos _)] at hh
  norm_num at hh
  nlinarith

theorem potential_hessian_norm (z : Point 2) :
    ‖fderiv ℝ (gradient euclideanPotential) z‖ ≤ 8 := by
  rw [(gradient_potential_fderiv z).fderiv]
  have hm := matrix2_norm_le (hxx (z 0) (z 1)) (hxy (z 0) (z 1))
    (hxy (z 0) (z 1)) (hyy (z 0) (z 1))
  linarith [abs_hxx_le (z 0) (z 1), abs_hxy_le (z 0) (z 1), abs_hyy_le (z 0) (z 1)]

theorem smooth_euclideanPotential :
    LongTails.Setups.BirchSgd.SmoothObjective euclideanPotential 8 := by
  refine ⟨fun z => ?_, ?_⟩
  · rw [gradient_euclideanPotential]
    exact hasGradientAt_euclideanPotential z
  · intro x y
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (s := Set.univ) (𝕜 := ℝ)
      (fun z _ => (gradient_potential_fderiv z).differentiableAt)
      (fun z _ => potential_hessian_norm z) convex_univ (Set.mem_univ y) (Set.mem_univ x)

end BirchNonIIDInstability

namespace BirchNonIIDInstability

open OracleTemplate.Rennala (Point)

noncomputable def pxx (x y : ℝ) : ℝ := -2 * Real.tanh x * tanhSlope x * Real.tanh y
noncomputable def pxy (x y : ℝ) : ℝ := tanhSlope x * tanhSlope y
noncomputable def pyy (x y : ℝ) : ℝ := -2 * Real.tanh x * Real.tanh y * tanhSlope y

theorem perturbation_gradient_fderiv (z : Point 2) :
    HasFDerivAt (gradient perturbation)
      (matrix2 (pxx (z 0) (z 1)) (pxy (z 0) (z 1))
        (pxy (z 0) (z 1)) (pyy (z 0) (z 1))) z := by
  have hx := (coord 0).hasFDerivAt (x := z)
  have hy := (coord 1).hasFDerivAt (x := z)
  have ht := (hasDerivAt_tanhSlope_value (z 0)).comp_hasFDerivAt z hx
  have hu := (hasDerivAt_tanhSlope_value (z 1)).comp_hasFDerivAt z hy
  have hs := (hasDerivAt_tanhSlope (z 0)).comp_hasFDerivAt z hx
  have hr := (hasDerivAt_tanhSlope (z 1)).comp_hasFDerivAt z hy
  have h1 : HasFDerivAt (fun v : Point 2 => tanhSlope (v 0) * Real.tanh (v 1))
      (pxx (z 0) (z 1) • coord 0 + pxy (z 0) (z 1) • coord 1) z := by
    convert hs.mul hu using 1
    · rfl
    · ext v
      simp [pxx, pxy, coord]
      ring
  have h2 : HasFDerivAt (fun v : Point 2 => Real.tanh (v 0) * tanhSlope (v 1))
      (pxy (z 0) (z 1) • coord 0 + pyy (z 0) (z 1) • coord 1) z := by
    convert ht.mul hr using 1
    · rfl
    · ext v
      simp [pxy, pyy, coord]
      ring
  have he : gradient perturbation = fun v =>
      vec (tanhSlope (v 0) * Real.tanh (v 1)) (Real.tanh (v 0) * tanhSlope (v 1)) :=
    funext (fun v => (hasGradientAt_perturbation v).gradient)
  rw [he]
  exact hasFDerivAt_vec h1 h2

theorem perturbation_hessian_norm (z : Point 2) :
    ‖fderiv ℝ (gradient perturbation) z‖ ≤ 6 := by
  have ha := abs_mul_le_one_of_bounds
    (abs_mul_le_one_of_bounds (abs_tanh_le_one (z 0)) (abs_tanhSlope_le_one (z 0)))
    (abs_tanh_le_one (z 1))
  have hb := abs_mul_le_one_of_bounds (abs_tanhSlope_le_one (z 0)) (abs_tanhSlope_le_one (z 1))
  have hc := abs_mul_le_one_of_bounds
    (abs_mul_le_one_of_bounds (abs_tanh_le_one (z 0)) (abs_tanh_le_one (z 1)))
    (abs_tanhSlope_le_one (z 1))
  have hxx : |pxx (z 0) (z 1)| ≤ 2 := by
    dsimp [pxx]
    simp only [abs_mul] at ha ⊢
    norm_num
    nlinarith
  have hyy : |pyy (z 0) (z 1)| ≤ 2 := by
    dsimp [pyy]
    simp only [abs_mul] at hc ⊢
    norm_num
    nlinarith
  rw [(perturbation_gradient_fderiv z).fderiv]
  have hm := matrix2_norm_le (pxx (z 0) (z 1)) (pxy (z 0) (z 1))
    (pxy (z 0) (z 1)) (pyy (z 0) (z 1))
  change |pxy (z 0) (z 1)| ≤ 1 at hb
  linarith

end BirchNonIIDInstability

namespace BirchNonIIDInstability

open OracleTemplate.Rennala (Point)
open LongTails.Setups.BirchNonIID

theorem gradient_client_function (δ sign : ℝ) :
    gradient (clientPotential δ sign) = fun z =>
      gradient euclideanPotential z + (sign * δ) • gradient perturbation z := by
  funext z
  rw [gradient_clientPotential, gradient_euclideanPotential, (hasGradientAt_perturbation z).gradient]
  ext i
  fin_cases i <;> simp [vec] <;> ring

theorem client_gradient_fderiv (δ sign : ℝ) (z : Point 2) :
    HasFDerivAt (gradient (clientPotential δ sign))
      (fderiv ℝ (gradient euclideanPotential) z +
        (sign * δ) • fderiv ℝ (gradient perturbation) z) z := by
  rw [gradient_client_function]
  have hf := (gradient_potential_fderiv z).differentiableAt.hasFDerivAt
  have hp := (perturbation_gradient_fderiv z).differentiableAt.hasFDerivAt
  exact hf.add (hp.const_smul (sign * δ))

theorem secondOrderSimilarity_lowerInstance {δ : ℝ} (hδ : 0 ≤ δ) :
    SecondOrderSimilarity (lowerInstance δ) (6 * δ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i z
    exact (client_gradient_fderiv δ (clientSign i) z).differentiableAt
  · rw [objective_lowerInstance]
    intro z
    exact (gradient_potential_fderiv z).differentiableAt
  · intro i z
    rw [objective_lowerInstance]
    change ‖fderiv ℝ (gradient (clientPotential δ (clientSign i))) z - _‖ ≤ _
    rw [(client_gradient_fderiv δ (clientSign i) z).fderiv, add_sub_cancel_left, norm_smul]
    have hs : ‖clientSign i * δ‖ = δ := by
      rw [Real.norm_eq_abs, abs_mul, abs_clientSign, abs_of_nonneg hδ, one_mul]
    rw [hs]
    nlinarith [mul_le_mul_of_nonneg_left (perturbation_hessian_norm z) hδ]

end BirchNonIIDInstability

namespace BirchNonIIDInstability

open LongTails.Setups.BirchNonIID

/-- Public parameters for the two-client counterexample family. -/
noncomputable def lowerParams (δ s ε : ℝ) : Params 2 where
  d := 2
  L := 8
  σ := fun _ => 0
  ε := ε
  Δ := 9 / 4
  ζ := 2 * δ
  δ := 6 * δ
  similarity := .firstAndSecondOrder
  x0 := vec s 0

theorem lowerParams_valid {δ s ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε) :
    Valid (lowerParams δ s ε) := by
  dsimp [Valid, lowerParams]
  exact ⟨by norm_num, by norm_num, by norm_num, fun _ => le_rfl, hε,
    by norm_num, by positivity, by positivity⟩

theorem lowerInstance_objectiveClass {δ s ε : ℝ} (hδ : 0 ≤ δ)
    (hs : s ∈ Set.Icc (4 / 25 : ℝ) (9 / 50)) :
    ObjectiveClass (lowerParams δ s ε) (lowerInstance δ) := by
  unfold ObjectiveClass
  dsimp only [lowerParams]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i z
    change HasGradientAt (clientPotential δ (clientSign i))
      (gradient (clientPotential δ (clientSign i)) z) z
    rw [gradient_clientPotential]
    exact hasGradientAt_clientPotential δ (clientSign i) z
  · rw [objective_lowerInstance]
    exact smooth_euclideanPotential
  · rw [objective_lowerInstance]
    intro z
    exact potential_lower (z 0) (z 1)
  · rw [objective_lowerInstance]
    exact potential_anchor_gap hs
  · exact ⟨firstOrderSimilarity_lowerInstance hδ, secondOrderSimilarity_lowerInstance hδ⟩

/-- The stagnating instance satisfies the original objective assumptions globally. -/
theorem objectiveClass_stagnation {δ ε : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 1000000) (hε : 0 < ε) :
    ∃ s ∈ Set.Icc (4 / 25 : ℝ) (9 / 50),
      Valid (lowerParams δ s ε) ∧
      ObjectiveClass (lowerParams δ s ε) (lowerInstance δ) ∧
      ∀ r : ℕ, (81 / 2500 : ℝ) ≤
        ‖gradient (objective (lowerInstance δ))
          (serverPath (lowerInstance δ) (lowerParams δ s ε).x0 (1 / 100)
            (instabilityHorizon δ) r)‖ ^ 2 := by
  obtain ⟨s, hs, hr⟩ := euclidean_server_stagnation hδ0 hδ1
  exact ⟨s, hs, lowerParams_valid hδ0.le hε, lowerInstance_objectiveClass hδ0.le hs,
    fun r => (hr r).2⟩

end BirchNonIIDInstability

open MeasureTheory ProbabilityTheory

namespace BirchNonIIDInstability

open OracleTemplate.Rennala (Point)
open LongTails.Setups.BirchNonIID

noncomputable def unitLaw : ProbabilityMeasure Unit := ⟨Measure.dirac (), inferInstance⟩
noncomputable def unitStreamLaw : ProbabilityMeasure (ℕ → Unit) :=
  ⟨Measure.infinitePi (fun _ : ℕ => (unitLaw : Measure Unit)), inferInstance⟩

theorem unitStream_iid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
    (fun k (ξ : ℕ → Unit) => ξ k) (unitLaw : Measure Unit)
    (unitStreamLaw : Measure (ℕ → Unit)) := by
  refine ⟨fun k => measurable_pi_apply k, ?_, ?_⟩
  · exact iIndepFun_infinitePi (X := fun (_ : ℕ) (x : Unit) => x) (fun _ => measurable_id)
  · intro k
    exact Measure.infinitePi_map_eval (fun _ : ℕ => (unitLaw : Measure Unit)) k

noncomputable def exactClient (δ : ℝ) (i : Fin 2) (z : Point 2) (_ : Unit) : Point 2 :=
  gradient ((lowerInstance δ).localObjective i) z

theorem exactClient_stochastic (δ : ℝ) (i : Fin 2) :
    LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point 2) Unit
      (unitLaw : Measure Unit) ((lowerInstance δ).localObjective i) (exactClient δ i) 0 := by
  have hc : Continuous (gradient ((lowerInstance δ).localObjective i)) :=
    continuous_iff_continuousAt.mpr (fun z => (client_gradient_fderiv δ (clientSign i) z).continuousAt)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hc.measurable.comp measurable_fst
  · intro z
    exact integrable_const _
  · intro z
    simp [exactClient]
  · intro z
    simp only [exactClient, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact integrable_const _
  · intro z
    simp [exactClient]

noncomputable def lowerOracle (δ : ℝ) : OracleTemplate.Oracle (Point 2) (Point 2) 2 :=
  workerOracle unitStreamLaw (exactClient δ)

theorem lowerOracle_admissible {δ s ε : ℝ} (hδ : 0 ≤ δ)
    (hs : s ∈ Set.Icc (4 / 25 : ℝ) (9 / 50)) :
    Admissible (lowerParams δ s ε) (lowerInstance δ) (lowerOracle δ) := by
  refine ⟨lowerInstance_objectiveClass hδ hs, ?_⟩
  refine ⟨Unit, inferInstance, unitLaw, unitStreamLaw, exactClient δ, unitStream_iid, ?_, rfl⟩
  exact fun i => exactClient_stochastic δ i

end BirchNonIIDInstability

open scoped BigOperators

namespace BirchNonIIDInstability

open OracleTemplate.Rennala (Point)
open LongTails.Setups.BirchNonIID

theorem roundGradientEnergy_anchor_lower {workers d K : ℕ} (hK : 0 < K)
    (I : Instance workers d) (x : Point d) (η : ℝ) :
    (workers : ℝ) * ‖gradient (objective I) x‖ ^ 2 ≤ roundGradientEnergy I x η K := by
  unfold roundGradientEnergy
  have h (i : Fin workers) : ‖gradient (objective I) x‖ ^ 2 ≤
      ∑ k ∈ Finset.range K, ‖gradient (objective I) (localPath I i x η k)‖ ^ 2 := by
    have he := Finset.single_le_sum (s := Finset.range K)
      (f := fun k => ‖gradient (objective I) (localPath I i x η k)‖ ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_range.mpr hK)
    simpa only [localPath] using he
  simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)

theorem referencePoint_average_lower {workers d K R : ℕ} (hw : 0 < workers)
    (hK : 0 < K) (hR : 0 < R) (I : Instance workers d) (x0 : Point d)
    (η c : ℝ) (hl : ∀ r, c ≤ ‖gradient (objective I) (serverPath I x0 η K r)‖ ^ 2) :
    c / (K : ℝ) ≤ (1 / ((workers * K * R : ℕ) : ℝ)) *
      ∑ j : Fin (workers * K * R), ‖gradient (objective I) (referencePoint hw I x0 η K j.val)‖ ^ 2 := by
  rw [referencePoint_energy_sum hw hK]
  have he : (R : ℝ) * ((workers : ℝ) * c) ≤
      ∑ r ∈ Finset.range R, roundGradientEnergy I (serverPath I x0 η K r) η K := by
    have hb (r : ℕ) : (workers : ℝ) * c ≤
        roundGradientEnergy I (serverPath I x0 η K r) η K :=
      (mul_le_mul_of_nonneg_left (hl r) (Nat.cast_nonneg workers)).trans
        (roundGradientEnergy_anchor_lower hK I _ η)
    simpa using Finset.sum_le_sum (s := Finset.range R) (fun r _ => hb r)
  have hw' : (workers : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hw
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hR
  calc
    c / (K : ℝ) = (1 / ((workers * K * R : ℕ) : ℝ)) *
        ((R : ℝ) * ((workers : ℝ) * c)) := by push_cast; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)

theorem instabilityHorizon_pos (δ : ℝ) : 0 < instabilityHorizon δ := by
  unfold instabilityHorizon
  omega

end BirchNonIIDInstability

open MeasureTheory

namespace BirchNonIIDInstability

open OracleTemplate
open LongTails.Setups.BirchNonIID

theorem exact_output_lower {δ s : ℝ} {K R : ℕ} (hK : 0 < K) (hR : 0 < R)
    (hl : ∀ r, (81 / 2500 : ℝ) ≤ ‖gradient (objective (lowerInstance δ))
      (serverPath (lowerInstance δ) (vec s 0) (1 / 100) K r)‖ ^ 2) :
    let A := correctedAveraging 2 2 K R (by norm_num) hK hR (vec s 0) (1 / 100)
    let Q := (A.law : Measure _).prod ((lowerOracle δ).law : Measure _)
    (81 / 2500 : ℝ) / (K : ℝ) ≤
      ∫ seed : A.Seed × ((k : ℕ) → (lowerOracle δ).Seed k),
        ‖gradient (objective (lowerInstance δ))
          (execute (lowerOracle δ) A (fun _ => K * R) seed.1 seed.2)‖ ^ 2 ∂Q := by
  have hf (i : Fin 2) (z : OracleTemplate.Rennala.Point 2) :
      HasGradientAt ((lowerInstance δ).localObjective i)
        (gradient ((lowerInstance δ).localObjective i) z) z := by
    change HasGradientAt (clientPotential δ (clientSign i))
      (gradient (clientPotential δ (clientSign i)) z) z
    rw [gradient_clientPotential]
    exact hasGradientAt_clientPotential δ (clientSign i) z
  have hm := correctedAveraging_output_moments (by norm_num : 0 < 2) hK hR
    (lowerInstance δ) hf (exactClient δ) unitStream_iid (exactClient_stochastic δ) (vec s 0) (1 / 100)
  have hb := referencePoint_average_lower (by norm_num : 0 < 2) hK hR
    (lowerInstance δ) (vec s 0) (1 / 100) (81 / 2500) hl
  set_option backward.isDefEq.respectTransparency false in
    exact hb.trans hm.2.symm.le

/-- A fully admissible instance defeats the actual uniformly sampled query output,
for every positive number of rounds, when the horizon is the constructed one. -/
theorem admissible_sampled_output_failure {δ ε : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 1000000) (hε0 : 0 < ε)
    (hε : ε < (81 / 2500 : ℝ) / (instabilityHorizon δ : ℝ)) :
    ∃ s ∈ Set.Icc (4 / 25 : ℝ) (9 / 50),
      Valid (lowerParams δ s ε) ∧
      Admissible (lowerParams δ s ε) (lowerInstance δ) (lowerOracle δ) ∧
      ∀ (R : ℕ) (hR : 0 < R),
        let K := instabilityHorizon δ
        let A := correctedAveraging 2 2 K R (by norm_num) (instabilityHorizon_pos δ) hR
          (vec s 0) (1 / 100)
        ¬ (spec 2).successful (lowerParams δ s ε) (lowerInstance δ)
          (fun seed : A.Seed × ((k : ℕ) → (lowerOracle δ).Seed k) =>
            execute (lowerOracle δ) A (fun _ => K * R) seed.1 seed.2)
          ⟨(A.law : Measure _).prod ((lowerOracle δ).law : Measure _), inferInstance⟩ := by
  obtain ⟨s, hs, hr⟩ := euclidean_server_stagnation hδ0 hδ1
  refine ⟨s, hs, lowerParams_valid hδ0.le hε0, lowerOracle_admissible hδ0.le hs, ?_⟩
  intro R hR
  have hb := exact_output_lower (instabilityHorizon_pos δ) hR (fun r => (hr r).2)
  dsimp only
  intro hsuccess
  have ha := hsuccess.2.2
  change _ ≤ ε at ha
  exact (not_le_of_gt hε) (hb.trans ha)

end BirchNonIIDInstability

namespace BirchNonIIDInstability

theorem instabilityHorizon_log_formula {δ : ℝ} (hδ : 0 < δ) :
    instabilityHorizon δ =
      11002 + ⌈(Real.log 6250 + Real.log (1 / δ)) / Real.log (1009 / 1000 : ℝ)⌉₊ := by
  have he : (1 / 10 : ℝ) / ((16 / 1000000 : ℝ) * δ) = 6250 * (1 / δ) := by
    field_simp
    ring
  unfold instabilityHorizon
  rw [he, Real.log_mul (by norm_num : (6250 : ℝ) ≠ 0) (by positivity : (1 / δ : ℝ) ≠ 0)]
  omega

/-- Explicit two-sided logarithmic horizon bounds, including all rounding overhead. -/
theorem instabilityHorizon_log_bounds {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    11002 + (Real.log 6250 + Real.log (1 / δ)) / Real.log (1009 / 1000 : ℝ) ≤
      (instabilityHorizon δ : ℝ) ∧
    (instabilityHorizon δ : ℝ) <
      11003 + (Real.log 6250 + Real.log (1 / δ)) / Real.log (1009 / 1000 : ℝ) := by
  have hi : (1 : ℝ) ≤ 1 / δ := (le_div_iff₀ hδ0).mpr (by simpa using hδ1)
  have hn : 0 ≤ (Real.log 6250 + Real.log (1 / δ)) / Real.log (1009 / 1000 : ℝ) :=
    div_nonneg (add_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg hi))
      (Real.log_pos (by norm_num)).le
  rw [instabilityHorizon_log_formula hδ0]
  push_cast
  constructor
  · linarith [Nat.le_ceil ((Real.log 6250 + Real.log (1 / δ)) / Real.log (1009 / 1000 : ℝ))]
  · linarith [Nat.ceil_lt_add_one hn]

end BirchNonIIDInstability

open Filter
open scoped Topology

namespace BirchNonIIDInstability

theorem amplitude_mul_horizon_tendsto_zero :
    Tendsto (fun δ : ℝ => δ * (instabilityHorizon δ : ℝ)) (𝓝[>] 0) (𝓝 0) := by
  have hid : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hlog : Tendsto (fun δ : ℝ => Real.log δ * δ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one] using tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 1)
  have hu : Tendsto (fun δ : ℝ => 11003 * δ +
      (Real.log 6250 * δ - Real.log δ * δ) / Real.log (1009 / 1000 : ℝ))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using (hid.const_mul 11003).add (((hid.const_mul (Real.log 6250)).sub hlog).div_const _)
  apply squeeze_zero' ?_ ?_ hu
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact mul_nonneg (le_of_lt hδ) (Nat.cast_nonneg _)
  · have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < 1 :=
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with δ hδ hs
    have hb := mul_le_mul_of_nonneg_left (instabilityHorizon_log_bounds hδ hs.le).2.le hδ.le
    have he : δ * (11003 + (Real.log 6250 + Real.log (1 / δ)) /
        Real.log (1009 / 1000 : ℝ)) = 11003 * δ +
        (Real.log 6250 * δ - Real.log δ * δ) / Real.log (1009 / 1000 : ℝ) := by
      rw [one_div, Real.log_inv]
      ring
    exact he ▸ hb

/-- The instability persists despite an arbitrarily small step × horizon × similarity product.
The setup's similarity parameter is six times the construction amplitude. -/
theorem step_horizon_similarity_tendsto_zero :
    Tendsto (fun δ : ℝ => (1 / 100 : ℝ) * (instabilityHorizon δ : ℝ) * (6 * δ))
      (𝓝[>] 0) (𝓝 0) := by
  have h := amplitude_mul_horizon_tendsto_zero.const_mul (6 / 100 : ℝ)
  convert h using 1 <;> first | (funext δ; ring) | norm_num

theorem exists_arbitrarily_small_similarity_product {τ : ℝ} (hτ : 0 < τ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 1000000 ∧
      (1 / 100 : ℝ) * (instabilityHorizon δ : ℝ) * (6 * δ) < τ := by
  have hp : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      (1 / 100 : ℝ) * (instabilityHorizon δ : ℝ) * (6 * δ) < τ :=
    (tendsto_order.mp step_horizon_similarity_tendsto_zero).2 τ hτ
  have hs : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < 1 / 1000000 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 1000000)).filter_mono nhdsWithin_le_nhds
  have he : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ ∧ δ ≤ 1 / 1000000 ∧
      (1 / 100 : ℝ) * (instabilityHorizon δ : ℝ) * (6 * δ) < τ := by
    filter_upwards [self_mem_nhdsWithin, hs, hp] with δ hd hs hp
    exact ⟨hd, hs.le, hp⟩
  exact he.exists

end BirchNonIIDInstability
