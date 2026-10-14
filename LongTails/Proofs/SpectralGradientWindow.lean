import LongTails.Proofs.SpectralGradientFit
import LongTails.Proofs.SpectralGradientNonlinear

open scoped RealInnerProductSpace

namespace OracleTemplate.SpectralGradient

open LongTails.Setups.MinimizerRegularHessian

lemma linear_probe_nonexpansive (p : Params) (hμ : 0 < p.μ) (hμL : p.μ ≤ p.L)
    (A : Model p.E)
    (hA : ∀ x, p.μ * ‖x‖ ^ 2 ≤ ⟪A.map x, x⟫ ∧ ⟪A.map x, x⟫ ≤ p.L * ‖x‖ ^ 2)
    (x y : p.E) :
    ‖(x - (1 / (2 * p.L)) • A.map x) - (y - (1 / (2 * p.L)) • A.map y)‖ ≤ ‖x - y‖ := by
  have hL : 0 < p.L := hμ.trans_le hμL
  have hh := probe_step_bound A.map A.symmetric hμ hμL (fun x => (hA x).1) (fun x => (hA x).2) (x - y)
  have he : x - y - (1 / (2 * p.L)) • A.map (x - y) =
      (x - (1 / (2 * p.L)) • A.map x) - (y - (1 / (2 * p.L)) • A.map y) := by
    rw [map_sub]; module
  rw [he] at hh
  apply hh.trans
  have hp : 0 ≤ p.μ / (2 * p.L) := by positivity
  nlinarith [norm_nonneg (x - y)]

lemma linear_window_bound (p : Params) (hμ : 0 < p.μ) (hμL : p.μ ≤ p.L)
    (A B : Model p.E)
    (hA : ∀ x, p.μ * ‖x‖ ^ 2 ≤ ⟪A.map x, x⟫ ∧ ⟪A.map x, x⟫ ≤ p.L * ‖x‖ ^ 2)
    (hB : ∀ x, p.μ * ‖x‖ ^ 2 ≤ ⟪B.map x, x⟫ ∧ ⟪B.map x, x⟫ ≤ p.L * ‖x‖ ^ 2)
    (q : ℕ → p.E) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrA : ∀ j < Module.finrank ℝ p.E,
      ‖q (j + 1) - (q j - (1 / (2 * p.L)) • A.map (q j))‖ ≤ δ)
    (hrB : ∀ j < Module.finrank ℝ p.E,
      ‖q (j + 1) - (q j - (1 / (2 * p.L)) • B.map (q j))‖ ≤ δ) :
    ‖sweep (LinearMap.id - A.map.toLinearMap)
      (List.ofFn (fun i : Fin (Module.finrank ℝ p.E) => 1 / B.symmetric.eigenvalues rfl i))
      (q (Module.finrank ℝ p.E))‖ ≤
      3 * (Module.finrank ℝ p.E : ℝ) * δ * (4 * p.L / p.μ) ^ Module.finrank ℝ p.E := by
  let a := 1 / (2 * p.L)
  let κ := p.L / p.μ
  let n := Module.finrank ℝ p.E
  let C : p.E →ₗ[ℝ] p.E := LinearMap.id - a • A.map.toLinearMap
  let D : p.E →ₗ[ℝ] p.E := LinearMap.id - a • B.map.toLinearMap
  let steps := List.ofFn (fun i : Fin n => 1 / B.symmetric.eigenvalues rfl i)
  let rs := steps.map (fun η => η / a)
  have hL : 0 < p.L := hμ.trans_le hμL
  have ha : 0 < a := by dsimp [a]; positivity
  have hk : 0 ≤ κ := by dsimp [κ]; positivity
  have hn : rs.length = n := by simp [rs, steps]
  have heig (i : Fin n) := TemporalDiscrepancy.spectral_eigenvalue_bounds B.map B.symmetric
    (fun x => (hB x).1) (fun x => (hB x).2) i
  have hc : ∀ x y, ‖C x - C y‖ ≤ ‖x - y‖ := linear_probe_nonexpansive p hμ hμL A hA
  have hd : ∀ x y, ‖D x - D y‖ ≤ ‖x - y‖ := linear_probe_nonexpansive p hμ hμL B hB
  have hnorm (r : ℝ) (hr : r ∈ rs) : |r| + |1 - r| ≤ 4 * κ := by
    obtain ⟨η, hη, rfl⟩ := List.mem_map.mp hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hη
    have hi := heig i
    have hi0 : 0 < B.symmetric.eigenvalues rfl i := hμ.trans_le hi.1
    have hratio : (1 / B.symmetric.eigenvalues rfl i) / a =
        2 * p.L / B.symmetric.eigenvalues rfl i := by dsimp [a]; field_simp
    rw [hratio]
    have hlo : 2 ≤ 2 * p.L / B.symmetric.eigenvalues rfl i :=
      (le_div_iff₀ hi0).mpr (by linarith [hi.2])
    have hhi : 2 * p.L / B.symmetric.eigenvalues rfl i ≤ 2 * p.L / p.μ :=
      div_le_div_of_nonneg_left (by positivity) hμ hi.1
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    have he : 2 * p.L / p.μ = 2 * κ := by dsimp [κ]; ring
    rw [he] at hhi
    nlinarith only [hhi]
  have hstep (r : ℝ) (hr : r ∈ rs) (x : p.E) :
      ‖r • C x + (1 - r) • x‖ ≤ κ * ‖x‖ := by
    obtain ⟨η, hη, rfl⟩ := List.mem_map.mp hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hη
    have he : ((1 / B.symmetric.eigenvalues rfl i) / a) • C x +
        (1 - (1 / B.symmetric.eigenvalues rfl i) / a) • x =
        x - (1 / B.symmetric.eigenvalues rfl i) • A.map x := by
      simp only [C, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
        ContinuousLinearMap.coe_coe, smul_sub, smul_smul, div_mul_cancel₀ _ ha.ne']
      module
    rw [he]
    exact correction_step_bound A.map A.symmetric hμ hμL (heig i).1
      (fun x => (hA x).1) (fun x => (hA x).2) x
  have hann : sweep D rs (q 0) = 0 := by
    have he : rs = List.ofFn (fun i : Fin n => 1 / (a * B.symmetric.eigenvalues rfl i)) := by
      simp only [rs, steps, List.map_ofFn]
      congr 1
      funext i
      simp only [Function.comp_apply]
      ring
    rw [he]
    exact spectral_sweep_annihilates B.map B.symmetric ha.ne'
      (fun i => (hμ.trans_le (heig i).1).ne') _
  have hh := sweep_probe_bound C D q hδ hk (by positivity : 0 ≤ 4 * κ) hc hd hrA hrB rs hn hnorm hstep hann
  have he : sweep C rs = sweep (LinearMap.id - A.map.toLinearMap) steps :=
    sweep_rescale A.map.toLinearMap ha.ne' steps
  rw [he] at hh
  have hp : κ ^ n ≤ (4 * κ) ^ n := pow_le_pow_left₀ hk (by linarith) n
  have hm := mul_le_mul_of_nonneg_right hp (mul_nonneg (Nat.cast_nonneg n) hδ)
  have heq : 4 * p.L / p.μ = 4 * κ := by dsimp [κ]; ring
  rw [heq]
  change ‖sweep (LinearMap.id - A.map.toLinearMap) steps (q n)‖ ≤ 3 * (n : ℝ) * δ * (4 * κ) ^ n
  nlinarith only [hh, hm]

lemma window_gradient_bound (p : Params) (hμ : 0 < p.μ) (hμL : p.μ ≤ p.L) (hM : 0 ≤ p.M)
    {f : p.E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ (gradient f))
    (hs : ∀ x y, f x + ⟪gradient f x, y - x⟫ + p.μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (u : p.E) (hu : gradient f u = 0)
    (hH : ∀ z, ‖fderiv ℝ (gradient f) z - fderiv ℝ (gradient f) u‖ ≤ p.M * ‖z - u‖)
    (x : p.E) :
    ‖gradient f (window p (gradient f) x)‖ ≤
      4 * ((Module.finrank ℝ p.E : ℝ) + 1) ^ 2 *
        (4 * p.L ^ 2 / p.μ ^ 2) ^ Module.finrank ℝ p.E * p.M / p.μ ^ 2 * ‖gradient f x‖ ^ 2 := by
  let d := Module.finrank ℝ p.E
  let κ := p.L / p.μ
  let c := p.M / p.μ ^ 2
  let G := ‖gradient f x‖
  let q := fun j => gradient f (probePoint p (gradient f) x j)
  let history := probeHistory p (gradient f) x (d + 1)
  let B := fit p history
  let A : Model p.E := ⟨fderiv ℝ (gradient f) u, hessian_symmetric hf hg u⟩
  let steps := spectralSteps p history
  let δ := p.M * G ^ 2 / (2 * p.μ * p.L)
  have hL : 0 < p.L := hμ.trans_le hμL
  have hk1 : 1 ≤ κ := (le_div_iff₀ hμ).mpr (by simpa using hμL)
  have hk : 0 ≤ κ := by linarith
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hG : 0 ≤ G := norm_nonneg _
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hex : ∃ B, Fits p history B := probe_fit_exists p hμ hμL hM hf hg hs hlip u hu hH x
  have hfit : Fits p history B := fit_fits p history hex
  have hA : ∀ v, p.μ * ‖v‖ ^ 2 ≤ ⟪A.map v, v⟫ ∧ ⟪A.map v, v⟫ ≤ p.L * ‖v‖ ^ 2 :=
    fun v => ⟨NonlinearTemporalDiscrepancy.hessian_lower_bound hg hs u v,
      NonlinearTemporalDiscrepancy.hessian_upper_bound hL.le hlip u v⟩
  have hrA : ∀ j < d, ‖q (j + 1) - (q j - (1 / (2 * p.L)) • A.map (q j))‖ ≤ δ :=
    fun j _ => probe_residual p hμ hμL hM hf hg hs hlip u hu hH x j
  have hrB : ∀ j < d, ‖q (j + 1) - (q j - (1 / (2 * p.L)) • B.map (q j))‖ ≤ δ := by
    intro j hj
    have hh := hfit.2 j hj
    dsimp [history] at hh
    rw [probeHistory_getD p (gradient f) x (by omega : j + 1 < d + 1),
      probeHistory_getD p (gradient f) x (by omega : j < d + 1),
      probeHistory_getD p (gradient f) x (by omega : 0 < d + 1), probePoint_zero] at hh
    exact hh
  have hlinear : ‖sweep (LinearMap.id - A.map.toLinearMap) steps (q d)‖ ≤
      3 * (d : ℝ) * δ * (4 * p.L / p.μ) ^ d :=
    linear_window_bound p hμ hμL A B hA hfit.1 q hδ hrA hrB
  have hsteps (η : ℝ) (hη : η ∈ steps) : 0 < η ∧ η ≤ 1 / p.μ :=
    spectralSteps_bounds p hμ history hex η hη
  have hgrowth (η : ℝ) (hη : η ∈ steps) (y : p.E) :
      ‖gradient f (y - η • gradient f y)‖ ≤ (2 * κ) * ‖gradient f y‖ := by
    convert gradient_growth hμ hμL (hsteps η hη).1.le (hsteps η hη).2 hlip y using 1;
      dsimp [κ]; ring
  have hlin (η : ℝ) (hη : η ∈ steps) (v : p.E) :
      ‖v - η • A.map v‖ ≤ κ * ‖v‖ := by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hη
    exact correction_step_bound A.map A.symmetric hμ hμL
      (fitted_eigenvalues p history hex i).1 (fun v => (hA v).1) (fun v => (hA v).2) v
  have hrem (η : ℝ) (hη : η ∈ steps) (y : p.E) :
      ‖gradient f (y - η • gradient f y) - (gradient f y - η • A.map (gradient f y))‖ ≤
        c * (2 * κ) * ‖gradient f y‖ ^ 2 :=
    step_remainder hμ hM (by linarith) (hsteps η hη).1.le (hsteps η hη).2 hg hs u hu hH y (hgrowth η hη y)
  have herr := nonlinear_sweep_error (gradient f) A.map.toLinearMap hk (by linarith : 1 ≤ 2 * κ)
    (by linarith : κ ≤ 2 * κ) hc steps hgrowth hlin hrem (probePoint p (gradient f) x d)
  have hlen : steps.length = d := spectralSteps_length p history
  rw [hlen] at herr
  have hq : ‖q d‖ ≤ G := probe_gradient_bound p hμ hμL hf hg hs hlip x d
  have herr' : ‖gradient f (window p (gradient f) x) -
      sweep (LinearMap.id - A.map.toLinearMap) steps (q d)‖ ≤
      (d : ℝ) * c * (2 * κ) ^ (2 * d) * G ^ 2 := by
    apply herr.trans
    gcongr
  have hδc : δ ≤ c * G ^ 2 := by
    have hh : p.μ ^ 2 ≤ 2 * p.μ * p.L := by nlinarith [mul_le_mul_of_nonneg_left hμL hμ.le]
    have hh' := div_le_div_of_nonneg_left (mul_nonneg hM (sq_nonneg G)) (sq_pos_of_pos hμ) hh
    dsimp [δ, c]
    convert hh' using 1; ring
  have hpow : (4 * p.L / p.μ) ^ d ≤ (4 * κ ^ 2) ^ d := by
    apply pow_le_pow_left₀ (by positivity)
    have he : 4 * p.L / p.μ = 4 * κ := by dsimp [κ]; ring
    rw [he]
    nlinarith
  have hpoweq : (2 * κ) ^ (2 * d) = (4 * κ ^ 2) ^ d := by rw [pow_mul]; congr 1; ring
  have hlinear' : ‖sweep (LinearMap.id - A.map.toLinearMap) steps (q d)‖ ≤
      3 * (d : ℝ) * (c * G ^ 2) * (4 * κ ^ 2) ^ d := by
    apply hlinear.trans
    gcongr
  have hsum := norm_le_norm_sub_add (gradient f (window p (gradient f) x))
    (sweep (LinearMap.id - A.map.toLinearMap) steps (q d))
  rw [hpoweq] at herr'
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  have hp0 : 0 ≤ c * G ^ 2 * (4 * κ ^ 2) ^ d := by positivity
  have hcoeff : 4 * (d : ℝ) ≤ 4 * ((d : ℝ) + 1) ^ 2 := by nlinarith
  have hfinal := mul_le_mul_of_nonneg_right hcoeff hp0
  have heq : 4 * p.L ^ 2 / p.μ ^ 2 = 4 * κ ^ 2 := by dsimp [κ]; ring
  rw [heq]
  change ‖gradient f (window p (gradient f) x)‖ ≤
    4 * ((d : ℝ) + 1) ^ 2 * (4 * κ ^ 2) ^ d * p.M / p.μ ^ 2 * G ^ 2
  calc
    _ ≤ (d : ℝ) * c * (4 * κ ^ 2) ^ d * G ^ 2 +
        3 * (d : ℝ) * (c * G ^ 2) * (4 * κ ^ 2) ^ d :=
      hsum.trans (add_le_add herr' hlinear')
    _ = (4 * (d : ℝ)) * (c * G ^ 2 * (4 * κ ^ 2) ^ d) := by ring
    _ ≤ (4 * ((d : ℝ) + 1) ^ 2) * (c * G ^ 2 * (4 * κ ^ 2) ^ d) := hfinal
    _ = _ := by dsimp [c]; ring

end OracleTemplate.SpectralGradient
