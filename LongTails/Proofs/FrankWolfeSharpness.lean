import LongTails.Proofs.FrankWolfeCoordinates
import LongTails.Proofs.FrankWolfeSlowTrajectory
import LongTails.Proofs.FrankWolfeExecution

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.FrankWolfe.HardInstance

open LongTails.Setups.UniformlyConvexHolder

open HardDynamics

noncomputable def normalScale (r : ℝ) : ℝ := coefficient r * r / 2

lemma normalScale_pos {r : ℝ} (hr : 2 < r) : 0 < normalScale r :=
  div_pos (mul_pos (coefficient_pos hr) (by linarith)) (by norm_num)

noncomputable def params (q r start ε : ℝ) : Params where
  E := Plane
  L := 2
  x0 := point q r (normalScale r) start 1 1
  D := 4
  a := twoBallModulus q
  q := q
  c := errorConstant r
  r := r
  ε := ε

noncomputable def problem (q r start ε : ℝ) : Instance (params q r start ε).toPublic where
  f := objective r
  C := twoBall q

lemma params_valid {q r start ε : ℝ} (hq : 3 < q) (hr : 2 < r) (hε : 0 < ε) :
    spec.valid (params q r start ε) :=
  ⟨by norm_num [params], by norm_num [params], twoBallModulus_pos (by linarith), hq, errorConstant_pos hr, hr, hε⟩

lemma instance_admissible {q r start ε : ℝ} (hq : 3 < q) (hr : 2 < r)
    (hstart : point q r (normalScale r) start 1 1 ∈ twoBall q) :
    spec.admissible (params q r start ε) (problem q r start ε) (oracle q r (by linarith)) := by
  refine ⟨twoBall_compact (by linarith), twoBall_uniformly_convex (by linarith), hstart,
    fun x hx y hy => twoBall_diameter (by linarith) hx hy,
    objective_convex (by linarith) hr, ?_, ?_, ?_, ?_⟩
  · intro k seed x hx
    exact hasGradient hr x
  · intro k seed x hx y hy
    exact grad_lipschitz (by linarith) hr hx hy
  · intro k seed g
    exact lmo_spec q (by linarith) g
  · refine ⟨optimum, optimum_mem (by linarith), optimum_minimizes (by linarith) hr, ?_⟩
    intro x hx
    change Plane at x
    refine ⟨optimum, optimum_mem (by linarith), optimum_minimizes (by linarith) hr, ?_⟩
    change ‖(x : Plane) - optimum‖ ≤ errorConstant r * (objective r x - objective r optimum) ^ (1 / r)
    rw [objective_optimum hr, sub_zero]
    exact holder_bound (by linarith) hr hx

noncomputable def trajectory (q r start : ℝ) (n : ℕ) : Plane :=
  let p := normalizedOrbit q r (normalScale r) start n
  point q r (normalScale r) p.1 p.2 ((-1 : ℝ) ^ n)

lemma trajectory_zero (q r start : ℝ) :
    trajectory q r start 0 = point q r (normalScale r) start 1 1 := rfl

lemma trajectory_step {q r start δ radius : ℝ} (hq : 3 < q) (hr : 2 < r)
    (hδ : 0 ≤ δ) (hδquarter : δ ≤ 1 / 4) (hstart : 0 < start) (hstartmax : start ≤ radius)
    (hstable : ∀ u ∈ Icc (0 : ℝ) radius, ∀ v ∈ Icc (1 - δ) (1 + δ),
      0 < radial q r (normalScale r) u v ∧ stepSize q r (normalScale r) u v ≤ 1 ∧
      (r - 2 / q + 1) * radial q r (normalScale r) u v * u ^ (r - 2 / q) ≤ 1 / 2 ∧
      |transverse q r (normalScale r) u v - 1| ≤ δ) (n : ℕ) :
    trajectory q r start (n + 1) = shortStep 2 (trajectory q r start n)
      (grad r (trajectory q r start n)) (lmo q (by linarith) (grad r (trajectory q r start n))) := by
  let m := normalScale r
  let u := (normalizedOrbit q r m start n).1
  let v := (normalizedOrbit q r m start n).2
  let sign := (-1 : ℝ) ^ n
  have hm := normalScale_pos hr
  have hinv := normalizedOrbit_invariant hq hr hδ hstart hstartmax
    (fun u hu v hv => ⟨(hstable u hu v hv).1, (hstable u hu v hv).2.2⟩) n
  have hu : 0 < u := hinv.1
  have hv : 0 < v := by have hh := hinv.2.2.1; dsimp [v]; linarith
  have hs := hstable u ⟨hu.le, hinv.2.1.trans hstartmax⟩ v hinv.2.2
  have hsign : sign ^ 2 = 1 := by dsimp [sign]; rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  have he := (exponents_pos hq hr).1
  have hρ : 0 ≤ radial q r m u v * u ^ (r - 2 / q) :=
    mul_nonneg hs.1.le (Real.rpow_nonneg hu.le _)
  have hf : 0 < 1 - radial q r m u v * u ^ (r - 2 / q) := by
    have hh := hs.2.2.1
    have hh' := mul_nonneg he.le hρ
    nlinarith
  have hg : grad r (point q r m u v sign) = coordinateGradient q r m u v sign := point_gradient
  have hupdate := coordinate_update hq hm hu hv hsign hs.2.1 hf
  change trajectory q r start (n + 1) = shortStep 2 (point q r m u v sign)
    (grad r (point q r m u v sign)) (lmo q _ (grad r (point q r m u v sign)))
  rw [hg, lmo_eq_atom hq hm hu hv hsign, hupdate]
  dsimp [trajectory, normalizedOrbit, u, v, sign, m]
  rw [pow_succ]
  congr 1; ring

lemma exists_slow_execution {q r : ℝ} (hq : 3 < q) (hr : 2 < r) :
    ∃ start > 0,
      (∀ ε > 0, spec.valid (params q r start ε) ∧
        spec.admissible (params q r start ε) (problem q r start ε) (oracle q r (by linarith))) ∧
      ∀ K : ℕ, coefficient r *
        (start ^ (-(r - 2 / q)) + 64 * (r - 2 / q) * normalScale r * (K / 2 : ℕ)) ^
          (-r / (r - 2 / q)) ≤
        objective r ((execute (oracle q r (by linarith))
          (shortStepFrankWolfe 2 (point q r (normalScale r) start 1 1)) (fun _ => K))) := by
  have hm := normalScale_pos hr
  obtain ⟨δ, hδ, hδquarter, radius, hrad, hradh, hstable⟩ := exists_stable_strip hq hr hm
  obtain ⟨feasibleRadius, hfeaspos, hfeas⟩ := small_start_feasible hq hr hm
  let start := min radius feasibleRadius
  have hstart : 0 < start := lt_min hrad hfeaspos
  have hstartrad : start ≤ radius := min_le_left _ _
  have hstartfeas : point q r (normalScale r) start 1 1 ∈ twoBall q :=
    hfeas start ⟨hstart, min_le_right _ _⟩
  have hcore : ∀ u ∈ Icc (0 : ℝ) radius, ∀ v ∈ Icc (1 - δ) (1 + δ),
      0 < radial q r (normalScale r) u v ∧
      (r - 2 / q + 1) * radial q r (normalScale r) u v * u ^ (r - 2 / q) ≤ 1 / 2 ∧
      |transverse q r (normalScale r) u v - 1| ≤ δ := by
    intro u hu v hv
    obtain ⟨hc, _, _, _, _, _, hρ, hV⟩ := hstable u hu v hv
    exact ⟨hc, hρ, hV⟩
  have hinv := normalizedOrbit_invariant hq hr hδ.le hstart hstartrad hcore
  have hstep : ∀ n, trajectory q r start (n + 1) = shortStep 2 (trajectory q r start n)
      (grad r (trajectory q r start n)) (lmo q (by linarith) (grad r (trajectory q r start n))) := by
    apply trajectory_step hq hr hδ.le hδquarter hstart hstartrad
    intro u hu v hv
    obtain ⟨hc, _, _, _, _, hγ, hρ, hV⟩ := hstable u hu v hv
    exact ⟨hc, hγ.le, hρ, hV⟩
  have hbound : ∀ n, (normalizedOrbit q r (normalScale r) start n).1 ^ (-(r - 2 / q)) ≤
      start ^ (-(r - 2 / q)) + 64 * (r - 2 / q) * normalScale r * n := by
    apply normalizedOrbit_reciprocal_bound hq hr hδ.le hstart hstartrad
    intro u hu v hv
    obtain ⟨hc, hcupper, _, _, _, _, hρ, hV⟩ := hstable u hu v hv
    have hc0 := radial_center_le hq hr hm.le
    exact ⟨hc, by nlinarith, hρ, hV⟩
  refine ⟨start, hstart, fun ε hε => ⟨params_valid hq hr hε, instance_admissible hq hr hstartfeas⟩, ?_⟩
  intro K
  have hex := execute_short_step (oracle q r (by linarith)) 2 (point q r (normalScale r) start 1 1)
    (fun _ => ()) (trajectory q r start) (trajectory_zero q r start) hstep K
  rw [hex]
  let u := (normalizedOrbit q r (normalScale r) start (K / 2)).1
  have hp := power_lower_of_reciprocal_upper (hinv (K / 2)).1 (exponents_pos hq hr).1
    (by linarith : 0 ≤ r) (hbound (K / 2))
  have hmul := mul_le_mul_of_nonneg_left hp (coefficient_pos hr).le
  have hobj : coefficient r * u ^ r ≤ objective r (trajectory q r start (K / 2)) := by
    dsimp [objective, trajectory, point, u]
    rw [sub_sub_cancel]
    nlinarith [sq_nonneg (((-1 : ℝ) ^ (K / 2)) *
      k q (normalScale r) (normalizedOrbit q r (normalScale r) start (K / 2)).2 *
      (normalizedOrbit q r (normalScale r) start (K / 2)).1 ^ (r - 1 / q))]
  exact hmul.trans hobj

end OracleTemplate.FrankWolfe.HardInstance
