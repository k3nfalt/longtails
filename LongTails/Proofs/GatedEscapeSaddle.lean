import LongTails.Proofs.GatedEscapeAttemptProb

namespace LongTails.Proofs.GatedEscapeSaddle

open MeasureTheory ProbabilityTheory LongTails.Algorithms.GatedPerturbedEscape
  LongTails.Proofs.GatedEscapeProcess LongTails.Proofs.GatedEscapeMoments
  LongTails.Proofs.GatedEscapePhases LongTails.Proofs.GatedEscapeAttempt
  LongTails.Proofs.GatedEscapeMeasurable LongTails.Proofs.GatedEscapeEscape
  LongTails.Proofs.GatedEscapeTrajProb LongTails.Proofs.GatedEscapeEnergy
  LongTails.Proofs.GatedEscapeCoupling LongTails.Proofs.GatedEscapeSlice
  LongTails.Proofs.GatedEscapePancake LongTails.Proofs.GatedEscapeDirection
  LongTails.Proofs.StrongGrowthAgdBlocks LongTails.Proofs.ComparisonTrustTaylor
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p] {σ : ℝ}
variable (cfg : Config) (d : ℕ) (g : E → Ω → E) (f : E → ℝ)

structure SHyp (L ρ γ σ : ℝ) (d : ℕ) : Prop where
  hL : 0 < L
  hρ : 0 < ρ
  hγ : 0 < γ
  hγL : γ ≤ L
  hη : cfg.η = 1 / L
  hθ : 0 < cfg.θ
  hr : cfg.r = cfg.θ / ρ
  hs0 : cfg.s0 = cfg.r / 256
  hθγ : 8 * cfg.θ ≤ γ
  hT : 0 < cfg.T
  hμ : 40 * cfg.θ * cfg.T ≤ L
  haT : (1 + 1 / (5 * (cfg.T : ℝ))) ^ cfg.T ≤ 5 / 4
  hTL : L ≤ 60 * cfg.θ * (cfg.T + 1)
  hτ0 : 0 < cfg.τ0
  h3τ0 : 3 * cfg.τ0 ≤ cfg.r * cfg.θ / 8
  hgrow : 20480 * Real.sqrt d ≤ (1 + (γ - 4 * cfg.θ) / L) ^ cfg.T
  hd : 0 < d
  hb : 0 < cfg.b
  hbdev : 2 ^ 38 * d * σ ^ 2 ≤ cfg.b * L * γ * cfg.r ^ 2
  hbL1 : 2 ^ 21 * (cfg.T : ℝ) ^ 2 * σ ^ 2 ≤ cfg.b * L ^ 2 * cfg.r ^ 2
  hben : 32 * (1 + Real.log cfg.T) * σ ^ 2 ≤ L * cfg.b * cfg.θ * cfg.r ^ 2

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma psi_init_le {ι : Type} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ) {η : ℝ}
    (hη : 0 < η) (heig : ∀ j, η * eig j ≤ 1) (T : ℕ) (v0 : E) :
    Psi b eig η T (v0, 0, 0) ≤ ‖v0‖ ^ 2 / (η * (T + 1)) := by
  unfold Psi
  simp only [Nat.sub_zero]
  have hterm : ∀ j ∈ posSet eig, eig j * (1 - η * eig j) ^ T * ⟪b j, v0⟫ ^ 2 ≤
      ⟪b j, v0⟫ ^ 2 / (η * (T + 1)) := by
    intro j hj
    have hpos : 0 < eig j := (Finset.mem_filter.mp hj).2
    have hx := xpow_le (η * eig j) (by positivity) (heig j) T
    have e : eig j * (1 - η * eig j) ^ T = (η * eig j * (1 - η * eig j) ^ T) / η := by
      field_simp
    rw [e]
    have : η * eig j * (1 - η * eig j) ^ T / η ≤ 1 / (T + 1) / η :=
      div_le_div_of_nonneg_right hx hη.le
    calc η * eig j * (1 - η * eig j) ^ T / η * ⟪b j, v0⟫ ^ 2 ≤ 1 / (T + 1) / η * ⟪b j, v0⟫ ^ 2 :=
          mul_le_mul_of_nonneg_right this (sq_nonneg _)
      _ = ⟪b j, v0⟫ ^ 2 / (η * (T + 1)) := by field_simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [← b.sum_sq_inner_right v0]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)

omit [MeasurableSpace E] [BorelSpace E] in
lemma eig_le_of_lip {L : ℝ} (hL : 0 ≤ L) (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x : E) : ‖fderiv ℝ (gradient f) x‖ ≤ L := by
  have hl : LipschitzWith ⟨L, hL⟩ (gradient f) :=
    LipschitzWith.of_dist_le_mul fun y z => by rw [dist_eq_norm, dist_eq_norm]; exact hlip y z
  exact norm_fderiv_le_of_lipschitz ℝ hl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma eig_bounds {ι : Type} [Fintype ι] (H : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (hc : ∀ i v, ⟪b i, H v⟫ = eig i * ⟪b i, v⟫) {L : ℝ} (hH : ‖H‖ ≤ L) (i : ι) :
    -L ≤ eig i ∧ eig i ≤ L := by
  have h1 : ⟪b i, H (b i)⟫ = eig i := by
    rw [hc, real_inner_self_eq_norm_sq, b.orthonormal.1 i]; ring
  have h2 : |⟪b i, H (b i)⟫| ≤ L := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [b.orthonormal.1 i, one_mul]
    exact (H.le_opNorm _).trans (by rw [b.orthonormal.1 i, mul_one]; exact hH)
  rw [h1] at h2
  exact abs_le.mp h2

lemma pow_le_exp {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : (1 + x) ^ n ≤ Real.exp (n * x) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) n

omit [MeasurableSpace E] [BorelSpace E] in
lemma spectral_setup {L ρ : ℝ} (hsm : Smooth f L ρ) (x : E) (hpos : 0 < Module.finrank ℝ E) :
    ∃ n : ℕ, ∃ b : OrthonormalBasis (Fin (n + 1)) ℝ E, ∃ eig : Fin (n + 1) → ℝ,
      ∀ i v, ⟪b i, fderiv ℝ (gradient f) x v⟫ = eig i * ⟪b i, v⟫ := by
  have hC := hsm.sym x
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℝ E = n + 1 := ⟨Module.finrank ℝ E - 1, by omega⟩
  refine ⟨n, (hC.eigenvectorBasis rfl).reindex (finCongr hn),
    fun i => hC.eigenvalues rfl ((finCongr hn).symm i), fun i v => ?_⟩
  rw [OrthonormalBasis.reindex_apply]
  exact LongTails.Proofs.RelativeCurvatureSpectrum.symmetric_coordinates _ hC _ v

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma exists_neg_eig {ι : Type} [Fintype ι] (H : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E)
    (eig : ι → ℝ) (hc : ∀ i v, ⟪b i, H v⟫ = eig i * ⟪b i, v⟫) {γ : ℝ}
    (hsad : ∃ v : E, ⟪v, H v⟫ < -γ * ‖v‖ ^ 2) : ∃ i, eig i < -γ := by
  obtain ⟨v, hv⟩ := hsad
  by_contra hno
  push Not at hno
  have he := LongTails.Proofs.RelativeCurvatureSpectrum.quadratic_decomposition H b eig hc v
  have : -γ * ‖v‖ ^ 2 ≤ ⟪v, H v⟫ := by
    rw [he, ← b.sum_sq_inner_right, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hno i) (sq_nonneg _))
  linarith

lemma exp_015 : Real.exp (3 / 20) ≤ 118 / 100 := by
  have h := Real.exp_bound_div_one_sub_of_interval (x := 3 / 20) (by norm_num) (by norm_num)
  refine h.trans ?_
  norm_num

lemma dev_numeric {η L γ γ' θ σ b r d qd qp δn : ℝ} {T T' : ℕ} (hηL : η = 1 / L) (hL : 0 < L)
    (hγ : 0 < γ) (hγγ' : γ < γ') (hθ : 0 < θ) (hb : 0 < b) (hr : 0 < r) (hd : 0 < d)
    (hqd : qd = 1 + η * γ' + η * (2 * θ)) (hqp : qp = 1 + η * γ' - 2 * (η * (2 * θ)))
    (hqp1 : 1 ≤ qp) (hT'T : (T' : ℝ) ≤ T) (hηθT : η * θ * T ≤ 1 / 40)
    (hqpT' : qp ^ T' ≤ 2 * (20480 * Real.sqrt d)) (hδn : δn = r / 2)
    (hbdev : 2 ^ 38 * d * σ ^ 2 ≤ b * L * γ * r ^ 2) :
    η ^ 2 * σ ^ 2 / b / (qd ^ 2 - 1) * (qd ^ (2 * T') / δn ^ 2) ≤ 3 / 100 := by
  have hη : 0 < η := by rw [hηL]; positivity
  have hηθ : 0 < η * θ := mul_pos hη hθ
  have hq1 : η * γ ≤ qd - 1 := by
    rw [hqd]; nlinarith [mul_le_mul_of_nonneg_left hγγ'.le hη.le]
  have hηγ : 0 < η * γ := mul_pos hη hγ
  have hqd1 : 1 < qd := by linarith
  have hq2 : 2 * (η * γ) ≤ qd ^ 2 - 1 := by nlinarith
  have hratio : qd ≤ qp * (1 + 6 * (η * θ)) := by
    nlinarith [mul_nonneg hηθ.le (sub_nonneg.mpr hqp1)]
  have hexp : (1 + 6 * (η * θ)) ^ T' ≤ 118 / 100 := by
    refine (pow_le_exp (by positivity) T').trans ?_
    refine le_trans (Real.exp_le_exp.mpr ?_) exp_015
    nlinarith [mul_le_mul_of_nonneg_left hT'T hηθ.le]
  have hA : qd ^ T' ≤ 2 * (20480 * Real.sqrt d) * (118 / 100) := by
    calc qd ^ T' ≤ (qp * (1 + 6 * (η * θ))) ^ T' := pow_le_pow_left₀ (by linarith) hratio T'
      _ = qp ^ T' * (1 + 6 * (η * θ)) ^ T' := mul_pow _ _ _
      _ ≤ 2 * (20480 * Real.sqrt d) * (118 / 100) :=
          mul_le_mul hqpT' hexp (by positivity) (by positivity)
  have hA2 : qd ^ (2 * T') ≤ (2 * (20480 * Real.sqrt d) * (118 / 100)) ^ 2 := by
    rw [pow_mul']; exact pow_le_pow_left₀ (pow_nonneg (by linarith) _) hA 2
  have hX : (2 * (20480 * Real.sqrt d) * (118 / 100)) ^ 2 = (2 * 20480 * (118 / 100)) ^ 2 * d := by
    rw [show (2 * (20480 * Real.sqrt d) * (118 / 100)) ^ 2 =
      (2 * 20480 * (118 / 100)) ^ 2 * Real.sqrt d ^ 2 by ring, Real.sq_sqrt hd.le]
  have hstep1 : η ^ 2 * σ ^ 2 / b / (qd ^ 2 - 1) ≤ η * σ ^ 2 / (2 * b * γ) := by
    rw [div_div, div_le_div_iff₀ (mul_pos hb (by linarith)) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hq2 (by positivity : (0 : ℝ) ≤ η * σ ^ 2 * b)]
  have hstep2 : qd ^ (2 * T') / δn ^ 2 ≤ (2 * 20480 * (118 / 100)) ^ 2 * d / (r / 2) ^ 2 := by
    rw [hδn, ← hX]; exact div_le_div_of_nonneg_right hA2 (by positivity)
  have hL' : L ≠ 0 := hL.ne'
  have hb' : b ≠ 0 := hb.ne'
  have hγ' : γ ≠ 0 := hγ.ne'
  have hr' : r ≠ 0 := hr.ne'
  calc η ^ 2 * σ ^ 2 / b / (qd ^ 2 - 1) * (qd ^ (2 * T') / δn ^ 2)
      ≤ η * σ ^ 2 / (2 * b * γ) * ((2 * 20480 * (118 / 100)) ^ 2 * d / (r / 2) ^ 2) :=
        mul_le_mul hstep1 hstep2 (div_nonneg (pow_nonneg (by linarith) _) (sq_nonneg _))
          (by positivity)
    _ = (2 * (2 * 20480 * (118 / 100)) ^ 2) * (d * σ ^ 2) / (L * b * γ * r ^ 2) := by
        rw [hηL]; field_simp
    _ ≤ 3 / 100 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hbdev]

lemma l1_numeric {η L σ b r : ℝ} {T : ℕ} (hηL : η = 1 / L) (hL : 0 < L) (hb : 0 < b) (hr : 0 < r)
    (hσ : 0 ≤ σ) (hbL1 : 2 ^ 21 * (T : ℝ) ^ 2 * σ ^ 2 ≤ b * L ^ 2 * r ^ 2) :
    T * (η * (σ / Real.sqrt b)) / (r / 40) ≤ 3 / 100 := by
  have hη : 0 < η := by rw [hηL]; positivity
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  rw [div_le_iff₀ (by positivity)]
  have hnn : 0 ≤ T * (η * (σ / Real.sqrt b)) := by positivity
  have hsq : (T * (η * (σ / Real.sqrt b))) ^ 2 ≤ (3 / 100 * (r / 40)) ^ 2 := by
    have e : (T * (η * (σ / Real.sqrt b))) ^ 2 = (T : ℝ) ^ 2 * σ ^ 2 / (L ^ 2 * b) := by
      rw [hηL, mul_pow, mul_pow, div_pow, div_pow, Real.sq_sqrt hb.le]; field_simp
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith [hbL1]
  exact (pow_le_pow_iff_left₀ hnn (by positivity) (by norm_num)).mp hsq

set_option maxHeartbeats 1600000 in
theorem traj_fail_fixed {L ρ γ : ℝ} (H : SHyp cfg L ρ γ σ d) (hdE : d = Module.finrank ℝ E)
    (hsm : Smooth f L ρ) (hN : Noise g (gradient f) p σ) (hσ : 0 ≤ σ) (x g0 : E)
    (hA0 : ‖g0 - gradient f x‖ ≤ 3 * cfg.τ0)
    (hsad : ∃ v : E, ⟪v, fderiv ℝ (gradient f) x v⟫ < -γ * ‖v‖ ^ 2) :
    ∃ S : Set E, MeasurableSet S ∧ (stdGaussian E S).toReal ≤ 1 / 64 + 1 / 40 ∧
      ∀ z ∉ S, ∫ B, (if TG cfg (fderiv ℝ (gradient f) x) cfg.θ
          (vrun cfg g x g0 (clip cfg.r ((cfg.s0 / Real.sqrt d) • z)) B cfg.T) then (0 : ℝ) else 1)
        ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) ≤ 1 / 10 := by
  set Hm := fderiv ℝ (gradient f) x with hHm
  have hL := H.hL
  have hρ := H.hρ
  have hθ := H.hθ
  have hηd := H.hη
  have hr : 0 < cfg.r := by rw [H.hr]; positivity
  have hρr : ρ * cfg.r = cfg.θ := by rw [H.hr]; field_simp
  have hη : 0 < cfg.η := by rw [hηd]; positivity
  have hdpos : (0 : ℝ) < d := by exact_mod_cast H.hd
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdpos
  obtain ⟨n, b, eig, hc⟩ := spectral_setup f hsm x (by rw [← hdE]; exact H.hd)
  obtain ⟨j0, _, hj0min⟩ := Finset.exists_min_image Finset.univ eig ⟨0, Finset.mem_univ _⟩
  set γ' := -eig j0 with hγ'def
  obtain ⟨i1, hi1⟩ := exists_neg_eig Hm b eig hc hsad
  have hγ' : γ < γ' := by have := hj0min i1 (Finset.mem_univ _); linarith
  have hHn : ‖Hm‖ ≤ L := eig_le_of_lip f hL.le hsm.lip x
  have heigb := eig_bounds Hm b eig hc hHn
  have hγ'L : γ' ≤ L := by have := (heigb j0).1; linarith
  have heig : ∀ i, cfg.η * eig i ≤ 1 := by
    intro i; rw [hηd, div_mul_eq_mul_div, one_mul, div_le_one hL]; exact (heigb i).2
  have hηγ' : cfg.η * γ' ≤ 1 := by rw [hηd, div_mul_eq_mul_div, one_mul, div_le_one hL]; exact hγ'L
  have ha : ∀ i, |1 - cfg.η * eig i| ≤ 1 + cfg.η * γ' := by
    intro i
    have h1 := hj0min i (Finset.mem_univ _)
    rw [abs_of_nonneg (by linarith [heig i])]
    nlinarith
  have hθγ := H.hθγ
  set ζ := 2 * cfg.θ with hζ
  set R := 2 * cfg.r with hR
  set qp := 1 + cfg.η * γ' - 2 * (cfg.η * ζ) with hqp
  have hqp1 : 1 + (γ - 4 * cfg.θ) / L ≤ qp := by
    rw [hqp, hζ, hηd]
    have : (γ - 4 * cfg.θ) / L ≤ (γ' - 4 * cfg.θ) / L := div_le_div_of_nonneg_right (by linarith) hL.le
    have e : 1 + 1 / L * γ' - 2 * (1 / L * (2 * cfg.θ)) = 1 + (γ' - 4 * cfg.θ) / L := by
      field_simp; ring
    rw [e]; linarith
  have hqp_ge : 1 ≤ qp := by
    have : 0 ≤ (γ - 4 * cfg.θ) / L := div_nonneg (by linarith) hL.le
    linarith
  have hqp_le : qp ≤ 2 := by rw [hqp]; nlinarith [mul_pos hη hθ]
  set G0 : ℝ := 20480 * Real.sqrt d with hG0
  have hG0pos : 1 < G0 := by
    have : 1 ≤ Real.sqrt d := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by exact_mod_cast H.hd)
    rw [hG0]; nlinarith
  have hex : ∃ t : ℕ, G0 ≤ qp ^ t :=
    ⟨cfg.T, H.hgrow.trans (pow_le_pow_left₀ (by
      have : 0 ≤ (γ - 4 * cfg.θ) / L := div_nonneg (by linarith) hL.le
      linarith) hqp1 _)⟩
  classical
  set T' := Nat.find hex with hT'def
  have hT'T : T' ≤ cfg.T := Nat.find_min' hex (H.hgrow.trans (pow_le_pow_left₀ (by
      have : 0 ≤ (γ - 4 * cfg.θ) / L := div_nonneg (by linarith) hL.le
      linarith) hqp1 _))
  have hG0T' : G0 ≤ qp ^ T' := Nat.find_spec hex
  have hT'pos : 1 ≤ T' := by
    by_contra h0
    have : T' = 0 := by omega
    rw [this, pow_zero] at hG0T'; linarith
  have hqpT' : qp ^ T' ≤ 2 * G0 := by
    obtain ⟨m, hm⟩ : ∃ m, T' = m + 1 := ⟨T' - 1, by omega⟩
    have hlt : ¬ G0 ≤ qp ^ m := Nat.find_min hex (by omega)
    push Not at hlt
    rw [hm, pow_succ]
    nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ qp) m]
  have hμ := H.hμ
  have hTr : (0 : ℝ) < cfg.T := by exact_mod_cast H.hT
  have hηθT : cfg.η * cfg.θ * cfg.T ≤ 1 / 40 := by
    rw [hηd]; field_simp; nlinarith
  have hsmall : 8 * (cfg.η * ζ) * T' ≤ 1 := by
    have : (T' : ℝ) ≤ cfg.T := by exact_mod_cast hT'T
    rw [hζ]; nlinarith [mul_pos hη hθ]
  have hgap : 2 * (cfg.η * ζ) ≤ cfg.η * γ' := by rw [hζ]; nlinarith
  set c := cfg.s0 / Real.sqrt d with hcdef
  have hc0 : 0 < c := by rw [hcdef, H.hs0]; positivity
  have hslice := bad_measure hsm hρ.le x g0 b eig hc j0 (η := cfg.η) (R := R) (ζ := ζ) (γ' := γ') (c := c)
    (Tn := T') (by rw [hγ'def]; ring) ha hη (by rw [hR, hζ]; nlinarith) (by positivity) hgap hsmall hc0
  set S1 := {z : E | ∀ t ≤ T', ‖orbit (fun w => w - cfg.η • (gradient f (x + w) - g0)) t (c • z)‖ ≤ R}
  set S2 := {z : E | 64 * (Module.finrank ℝ E : ℝ) < ‖z‖ ^ 2}
  have hgc : Continuous (gradient f) :=
    LipschitzWith.continuous (K := ⟨|L|, abs_nonneg L⟩) (LipschitzWith.of_dist_le_mul fun y z => by
      rw [dist_eq_norm, dist_eq_norm]
      exact (hsm.lip y z).trans (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _)))
  have hS1m : MeasurableSet S1 := by
    have hΦc : Continuous (fun w : E => w - cfg.η • (gradient f (x + w) - g0)) :=
      continuous_id.sub (((hgc.comp (continuous_const.add continuous_id)).sub continuous_const).const_smul _)
    have : S1 = ⋂ t ∈ Finset.range (T' + 1),
        {z : E | ‖orbit (fun w => w - cfg.η • (gradient f (x + w) - g0)) t (c • z)‖ ≤ R} := by
      ext z; simp [S1]
    rw [this]
    exact Finset.measurableSet_biInter _ (fun t _ => measurableSet_le
      (((orbit_continuous hΦc t).comp (continuous_const_smul c)).norm.measurable) measurable_const)
  have hS2m : MeasurableSet S2 := measurableSet_lt measurable_const (by fun_prop)
  refine ⟨S1 ∪ S2, hS1m.union hS2m, ?_, fun z hz => ?_⟩
  · have h1 : (stdGaussian E S1).toReal ≤ 1 / 40 := by
      refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hslice).trans ?_
      rw [ENNReal.toReal_ofReal (by positivity)]
      rw [div_le_iff₀ (by positivity)]
      have : c * G0 = 80 * cfg.r := by
        rw [hcdef, hG0, H.hs0]; field_simp; ring
      have hm : c * G0 ≤ c * qp ^ T' := mul_le_mul_of_nonneg_left hG0T' hc0.le
      rw [hR]; nlinarith
    have h2 : (stdGaussian E S2).toReal ≤ 1 / 64 := by
      have hint := LongTails.Proofs.GatedEscapeGaussian.norm_sq_tail (E := E) 64 (by norm_num)
      have e : (fun z : E => if 64 * (Module.finrank ℝ E : ℝ) < ‖z‖ ^ 2 then (1 : ℝ) else 0) =
          S2.indicator (fun _ => 1) := by
        funext z; simp only [S2, Set.indicator_apply, Set.mem_ofPred_eq]
      rw [e, integral_indicator_const _ hS2m, smul_eq_mul, mul_one, measureReal_def] at hint
      exact hint
    have hu := measure_union_le (μ := stdGaussian E) S1 S2
    have := ENNReal.toReal_mono (by
      exact ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hu
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at this
    linarith
  · rw [Set.mem_union, not_or] at hz
    obtain ⟨hz1, hz2⟩ := hz
    have hzsq : ‖z‖ ^ 2 ≤ 64 * d := by
      simp only [S2, Set.mem_ofPred_eq, not_lt] at hz2; rw [hdE]; exact hz2
    have hzn : ‖z‖ ≤ 8 * Real.sqrt d := by
      have h8 : (8 * Real.sqrt d) ^ 2 = 64 * d := by rw [mul_pow, Real.sq_sqrt hdpos.le]; ring
      exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (by rw [h8]; exact hzsq)
    have hcz : ‖c • z‖ ≤ cfg.r / 32 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc0]
      calc c * ‖z‖ ≤ c * (8 * Real.sqrt d) := mul_le_mul_of_nonneg_left hzn hc0.le
        _ = cfg.r / 32 := by rw [hcdef, H.hs0]; field_simp; ring
    have hclipz : clip cfg.r (c • z) = c • z := by
      unfold clip; rw [ite_eq_left (hcz.trans (by linarith))]
    rw [hclipz]
    have hexit : ∃ t ≤ T', R < ‖orbit (nmap cfg f x g0) t (c • z)‖ := by
      simp only [S1, Set.mem_ofPred_eq, not_forall, not_le, exists_prop] at hz1
      exact hz1
    set U := 5 * cfg.θ * cfg.r / 8 with hUdef
    have hU : ∀ v : E, ‖v‖ ≤ cfg.r → ‖gradient f (x + v) - Hm v - g0‖ ≤ U := by
      intro v hv
      have ht := hsm.grad_taylor x v
      have e : gradient f (x + v) - Hm v - g0 = (gradient f (x + v) - gradient f x - Hm v) + (gradient f x - g0) := by
        abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      have hv2 : ‖v‖ ^ 2 ≤ cfg.r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hv 2
      have h1 : ρ * ‖v‖ ^ 2 / 2 ≤ cfg.θ * cfg.r / 2 := by
        have := mul_le_mul_of_nonneg_left hv2 hρ.le
        rw [show ρ * cfg.r ^ 2 = (ρ * cfg.r) * cfg.r by ring, hρr] at this
        linarith
      have h2 : ‖gradient f x - g0‖ ≤ cfg.r * cfg.θ / 8 := by
        rw [norm_sub_rev]; linarith [H.h3τ0]
      rw [hUdef]; linarith
    have hTU : cfg.T * (cfg.η * U) ≤ cfg.r / 64 := by
      rw [hUdef]; nlinarith [mul_pos hr hθ]
    set δn := cfg.r / 2 with hδn
    set qd := 1 + cfg.η * γ' + cfg.η * (ρ * R) with hqd
    have hqd1 : 1 < qd := by rw [hqd]; have := mul_pos hη (lt_of_le_of_lt (by linarith) hγ'); nlinarith [mul_pos hρ hr]
    have hlin : ∀ u w : E, ‖u‖ ≤ R → ‖w‖ ≤ R →
        ‖(u - w) - cfg.η • (gradient f (x + u) - gradient f (x + w))‖ ≤ qd * ‖u - w‖ := by
      intro u w hu hw
      have hrem := grad_remainder hsm hρ.le x (x + w) (x + u) (R := R) (by simpa using hw) (by simpa using hu)
      have hd' : x + u - (x + w) = u - w := by abel
      rw [hd'] at hrem
      have hlin1 := linear_step_norm Hm b eig hc (by nlinarith [mul_pos hη hθ] : (0 : ℝ) ≤ 1 + cfg.η * γ') ha (u - w)
      have e : (u - w) - cfg.η • (gradient f (x + u) - gradient f (x + w)) =
          ((u - w) - cfg.η • Hm (u - w)) - cfg.η • (gradient f (x + u) - gradient f (x + w) - Hm (u - w)) := by
        module
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
      have := mul_le_mul_of_nonneg_left hrem hη.le
      rw [hqd]; nlinarith
    have hμθ : 8 * cfg.θ ≤ L / (5 * cfg.T) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have haT : (1 + cfg.η * (L / (5 * cfg.T))) ^ cfg.T ≤ 5 / 4 := by
      have e : cfg.η * (L / (5 * cfg.T)) = 1 / (5 * (cfg.T : ℝ)) := by rw [hηd]; field_simp
      rw [e]; exact H.haT
    have hmain := traj_prob cfg g f H.hb hN hσ hsm x g0 (c • z) b eig hc (δn := δn) hη hr hθ heig hμθ haT
      hT'T hU hTU (by positivity) (by rw [hR, hδn]; linarith) hqd1 hlin hexit hcz
    refine hmain.trans ?_
    have hbpos : (0 : ℝ) < cfg.b := by exact_mod_cast H.hb
    have hdev : cfg.η ^ 2 * σ ^ 2 / cfg.b / (qd ^ 2 - 1) * (qd ^ (2 * T') / δn ^ 2) ≤ 3 / 100 := by
      have hρR : ρ * R = 2 * cfg.θ := by rw [hR]; linarith
      exact dev_numeric hηd hL H.hγ hγ' hθ hbpos hr hdpos (by rw [hqd, hρR]) (by rw [hqp, hζ])
        hqp_ge (by exact_mod_cast hT'T) hηθT (by rw [← hG0]; exact hqpT') hδn H.hbdev
    have hl1 : cfg.T * (cfg.η * (σ / Real.sqrt cfg.b)) / (cfg.r / 40) ≤ 3 / 100 :=
      l1_numeric hηd hL hbpos hr hσ H.hbL1
    have hen : (Psi b eig cfg.η cfg.T (c • z, 0, 0) + cfg.T * (3 * cfg.η * U ^ 2) +
        cfg.η * (σ ^ 2 / cfg.b) * (1 + Real.log cfg.T)) / (4 * cfg.θ * cfg.r ^ 2) ≤ 3 / 100 := by
      have hpsi := psi_init_le b eig hη heig cfg.T (c • z)
      have hcz2 : ‖c • z‖ ^ 2 ≤ (cfg.r / 32) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hcz 2
      have h1 : Psi b eig cfg.η cfg.T (c • z, 0, 0) ≤ 60 * cfg.θ * cfg.r ^ 2 / 1024 := by
        refine hpsi.trans ?_
        rw [div_le_iff₀ (by positivity)]
        have hTL := H.hTL
        have e : cfg.η * (cfg.T + 1) = (cfg.T + 1) / L := by rw [hηd]; ring
        rw [e]
        have : (cfg.r / 32) ^ 2 * L ≤ 60 * cfg.θ * cfg.r ^ 2 / 1024 * (cfg.T + 1) := by nlinarith
        calc ‖c • z‖ ^ 2 ≤ (cfg.r / 32) ^ 2 := hcz2
          _ ≤ 60 * cfg.θ * cfg.r ^ 2 / 1024 * ((cfg.T + 1) / L) := by
              rw [mul_div_assoc', le_div_iff₀ hL]; linarith
      have h2 : cfg.T * (3 * cfg.η * U ^ 2) ≤ 75 * cfg.θ * cfg.r ^ 2 / 2560 := by
        rw [hUdef, hηd]
        have : (cfg.T : ℝ) ≤ L / (40 * cfg.θ) := by rw [le_div_iff₀ (by positivity)]; linarith
        have e : cfg.T * (3 * (1 / L) * (5 * cfg.θ * cfg.r / 8) ^ 2) =
            cfg.T * (75 * cfg.θ ^ 2 * cfg.r ^ 2 / (64 * L)) := by ring
        rw [e]
        calc cfg.T * (75 * cfg.θ ^ 2 * cfg.r ^ 2 / (64 * L)) ≤
            L / (40 * cfg.θ) * (75 * cfg.θ ^ 2 * cfg.r ^ 2 / (64 * L)) :=
              mul_le_mul_of_nonneg_right this (by positivity)
          _ = 75 * cfg.θ * cfg.r ^ 2 / 2560 := by field_simp; ring
      have h3 : cfg.η * (σ ^ 2 / cfg.b) * (1 + Real.log cfg.T) ≤ cfg.θ * cfg.r ^ 2 / 32 := by
        rw [hηd]
        have e : 1 / L * (σ ^ 2 / cfg.b) * (1 + Real.log cfg.T) = (1 + Real.log cfg.T) * σ ^ 2 / (L * cfg.b) := by
          field_simp
        rw [e, div_le_iff₀ (by positivity)]
        nlinarith [H.hben]
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_pos hθ (pow_pos hr 2)]
    linarith


lemma vrun_meas (hg : Measurable (Function.uncurry g)) (x : E) : ∀ T : ℕ,
    Measurable (fun q : E × E × (ℕ → (Fin cfg.b → Ω)) => vrun cfg g x q.1 q.2.1 q.2.2 T) := by
  intro T
  induction T with
  | zero => exact measurable_fst.comp measurable_snd
  | succ T ih =>
    show Measurable (fun q : E × E × (ℕ → (Fin cfg.b → Ω)) =>
      clip cfg.r (vrun cfg g x q.1 q.2.1 q.2.2 T - cfg.η • (bmean cfg g (x + vrun cfg g x q.1 q.2.1 q.2.2 T) (q.2.2 T) - q.1)))
    have hb := bmean_measurable_joint cfg hg (q := fun q : E × E × (ℕ → (Fin cfg.b → Ω)) =>
      x + vrun cfg g x q.1 q.2.1 q.2.2 T) (measurable_const.add ih)
    have hb2 : Measurable (fun q : E × E × (ℕ → (Fin cfg.b → Ω)) =>
        bmean cfg g (x + vrun cfg g x q.1 q.2.1 q.2.2 T) (q.2.2 T)) :=
      hb.comp (measurable_id.prodMk ((measurable_pi_apply T).comp (measurable_snd.comp measurable_snd)))
    exact (LongTails.Proofs.GatedEscapeMeasurable.measurable_clip cfg.r).comp (ih.sub ((hb2.sub measurable_fst).const_smul _))

omit [BorelSpace E] in
lemma integral_fst_stream (φ : (ℕ → (Fin cfg.b → Ω)) → ℝ) (hφ : Measurable φ) :
    ∫ tail, φ (fun n => (tail n).1)
        ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p).prod (stdGaussian E)) =
      ∫ B, φ B ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) := by
  have hmap := Measure.infinitePi_map_pi (μ := fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p).prod (stdGaussian E))
    (f := fun _ => (Prod.fst : (Fin cfg.b → Ω) × E → Fin cfg.b → Ω)) (fun _ => measurable_fst)
  have hfst : ((Measure.pi fun _ : Fin cfg.b => p).prod (stdGaussian E)).map Prod.fst =
      Measure.pi fun _ : Fin cfg.b => p := by
    rw [Measure.map_fst_prod]; simp
  simp_rw [hfst] at hmap
  have hm : AEMeasurable (fun (x : ℕ → (Fin cfg.b → Ω) × E) (i : ℕ) => (x i).1)
      (Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p).prod (stdGaussian E)) :=
    (measurable_pi_iff.mpr fun n => measurable_fst.comp (measurable_pi_apply n)).aemeasurable
  rw [← hmap, integral_map hm hφ.aestronglyMeasurable]

omit [BorelSpace E] in
lemma integral_snd_prod' (μ : Measure (Fin cfg.b → Ω)) [IsProbabilityMeasure μ] (F : E → ℝ) (hF : Measurable F) :
    ∫ y, F y.2 ∂(μ.prod (stdGaussian E)) = ∫ z, F z ∂(stdGaussian E) := by
  rw [← integral_map measurable_snd.aemeasurable hF.aestronglyMeasurable, Measure.map_snd_prod]
  simp

lemma vrun_joint_measurable (hg : Measurable (Function.uncurry g)) (hgf : Continuous (gradient f))
    (x g0 : E) (T : ℕ) (V : (Fin cfg.b → Ω) × E → E) (hV : Measurable V) :
    Measurable (fun q : ((Fin cfg.b → Ω) × E) × (ℕ → (Fin cfg.b → Ω) × E) =>
      vrun cfg g x g0 (V q.1) (fun n => (q.2 n).1) T) := by
  have hstep := tstep_measurable cfg g (gradient f) hg hgf x g0
  have hr := run_measurable₂ (tstep cfg g (gradient f) x g0) hstep T
  have h2 : (fun q : ((Fin cfg.b → Ω) × E) × (ℕ → (Fin cfg.b → Ω) × E) =>
      vrun cfg g x g0 (V q.1) (fun n => (q.2 n).1) T) =
      fun q => (run (tstep cfg g (gradient f) x g0) (V q.1, 0, 0) (fun n => (q.2 n).1) T).1 := by
    funext q; exact ((tstep_run cfg g f x g0 (V q.1) _ T).1).symm
  rw [h2]
  have hin : Measurable (fun q : ((Fin cfg.b → Ω) × E) × (ℕ → (Fin cfg.b → Ω) × E) =>
      (((V q.1, (0 : ℕ), (0 : ℝ)) : E × ℕ × ℝ), fun n => (q.2 n).1)) :=
    ((hV.comp measurable_fst).prodMk measurable_const).prodMk
      (measurable_pi_iff.mpr fun n => measurable_fst.comp ((measurable_pi_apply n).comp measurable_snd))
  exact measurable_fst.comp (hr.comp hin)

theorem inner_traj {L ρ γ : ℝ} (H : SHyp cfg L ρ γ σ d) (hdE : d = Module.finrank ℝ E)
    (hsm : Smooth f L ρ) (hN : Noise g (gradient f) p σ) (hσ : 0 ≤ σ) (x g0 : E)
    (hA0 : ‖g0 - gradient f x‖ ≤ 3 * cfg.τ0)
    (hsad : ∃ v : E, ⟪v, fderiv ℝ (gradient f) x v⟫ < -γ * ‖v‖ ^ 2) :
    ∫ tail, (if TG cfg (fderiv ℝ (gradient f) x) cfg.θ
        (vrun cfg g x g0 (clip cfg.r ((cfg.s0 / Real.sqrt d) • (tail 0).2)) (fun n => (tail (1 + n)).1)
          cfg.T) then (0 : ℝ) else 1)
      ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p).prod (stdGaussian E)) ≤
      3 / 20 := by
  set ν := (Measure.pi fun _ : Fin cfg.b => p).prod (stdGaussian E)
  obtain ⟨S, hSm, hSγ, hS⟩ := traj_fail_fixed cfg d g f H hdE hsm hN hσ x g0 hA0 hsad
  have hgf : Continuous (gradient f) :=
    LipschitzWith.continuous (K := ⟨|L|, abs_nonneg L⟩) (LipschitzWith.of_dist_le_mul fun y z => by
      rw [dist_eq_norm, dist_eq_norm]
      exact (hsm.lip y z).trans (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _)))
  set V : (Fin cfg.b → Ω) × E → E := fun y => clip cfg.r ((cfg.s0 / Real.sqrt d) • y.2) with hV
  have hVm : Measurable V := (LongTails.Proofs.GatedEscapeMeasurable.measurable_clip cfg.r).comp (measurable_snd.const_smul _)
  set F2 : ((Fin cfg.b → Ω) × E) → (ℕ → (Fin cfg.b → Ω) × E) → ℝ := fun y tail =>
    if TG cfg (fderiv ℝ (gradient f) x) cfg.θ (vrun cfg g x g0 (V y) (fun n => (tail n).1) cfg.T)
    then 0 else 1 with hF2
  have hF2m : Measurable (Function.uncurry F2) :=
    Measurable.ite ((vrun_joint_measurable cfg g f hN.meas hgf x g0 cfg.T V hVm)
      (TG_measurable cfg _ cfg.θ)) measurable_const measurable_const
  have : Nonempty ((Fin cfg.b → Ω) × E) := Measure.nonempty_of_neZero ν
  set a : (Fin cfg.b → Ω) × E := Classical.arbitrary _
  set step0 : ((Fin cfg.b → Ω) × E) → ((Fin cfg.b → Ω) × E) → ((Fin cfg.b → Ω) × E) := fun _ y => y
  have hstep0 : Measurable (Function.uncurry step0) := measurable_snd
  have hrw : (fun tail : ℕ → (Fin cfg.b → Ω) × E => (if TG cfg (fderiv ℝ (gradient f) x) cfg.θ
        (vrun cfg g x g0 (clip cfg.r ((cfg.s0 / Real.sqrt d) • (tail 0).2)) (fun n => (tail (1 + n)).1)
          cfg.T) then (0 : ℝ) else 1)) = fun tail => F2 (run step0 a tail 1) (shift 1 tail) := by
    funext tail; rfl
  have hint : Integrable (fun tail => F2 (run step0 a tail 1) (shift 1 tail)) (Measure.infinitePi fun _ : ℕ => ν) :=
    Integrable.of_bound (C := 1)
      (hF2m.comp ((run_measurable step0 a hstep0 1).prodMk (shift_measurable 1))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun β => by simp only [hF2]; split_ifs <;> simp)
  rw [hrw, tail_integral step0 a ν hstep0 1 F2 hF2m hint]
  have hinner_m : Measurable (fun y => ∫ tail, F2 y tail ∂(Measure.infinitePi fun _ : ℕ => ν)) :=
    (hF2m.stronglyMeasurable.integral_prod_right' (ν := Measure.infinitePi fun _ : ℕ => ν)).measurable
  have hev : ∫ β, ∫ tail, F2 (run step0 a β 1) tail ∂(Measure.infinitePi fun _ : ℕ => ν)
      ∂(Measure.infinitePi fun _ : ℕ => ν) = ∫ y, ∫ tail, F2 y tail ∂(Measure.infinitePi fun _ : ℕ => ν) ∂ν :=
    integral_eval ν (fun y => ∫ tail, F2 y tail ∂(Measure.infinitePi fun _ : ℕ => ν)) hinner_m
  rw [hev]
  have hpt : ∀ y, ∫ tail, F2 y tail ∂(Measure.infinitePi fun _ : ℕ => ν) ≤
      S.indicator (fun _ => (1 : ℝ)) y.2 + 1 / 10 := by
    intro y
    have hφ : Measurable (fun B : ℕ → (Fin cfg.b → Ω) =>
        if TG cfg (fderiv ℝ (gradient f) x) cfg.θ (vrun cfg g x g0 (V y) B cfg.T) then (0 : ℝ) else 1) := by
      have := (vrun_joint_measurable cfg g f hN.meas hgf x g0 cfg.T V hVm)
      refine Measurable.ite ?_ measurable_const measurable_const
      have hv : Measurable (fun B : ℕ → (Fin cfg.b → Ω) => vrun cfg g x g0 (V y) B cfg.T) := by
        have h2 : (fun B : ℕ → (Fin cfg.b → Ω) => vrun cfg g x g0 (V y) B cfg.T) =
            fun B => (run (tstep cfg g (gradient f) x g0) (V y, 0, 0) B cfg.T).1 := by
          funext B; exact ((tstep_run cfg g f x g0 (V y) B cfg.T).1).symm
        rw [h2]
        exact measurable_fst.comp (run_measurable _ _ (tstep_measurable cfg g (gradient f) hN.meas hgf x g0) _)
      exact hv (TG_measurable cfg _ cfg.θ)
    have he := integral_fst_stream cfg (E := E) (p := p) (fun B => if TG cfg (fderiv ℝ (gradient f) x) cfg.θ
      (vrun cfg g x g0 (V y) B cfg.T) then (0 : ℝ) else 1) hφ
    simp only [hF2]
    rw [he]
    by_cases hy : y.2 ∈ S
    · rw [Set.indicator_of_mem hy]
      have : ∫ B, (if TG cfg (fderiv ℝ (gradient f) x) cfg.θ (vrun cfg g x g0 (V y) B cfg.T) then (0 : ℝ) else 1)
          ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) ≤ 1 := by
        calc _ ≤ ∫ _B, (1 : ℝ) ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) :=
              integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => by split_ifs <;> norm_num)
                (integrable_const _) (Filter.Eventually.of_forall fun _ => by split_ifs <;> norm_num)
          _ = 1 := by simp
      linarith
    · rw [Set.indicator_of_notMem hy, zero_add]
      exact hS y.2 hy
  have hiS1 : Integrable (fun y : (Fin cfg.b → Ω) × E => S.indicator (fun _ => (1 : ℝ)) y.2) ν :=
    Integrable.of_bound (C := 1) (((measurable_const.indicator hSm).comp measurable_snd).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => by
        by_cases hy : y.2 ∈ S <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy])
  have hiS := hiS1.add (integrable_const (1 / 10 : ℝ))
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => integral_nonneg fun _ => by
    simp only [hF2]; split_ifs <;> norm_num) hiS (Filter.Eventually.of_forall hpt)).trans ?_
  rw [integral_add' hiS1 (integrable_const _)]
  rw [integral_snd_prod' cfg _ (S.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hSm),
    integral_indicator_const _ hSm, integral_const]
  simp only [smul_eq_mul, mul_one, measureReal_def]
  have hν1 : (ν Set.univ).toReal = 1 := by simp [ν]
  rw [hν1]
  linarith

theorem prob_traj {L ρ γ : ℝ} (H : SHyp cfg L ρ γ σ d) (hdE : d = Module.finrank ℝ E)
    (hsm : Smooth f L ρ) (hN : Noise g (gradient f) p σ) (hσ : 0 ≤ σ) (hM : 0 < cfg.M)
    (s : State E) (hd : s.done = false) (hph : s.ph = .grad0) (hj : s.j = 0)
    (hsad : ∃ v : E, ⟪v, fderiv ℝ (gradient f) s.x v⟫ < -γ * ‖v‖ ^ 2) :
    ∫ β, (if A0S cfg f s.x (run (astep cfg d g) s β (alen cfg)) ∧
        ¬ TG cfg (fderiv ℝ (gradient f) s.x) cfg.θ (run (astep cfg d g) s β (alen cfg)).v
      then (1 : ℝ) else 0)
      ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p).prod (stdGaussian E)) ≤
      3 / 20 := by
  set ν := (Measure.pi fun _ : Fin cfg.b => p).prod (stdGaussian E)
  have hstep := measurable_astep cfg d g hN.meas
  have hgf : Continuous (gradient f) :=
    LipschitzWith.continuous (K := ⟨|L|, abs_nonneg L⟩) (LipschitzWith.of_dist_le_mul fun y z => by
      rw [dist_eq_norm, dist_eq_norm]
      exact (hsm.lip y z).trans (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _)))
  set F : State E → (ℕ → (Fin cfg.b → Ω) × E) → ℝ := fun s1 tail =>
    if ‖s1.g0 - gradient f s.x‖ ≤ 3 * cfg.τ0 ∧ ¬ TG cfg (fderiv ℝ (gradient f) s.x) cfg.θ
      (vrun cfg g s.x s1.g0 (clip cfg.r ((cfg.s0 / Real.sqrt d) • (tail 0).2)) (fun n => (tail (1 + n)).1) cfg.T)
    then 1 else 0 with hF
  have hFm : Measurable (Function.uncurry F) := by
    refine Measurable.ite ?_ measurable_const measurable_const
    rw [Set.ofPred_and]
    refine MeasurableSet.inter (measurableSet_le ((measurable_g0.comp measurable_fst).sub measurable_const).norm
      measurable_const) (MeasurableSet.compl ?_)
    have hv : Measurable (fun q : State E × (ℕ → (Fin cfg.b → Ω) × E) =>
        vrun cfg g s.x q.1.g0 (clip cfg.r ((cfg.s0 / Real.sqrt d) • (q.2 0).2)) (fun n => (q.2 (1 + n)).1) cfg.T) := by
      have h2 : (fun q : State E × (ℕ → (Fin cfg.b → Ω) × E) =>
          vrun cfg g s.x q.1.g0 (clip cfg.r ((cfg.s0 / Real.sqrt d) • (q.2 0).2)) (fun n => (q.2 (1 + n)).1) cfg.T) =
          fun q => (run (tstep cfg g (gradient f) s.x q.1.g0)
            (clip cfg.r ((cfg.s0 / Real.sqrt d) • (q.2 0).2), 0, 0) (fun n => (q.2 (1 + n)).1) cfg.T).1 := by
        funext q; exact ((tstep_run cfg g f s.x q.1.g0 _ _ cfg.T).1).symm
      have h3 : (fun q : State E × (ℕ → (Fin cfg.b → Ω) × E) =>
          vrun cfg g s.x q.1.g0 (clip cfg.r ((cfg.s0 / Real.sqrt d) • (q.2 0).2)) (fun n => (q.2 (1 + n)).1) cfg.T) =
          (fun q : E × E × (ℕ → (Fin cfg.b → Ω)) => vrun cfg g s.x q.1 q.2.1 q.2.2 cfg.T) ∘
            (fun q : State E × (ℕ → (Fin cfg.b → Ω) × E) =>
              (q.1.g0, clip cfg.r ((cfg.s0 / Real.sqrt d) • (q.2 0).2), fun n => (q.2 (1 + n)).1)) := rfl
      clear h2
      rw [h3]
      refine (vrun_meas cfg g hN.meas s.x cfg.T).comp ?_
      refine (measurable_g0.comp measurable_fst).prodMk (((LongTails.Proofs.GatedEscapeMeasurable.measurable_clip cfg.r).comp
        ((measurable_snd.comp ((measurable_pi_apply 0).comp measurable_snd)).const_smul _)).prodMk ?_)
      exact measurable_pi_iff.mpr fun n => measurable_fst.comp ((measurable_pi_apply (1 + n)).comp measurable_snd)
    exact hv (TG_measurable cfg _ cfg.θ)
  have hrw : (fun β => if A0S cfg f s.x (run (astep cfg d g) s β (alen cfg)) ∧
        ¬ TG cfg (fderiv ℝ (gradient f) s.x) cfg.θ (run (astep cfg d g) s β (alen cfg)).v
      then (1 : ℝ) else 0) = fun β => F (run (astep cfg d g) s β cfg.M) (shift cfg.M β) := by
    funext β
    obtain ⟨_, hg0, hv, _⟩ := post_core cfg d g s hd hph hj hM H.hT β
    have h1 : (run (astep cfg d g) s β cfg.M).g0 = select cfg.M cfg.τ0 (fill cfg g s.store s.x β cfg.M) := by
      rw [run_grad0_end cfg d g s hd hph hj hM β]
    simp only [hF, A0S, hv, hg0, h1, shift, Nat.add_zero]
    simp only [Nat.add_assoc]
  have hint : Integrable (fun β => F (run (astep cfg d g) s β cfg.M) (shift cfg.M β))
      (Measure.infinitePi fun _ : ℕ => ν) :=
    Integrable.of_bound (C := 1)
      (hFm.comp ((run_measurable _ s hstep cfg.M).prodMk (shift_measurable cfg.M))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun β => by simp only [hF]; split_ifs <;> simp)
  rw [hrw, tail_integral (astep cfg d g) s ν hstep cfg.M F hFm hint]
  have hinner : ∀ β, ∫ tail, F (run (astep cfg d g) s β cfg.M) tail ∂(Measure.infinitePi fun _ : ℕ => ν) ≤ 3 / 20 := by
    intro β
    set s1 := run (astep cfg d g) s β cfg.M
    by_cases hA : ‖s1.g0 - gradient f s.x‖ ≤ 3 * cfg.τ0
    · have hI := inner_traj cfg d g f H hdE hsm hN hσ s.x s1.g0 hA hsad
      refine le_trans (le_of_eq ?_) hI
      congr 1; funext tail
      simp only [hF, hA, true_and]
      split_ifs <;> simp_all
    · have : (fun tail => F s1 tail) = fun _ => (0 : ℝ) := by
        funext tail; simp only [hF, hA, false_and, ↓reduceIte]
      rw [this, integral_zero]; norm_num
  calc ∫ β, ∫ tail, F (run (astep cfg d g) s β cfg.M) tail ∂(Measure.infinitePi fun _ : ℕ => ν)
        ∂(Measure.infinitePi fun _ : ℕ => ν) ≤ ∫ _β, (3 / 20 : ℝ) ∂(Measure.infinitePi fun _ : ℕ => ν) :=
        integral_mono (tail_inner_integrable (astep cfg d g) s ν hstep cfg.M F hFm hint)
          (integrable_const _) hinner
    _ = 3 / 20 := by simp

theorem prob_miss {L ρ γ : ℝ} (H : SHyp cfg L ρ γ σ d) (hdE : d = Module.finrank ℝ E)
    (hsm : Smooth f L ρ) (hN : Noise g (gradient f) p σ) (hσ : 0 ≤ σ) (hM : 0 < cfg.M)
    (hM6 : (19 / 32 : ℝ) ^ cfg.M ≤ 1 / 20) (hτq : 0 < cfg.τq) (h3τq : 3 * cfg.τq ≤ 3 * cfg.θ / 8)
    (hvar0 : σ ^ 2 / cfg.b / cfg.τ0 ^ 2 ≤ 1 / 16) (hvarq : σ ^ 2 / cfg.b / (cfg.r * cfg.τq) ^ 2 ≤ 1 / 16)
    (s : State E) (hd : s.done = false) (hph : s.ph = .grad0) (hj : s.j = 0)
    (hsad : ∃ v : E, ⟪v, fderiv ℝ (gradient f) s.x v⟫ < -γ * ‖v‖ ^ 2) :
    ∫ β, (if accS cfg (run (astep cfg d g) s β (alen cfg)) then (0 : ℝ) else 1)
      ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p).prod (stdGaussian E)) ≤ 1 / 4 := by
  set ν := (Measure.pi fun _ : Fin cfg.b => p).prod (stdGaussian E)
  have hstep := measurable_astep cfg d g hN.meas
  have hrun := run_measurable (astep cfg d g) s hstep (alen cfg)
  have hgf : Continuous (gradient f) :=
    LipschitzWith.continuous (K := ⟨|L|, abs_nonneg L⟩) (LipschitzWith.of_dist_le_mul fun y z => by
      rw [dist_eq_norm, dist_eq_norm]
      exact (hsm.lip y z).trans (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _)))
  have hr : 0 < cfg.r := by rw [H.hr]; exact div_pos H.hθ H.hρ
  have hρr : ρ * cfg.r ≤ cfg.θ := by rw [H.hr, mul_div_cancel₀ _ H.hρ.ne']
  have hA0m : MeasurableSet {s' : State E | A0S cfg f s.x s'} :=
    measurableSet_le (measurable_g0.sub measurable_const).norm measurable_const
  have hTGm : MeasurableSet {s' : State E | TG cfg (fderiv ℝ (gradient f) s.x) cfg.θ s'.v} :=
    measurable_v (TG_measurable cfg _ cfg.θ)
  have hi1 : Integrable (fun β => (if A0S cfg f s.x (run (astep cfg d g) s β (alen cfg)) then (0 : ℝ) else 1))
      (Measure.infinitePi fun _ : ℕ => ν) :=
    Integrable.of_bound (C := 1) ((Measurable.ite (hrun hA0m) measurable_const measurable_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun β => by split_ifs <;> simp)
  have hi2 : Integrable (fun β => (if AqS cfg f s.x (run (astep cfg d g) s β (alen cfg)) then (0 : ℝ) else 1))
      (Measure.infinitePi fun _ : ℕ => ν) :=
    Integrable.of_bound (C := 1) ((Measurable.ite (hrun (LongTails.Proofs.GatedEscapeAttemptProb.AqS_measurable
      cfg f hgf s.x)) measurable_const measurable_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun β => by split_ifs <;> simp)
  have hi3 : Integrable (fun β => (if A0S cfg f s.x (run (astep cfg d g) s β (alen cfg)) ∧
        ¬ TG cfg (fderiv ℝ (gradient f) s.x) cfg.θ (run (astep cfg d g) s β (alen cfg)).v
      then (1 : ℝ) else 0)) (Measure.infinitePi fun _ : ℕ => ν) := by
    refine Integrable.of_bound (C := 1) ((Measurable.ite ?_ measurable_const measurable_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun β => by split_ifs <;> simp)
    rw [Set.ofPred_and]
    exact (hrun hA0m).inter (hrun hTGm).compl
  have hpt : ∀ β, (if accS cfg (run (astep cfg d g) s β (alen cfg)) then (0 : ℝ) else 1) ≤
      (if A0S cfg f s.x (run (astep cfg d g) s β (alen cfg)) then (0 : ℝ) else 1) +
      (if AqS cfg f s.x (run (astep cfg d g) s β (alen cfg)) then (0 : ℝ) else 1) +
      (if A0S cfg f s.x (run (astep cfg d g) s β (alen cfg)) ∧
        ¬ TG cfg (fderiv ℝ (gradient f) s.x) cfg.θ (run (astep cfg d g) s β (alen cfg)).v
      then (1 : ℝ) else 0) := by
    intro β
    set post := run (astep cfg d g) s β (alen cfg)
    obtain ⟨_, _, _, hw, _⟩ := post_core cfg d g s hd hph hj hM H.hT β
    by_cases hacc : accS cfg post
    · rw [ite_eq_left hacc]; split_ifs <;> norm_num
    · rw [ite_eq_right hacc]
      by_cases h0 : A0S cfg f s.x post
      · by_cases hq : AqS cfg f s.x post
        · by_cases htg : TG cfg (fderiv ℝ (gradient f) s.x) cfg.θ post.v
          · exfalso
            apply hacc
            refine ⟨htg.1, ?_⟩
            exact LongTails.Proofs.GatedEscapeAccept.accept_ok hsm H.hρ.le s.x post.g0 post.v hr hρr H.h3τ0 h3τq h0
              (by unfold AqS at hq; rw [hw] at hq; exact hq) htg.1 htg.2
          · rw [ite_eq_left h0, ite_eq_left hq, ite_eq_left ⟨h0, htg⟩]; norm_num
        · rw [ite_eq_left h0, ite_eq_right hq]; split_ifs <;> norm_num
      · rw [ite_eq_right h0]; split_ifs <;> norm_num
  have hm := integral_mono_of_nonneg (Filter.Eventually.of_forall fun β =>
    ite_nonneg le_rfl zero_le_one) ((hi1.add hi2).add hi3) (Filter.Eventually.of_forall hpt)
  rw [integral_add' (hi1.add hi2) hi3, integral_add' hi1 hi2] at hm
  have p1 := LongTails.Proofs.GatedEscapeAttemptProb.prob_A0 cfg d g f H.hb hN hM H.hT H.hτ0 hvar0 s hd hph hj
  have p2 := LongTails.Proofs.GatedEscapeAttemptProb.prob_Aq cfg d g f H.hb hN hM H.hT hr hτq hvarq hgf
    s hd hph hj
  have p3 := prob_traj cfg d g f H hdE hsm hN hσ hM s hd hph hj hsad
  linarith

end LongTails.Proofs.GatedEscapeSaddle
