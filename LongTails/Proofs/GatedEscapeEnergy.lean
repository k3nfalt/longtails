import LongTails.Proofs.GatedEscapeMoments
import LongTails.Proofs.GatedEscapeDirection
import LongTails.Proofs.StrongGrowthAgdDrift
import LongTails.Proofs.ComparisonTrustTaylor
import Mathlib.NumberTheory.Harmonic.Bounds

namespace LongTails.Proofs.GatedEscapeEnergy

open MeasureTheory ProbabilityTheory LongTails.Algorithms.GatedPerturbedEscape
  LongTails.Proofs.GatedEscapeProcess LongTails.Proofs.GatedEscapeMoments
  LongTails.Proofs.GatedEscapeDirection LongTails.Proofs.StrongGrowthAgdBlocks
  LongTails.Proofs.ComparisonTrustTaylor
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]
variable {σ : ℝ}
variable {ι : Type} [Fintype ι]

lemma xpow_le (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) : x * (1 - x) ^ k ≤ 1 / (k + 1) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h2 : (1 + x) ^ k * (1 - x) ^ k ≤ 1 := by
    rw [← mul_pow]; exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have h3 : 1 + k * x ≤ (1 + x) ^ k := one_add_mul_le_pow (by linarith) k
  have hp : 0 ≤ (1 - x) ^ k := pow_nonneg (by linarith) k
  have hp1 : (1 - x) ^ k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have key : (1 + k * x) * (1 - x) ^ k ≤ 1 := by nlinarith
  rw [le_div_iff₀ (by positivity)]
  nlinarith

lemma young_mode {a c x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    ((1 - x) * a - c) ^ 2 ≤ (1 - x) * a ^ 2 + (1 + 2 / x) * c ^ 2 := by
  have e : (1 + x / 2) * ((1 - x) * a) ^ 2 + (1 + 2 / x) * c ^ 2 - ((1 - x) * a - c) ^ 2 =
      (2 / x) * ((x / 2) * ((1 - x) * a) + c) ^ 2 := by field_simp; ring
  have h0 : 0 ≤ (2 / x) * ((x / 2) * ((1 - x) * a) + c) ^ 2 := by positivity
  have hc : (1 + x / 2) * (1 - x) ^ 2 ≤ 1 - x := by
    have h1 : (1 + x / 2) * (1 - x) ≤ 1 := by nlinarith
    have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ 1 - x)
    nlinarith
  have : (1 + x / 2) * ((1 - x) * a) ^ 2 ≤ (1 - x) * a ^ 2 := by
    rw [mul_pow, ← mul_assoc]; exact mul_le_mul_of_nonneg_right hc (sq_nonneg a)
  linarith

variable (cfg : Config) (g : E → Ω → E) (gf : E → E)

noncomputable def tstep (x g0 : E) (s : E × ℕ × ℝ) (ω : Fin cfg.b → Ω) : E × ℕ × ℝ :=
  (clip cfg.r (s.1 - cfg.η • (bmean cfg g (x + s.1) ω - g0)), s.2.1 + 1,
    s.2.2 + cfg.η * ‖bmean cfg g (x + s.1) ω - gf (x + s.1)‖)

lemma measurable_clip (r : ℝ) : Measurable (fun u : E => clip r u) := by
  unfold clip
  exact Measurable.ite (measurableSet_le measurable_norm measurable_const) measurable_id
    ((measurable_const.div measurable_norm).smul measurable_id)

lemma tstep_measurable (hg : Measurable (Function.uncurry g)) (hgf : Continuous gf) (x g0 : E) :
    Measurable (Function.uncurry (tstep cfg g gf x g0)) := by
  have hb : Measurable (fun z : (E × ℕ × ℝ) × (Fin cfg.b → Ω) => bmean cfg g (x + z.1.1) z.2) :=
    bmean_measurable_joint cfg hg (q := fun s : E × ℕ × ℝ => x + s.1)
      (measurable_const.add measurable_fst)
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · exact (measurable_clip cfg.r).comp
      ((measurable_fst.comp measurable_fst).sub ((hb.sub measurable_const).const_smul _))
  · exact (measurable_fst.comp (measurable_snd.comp measurable_fst)).add_const 1
  · exact (measurable_snd.comp (measurable_snd.comp measurable_fst)).add
      ((hb.sub (hgf.measurable.comp (measurable_const.add
        (measurable_fst.comp measurable_fst)))).norm.const_mul _)

variable {cfg g gf}

noncomputable def posSet (eig : ι → ℝ) : Finset ι := Finset.univ.filter (fun j => 0 < eig j)

noncomputable def Psi (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ) (η : ℝ) (T : ℕ) (s : E × ℕ × ℝ) : ℝ :=
  ∑ j ∈ posSet eig, eig j * (1 - η * eig j) ^ (T - s.2.1) * ⟪b j, s.1⟫ ^ 2

lemma Psi_measurable (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ) (η : ℝ) (T : ℕ) :
    Measurable (Psi b eig η T) := by
  unfold Psi
  refine Finset.measurable_sum _ (fun j _ => ?_)
  refine Measurable.mul ?_ ((Measurable.inner measurable_const measurable_fst).pow_const 2)
  refine measurable_const.mul ?_
  have : Measurable (fun s : E × ℕ × ℝ => T - s.2.1) :=
    measurable_from_top.comp (measurable_fst.comp measurable_snd)
  exact (measurable_from_top (f := fun k : ℕ => (1 - η * eig j) ^ k)).comp this

lemma inner_err_sq_integrable (hb : 0 < cfg.b) (h : Noise g gf p σ) (q v : E) :
    Integrable (fun ω => ⟪v, bmean cfg g q ω - gf q⟫ ^ 2) (Measure.pi fun _ : Fin cfg.b => p) := by
  have hi1 : Integrable (fun ω => ⟪v, bmean cfg g q ω - gf q⟫) (Measure.pi fun _ : Fin cfg.b => p) :=
    (err_integrable cfg hb h q).const_inner v
  refine ((err_sq_integrable cfg hb h q).const_mul (‖v‖ ^ 2)).mono' (hi1.aestronglyMeasurable.pow 2)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_pow, ← mul_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm v _) 2

lemma shift_sq_integrable (hb : 0 < cfg.b) (h : Noise g gf p σ) (q v A : E) (η : ℝ) :
    Integrable (fun ω => ⟪v, A - η • (bmean cfg g q ω - gf q)⟫ ^ 2)
      (Measure.pi fun _ : Fin cfg.b => p) := by
  have hi1 : Integrable (fun ω => ⟪v, bmean cfg g q ω - gf q⟫) (Measure.pi fun _ : Fin cfg.b => p) :=
    (err_integrable cfg hb h q).const_inner v
  have hi2 := inner_err_sq_integrable (cfg := cfg) (gf := gf) hb h q v
  have hexp : (fun ω => ⟪v, A - η • (bmean cfg g q ω - gf q)⟫ ^ 2) =
      fun ω => ⟪v, A⟫ ^ 2 - 2 * η * ⟪v, A⟫ * ⟪v, bmean cfg g q ω - gf q⟫ +
        η ^ 2 * ⟪v, bmean cfg g q ω - gf q⟫ ^ 2 := by
    funext ω; rw [inner_sub_right, inner_smul_right]; ring
  rw [hexp]
  exact ((integrable_const _).sub (hi1.const_mul _)).add (hi2.const_mul _)

section drift

variable (hb : 0 < cfg.b) (h : Noise g gf p σ)
variable (x g0 : E) (H : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
  (hc : ∀ i v, ⟪b i, H v⟫ = eig i * ⟪b i, v⟫)

set_option maxHeartbeats 800000 in
include hb h hc in
theorem psi_step (hgf : Continuous gf) (hη : 0 < cfg.η) (hr : 0 ≤ cfg.r) (heig : ∀ j, cfg.η * eig j ≤ 1) (T : ℕ) (U : ℝ)
    (s : E × ℕ × ℝ) (ht : s.2.1 < T)
    (hU : ‖gf (x + s.1) - H s.1 - g0‖ ≤ U) :
    ∫ ω, Psi b eig cfg.η T (tstep cfg g gf x g0 s ω) ∂(Measure.pi fun _ : Fin cfg.b => p) ≤
      Psi b eig cfg.η T s + 3 * cfg.η * U ^ 2 +
        cfg.η * (σ ^ 2 / cfg.b) / ((T - s.2.1 : ℕ) : ℝ) := by
  obtain ⟨η, hηd⟩ : ∃ η, η = cfg.η := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = s.1 := ⟨_, rfl⟩
  obtain ⟨t, htd⟩ : ∃ t, t = s.2.1 := ⟨_, rfl⟩
  obtain ⟨fo, hfo⟩ : ∃ fo, fo = gf (x + v) - H v - g0 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = v - η • H v - η • fo := ⟨_, rfl⟩
  rw [← hηd] at hη heig ⊢
  rw [← htd] at ht ⊢
  rw [← hv] at hU
  have hpre : ∀ ω, s.1 - η • (bmean cfg g (x + s.1) ω - g0) =
      A - η • (bmean cfg g (x + v) ω - gf (x + v)) := by
    intro ω; rw [hA, hfo, ← hv]; module
  have hk : T - (t + 1) + 1 = T - t := by omega
  have hTt : (0 : ℝ) < ((T - t : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < T - t)
  obtain ⟨w', hw'⟩ : ∃ w' : ι → ℝ, ∀ j, w' j = eig j * (1 - η * eig j) ^ (T - (t + 1)) :=
    ⟨_, fun _ => rfl⟩
  have hw0 : ∀ j ∈ posSet eig, 0 ≤ w' j := by
    intro j hj
    have hpos : 0 < eig j := (Finset.mem_filter.mp hj).2
    rw [hw']; exact mul_nonneg hpos.le (pow_nonneg (by linarith [heig j]) _)
  have hPsi_next : ∀ ω, Psi b eig η T (tstep cfg g gf x g0 s ω) ≤
      ∑ j ∈ posSet eig, w' j * ⟪b j, A - η • (bmean cfg g (x + v) ω - gf (x + v))⟫ ^ 2 := by
    intro ω
    unfold Psi tstep
    apply Finset.sum_le_sum
    intro j hj
    obtain ⟨c, hc0, hc1, hcl, _⟩ := clip_eq_smul cfg.r (s.1 - cfg.η • (bmean cfg g (x + s.1) ω - g0)) hr
    rw [hcl, ← hηd, hpre, inner_smul_right, mul_pow, ← htd]
    have hc2 : c ^ 2 ≤ 1 := by nlinarith
    have hwj := hw0 j hj
    rw [hw'] at hwj ⊢
    have hsq := sq_nonneg (⟪b j, A - η • (bmean cfg g (x + v) ω - gf (x + v))⟫)
    calc eig j * (1 - η * eig j) ^ (T - (t + 1)) * (c ^ 2 * ⟪b j, A - η • (bmean cfg g (x + v) ω - gf (x + v))⟫ ^ 2)
        ≤ eig j * (1 - η * eig j) ^ (T - (t + 1)) * (1 * ⟪b j, A - η • (bmean cfg g (x + v) ω - gf (x + v))⟫ ^ 2) := by
          gcongr
      _ = _ := by ring
  have hRint : Integrable (fun ω => ∑ j ∈ posSet eig, w' j *
      ⟪b j, A - η • (bmean cfg g (x + v) ω - gf (x + v))⟫ ^ 2) (Measure.pi fun _ : Fin cfg.b => p) :=
    integrable_finsetSum _ (fun j _ => (shift_sq_integrable hb h (x + v) (b j) A η).const_mul _)
  have hLmeas : AEStronglyMeasurable (fun ω => Psi b eig η T (tstep cfg g gf x g0 s ω))
      (Measure.pi fun _ : Fin cfg.b => p) := by
    refine ((Psi_measurable b eig η T).comp ?_).aestronglyMeasurable
    exact (tstep_measurable cfg g gf h.meas hgf x g0).comp (measurable_const.prodMk measurable_id)
  have hPnn : ∀ ω, 0 ≤ Psi b eig η T (tstep cfg g gf x g0 s ω) := by
    intro ω; unfold Psi
    refine Finset.sum_nonneg fun j hj => ?_
    have hpos : 0 < eig j := (Finset.mem_filter.mp hj).2
    exact mul_nonneg (mul_nonneg hpos.le (pow_nonneg (by linarith [heig j]) _)) (sq_nonneg _)
  have hmono := integral_mono_of_nonneg (Filter.Eventually.of_forall hPnn) hRint
    (Filter.Eventually.of_forall hPsi_next)
  refine hmono.trans ?_
  rw [integral_finsetSum _ (fun j _ => (shift_sq_integrable hb h (x + v) (b j) A η).const_mul _)]
  simp_rw [integral_const_mul, integral_sq_shift cfg hb h (x + v) A (b _) η]
  set e2 : ι → ℝ := fun j => ∫ ω, ⟪b j, bmean cfg g (x + v) ω - gf (x + v)⟫ ^ 2
    ∂(Measure.pi fun _ : Fin cfg.b => p) with he2
  have he2nn : ∀ j, 0 ≤ e2 j := fun j => integral_nonneg fun _ => sq_nonneg _
  have hesum : ∑ j, e2 j ≤ σ ^ 2 / cfg.b := by
    rw [he2, ← integral_finsetSum _ (fun j _ => inner_err_sq_integrable hb h (x + v) (b j))]
    simp_rw [b.sum_sq_inner_right]
    exact integral_err_sq cfg hb h (x + v)
  have hterm : ∀ j ∈ posSet eig, w' j * (⟪b j, A⟫ ^ 2 + η ^ 2 * e2 j) ≤
      eig j * (1 - η * eig j) ^ (T - t) * ⟪b j, v⟫ ^ 2 + 3 * η * ⟪b j, fo⟫ ^ 2 +
        η / ((T - t : ℕ) : ℝ) * e2 j := by
    intro j hj
    have hpos : 0 < eig j := (Finset.mem_filter.mp hj).2
    have hx0 : 0 < η * eig j := mul_pos hη hpos
    have hx1 : η * eig j ≤ 1 := heig j
    have hAj : ⟪b j, A⟫ = (1 - η * eig j) * ⟪b j, v⟫ - η * ⟪b j, fo⟫ := by
      rw [hA, inner_sub_right, inner_sub_right, inner_smul_right, inner_smul_right, hc]; ring
    have hy := young_mode (a := ⟪b j, v⟫) (c := η * ⟪b j, fo⟫) hx0 hx1
    rw [← hAj] at hy
    have hpk : 0 ≤ (1 - η * eig j) ^ (T - (t + 1)) := pow_nonneg (by linarith) _
    have hpk1 : (1 - η * eig j) ^ (T - (t + 1)) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hw'j : w' j = eig j * (1 - η * eig j) ^ (T - (t + 1)) := hw' j
    have hwnn : 0 ≤ w' j := hw0 j hj
    have h1 : w' j * ⟪b j, A⟫ ^ 2 ≤ eig j * (1 - η * eig j) ^ (T - t) * ⟪b j, v⟫ ^ 2 +
        3 * η * ⟪b j, fo⟫ ^ 2 := by
      have hm := mul_le_mul_of_nonneg_left hy hwnn
      have e3 : w' j * ((1 - η * eig j) * ⟪b j, v⟫ ^ 2) =
          eig j * (1 - η * eig j) ^ (T - t) * ⟪b j, v⟫ ^ 2 := by
        rw [hw'j, ← hk, pow_succ]; ring
      have e4 : w' j * ((1 + 2 / (η * eig j)) * (η * ⟪b j, fo⟫) ^ 2) =
          (1 - η * eig j) ^ (T - (t + 1)) * (η * (η * eig j) + 2 * η) * ⟪b j, fo⟫ ^ 2 := by
        rw [hw'j]; field_simp
      have e5 : (1 - η * eig j) ^ (T - (t + 1)) * (η * (η * eig j) + 2 * η) * ⟪b j, fo⟫ ^ 2 ≤
          3 * η * ⟪b j, fo⟫ ^ 2 := by
        have : (1 - η * eig j) ^ (T - (t + 1)) * (η * (η * eig j) + 2 * η) ≤ 3 * η := by
          have h6 : η * (η * eig j) ≤ η := by nlinarith
          nlinarith
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
      rw [mul_add] at hm
      linarith
    have h2 : w' j * (η ^ 2 * e2 j) ≤ η / ((T - t : ℕ) : ℝ) * e2 j := by
      have hb2 := xpow_le (η * eig j) hx0.le hx1 (T - (t + 1))
      have hcast : ((T - (t + 1) : ℕ) : ℝ) + 1 = ((T - t : ℕ) : ℝ) := by
        rw [← hk]; push_cast; ring
      rw [hcast] at hb2
      have hwle : η * w' j ≤ 1 / ((T - t : ℕ) : ℝ) := by rw [hw'j]; linarith
      have hw2 : w' j * η ^ 2 ≤ η / ((T - t : ℕ) : ℝ) := by
        calc w' j * η ^ 2 = η * (η * w' j) := by ring
          _ ≤ η * (1 / ((T - t : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hwle hη.le
          _ = η / ((T - t : ℕ) : ℝ) := by ring
      calc w' j * (η ^ 2 * e2 j) = (w' j * η ^ 2) * e2 j := by ring
        _ ≤ η / ((T - t : ℕ) : ℝ) * e2 j := mul_le_mul_of_nonneg_right hw2 (he2nn j)
    rw [mul_add]
    linarith
  have hsum1 := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum1
  have hPs : ∑ j ∈ posSet eig, eig j * (1 - η * eig j) ^ (T - t) * ⟪b j, v⟫ ^ 2 =
      Psi b eig η T s := by unfold Psi; rw [← htd, ← hv]
  have hfo3 : ∑ j ∈ posSet eig, 3 * η * ⟪b j, fo⟫ ^ 2 ≤ 3 * η * U ^ 2 := by
    rw [← Finset.mul_sum]
    have h7 : ∑ j ∈ posSet eig, ⟪b j, fo⟫ ^ 2 ≤ ‖fo‖ ^ 2 := by
      rw [← b.sum_sq_inner_right fo]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    have h8 : ‖fo‖ ^ 2 ≤ U ^ 2 := by
      rw [hfo]; exact pow_le_pow_left₀ (norm_nonneg _) hU 2
    have : 0 ≤ 3 * η := by linarith
    nlinarith
  have hnoise : ∑ j ∈ posSet eig, η / ((T - t : ℕ) : ℝ) * e2 j ≤ η * (σ ^ 2 / cfg.b) / ((T - t : ℕ) : ℝ) := by
    rw [← Finset.mul_sum]
    have h9 : ∑ j ∈ posSet eig, e2 j ≤ σ ^ 2 / cfg.b :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => he2nn j)).trans hesum
    have : 0 ≤ η / ((T - t : ℕ) : ℝ) := div_nonneg hη.le hTt.le
    calc η / ((T - t : ℕ) : ℝ) * ∑ j ∈ posSet eig, e2 j ≤ η / ((T - t : ℕ) : ℝ) * (σ ^ 2 / cfg.b) :=
          mul_le_mul_of_nonneg_left h9 this
      _ = η * (σ ^ 2 / cfg.b) / ((T - t : ℕ) : ℝ) := by ring
  rw [hPs] at hsum1
  linarith

end drift

section totals

variable (hb : 0 < cfg.b) (h : Noise g gf p σ) (hgf : Continuous gf)
variable (x g0 : E) (H : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
  (hc : ∀ i v, ⟪b i, H v⟫ = eig i * ⟪b i, v⟫)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma Psi_nonneg (heig : ∀ j, cfg.η * eig j ≤ 1) (T : ℕ) (s : E × ℕ × ℝ) :
    0 ≤ Psi b eig cfg.η T s := by
  unfold Psi
  refine Finset.sum_nonneg fun j hj => ?_
  have hpos : 0 < eig j := (Finset.mem_filter.mp hj).2
  exact mul_nonneg (mul_nonneg hpos.le (pow_nonneg (by linarith [heig j]) _)) (sq_nonneg _)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma Psi_le (hη : 0 ≤ cfg.η) (heig : ∀ j, cfg.η * eig j ≤ 1) (T : ℕ) (s : E × ℕ × ℝ) :
    Psi b eig cfg.η T s ≤ (∑ j ∈ posSet eig, eig j) * ‖s.1‖ ^ 2 := by
  unfold Psi
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  have hpos : 0 < eig j := (Finset.mem_filter.mp hj).2
  have hp1 : (1 - cfg.η * eig j) ^ (T - s.2.1) ≤ 1 :=
    pow_le_one₀ (by linarith [heig j]) (by nlinarith [mul_nonneg hη hpos.le])
  have hp0 : 0 ≤ (1 - cfg.η * eig j) ^ (T - s.2.1) := pow_nonneg (by linarith [heig j]) _
  have hin : ⟪b j, s.1⟫ ^ 2 ≤ ‖s.1‖ ^ 2 := by
    have := abs_real_inner_le_norm (b j) s.1
    rw [b.orthonormal.1 j, one_mul] at this
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have : eig j * (1 - cfg.η * eig j) ^ (T - s.2.1) ≤ eig j := by nlinarith
  nlinarith [sq_nonneg ⟪b j, s.1⟫]

include hb h hgf hc in
theorem energy_total (hη : 0 < cfg.η) (hr : 0 ≤ cfg.r) (heig : ∀ j, cfg.η * eig j ≤ 1)
    (T : ℕ) (U : ℝ) (hU : ∀ v : E, ‖v‖ ≤ cfg.r → ‖gf (x + v) - H v - g0‖ ≤ U)
    (v0 : E) (hv0 : ‖v0‖ ≤ cfg.r) :
    ∫ β, Psi b eig cfg.η T (run (tstep cfg g gf x g0) (v0, 0, 0) β T)
        ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) ≤
      Psi b eig cfg.η T (v0, 0, 0) + T * (3 * cfg.η * U ^ 2) +
        cfg.η * (σ ^ 2 / cfg.b) * (1 + Real.log T) := by
  set ν := Measure.pi fun _ : Fin cfg.b => p
  set step := tstep cfg g gf x g0
  have hstep : Measurable (Function.uncurry step) := tstep_measurable cfg g gf h.meas hgf x g0
  set Inv : ℕ → Set (E × ℕ × ℝ) := fun t => {s | s.2.1 = t ∧ ‖s.1‖ ≤ cfg.r} with hInv
  have hInvStep : ∀ t, ∀ s ∈ Inv t, ∀ y, step s y ∈ Inv (t + 1) := by
    intro t s hs y
    refine ⟨by simp only [step, tstep]; rw [hs.1], clip_norm_le _ _ hr⟩
  have hs0 : ((v0, 0, 0) : E × ℕ × ℝ) ∈ Inv 0 := ⟨rfl, hv0⟩
  set cfun : E × ℕ × ℝ → ℝ := fun s => 3 * cfg.η * U ^ 2 +
    cfg.η * (σ ^ 2 / cfg.b) / ((T - s.2.1 : ℕ) : ℝ) with hcfun
  have hcm : Measurable cfun := by
    refine measurable_const.add ?_
    exact measurable_const.div ((measurable_from_top (f := fun k : ℕ => ((T - k : ℕ) : ℝ))).comp
      (measurable_fst.comp measurable_snd))
  have hrun_inv : ∀ β t, run step (v0, 0, 0) β t ∈ Inv t :=
    fun β t => run_mem_inv step (v0, 0, 0) Inv hInvStep hs0 β t
  have hYint : ∀ t, Integrable (fun β => Psi b eig cfg.η T (run step (v0, 0, 0) β t))
      (Measure.infinitePi fun _ : ℕ => ν) := by
    intro t
    refine Integrable.of_bound (C := (∑ j ∈ posSet eig, eig j) * cfg.r ^ 2)
      ((Psi_measurable b eig cfg.η T).comp (run_measurable step _ hstep t)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun β => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Psi_nonneg b eig heig T _)]
    refine (Psi_le b eig hη.le heig T _).trans ?_
    have hsum : 0 ≤ ∑ j ∈ posSet eig, eig j :=
      Finset.sum_nonneg fun j hj => (Finset.mem_filter.mp hj).2.le
    have h1 := (hrun_inv β t).2
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h1 2) hsum
  have hcint : ∀ t, Integrable (fun β => cfun (run step (v0, 0, 0) β t))
      (Measure.infinitePi fun _ : ℕ => ν) := by
    intro t
    have : (fun β => cfun (run step (v0, 0, 0) β t)) = fun _ => cfun ((0 : E), t, (0 : ℝ)) := by
      funext β; simp only [hcfun]; rw [(hrun_inv β t).1]
    rw [this]; exact integrable_const _
  have hdr := drift step (v0, 0, 0) ν hstep 1 Inv hInvStep hs0
    (Psi b eig cfg.η T) cfun (fun _ _ => 0) (Psi_measurable b eig cfg.η T) hcm measurable_const
    hYint hcint (fun _ => integrable_const _) T (by
      intro e he s hs
      simp only [add_zero]
      have hrun1 : ∀ tail, run step s tail 1 = step s (tail 0) := fun _ => rfl
      simp_rw [hrun1]
      rw [integral_eval ν (fun y => Psi b eig cfg.η T (step s y))
        ((Psi_measurable b eig cfg.η T).comp (hstep.comp (measurable_const.prodMk measurable_id)))]
      have hst := psi_step hb h x g0 H b eig hc hgf hη hr heig T U s (by rw [hs.1, mul_one]; exact he)
        (hU s.1 hs.2)
      simp only [hcfun]
      linarith)
  simp only [mul_one, integral_zero, Finset.sum_const_zero, add_zero] at hdr
  refine hdr.trans ?_
  have hsumc : ∑ e ∈ Finset.range T, ∫ β, cfun (run step (v0, 0, 0) β e)
      ∂(Measure.infinitePi fun _ : ℕ => ν) =
      ∑ e ∈ Finset.range T, (3 * cfg.η * U ^ 2 + cfg.η * (σ ^ 2 / cfg.b) / ((T - e : ℕ) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro e _
    have : (fun β => cfun (run step (v0, 0, 0) β e)) = fun _ =>
        3 * cfg.η * U ^ 2 + cfg.η * (σ ^ 2 / cfg.b) / ((T - e : ℕ) : ℝ) := by
      funext β; simp only [hcfun]; rw [(hrun_inv β e).1]
    rw [this, integral_const]; simp
  rw [hsumc, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hharm : ∑ e ∈ Finset.range T, (1 : ℝ) / ((T - e : ℕ) : ℝ) ≤ 1 + Real.log T := by
    have h1 : ∑ e ∈ Finset.range T, (1 : ℝ) / ((T - e : ℕ) : ℝ) = (harmonic T : ℝ) := by
      rw [harmonic]
      push_cast
      rw [← Finset.sum_range_reflect (fun j => ((j : ℝ) + 1)⁻¹) T]
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mem_range] at he
      rw [one_div]
      congr 1
      have : T - 1 - e + 1 = T - e := by omega
      rw [← this]; push_cast; ring
    rw [h1]; exact harmonic_le_one_add_log T
  have hk : ∑ e ∈ Finset.range T, cfg.η * (σ ^ 2 / cfg.b) / ((T - e : ℕ) : ℝ) =
      cfg.η * (σ ^ 2 / cfg.b) * ∑ e ∈ Finset.range T, (1 : ℝ) / ((T - e : ℕ) : ℝ) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro e _; ring
  rw [hk]
  have hnn : 0 ≤ cfg.η * (σ ^ 2 / cfg.b) := by positivity
  nlinarith

end totals

section accum

variable (hb : 0 < cfg.b) (h : Noise g gf p σ) (hgf : Continuous gf) (x g0 : E)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma acc_measurable (A : ℝ) : Measurable (fun s : E × ℕ × ℝ => min s.2.2 A) :=
  (measurable_snd.comp measurable_snd).min measurable_const

include hb h hgf in
theorem acc_total (hσ : 0 ≤ σ) (hη : 0 ≤ cfg.η) (A : ℝ) (hA : 0 ≤ A) (v0 : E) (n : ℕ) :
    ∫ β, min (run (tstep cfg g gf x g0) (v0, 0, 0) β n).2.2 A
        ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) ≤
      n * (cfg.η * (σ / Real.sqrt cfg.b)) := by
  set ν := Measure.pi fun _ : Fin cfg.b => p
  set step := tstep cfg g gf x g0
  have hstep : Measurable (Function.uncurry step) := tstep_measurable cfg g gf h.meas hgf x g0
  set Inv : ℕ → Set (E × ℕ × ℝ) := fun _ => {s | 0 ≤ s.2.2} with hInv
  have hInvStep : ∀ t, ∀ s ∈ Inv t, ∀ y, step s y ∈ Inv (t + 1) := by
    intro t s hs y
    show 0 ≤ s.2.2 + cfg.η * ‖bmean cfg g (x + s.1) y - gf (x + s.1)‖
    exact add_nonneg hs (mul_nonneg hη (norm_nonneg _))
  have hs0 : ((v0, 0, 0) : E × ℕ × ℝ) ∈ Inv 0 := le_refl (0 : ℝ)
  have hmem : ∀ β t, run step (v0, 0, 0) β t ∈ Inv t := fun β t => run_mem_inv step _ Inv hInvStep hs0 β t
  have hYint : ∀ t, Integrable (fun β => min (run step (v0, 0, 0) β t).2.2 A) (Measure.infinitePi fun _ : ℕ => ν) := by
    intro t
    refine Integrable.of_bound (C := A) ((acc_measurable A).comp (run_measurable step _ hstep t)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun β => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hmem β t) hA)]
    exact min_le_right _ _
  have hdr := drift step (v0, 0, 0) ν hstep 1 Inv hInvStep hs0 (fun s => min s.2.2 A)
    (fun _ => cfg.η * (σ / Real.sqrt cfg.b)) (fun _ _ => 0) (acc_measurable A) measurable_const measurable_const
    hYint (fun _ => integrable_const _) (fun _ => integrable_const _) n (by
      intro e _ s hs
      simp only [add_zero]
      have hrun1 : ∀ tail, run step s tail 1 = step s (tail 0) := fun _ => rfl
      simp_rw [hrun1]
      have hm : Measurable (fun y => min (step s y).2.2 A) :=
        (acc_measurable A).comp (hstep.comp (measurable_const.prodMk measurable_id))
      rw [integral_eval ν (fun y => min (step s y).2.2 A) hm]
      have hpt : ∀ y, min (step s y).2.2 A ≤ min s.2.2 A + cfg.η * ‖bmean cfg g (x + s.1) y - gf (x + s.1)‖ := by
        intro y
        show min (s.2.2 + cfg.η * ‖bmean cfg g (x + s.1) y - gf (x + s.1)‖) A ≤ _
        have hnn : 0 ≤ cfg.η * ‖bmean cfg g (x + s.1) y - gf (x + s.1)‖ := mul_nonneg hη (norm_nonneg _)
        rcases le_total s.2.2 A with h1 | h1
        · rw [min_eq_left h1]; exact min_le_left _ _
        · rw [min_eq_right h1]; exact (min_le_right _ _).trans (by linarith)
      have hi1 : Integrable (fun y => cfg.η * ‖bmean cfg g (x + s.1) y - gf (x + s.1)‖) ν :=
        ((err_integrable cfg hb h (x + s.1)).norm).const_mul _
      have hmi : Integrable (fun y => min (step s y).2.2 A) ν := by
        refine Integrable.of_bound (C := A) hm.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hInvStep 0 s hs y) hA)]
        exact min_le_right _ _
      calc ∫ y, min (step s y).2.2 A ∂ν ≤ ∫ y, (min s.2.2 A + cfg.η * ‖bmean cfg g (x + s.1) y - gf (x + s.1)‖) ∂ν :=
            integral_mono hmi ((integrable_const _).add hi1) hpt
        _ = min s.2.2 A + cfg.η * ∫ y, ‖bmean cfg g (x + s.1) y - gf (x + s.1)‖ ∂ν := by
            rw [integral_add (integrable_const _) hi1, integral_const, integral_const_mul]
            simp
        _ ≤ min s.2.2 A + cfg.η * (σ / Real.sqrt cfg.b) := by
            have := integral_norm_err cfg hb h hσ (x + s.1)
            nlinarith)
  simp only [mul_one, integral_zero, Finset.sum_const_zero, add_zero, integral_const, probReal_univ,
    one_smul, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hdr
  have h0 : min (((v0, 0, 0) : E × ℕ × ℝ)).2.2 A = 0 := min_eq_left hA
  rw [h0, zero_add] at hdr
  exact hdr

end accum

end LongTails.Proofs.GatedEscapeEnergy
