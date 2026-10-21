import LongTails.Proofs.NormSubGaussian
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.LightTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma independent_norm_add_exp_control {S X : Ω → E} {σ v a : ℝ}
    (hσ : 0 < σ) (hv : 0 < v) (ha : 0 ≤ a) (has : 2*a*σ^2 ≤ 1)
    (hcoef : (a+16*a^2*σ^2)*v+a*σ^2 ≤ 1)
    (hS : Measurable S) (hX : Measurable X) (hind : IndepFun S X P)
    (hXi : Integrable X P) (hzero : (∫ ω, X ω ∂P) = 0)
    (hiX : Integrable (fun ω => Real.exp (‖X ω‖^2/σ^2)) P)
    (hbX : (∫ ω, Real.exp (‖X ω‖^2/σ^2) ∂P) ≤ Real.exp 1)
    (hiS : Integrable (fun ω => Real.exp (‖S ω‖^2/v)) P)
    (hbS : (∫ ω, Real.exp (‖S ω‖^2/v) ∂P) ≤ Real.exp 1) :
    Integrable (fun ω => Real.exp (a*‖S ω+X ω‖^2)) P ∧
      (∫ ω, Real.exp (a*‖S ω+X ω‖^2) ∂P) ≤ Real.exp 1 := by
  have hni : Measurable (fun x : E => Real.exp (‖x‖^2/σ^2)) := by fun_prop
  have hns : Measurable (fun x : E => Real.exp (‖x‖^2/v)) := by fun_prop
  have hXi' : Integrable (fun x : E => x) (P.map X) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hX.aemeasurable).mpr hXi
  have hz' : (∫ x : E, x ∂P.map X) = 0 := by
    rw [integral_map hX.aemeasurable (f := fun x : E => x) measurable_id.aestronglyMeasurable]
    exact hzero
  have hiX' := (integrable_map_measure hni.aestronglyMeasurable hX.aemeasurable).mpr hiX
  have hiS' := (integrable_map_measure hns.aestronglyMeasurable hS.aemeasurable).mpr hiS
  have hbX' : (∫ x : E, Real.exp (‖x‖^2/σ^2) ∂P.map X) ≤ Real.exp 1 := by
    rw [integral_map hX.aemeasurable hni.aestronglyMeasurable]
    exact hbX
  have hbS' : (∫ x : E, Real.exp (‖x‖^2/v) ∂P.map S) ≤ Real.exp 1 := by
    rw [integral_map hS.aemeasurable hns.aestronglyMeasurable]
    exact hbS
  have h := norm_add_exp_control hσ hv ha has hcoef measurable_id measurable_id
    hXi' hz' hiX' hbX' hiS' hbS'
  simp only [id_eq] at h
  have hpair := hS.prodMk hX
  have hfunc : Measurable (fun z : E × E => Real.exp (a*‖z.1+z.2‖^2)) := by fun_prop
  rw [← hind.map_prod_eq_prod_map_map hS.aemeasurable hX.aemeasurable] at h
  refine ⟨(integrable_map_measure hfunc.aestronglyMeasurable hpair.aemeasurable).mp h.1, ?_⟩
  rw [integral_map hpair.aemeasurable hfunc.aestronglyMeasurable] at h
  exact h.2

lemma batch_sum_coefficients {q n : ℝ} (hq : 0 < q) (hn : 0 ≤ n) :
    2*(1/(32*(n+1)*q))*q ≤ 1 ∧
      ((1/(32*(n+1)*q))+16*(1/(32*(n+1)*q))^2*q)*(32*n*q)+
        (1/(32*(n+1)*q))*q ≤ 1 := by
  have hn1 : 0 < n+1 := by linarith
  constructor
  · field_simp
    nlinarith
  · field_simp
    nlinarith [sq_nonneg n]

lemma sum_norm_exp_control (X : ℕ → Ω → E) {σ : ℝ} (hσ : 0 < σ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hXi : ∀ i, Integrable (X i) P) (hzero : ∀ i, (∫ ω, X i ω ∂P) = 0)
    (hiX : ∀ i, Integrable (fun ω => Real.exp (‖X i ω‖^2/σ^2)) P)
    (hbX : ∀ i, (∫ ω, Real.exp (‖X i ω‖^2/σ^2) ∂P) ≤ Real.exp 1) (n : ℕ) :
    Integrable (fun ω => Real.exp (‖∑ i ∈ Finset.range n, X i ω‖^2/(32*n*σ^2))) P ∧
      (∫ ω, Real.exp (‖∑ i ∈ Finset.range n, X i ω‖^2/(32*n*σ^2)) ∂P) ≤ Real.exp 1 := by
  induction n with
  | zero => simp [Real.one_le_exp_iff]
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      have hi : Integrable (fun ω => Real.exp ((1/32 : ℝ)*(‖X 0 ω‖^2/σ^2))) P :=
        integrable_exp_mul_of_nonneg_of_le (u := 1) (by simpa using hiX 0)
          (by norm_num) (by norm_num)
      have hb := integral_exp_scale_le (hiX 0) (hbX 0) (show 0 ≤ (1/32 : ℝ) by norm_num)
        (show (1/32 : ℝ) ≤ 1 by norm_num)
      have he : (fun ω => Real.exp (‖∑ i ∈ Finset.range 1, X i ω‖^2/(32*1*σ^2))) =
          fun ω => Real.exp ((1/32 : ℝ)*(‖X 0 ω‖^2/σ^2)) := by
        ext ω
        simp only [Finset.sum_range_one, mul_one]
        congr 1
        ring
      simp only [Nat.zero_add, Nat.cast_one]
      rw [he]
      exact ⟨hi, hb.trans (Real.exp_le_exp.mpr (by norm_num))⟩
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hcoeff := batch_sum_coefficients (sq_pos_of_pos hσ) (show 0 ≤ (n : ℝ) by positivity)
      have hS : Measurable (fun ω => ∑ i ∈ Finset.range n, X i ω) := by fun_prop
      have hind' : IndepFun (fun ω => ∑ i ∈ Finset.range n, X i ω) (X n) P := by
        have he : (∑ i ∈ Finset.range n, X i) = (fun ω => ∑ i ∈ Finset.range n, X i ω) := by
          ext ω
          simp
        rw [← he]
        exact hind.indepFun_finsetSum_of_notMem hX (by simp)
      have h := independent_norm_add_exp_control hσ
        (show 0 < 32*(n : ℝ)*σ^2 by positivity)
        (show 0 ≤ 1/(32*((n : ℝ)+1)*σ^2) by positivity)
        hcoeff.1 hcoeff.2 hS (hX n) hind' (hXi n) (hzero n) (hiX n) (hbX n) ih.1 ih.2
      have he : (fun ω => Real.exp ((1/(32*((n : ℝ)+1)*σ^2))*
          ‖(∑ i ∈ Finset.range n, X i ω)+X n ω‖^2)) =
          fun ω => Real.exp (‖∑ i ∈ Finset.range (n+1), X i ω‖^2/(32*(n+1)*σ^2)) := by
        ext ω
        rw [Finset.sum_range_succ]
        congr 1
        ring
      rw [he] at h
      simpa only [Nat.cast_add, Nat.cast_one] using h

lemma mean_norm_exp_control (X : ℕ → Ω → E) {σ : ℝ} (hσ : 0 < σ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hXi : ∀ i, Integrable (X i) P) (hzero : ∀ i, (∫ ω, X i ω ∂P) = 0)
    (hiX : ∀ i, Integrable (fun ω => Real.exp (‖X i ω‖^2/σ^2)) P)
    (hbX : ∀ i, (∫ ω, Real.exp (‖X i ω‖^2/σ^2) ∂P) ≤ Real.exp 1)
    (n : ℕ) (hn : 0 < n) :
    Integrable (fun ω => Real.exp (‖(1/(n : ℝ)) • (∑ i ∈ Finset.range n, X i ω)‖^2/
      (32*σ^2/n))) P ∧
      (∫ ω, Real.exp (‖(1/(n : ℝ)) • (∑ i ∈ Finset.range n, X i ω)‖^2/
        (32*σ^2/n)) ∂P) ≤ Real.exp 1 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have he : (fun ω => Real.exp (‖(1/(n : ℝ)) • (∑ i ∈ Finset.range n, X i ω)‖^2/
      (32*σ^2/n))) =
      fun ω => Real.exp (‖∑ i ∈ Finset.range n, X i ω‖^2/(32*n*σ^2)) := by
    ext ω
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    congr 1
    field_simp

  rw [he]
  exact sum_norm_exp_control X hσ hX hind hXi hzero hiX hbX n

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] in
omit [MeasurableSpace E] in
lemma finite_mean_integral {X : Ω → E} (hXi : Integrable X P) (n : ℕ) (hn : 0 < n) :
    Integrable (fun ξ : Fin n → Ω => (1/(n : ℝ)) • ∑ i, X (ξ i))
      (Measure.pi fun _ : Fin n => P) ∧
      (∫ ξ : Fin n → Ω, (1/(n : ℝ)) • ∑ i, X (ξ i)
        ∂Measure.pi (fun _ : Fin n => P)) = ∫ ω, X ω ∂P := by
  have hi (i : Fin n) : Integrable (fun ξ : Fin n → Ω => X (ξ i))
      (Measure.pi fun _ : Fin n => P) :=
    (measurePreserving_eval (fun _ : Fin n => P) i).integrable_comp_of_integrable hXi
  refine ⟨(integrable_finsetSum _ (fun i _ => hi i)).smul _, ?_⟩
  rw [integral_smul, integral_finsetSum _ (fun i _ => hi i)]
  have he (i : Fin n) : (∫ ξ : Fin n → Ω, X (ξ i) ∂Measure.pi (fun _ : Fin n => P)) =
      ∫ ω, X ω ∂P := by
    have hl : HasLaw (fun ξ : Fin n → Ω => ξ i) P (Measure.pi fun _ : Fin n => P) :=
      ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval (fun _ : Fin n => P) i).map_eq⟩
    exact hl.integral_comp hXi.aestronglyMeasurable
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  simp [hn']

lemma finite_mean_norm_exp_control {X : Ω → E} {σ : ℝ} (hσ : 0 < σ)
    (hX : Measurable X) (hXi : Integrable X P) (hzero : (∫ ω, X ω ∂P) = 0)
    (hiX : Integrable (fun ω => Real.exp (‖X ω‖^2/σ^2)) P)
    (hbX : (∫ ω, Real.exp (‖X ω‖^2/σ^2) ∂P) ≤ Real.exp 1) (n : ℕ) (hn : 0 < n) :
    Integrable (fun ξ : Fin n → Ω => Real.exp (‖(1/(n : ℝ)) • ∑ i, X (ξ i)‖^2/(32*σ^2/n)))
      (Measure.pi fun _ : Fin n => P) ∧
      (∫ ξ : Fin n → Ω, Real.exp (‖(1/(n : ℝ)) • ∑ i, X (ξ i)‖^2/(32*σ^2/n))
        ∂Measure.pi (fun _ : Fin n => P)) ≤ Real.exp 1 := by
  let Q := Measure.infinitePi fun _ : ℕ => P
  have heval (i : ℕ) : HasLaw (fun ξ : ℕ → Ω => ξ i) P Q :=
    ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ _⟩
  have hm : Measurable (fun ω => Real.exp (‖X ω‖^2/σ^2)) := by fun_prop
  have hseqi (i : ℕ) : Integrable (fun ξ : ℕ → Ω => X (ξ i)) Q :=
    (heval i).integrable_comp hXi
  have hseqzero (i : ℕ) : (∫ ξ : ℕ → Ω, X (ξ i) ∂Q) = 0 :=
    ((heval i).integral_comp hXi.aestronglyMeasurable).trans hzero
  have hseqexp (i : ℕ) : Integrable (fun ξ : ℕ → Ω => Real.exp (‖X (ξ i)‖^2/σ^2)) Q :=
    (heval i).integrable_comp hiX
  have hseqbound (i : ℕ) : (∫ ξ : ℕ → Ω, Real.exp (‖X (ξ i)‖^2/σ^2) ∂Q) ≤ Real.exp 1 := by
    rw [show (fun ξ : ℕ → Ω => Real.exp (‖X (ξ i)‖^2/σ^2)) =
      (fun ω => Real.exp (‖X ω‖^2/σ^2)) ∘ (fun ξ => ξ i) from rfl,
      (heval i).integral_comp hm.aestronglyMeasurable]
    exact hbX
  have h := mean_norm_exp_control (P := Q) (fun i ξ => X (ξ i)) hσ (fun _ => by fun_prop)
    (iIndepFun_infinitePi (X := fun _ => X) (fun _ => hX)) hseqi hseqzero hseqexp hseqbound n hn
  have hp : MeasurePreserving (fun ξ : ℕ → Ω => fun i : Fin n => ξ i)
      Q (Measure.pi fun _ : Fin n => P) := by
    refine ⟨by fun_prop, ?_⟩
    have hind := (iIndepFun_infinitePi (P := fun _ : ℕ => P)
      (X := fun _ (ω : Ω) => ω) (fun _ => measurable_id)).precomp
      (g := fun i : Fin n => i.val) Fin.val_injective
    have hh := hind.map_fun_eq_pi_map (fun i : Fin n => (measurable_pi_apply i.val).aemeasurable)
    simpa only [Measure.infinitePi_map_eval] using hh
  have hfunc : Measurable (fun ξ : Fin n → Ω =>
      Real.exp (‖(1/(n : ℝ)) • ∑ i, X (ξ i)‖^2/(32*σ^2/n))) := by fun_prop
  have he : (fun ξ : ℕ → Ω => Real.exp (‖(1/(n : ℝ)) •
      (∑ i ∈ Finset.range n, X (ξ i))‖^2/(32*σ^2/n))) =
      (fun ξ : Fin n → Ω => Real.exp (‖(1/(n : ℝ)) • ∑ i, X (ξ i)‖^2/(32*σ^2/n))) ∘
        (fun ξ : ℕ → Ω => fun i : Fin n => ξ i) := by
    ext ξ
    simp only [Function.comp_def]
    rw [Finset.sum_range (fun i => X (ξ i))]
  rw [he] at h
  refine ⟨(hp.integrable_comp hfunc.aestronglyMeasurable).mp h.1, ?_⟩
  have hl : HasLaw (fun ξ : ℕ → Ω => fun i : Fin n => ξ i) (Measure.pi fun _ : Fin n => P) Q :=
    ⟨hp.measurable.aemeasurable, hp.map_eq⟩
  have hb := h.2
  rwa [hl.integral_comp hfunc.aestronglyMeasurable] at hb

omit [IsProbabilityMeasure P] [InnerProductSpace ℝ E]
    [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] in
omit [MeasurableSpace E] in
lemma ae_zero_of_integral_sq_norm_nonpos {X : Ω → E}
    (hi : Integrable (fun ω => ‖X ω‖^2) P)
    (hbound : (∫ ω, ‖X ω‖^2 ∂P) ≤ 0) : X =ᵐ[P] 0 := by
  have he : (∫ ω, ‖X ω‖^2 ∂P) = 0 :=
    le_antisymm hbound (integral_nonneg (fun _ => sq_nonneg _))
  have hz := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hi).mp he
  filter_upwards [hz] with ω hω
  simpa only [Pi.zero_apply, sq_eq_zero_iff, norm_eq_zero] using hω

omit [IsProbabilityMeasure P] [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma norm_exp_enlarge {X : Ω → E} {r v : ℝ} (hr : 0 < r) (hrv : r ≤ v)
    (hX : Measurable X) (hi : Integrable (fun ω => Real.exp (‖X ω‖^2/r)) P)
    (hb : (∫ ω, Real.exp (‖X ω‖^2/r) ∂P) ≤ Real.exp 1) :
    Integrable (fun ω => Real.exp (‖X ω‖^2/v)) P ∧
      (∫ ω, Real.exp (‖X ω‖^2/v) ∂P) ≤ Real.exp 1 := by
  have hp (ω : Ω) : Real.exp (‖X ω‖^2/v) ≤ Real.exp (‖X ω‖^2/r) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_left (sq_nonneg _) hr hrv)
  have hi' : Integrable (fun ω => Real.exp (‖X ω‖^2/v)) P := by
    refine hi.mono' (by fun_prop) (ae_of_all _ (fun ω => ?_))
    simpa only [Real.norm_eq_abs, Real.abs_exp] using hp ω
  exact ⟨hi', (integral_mono hi' hi hp).trans hb⟩

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] in
omit [MeasurableSpace E] in
lemma finite_mean_exp_of_ae_zero {X : Ω → E} (hz : X =ᵐ[P] 0) (n : ℕ) (v : ℝ) :
    Integrable (fun ξ : Fin n → Ω => Real.exp (‖(1/(n : ℝ)) • ∑ i, X (ξ i)‖^2/v))
      (Measure.pi fun _ : Fin n => P) ∧
      (∫ ξ : Fin n → Ω, Real.exp (‖(1/(n : ℝ)) • ∑ i, X (ξ i)‖^2/v)
        ∂Measure.pi (fun _ : Fin n => P)) ≤ Real.exp 1 := by
  have hcoord (i : Fin n) : ∀ᵐ ξ : Fin n → Ω ∂Measure.pi (fun _ : Fin n => P), X (ξ i) = 0 :=
    (measurePreserving_eval (fun _ : Fin n => P) i).quasiMeasurePreserving.tendsto_ae.eventually hz
  have hall : ∀ᵐ ξ : Fin n → Ω ∂Measure.pi (fun _ : Fin n => P), ∀ i, X (ξ i) = 0 :=
    ae_all_iff.mpr hcoord
  have he : (fun ξ : Fin n → Ω => Real.exp (‖(1/(n : ℝ)) • ∑ i, X (ξ i)‖^2/v)) =ᵐ[
      Measure.pi (fun _ : Fin n => P)] (fun _ => (1 : ℝ)) := by
    filter_upwards [hall] with ξ hξ
    simp [hξ]
  refine ⟨(integrable_const (1 : ℝ)).congr he.symm, ?_⟩
  rw [integral_congr_ae he]
  simp [Real.one_le_exp_iff]

end OracleTemplate.LightTail
