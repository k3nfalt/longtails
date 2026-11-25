import LongTails.Algorithms.TwoTapLogisticGd
import LongTails.Proofs.Execution
import LongTails.Proofs.LogisticRiskBudget
import LongTails.Proofs.LogisticSpatialResponse

open OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Proofs.TwoTapLogisticDescent

open LongTails.Setups.TwoTapLogisticSeparation
open LongTails.Setups.TwoSampleQuadraticPerceptron (Space Features margin direction shift)
open LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding
open LongTails.Proofs.LogisticSpatialResponse
open LongTails.Proofs.LogisticRiskBudget
open LongTails.Algorithms.TwoTapLogisticGd

variable (p : Params) (X : Data p)

noncomputable def weight (θ : Space .conv p.d) (i : Fin p.n) : ℝ :=
  (p.n : ℝ)⁻¹ * Real.sigmoid (-margin .conv p.d (X i) θ)

noncomputable def signedMean (θ : Space .conv p.d) : Features p.d :=
  ∑ i, weight p X θ i • X i

noncomputable def tapEnergy (θ : Space .conv p.d) : ℝ := θ.1.1^2+θ.1.2^2

noncomputable def energy (θ : Space .conv p.d) : ℝ := tapEnergy p θ+‖θ.2‖^2

noncomputable def intensity (θ : Space .conv p.d) : ℝ := ∑ i, weight p X θ i

noncomputable def advance (η : ℝ) (θ : Space .conv p.d) : Space .conv p.d :=
  θ+η • descent p X θ

lemma weights_nonneg (θ : Space .conv p.d) (i : Fin p.n) : 0 ≤ weight p X θ i := by
  exact mul_nonneg (by positivity) (Real.sigmoid_nonneg _)

lemma sum_mass : (∑ _ : Fin p.n, (p.n : ℝ)⁻¹) = 1 := by
  simp [nsmul_eq_mul, p.n.ne_zero]

lemma risk_pos (θ : Space .conv p.d) : 0 < risk p X θ := by
  apply Finset.sum_pos (fun i _ => mul_pos (by positivity) (loss_pos _)) Finset.univ_nonempty

lemma intensity_le_risk (θ : Space .conv p.d) : intensity p X θ ≤ risk p X θ :=
  Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (posterior_le_loss _) (by positivity)

lemma signed_norm (θ : Space .conv p.d) (hR : ∀ i, ‖X i‖ ≤ p.R) :
    ‖signedMean p X θ‖ ≤ p.R * intensity p X θ := by
  rw [intensity, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (weights_nonneg p X θ i), mul_comm p.R]
  exact mul_le_mul_of_nonneg_left (hR i) (weights_nonneg p X θ i)

lemma descent_eq (θ : Space .conv p.d) :
    let g := signedMean p X θ
    descent p X θ = ((⟪g,θ.2⟫,⟪shift g,θ.2⟫), θ.1.1 • g+θ.1.2 • shift g) := by
  dsimp only
  simp only [descent, signedMean, weight, direction, shift_sum, shift_smul, sum_inner,
    real_inner_smul_left, Finset.smul_sum]
  ext <;> simp [Finset.sum_apply, smul_add, smul_smul, mul_comm, Finset.sum_add_distrib,
    Prod.fst_sum, Prod.snd_sum]

lemma channel_dynamics (θ : Space .conv p.d) (η σ : ℝ) (hσ : σ^2=1) :
    let θ₁ := advance p X η θ
    let θ₂ := advance p X η θ₁
    let g := signedMean p X θ
    let k := signedMean p X θ₁
    θ₂.1.1+σ*θ₂.1.2 = (1-η^2*‖g+σ • shift g‖^2/2)*(θ.1.1+σ*θ.1.2) +
      η*⟪g+k+σ • shift (g+k),θ₁.2⟫ := by
  have hr (w : Space .conv p.d) : advance p X η w =
      ((w.1.1+η*⟪signedMean p X w,w.2⟫,w.1.2+η*⟪shift (signedMean p X w),w.2⟫),
        w.2+η • (w.1.1 • signedMean p X w+w.1.2 • shift (signedMean p X w))) := by
    rw [advance,descent_eq]; rfl
  simpa only [hr] using channel_pair θ.1.1 θ.1.2 σ η (signedMean p X θ)
    (signedMean p X (advance p X η θ)) θ.2 hσ

lemma valid_execution (η : ℝ) (O : Oracle (Space .conv p.d) (Space .conv p.d))
    (ho : ∀ k q ω, O.answer k q ω = descent p X q.2) (t : ℕ)
    (ω : (algorithm p η).Seed) (ξ : (k : ℕ) → O.Seed k) :
    execute O (algorithm p η) (fun _ => t) ω ξ = (advance p X η)^[t] p.start := by
  rw [execute_eq_of_answer_eq O (descent p X) (fun h q s => ho h (0,q) s), execute_iterate]
  rfl

lemma family_compliance (η : ℝ) (h : 0 < η) : family p (algorithm p η) :=
  ⟨η,id,h,fun _ => rfl,fun _ => rfl,fun _ _ => rfl,fun _ => rfl⟩

lemma descent_energy_upper (θ : Space .conv p.d)
    (hX : ∀ i, ‖X i‖ ≤ p.R) :
    energy p (descent p X θ) ≤ 4*p.R^2*energy p θ*(intensity p X θ)^2 := by
  have hQ : 0 ≤ intensity p X θ := Finset.sum_nonneg fun i _ => weights_nonneg _ _ _ _
  have hn := pow_le_pow_left₀ (norm_nonneg _) (signed_norm p X θ hX) 2
  rw [descent_eq]
  unfold energy tapEnergy
  dsimp only
  apply (gradient_size_sq _ _ _ _).trans
  have hz : 0 ≤ θ.1.1^2+θ.1.2^2+‖θ.2‖^2 := by positivity
  have hh := mul_le_mul_of_nonneg_left hn (show 0 ≤ 2*(θ.1.1^2+θ.1.2^2+‖θ.2‖^2) by positivity)
  nlinarith only [hh, mul_nonneg (sq_nonneg p.R)
    (mul_nonneg hz (sq_nonneg (intensity p X θ)))]

lemma descent_energy_lower (θ : Space .conv p.d) (hγ : 0 ≤ p.γ)
    (S : ∃ u v : Features p.d, ‖u‖ ≤ 1 ∧ ‖v‖ ≤ 1 ∧
      (∀ i, p.γ ≤ ⟪X i+shift (X i),u⟫) ∧ (∀ i, p.γ ≤ ⟪X i-shift (X i),v⟫)) :
    (p.γ/2)^2*tapEnergy p θ*(intensity p X θ)^2 ≤ energy p (descent p X θ) := by
  obtain ⟨u,v,hu,hv,hp,hm⟩ := S
  have H := uniform_filter_gradient X (weight p X θ) u v θ.1.1 θ.1.2 p.γ hγ
    (weights_nonneg p X θ) hu hv hp hm
  change p.γ^2*tapEnergy p θ*(intensity p X θ)^2 ≤
    2*‖θ.1.1 • signedMean p X θ+θ.1.2 • shift (signedMean p X θ)‖^2 at H
  rw [descent_eq]
  simp only [energy, tapEnergy] at H ⊢
  nlinarith only [H, sq_nonneg ⟪signedMean p X θ,θ.2⟫, sq_nonneg ⟪shift (signedMean p X θ),θ.2⟫,
    sq_nonneg ‖θ.1.1 • signedMean p X θ+θ.1.2 • shift (signedMean p X θ)‖]

lemma advance_risk (θ : Space .conv p.d) (η : ℝ) (hη : 0 ≤ η)
    (hR : 0 ≤ p.R) (hX : ∀ i, ‖X i‖ ≤ p.R) (hF : risk p X θ ≤ 1)
    (hstep : η*p.R ≤ 1/8) (hcurv : η*p.R^2*energy p θ*risk p X θ ≤ 1/32) :
    risk p X (advance p X η θ) ≤ risk p X θ - η*energy p (descent p X θ)/2 := by
  let g := signedMean p X θ
  let e := ⟪g,θ.2⟫
  let f := ⟪shift g,θ.2⟫
  let h := θ.1.1 • g+θ.1.2 • shift g
  let G := energy p (descent p X θ)
  let Q := intensity p X θ
  let z := energy p θ
  let m := fun i => margin .conv p.d (X i) θ
  let s := fun i => margin .conv p.d (X i) (advance p X η θ) - m i
  have hg : G=e^2+f^2+‖h‖^2 := by simp [G,energy,tapEnergy,descent_eq,g,e,f,h]
  have hgn : 0 ≤ G := by rw [hg]; positivity
  have hz : 0 ≤ z := by dsimp [z,energy,tapEnergy]; positivity
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun i _ => weights_nonneg _ _ _ _
  have hq := intensity_le_risk p X θ
  have hQ1 : Q ≤ 1 := hq.trans hF
  have hQcur : η*p.R^2*z*Q ≤ 1/32 :=
    (mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ η*p.R^2*z)).trans hcurv
  have hgupper := descent_energy_upper p X θ hX
  have hpoint : ∀ i, |s i| ≤ 1 ∧ (s i)^2 ≤ 9*η^2*p.R^2*z*G := by
    intro i
    have hs : s i = η*(e*⟪X i,θ.2⟫+f*⟪shift (X i),θ.2⟫+
        ⟪θ.1.1 • X i+θ.1.2 • shift (X i),h⟫)+η^2*⟪e • X i+f • shift (X i),h⟫ := by
      rcases θ with ⟨⟨a,b⟩,v⟩
      simp only [s, m, advance, descent_eq]
      exact margin_increment a b e f η _ _ _
    rw [hs]
    apply logit_step_bounds hη hR hz hQ hgn hQ1 hstep hQcur hgupper
    · apply (first_variation_sq _ _ _ _ _ _ _).trans
      rw [hg]
      have hn := pow_le_pow_left₀ (norm_nonneg _) (hX i) 2
      change _ ≤ 4*p.R^2*(θ.1.1^2+θ.1.2^2+‖θ.2‖^2)*(e^2+f^2+‖h‖^2)
      gcongr
    · exact (second_variation_bound _ _ _ _).trans
        (by rw [hg]; exact mul_le_mul_of_nonneg_right (hX i) (by positivity))
  have hmean : ∑ i, weight p X θ i*s i =
      η*G+η^2*⟪e • g+f • shift g,h⟫ := by
    rcases θ with ⟨⟨a,b⟩,v⟩
    simp only [s,m,advance,descent_eq]
    rw [hg]
    exact mean_margin_increment _ _ _ _ _ _
  have hlin : η*G*(1-1/8) ≤ ∑ i, weight p X θ i*s i := by
    rw [hmean]
    have hn : ‖g‖ ≤ p.R*Q := signed_norm p X θ hX
    have ha := (abs_le.mp (second_variation_bound e f g h)).1
    rw [← hg] at ha
    have hG := mul_le_mul_of_nonneg_right hn hgn
    have hq0 : η*p.R*Q ≤ 1/8 :=
      (by simpa using mul_le_mul_of_nonneg_left hQ1 (mul_nonneg hη hR) : η*p.R*Q ≤ η*p.R).trans hstep
    have hb := mul_le_mul_of_nonneg_right hq0 (mul_nonneg hη hgn)
    have hc := mul_le_mul_of_nonneg_left (show -(p.R*Q*G) ≤ ⟪e • g+f • shift g,h⟫ by linarith) (sq_nonneg η)
    nlinarith only [hb,hc]
  have hvar : ∑ i, weight p X θ i*(s i)^2 ≤ η*G*(1/2-1/8) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      mul_le_mul_of_nonneg_left (hpoint i).2 (weights_nonneg p X θ i)
    rw [← Finset.sum_mul] at hh
    change _ ≤ Q*(9*η^2*p.R^2*z*G) at hh
    have hb := mul_le_mul_of_nonneg_right hQcur (mul_nonneg hη hgn)
    nlinarith only [hh,hb,mul_nonneg hη hgn]
  have hh := risk_step_of_margins (fun _ : Fin p.n => (p.n : ℝ)⁻¹) m s (fun _ => by positivity)
    (fun i => (hpoint i).1) η G (1/8) hlin hvar
  simpa [risk,s,m] using hh

noncomputable def imbalance (θ : Space .conv p.d) : ℝ := ‖θ.2‖^2-tapEnergy p θ

lemma imbalance_variation (θ : Space .conv p.d) (η : ℝ) :
    |imbalance p (advance p X η θ) - imbalance p θ| ≤ η^2*energy p (descent p X θ) := by
  rcases θ with ⟨⟨a,b⟩,v⟩
  let g := signedMean p X ((a,b),v)
  simp only [advance,descent_eq,imbalance,tapEnergy,energy]
  change |‖v+η • (a • g+b • shift g)‖^2-
    ((a+η*⟪g,v⟫)^2+(b+η*⟪shift g,v⟫)^2)-(‖v‖^2-(a^2+b^2))| ≤ _
  rw [layer_imbalance_step, abs_mul, abs_of_nonneg (sq_nonneg η)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg η)
  apply abs_le.mpr
  constructor <;> nlinarith only [sq_nonneg ⟪g,v⟫,sq_nonneg ⟪shift g,v⟫,
    sq_nonneg ‖a • g+b • shift g‖]

lemma energy_charge (θ : Space .conv p.d) (η : ℝ) (hη : 0 ≤ η)
    (hdes : η*energy p (descent p X θ) ≤ 2*(risk p X θ-risk p X (advance p X η θ))) :
    energy p (advance p X η θ)+2*η*risk p X (advance p X η θ)-
      (energy p θ+2*η*risk p X θ) ≤
      4*η*(intensity p X θ*Real.log (2/risk p X θ)-risk p X θ/2) := by
  let m := fun i => margin .conv p.d (X i) θ
  let w := weight p X θ
  have he := mean_work_le (fun _ : Fin p.n => (p.n : ℝ)⁻¹) m
    (fun _ => by positivity) (sum_mass p) (risk p X θ) (risk_pos p X θ) rfl
  have hw : ∑ i, w i*m i ≤ Real.log (2/risk p X θ)*intensity p X θ-risk p X θ/2 := by
    apply (le_of_eq _).trans he
    apply Finset.sum_congr rfl; intro i _
    dsimp [w,weight,m]; ring
  have hill : energy p (advance p X η θ)-energy p θ =
      4*η*(∑ i, w i*m i)+η^2*energy p (descent p X θ) := by
    rcases θ with ⟨⟨a,b⟩,v⟩
    dsimp only [m]
    rw [filtered_work]
    simp only [energy,tapEnergy,advance,descent_eq,margin]
    exact total_energy_step a b η (signedMean p X ((a,b),v)) v
  have ha := mul_le_mul_of_nonneg_left hdes hη
  have hb := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ 4*η)
  nlinarith only [hill,ha,hb]

lemma energy_next (θ : Space .conv p.d) (η : ℝ) (hη : 0 ≤ η) (hR : 0 ≤ p.R)
    (hX : ∀ i, ‖X i‖ ≤ p.R) (hf : risk p X θ ≤ 1) (hs : η*p.R ≤ 1/8) :
    energy p (advance p X η θ) ≤ 4*energy p θ := by
  let G := descent p X θ
  have hq : 0 ≤ intensity p X θ := Finset.sum_nonneg fun i _ => weights_nonneg _ _ _ _
  have hq1 := (intensity_le_risk p X θ).trans hf
  have hh := pow_le_pow_left₀ hq hq1 2
  have hz : 0 ≤ energy p θ := by dsimp [energy,tapEnergy]; positivity
  have hb := descent_energy_upper p X θ hX
  have hk : η^2*energy p G ≤ energy p θ := by
    have h1 : (η*p.R)^2 ≤ (1/8:ℝ)^2 := pow_le_pow_left₀ (by positivity) hs 2
    have ht := mul_le_mul_of_nonneg_left hb (sq_nonneg η)
    have h2 := mul_le_mul_of_nonneg_left hh (show 0 ≤ 4*(η*p.R)^2*energy p θ by positivity)
    have h3 := mul_le_mul_of_nonneg_right h1 hz
    dsimp [G]
    nlinarith only [ht,h2,h3,hz]
  have hnorm : ‖θ.2+η • G.2‖^2 ≤ 2*‖θ.2‖^2+2*η^2*‖G.2‖^2 := by
    have ht := norm_add_le θ.2 (η • G.2)
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hη] at ht
    nlinarith only [pow_le_pow_left₀ (norm_nonneg _) ht 2,
      sq_nonneg (‖θ.2‖-η*‖G.2‖)]
  change (θ.1.1+η*G.1.1)^2+(θ.1.2+η*G.1.2)^2+‖θ.2+η • G.2‖^2 ≤ _
  simp only [energy,tapEnergy] at hk ⊢
  nlinarith only [hk,hnorm,sq_nonneg (θ.1.1-η*G.1.1),sq_nonneg (θ.1.2-η*G.1.2)]

lemma mean_margin_bound (θ : Space .conv p.d) (hX : ∀ i, ‖X i‖ ≤ p.R) :
    Real.log 2-risk p X θ ≤ p.R*Real.sqrt (tapEnergy p θ)*‖θ.2‖ := by
  let m := fun i => margin .conv p.d (X i) θ
  have hbase := mean_loss_to_layer_product (fun _:Fin p.n => (p.n:ℝ)⁻¹) m
    (fun _ => by positivity) (sum_mass p)
  apply hbase.trans
  have hU : 0 ≤ tapEnergy p θ := by unfold tapEnergy; positivity
  have hpoint (i) : m i ≤ 2*p.R*Real.sqrt (tapEnergy p θ)*‖θ.2‖ := by
    have ht := filter_size_sq θ.1.1 θ.1.2 (X i)
    have hc : ‖θ.1.1 • X i+θ.1.2 • shift (X i)‖ ≤
        2*Real.sqrt (tapEnergy p θ)*‖X i‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      rw [mul_pow,mul_pow,Real.sq_sqrt hU]
      dsimp [tapEnergy]
      nlinarith only [ht,mul_nonneg (add_nonneg (sq_nonneg θ.1.1) (sq_nonneg θ.1.2)) (sq_nonneg ‖X i‖)]
    change θ.1.1*⟪X i,θ.2⟫+θ.1.2*⟪shift (X i),θ.2⟫ ≤ _
    rw [← real_inner_smul_left,← real_inner_smul_left,← inner_add_left]
    apply (real_inner_le_norm _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc _ ≤ _ := hc
         _ ≤ 2*Real.sqrt (tapEnergy p θ)*p.R :=
           mul_le_mul_of_nonneg_left (hX i) (by positivity)
         _ = _ := by ring
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    mul_le_mul_of_nonneg_left (hpoint i) (by positivity : 0 ≤ (p.n : ℝ)⁻¹)
  rw [← Finset.sum_mul, sum_mass, one_mul] at hsum
  linarith

end LongTails.Proofs.TwoTapLogisticDescent
