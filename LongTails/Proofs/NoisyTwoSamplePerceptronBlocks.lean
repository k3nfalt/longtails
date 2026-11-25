import LongTails.Proofs.NoisyTwoSamplePerceptronGaussian

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
open LongTails.Setups.FiniteLogisticTwoTap (Weights)
open LongTails.Proofs.FiniteLogisticTwoTapCoordinates
open LongTails.Proofs.NoisyTwoSamplePerceptronComplement
open LongTails.Proofs.NoisyTwoSamplePerceptronExecution
open LongTails.Proofs.NoisyTwoSamplePerceptronCoordinates
open LongTails.Proofs.NoisyTwoSamplePerceptronGaussian

namespace LongTails.Proofs.NoisyTwoSamplePerceptronBlocks

noncomputable def fast {d : ℕ} (i : Fin d) : StrongDual ℝ (Weights d) := component i 0+component i 1

lemma fast_value {d : ℕ} (i : Fin d) (w : Weights d) :
    fast i w = proj (coords i w) 0 + proj (coords i w) 1 := rfl

lemma fast_norm {d : ℕ} (i : Fin d) : 1/2 ≤ ‖fast i‖ := by
  let x : Weights d := EuclideanSpace.single (.inl 0) 1
  have H := (fast i).le_opNorm x
  have hx : fast i x = 1/Real.sqrt 2 := by simp [fast,component,coords,x,readSum]
  rw [hx] at H
  have hu : ‖x‖=1 := by simp [x]
  rw [hu,mul_one,Real.norm_eq_abs,abs_of_pos (by positivity)] at H
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  exact le_trans ((le_div_iff₀ (by positivity)).mpr (by nlinarith)) H

lemma fast_move {d : ℕ} (hd : 2 ≤ d) (i : Fin d) (hi : finRotate d i ≠ i)
    (μ σ : ℝ) (w g : Weights d) :
    fast i (move μ (gamma d) σ i w g false) = (1+c)*fast i w+σ*fast i g := by
  simp only [fast_value,proj_move hd i hi]
  simp [matrix,action,vec]
  ring

lemma independent_strip {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Y X : Ω → ℝ) (hY : Measurable Y) (hX : Measurable X) (hI : IndepFun Y X P)
    (hLaw : P.map X = gaussianReal 0 1) (A H : ℝ) (hA : 0 < A) :
    P {g | |Y g+A*X g| ≤ H} ≤ ENNReal.ofReal (H/A) := by
  let E := {z : ℝ × ℝ | |z.1+A*z.2| ≤ H}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  have hh : Measurable (fun ω => (Y ω,X ω)) := hY.prodMk hX
  calc
    _ = P.map (fun ω => (Y ω,X ω)) E := (Measure.map_apply hh hE).symm
    _ = ((P.map Y).prod (gaussianReal 0 1)) E := by rw [hI.map_prod_eq_prod_map_map hY.aemeasurable hX.aemeasurable,hLaw]
    _ ≤ ∫⁻ _ : ℝ, ENNReal.ofReal (H/A) ∂(P.map Y) := by
      rw [Measure.prod_apply hE]
      apply lintegral_mono
      intro y
      apply le_trans (GatedEscapeGaussian.gaussianReal_le_of_diam _ (D := 2*H/A) ?_)
      · apply ENNReal.ofReal_le_ofReal
        ring_nf
        rfl
      · intro a ha b hb
        change |y+A*a| ≤ H at ha
        change |y+A*b| ≤ H at hb
        rw [abs_le,le_div_iff₀ hA,← neg_div,div_le_iff₀ hA]
        constructor <;> nlinarith [(abs_le.mp ha).1,(abs_le.mp ha).2,(abs_le.mp hb).1,(abs_le.mp hb).2]
    _ = _ := by simp

lemma normalized_law {d : ℕ} (i : Fin d) :
    (stdGaussian (Weights d)).map (‖fast i‖⁻¹ • fast i : StrongDual ℝ (Weights d)) = gaussianReal 0 1 := by
  rw [dual_law,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (show ‖fast i‖ ≠ 0 by linarith [fast_norm i])]
  norm_num

noncomputable def law (d : ℕ) : Measure (ℕ → Weights d) :=
  Measure.infinitePi (fun _ : ℕ => stdGaussian (Weights d))

instance (d : ℕ) : IsProbabilityMeasure (law d) := by unfold law; infer_instance

lemma outside_indep {d : ℕ} (s : ℕ) (I : Finset ℕ) (hs : s ∉ I)
    (F : (I → Weights d) → ℝ) (hF : Measurable F) (i : Fin d) :
    IndepFun (fun g => F (fun j => g j)) (fun g => (‖fast i‖⁻¹ • fast i : StrongDual ℝ (Weights d)) (g s)) (law d) := by
  have H : iIndepFun (fun j (g : ℕ → Weights d) => g j) (law d) :=
    iIndepFun_infinitePi (X := fun _ => id)
    (fun _ => measurable_id)
  have H' := H.indepFun_finset I {s} (Finset.disjoint_singleton_right.mpr hs) (fun j => measurable_pi_apply j)
  let L : StrongDual ℝ (Weights d) := ‖fast i‖⁻¹ • fast i
  exact H'.comp hF (L.continuous.measurable.comp (measurable_pi_apply (⟨s,by simp⟩ : ({s}:Finset ℕ))))

noncomputable def forced {d : ℕ} (μ σ : ℝ) (i : Fin d) (x : Weights d)
    (g : ℕ → Weights d) (s : ℕ) : ℕ → ℝ
  | 0 => fast i (point μ (gamma d) σ i x g s)
  | n+1 => (1+c)*forced μ σ i x g s n+σ*fast i (g (s+n))

lemma forced_measurable {d : ℕ} (μ σ : ℝ) (i : Fin d) (x : Weights d) (s n : ℕ) :
    Measurable (fun g => forced μ σ i x g s n) := by
  induction n with
  | zero => exact (fast i).continuous.measurable.comp (point_measurable ..)
  | succ n ih => dsimp only [forced]; fun_prop

lemma forced_diff {d : ℕ} (μ σ : ℝ) (i : Fin d) (x : Weights d)
    (g v : ℕ → Weights d) (s n : ℕ) (h₀ : v s=0)
    (heq : ∀ t < s+(n+1), t≠s → g t=v t) :
    forced μ σ i x g s (n+1) = forced μ σ i x v s (n+1)+(1+c)^n*σ*fast i (g s) := by
  induction n with
  | zero =>
    simp [forced,h₀,point_congr μ (gamma _) σ i x g v s (fun t ht => heq t (by omega) (by omega))]
  | succ n ih =>
    have H := ih (fun t ht => heq t (by omega))
    simp only [forced] at H ⊢
    rw [H,heq (s+(n+1)) (by omega) (by omega),pow_succ]
    ring

lemma follows_first {d : ℕ} (hd : 2 ≤ d) (μ σ : ℝ) (i : Fin d) (hi : finRotate d i ≠ i)
    (x : Weights d) (g : ℕ → Weights d) (s n : ℕ)
    (h : ∀ j < n, choice μ i (point μ (gamma d) σ i x g (s+j)) = some false) :
    fast i (point μ (gamma d) σ i x g (s+n)) = forced μ σ i x g s n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Nat.add_assoc,point,h _ (by omega)]
    rw [fast_move hd i hi,ih (fun j hj => h j (by omega)),forced]

lemma forced_small {d : ℕ} (μ σ : ℝ) (hσ : 0 < σ) (i : Fin d) (x : Weights d)
    (s n : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    law d {g | |forced μ σ i x g s (n+1)| ≤ H} ≤ ENNReal.ofReal (2*H/((1+c)^n*σ)) := by
  classical
  let I := (Finset.range (s+(n+1))).erase s
  let extend := fun (v : I → Weights d) (t : ℕ) => if ht : t ∈ I then v ⟨t,ht⟩ else 0
  let shift := fun v => forced μ σ i x (extend v) s (n+1)
  let Y := fun (g : ℕ → Weights d) => shift (fun j : I => g j)
  let X := fun (g : ℕ → Weights d) => (‖fast i‖⁻¹ • fast i : StrongDual ℝ (Weights d)) (g s)
  have hs : s ∉ I := Finset.notMem_erase s _
  have hExt : Measurable extend := Measurable.of_eval (fun t => by
    dsimp [extend]
    split <;> fun_prop)
  have hSh : Measurable shift := (forced_measurable μ σ i x s (n+1)).comp hExt
  have hrest : Measurable (fun (g : ℕ → Weights d) (j : I) => g j) := by fun_prop
  have hY : Measurable Y := hSh.comp hrest
  have hX : Measurable X := (ContinuousLinearMap.continuous _).measurable.comp (measurable_pi_apply _)
  have hI : IndepFun Y X (law d) := outside_indep s I hs shift hSh i
  have hLaw : (law d).map X = gaussianReal 0 1 := by
    change (law d).map ((‖fast i‖⁻¹ • fast i : StrongDual ℝ (Weights d)) ∘ (fun g => g s)) = _
    rw [← Measure.map_map (‖fast i‖⁻¹ • fast i : StrongDual ℝ (Weights d)).continuous.measurable (measurable_pi_apply s)]
    rw [show (law d).map (fun g => g s) = stdGaussian _ from Measure.infinitePi_map_eval (fun _ : ℕ => stdGaussian (Weights d)) s]
    exact normalized_law i
  let A := (1+c)^n*σ*‖fast i‖
  have hf := fast_norm i
  have hc : 0 < 1+c := by dsimp [c]; positivity
  have hn := pow_pos hc n
  have hA : 0 < A := mul_pos (mul_pos hn hσ) (by linarith)
  have HH := independent_strip Y X hY hX hI hLaw A H hA
  have heq (g : ℕ → Weights d) : forced μ σ i x g s (n+1) = Y g+A*X g := by
    dsimp only [Y,shift]
    rw [forced_diff μ σ i x g (extend (fun j : I => g j)) s n (by simp [extend,hs]) (by
      intro t ht hts
      have htI : t ∈ I := Finset.mem_erase.mpr ⟨hts,Finset.mem_range.mpr ht⟩
      simp [extend,htI])]
    dsimp only [X,A]
    rw [smul_apply,smul_eq_mul]
    field_simp [show ‖fast i‖ ≠ 0 by linarith]
  simp_rw [heq]
  apply HH.trans
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_div_iff₀ hA (mul_pos hn hσ)).mpr
  dsimp [A]
  nlinarith only [mul_le_mul_of_nonneg_left hf (mul_nonneg hH (mul_nonneg hn.le hσ.le))]

end LongTails.Proofs.NoisyTwoSamplePerceptronBlocks
