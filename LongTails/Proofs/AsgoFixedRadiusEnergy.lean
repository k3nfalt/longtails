import LongTails.Proofs.AsgoFixedRadiusMatrix

open Matrix Finset
open scoped BigOperators

namespace OracleTemplate.AsgoFixedRadius

open LongTails.Setups.AsgoFixedRadius

lemma damped_energy_identity {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℝ) (G : Muon.Mat m n)
    (k : ℝ) (hB : B.PosSemidef) (hk : 0 < k) :
    let S := Core.matrixRoot (B + Core.gram G)
    let P := Core.matrixRoot B
    let A := S + k • (1 : Matrix (Fin m) (Fin m) ℝ)
    let D := S - P
    Core.weightedQuadratic (A⁻¹) G =
      2 * D.trace - (D * D * A⁻¹).trace - 2 * k * (D * A⁻¹).trace := by
  open Matrix in
  open scoped BigOperators in
  (
    classical
    let S := Core.matrixRoot (B + Core.gram G)
    let P := Core.matrixRoot B
    let A := S + k • (1 : Matrix (Fin m) (Fin m) ℝ)
    let D := S-P
    change Core.weightedQuadratic A⁻¹ G =
      2 * D.trace - (D*D*A⁻¹).trace - 2*k*(D*A⁻¹).trace
    have hG : (Core.gram G).PosSemidef := by
      delta Core.gram
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.posSemidef_self_mul_conjTranspose (Muon.toMatrix G)
    have hS : S*S = B+Core.gram G := (root_square _ (hB.add hG)).1
    have hP : P*P = B := (root_square B hB).1
    have hA : A.PosDef := Matrix.PosDef.posSemidef_add (root_psd _) (Matrix.PosDef.one.smul hk)
    obtain ⟨hAi, hAAi, hAiA⟩ := inverse_posDef A hA
    have he : Core.gram G = D*A+A*D-D*D-(2*k)•D := by
      calc
        Core.gram G = S*S-P*P := by rw [hS, hP, add_sub_cancel_left]
        _ = _ := by
          dsimp only [D,A]
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
            smul_mul_assoc, mul_smul_comm, mul_one, one_mul, smul_sub]
          module
    have hq : Core.weightedQuadratic A⁻¹ G = (Core.gram G*A⁻¹).trace := by
      delta Core.weightedQuadratic Core.gram
      rw [Matrix.trace_mul_cycle]
    rw [hq,he]
    simp only [Matrix.sub_mul, Matrix.add_mul, smul_mul_assoc, Matrix.trace_sub,
      Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
    have h1 : (D*A*A⁻¹).trace = D.trace := by rw [Matrix.mul_assoc, hAAi, mul_one]
    have h2 : (A*D*A⁻¹).trace = D.trace := by rw [Matrix.trace_mul_cycle, hAiA, one_mul]
    rw [h1,h2]
    ring
  )

lemma damped_energy_le {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℝ) (G : Muon.Mat m n)
    (k : ℝ) (hB : B.PosSemidef) (hk : 0 < k) :
    let S := Core.matrixRoot (B + Core.gram G)
    let A := S + k • (1 : Matrix (Fin m) (Fin m) ℝ)
    Core.weightedQuadratic (A⁻¹) G ≤ 2 * (S - Core.matrixRoot B).trace := by
  open Matrix in
  open scoped BigOperators in
  (
    classical
    let S := Core.matrixRoot (B+Core.gram G)
    let A := S+k•(1 : Matrix (Fin m) (Fin m) ℝ)
    let D := S-Core.matrixRoot B
    change Core.weightedQuadratic A⁻¹ G ≤ 2*D.trace
    have hG : (Core.gram G).PosSemidef := by
      delta Core.gram
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.posSemidef_self_mul_conjTranspose (Muon.toMatrix G)
    have hBG : Core.loewner B (B+Core.gram G) := by
      delta Core.loewner
      simpa only [add_sub_cancel_left] using hG
    have hD : D.PosSemidef := root_mono B (B+Core.gram G) hB hBG
    have hDD : (D*D).PosSemidef := by simpa only [pow_two] using hD.pow 2
    have hA : A.PosDef := Matrix.PosDef.posSemidef_add (root_psd _) (Matrix.PosDef.one.smul hk)
    have hAi := (inverse_posDef A hA).1.posSemidef
    have h1 := trace_mul_nonneg (D*D) A⁻¹ hDD hAi
    have h2 := trace_mul_nonneg D A⁻¹ hD hAi
    have he := damped_energy_identity B G k hB hk
    change Core.weightedQuadratic A⁻¹ G = 2*D.trace-(D*D*A⁻¹).trace-2*k*(D*A⁻¹).trace at he
    nlinarith
  )

lemma pathwise_regret {m n : ℕ} (x g : ℕ → Muon.Mat m n) (Wstar : Muon.Mat m n)
    (R F k : ℝ) (T : ℕ) (hR : 0 < R) (hF : 0 ≤ F) (hk : 0 < k)
    (hOp : ∀ t < T, Muon.spectralNorm (x t - Wstar) ≤ R)
    (hFrob : ∀ t < T, ‖x t - Wstar‖ ≤ F)
    (hStep : ∀ t < T,
      let S := Core.matrixRoot (∑ j ∈ range (t + 1), Core.gram (g j))
      let A := S + k • (1 : Matrix (Fin m) (Fin m) ℝ)
      x (t + 1) = x t - R • Muon.ofMatrix (A⁻¹ * Muon.toMatrix (g t))) :
    (∑ t ∈ range T, inner ℝ (g t) (x t - Wstar)) ≤
      (3 * R / 2) * (Core.matrixRoot (∑ t ∈ range T, Core.gram (g t))).trace +
        k * F ^ 2 / (2 * R) := by
  open Matrix in
  open scoped BigOperators in
  (
    classical
    by_cases hT : T=0
    · subst T
      delta Core.matrixRoot
      simp only [Finset.sum_range_zero, CFC.sqrt_zero, Matrix.trace_zero,
        mul_zero, zero_add]
      positivity
    have hTpos : 0<T := Nat.pos_of_ne_zero hT
    let B (t : ℕ) := ∑ j ∈ range t, Core.gram (g j)
    let S (t : ℕ) := Core.matrixRoot (B t)
    let A (t : ℕ) := S t+k•(1 : Matrix (Fin m) (Fin m) ℝ)
    let e (t : ℕ) := x t-Wstar
    have hB (t : ℕ) : (B t).PosSemidef := Matrix.posSemidef_sum _ (fun j _ => by
      delta Core.gram
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.posSemidef_self_mul_conjTranspose (Muon.toMatrix (g j)))
    have hA (t : ℕ) : (A t).PosDef :=
      Matrix.PosDef.posSemidef_add (root_psd _) (Matrix.PosDef.one.smul hk)
    have hS0 : S 0=0 := by
      dsimp only [S,B]
      delta Core.matrixRoot
      simp only [Finset.sum_range_zero,CFC.sqrt_zero]
    have hq (K : Matrix (Fin m) (Fin m) ℝ) (X : Muon.Mat m n) :
        Core.weightedQuadratic K X=(Core.gram X*K).trace := by
      delta Core.weightedQuadratic Core.gram
      rw [Matrix.trace_mul_cycle]
    have hone (t : ℕ) (ht : t<T) :
        2*R*inner ℝ (g t) (e t)+Core.weightedQuadratic (A (t+1)) (e (t+1)) ≤
          Core.weightedQuadratic (A t) (e t)+3*R^2*((S (t+1)).trace-(S t).trace) := by
      let D := S (t+1)-S t
      let E := Muon.toMatrix (e t)
      let G := Muon.toMatrix (g t)
      let Ai := (A (t+1))⁻¹
      have hsucc : B (t+1)=B t+Core.gram (g t) := Finset.sum_range_succ _ _
      have hG : (Core.gram (g t)).PosSemidef := by
        delta Core.gram
        simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
          Matrix.posSemidef_self_mul_conjTranspose G
      have hD : D.PosSemidef := by
        apply root_mono (B t) (B (t+1)) (hB t)
        delta Core.loewner
        simpa only [hsucc,add_sub_cancel_left] using hG
      have hAi : Ai.PosDef := (inverse_posDef (A (t+1)) (hA (t+1))).1
      have hAAi : A (t+1)*Ai=1 := (inverse_posDef (A (t+1)) (hA (t+1))).2.1
      have hAiA : Ai*A (t+1)=1 := (inverse_posDef (A (t+1)) (hA (t+1))).2.2
      have hAiT : Aiᵀ=Ai := by
        simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hAi.isHermitian.eq
      have he : e (t+1)=e t-R•Muon.ofMatrix (Ai*G) := by
        dsimp only [e]
        rw [hStep t ht]
        change x t-R•Muon.ofMatrix (Ai*G)-Wstar = (x t-Wstar)-R•Muon.ofMatrix (Ai*G)
        exact sub_right_comm _ _ _
      have h1 : (Eᵀ*A (t+1)*(Ai*G)).trace=inner ℝ (g t) (e t) := by
        calc
          _ = (Eᵀ*G).trace := by
            congr 1
            calc
              _=Eᵀ*(A (t+1)*Ai)*G := by simp only [Matrix.mul_assoc]
              _=_ := by rw [hAAi]; simp only [Matrix.mul_one]
          _=inner ℝ (e t) (g t) := (inner_trace _ _).symm
          _=_ := real_inner_comm _ _
      have h2 : ((Ai*G)ᵀ*A (t+1)*E).trace=inner ℝ (g t) (e t) := by
        rw [Matrix.transpose_mul,hAiT]
        calc
          _=(Gᵀ*E).trace := by
            congr 1
            calc
              _=Gᵀ*(Ai*A (t+1))*E := by simp only [Matrix.mul_assoc]
              _=_ := by rw [hAiA]; simp only [Matrix.mul_one]
          _=_ := (inner_trace _ _).symm
      have h3 : ((Ai*G)ᵀ*A (t+1)*(Ai*G)).trace=Core.weightedQuadratic Ai (g t) := by
        rw [Matrix.transpose_mul,hAiT]
        change (Gᵀ*Ai*A (t+1)*(Ai*G)).trace=(Gᵀ*Ai*G).trace
        congr 1
        calc
          _=Gᵀ*(Ai*A (t+1))*Ai*G := by simp only [Matrix.mul_assoc]
          _=_ := by rw [hAiA]; simp only [Matrix.mul_one]
      have hupdate : Core.weightedQuadratic (A (t+1)) (e (t+1))=
          Core.weightedQuadratic (A (t+1)) (e t)-2*R*inner ℝ (g t) (e t)+R^2*Core.weightedQuadratic Ai (g t) := by
        rw [he]
        change ((E-R•(Ai*G))ᵀ*A (t+1)*(E-R•(Ai*G))).trace=
          (Eᵀ*A (t+1)*E).trace-2*R*inner ℝ (g t) (e t)+R^2*Core.weightedQuadratic Ai (g t)
        simp only [Matrix.transpose_sub,Matrix.transpose_smul,Matrix.sub_mul,Matrix.mul_sub,
          Matrix.smul_mul,Matrix.mul_smul,Matrix.trace_sub,Matrix.trace_smul,smul_eq_mul,h1,h2,h3]
        ring
      have hspec := (spectral_gram_iff (e t) R hR).1 (hOp t ht)
      have htrace := trace_mul_nonneg D (R^2•(1 : Matrix (Fin m) (Fin m) ℝ)-Core.gram (e t)) hD hspec
      simp only [Matrix.mul_sub,Matrix.mul_smul,Matrix.mul_one,Matrix.trace_sub,
        Matrix.trace_smul,smul_eq_mul] at htrace
      have hqD : (D*Core.gram (e t)).trace=Core.weightedQuadratic D (e t) := by
        rw [hq,Matrix.trace_mul_comm]
      rw [hqD] at htrace
      have hAD : A (t+1)=A t+D := by dsimp only [A, D]; module
      have hdrift : Core.weightedQuadratic (A (t+1)) (e t)=
          Core.weightedQuadratic (A t) (e t)+Core.weightedQuadratic D (e t) := by
        rw [hAD]
        delta Core.weightedQuadratic
        simp only [Matrix.mul_add,Matrix.add_mul,Matrix.trace_add]
      have henergy := damped_energy_le (B t) (g t) k (hB t) hk
      change Core.weightedQuadratic (Core.matrixRoot (B t+Core.gram (g t))+k•1)⁻¹ (g t) ≤
        2*(Core.matrixRoot (B t+Core.gram (g t))-Core.matrixRoot (B t)).trace at henergy
      rw [← hsucc] at henergy
      change Core.weightedQuadratic Ai (g t) ≤ 2*D.trace at henergy
      have hDt : D.trace=(S (t+1)).trace-(S t).trace := Matrix.trace_sub _ _
      rw [hDt] at htrace henergy
      nlinarith [mul_le_mul_of_nonneg_left henergy (sq_nonneg R)]
    have hacc : ∀ t≤T,
        2*R*(∑ j ∈ range t, inner ℝ (g j) (e j))+Core.weightedQuadratic (A t) (e t) ≤
          Core.weightedQuadratic (A 0) (e 0)+3*R^2*(S t).trace := by
      intro t ht
      induction t with
      | zero => simp only [Finset.sum_range_zero,mul_zero,zero_add,hS0,Matrix.trace_zero,add_zero,le_refl]
      | succ t ih =>
        have hp := ih (Nat.le_trans (Nat.le_succ t) ht)
        have hs := hone t (Nat.lt_of_succ_le ht)
        rw [Finset.sum_range_succ]
        nlinarith
    have hfinal := hacc T le_rfl
    have hnonneg := quadratic_nonneg (A T) (e T) (hA T).posSemidef
    have hinit : Core.weightedQuadratic (A 0) (e 0)=k*‖e 0‖^2 := by
      delta Core.weightedQuadratic
      simp only [A,hS0,zero_add,Matrix.mul_smul,Matrix.mul_one,
        Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul]
      rw [← inner_trace,real_inner_self_eq_norm_sq]
    have hF0 : ‖e 0‖≤F := hFrob 0 hTpos
    have hF2 := (pow_le_pow_iff_left₀ (norm_nonneg (e 0)) hF two_ne_zero).2 hF0
    rw [hinit] at hfinal
    change (∑ t ∈ range T, inner ℝ (g t) (e t)) ≤ (3*R/2)*(S T).trace+k*F^2/(2*R)
    have hr : (3*R/2)*(S T).trace+k*F^2/(2*R)=
        (3*R^2*(S T).trace+k*F^2)/(2*R) := by field_simp
    rw [hr]
    apply (le_div_iff₀ (show 0<2*R by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_left hF2 hk.le]
  )

end OracleTemplate.AsgoFixedRadius
