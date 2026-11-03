import LongTails.Proofs.FiniteSumNondualLowerAveraging

open scoped BigOperators
open MeasureTheory

namespace LongTails.Proofs.FiniteSumNondualLowerBound

open FiniteSumNondualLowerAveraging FiniteSumNondualLowerComponents
open FiniteSumNondualLowerHiding FiniteSumNondualLowerSearch FiniteSumNondualLowerPolicy
open LongTails.Setups.FiniteSumNondualSmoothConvex OracleTemplate

lemma finite_integral_lower {Ω U V : Type*} [MeasurableSpace Ω] [Fintype U] [Fintype V]
    (P : ProbabilityMeasure Ω) (f : Ω → U → V → ℝ) (C : ℝ)
    (hint : ∀ u v, Integrable (fun ω => f ω u v) (P : Measure Ω))
    (hpoint : ∀ ω, C ≤ 32 * ∑ u, ∑ v, f ω u v) :
    C ≤ 32 * ∑ u, ∑ v, ∫ ω, f ω u v ∂(P : Measure Ω) := by
  have hinner (u : U) : Integrable (fun ω => ∑ v, f ω u v) (P : Measure Ω) :=
    integrable_finsetSum Finset.univ (fun v _ => hint u v)
  have hsum : Integrable (fun ω => ∑ u, ∑ v, f ω u v) (P : Measure Ω) :=
    integrable_finsetSum Finset.univ (fun u _ => hinner u)
  have hb := integral_mono (integrable_const C) (hsum.const_mul 32) hpoint
  have he : (∫ ω, ∑ u, ∑ v, f ω u v ∂(P : Measure Ω)) =
      ∑ u, ∑ v, ∫ ω, f ω u v ∂(P : Measure Ω) := by
    rw [integral_finsetSum Finset.univ (fun u _ => hinner u)]
    apply Finset.sum_congr rfl
    intro u _
    exact integral_finsetSum Finset.univ (fun v _ => hint u v)
  simpa only [integral_const, probReal_univ, one_smul, integral_const_mul, he] using hb

lemma successful_objective {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (p : Params) {k : ℕ} (δ a : ℝ) (hL : 0 ≤ p.L) (hδ : 0 ≤ δ)
    (π : Fin (k + 1) ↪ Fin p.d) (owner : Fin (k + 1) → Fin p.n)
    (hR : ((k : ℝ) + 1) * |a| ≤ p.R) (output : Ω → Feasible p)
    (hs : spec.successful p (hardComponent p.L δ a π owner) output P) :
    Integrable (fun ω => objective (hardComponent p.L δ a π owner) (output ω).val)
        (P : Measure Ω) ∧
      (∫ ω, objective (hardComponent p.L δ a π owner) (output ω).val ∂(P : Measure Ω)) ≤ p.ε := by
  obtain ⟨_, xstar, hm, hi, he⟩ := hs
  have hzero : objective (hardComponent p.L δ a π owner) xstar.val = 0 := by
    apply le_antisymm
    · have h := hm (hiddenPoint_mem p a π hR)
      change objective (hardComponent p.L δ a π owner) xstar.val ≤
        objective (hardComponent p.L δ a π owner) (hiddenPoint π a) at h
      rw [hard_objective_hiddenPoint p δ a hδ π owner] at h
      exact h
    · exact hard_objective_nonneg p δ a hL π owner xstar.val
  simpa only [hzero, sub_zero] using And.intro hi he

lemma ownerWords_card_pos (n k : ℕ) (hn : 0 < n) : 0 < Fintype.card (OwnerWords n k) := by
  simp only [OwnerWords, Fintype.card_coe, words_card]
  exact pow_pos hn k

lemma coordinateWords_card_pos (d k : ℕ) (hd : k + 1 ≤ d) :
    0 < Fintype.card (CoordinateWords d k) := by
  simp only [CoordinateWords, Fintype.card_coe, distinctWords_card, Finset.card_univ,
    Fintype.card_fin]
  exact Nat.descFactorial_pos.mpr hd

lemma exists_hard_failure {p : Params} {k : ℕ} (δ a D : ℝ)
    (hL : 0 ≤ p.L) (hδ : 0 < δ) (ha : 0 ≤ a)
    (hscale : ((k : ℝ) + 1) * δ ≤ a / 8)
    (hR : ((k : ℝ) + 1) * |a| ≤ p.R)
    (hD : 0 < D) (hDs : D + (k + 1 : ℕ) ≤ p.d)
    (A : Algorithm (Fin p.n × Feasible p) (Point p) (Feasible p))
    (P : ProbabilityMeasure (A.Seed × (ℕ → Unit))) (T : ℕ)
    (hk : 0 < k) (hT : 8 * T ≤ p.n * k)
    (hsize : 32 * (T + 1 : ℕ) * (k + 1 : ℕ) * (p.R / (δ / 4)) ≤ D)
    (hε : 32 * p.ε < 23 * (p.L * a ^ 2 / (16 * ((k : ℝ) + 1) * p.n))) :
    ∃ u : OwnerWords p.n k, ∃ v : CoordinateWords p.d k,
      ¬ spec.successful p (hardComponent p.L δ a (coordinateEmbedding v) (wordOwner 0 u.val))
        (fun ω : A.Seed × (ℕ → Unit) =>
          execute (hardOracle p δ a (coordinateEmbedding v) (wordOwner 0 u.val))
            A (fun _ => T) ω.1 ω.2) P := by
  classical
  by_contra h
  push Not at h
  have hs (u : OwnerWords p.n k) (v : CoordinateWords p.d k) :=
    successful_objective P p δ a hL hδ.le (coordinateEmbedding v) (wordOwner 0 u.val)
      hR _ (h u v)
  have hi (u : OwnerWords p.n k) (v : CoordinateWords p.d k) :
      Integrable (fun ω : A.Seed × (ℕ → Unit) => executionGap δ a A T ω.1 ω.2 u v)
        (P : Measure _) := (hs u v).1
  have hl := finite_integral_lower P
    (fun ω : A.Seed × (ℕ → Unit) => executionGap δ a A T ω.1 ω.2) _ hi
    (fun ω => execution_joint_gap δ a D hL hδ ha hscale hD hDs A T ω.1 ω.2 hk hT hsize)
  have hu : (∑ u : OwnerWords p.n k, ∑ v : CoordinateWords p.d k,
      ∫ ω : A.Seed × (ℕ → Unit), executionGap δ a A T ω.1 ω.2 u v ∂(P : Measure _)) ≤
      Fintype.card (OwnerWords p.n k) * (Fintype.card (CoordinateWords p.d k) : ℝ) * p.ε := by
    calc
      _ ≤ ∑ _ : OwnerWords p.n k, ∑ _ : CoordinateWords p.d k, p.ε :=
        Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => (hs u v).2))
      _ = _ := by simp [mul_assoc]
  have hd : k + 1 ≤ p.d := by
    have hd' : ((k + 1 : ℕ) : ℝ) ≤ p.d := by linarith
    exact_mod_cast hd'
  have hp : 0 < (Fintype.card (OwnerWords p.n k) : ℝ) *
      (Fintype.card (CoordinateWords p.d k) : ℝ) := by
    apply mul_pos
    · exact_mod_cast ownerWords_card_pos p.n k (NeZero.pos p.n)
    · exact_mod_cast coordinateWords_card_pos p.d k hd
  have hlt := mul_lt_mul_of_pos_right hε hp
  have hupper := mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℝ) ≤ 32)
  nlinarith

lemma not_convergence_at (budget : Params → Fin 1 → ℕ) (p : Params) (hp : spec.valid p)
    {k : ℕ} (δ a D : ℝ) (hδ : 0 < δ) (ha : 0 ≤ a)
    (hscale : ((k : ℝ) + 1) * δ ≤ a / 8)
    (hR : ((k : ℝ) + 1) * |a| ≤ p.R)
    (hD : 0 < D) (hDs : D + (k + 1 : ℕ) ≤ p.d)
    (hk : 0 < k) (hT : 8 * budget p 0 ≤ p.n * k)
    (hsize : 32 * (budget p 0 + 1 : ℕ) * (k + 1 : ℕ) * (p.R / (δ / 4)) ≤ D)
    (hε : 32 * p.ε < 23 * (p.L * a ^ 2 / (16 * ((k : ℝ) + 1) * p.n))) :
    ¬ Convergence spec budget := by
  classical
  rintro ⟨make, hresult, _⟩
  let A := make p
  let P : ProbabilityMeasure (A.Seed × (ℕ → Unit)) :=
    ⟨(A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩
  have hL : 0 ≤ p.L := hp.2.2.1.le
  obtain ⟨u, v, hf⟩ := exists_hard_failure δ a D hL hδ ha hscale hR hD hDs
    A P (budget p 0) hk hT hsize hε
  apply hf
  have hs := hresult p hp (hardComponent p.L δ a (coordinateEmbedding v) (wordOwner 0 u.val))
    (hardOracle p δ a (coordinateEmbedding v) (wordOwner 0 u.val))
    (hard_admissible p δ a hL hδ.le (coordinateEmbedding v) (wordOwner 0 u.val))
  have hb : budget p = fun _ => budget p 0 := by
    funext i
    exact congrArg (budget p) (Subsingleton.elim i 0)
  rw [hb] at hs
  exact hs

lemma normalized_not_convergence (budget : Params → Fin 1 → ℕ) (p : Params) (hp : spec.valid p)
    (k : ℕ) (hk : 0 < k) (hT : 8 * budget p 0 ≤ p.n * k)
    (hd : k + 1 + 1024 * (budget p 0 + 1) * (k + 1) ^ 3 ≤ p.d)
    (hε : 32 * p.n * ((k : ℝ) + 1) ^ 3 * p.ε < p.L * p.R ^ 2) :
    ¬ Convergence spec budget := by
  let K : ℝ := (k : ℝ) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hR : 0 < p.R := hp.2.2.2.1
  have hL : 0 < p.L := hp.2.2.1
  have hn : (0 : ℝ) < p.n := by exact_mod_cast (NeZero.pos p.n)
  have hdim : K + 1024 * (budget p 0 + 1 : ℕ) * K ^ 3 ≤ p.d := by
    dsimp [K]
    exact_mod_cast hd
  have hD : 0 < (p.d : ℝ) - K := by
    have ht : (0 : ℝ) < (budget p 0 + 1 : ℕ) := by positivity
    have hpos : 0 < 1024 * (budget p 0 + 1 : ℕ) * K ^ 3 := by positivity
    linarith
  apply not_convergence_at budget p hp (p.R / (8 * K ^ 2)) (p.R / K) ((p.d : ℝ) - K)
  · positivity
  · positivity
  · change K * (p.R / (8 * K ^ 2)) ≤ (p.R / K) / 8
    apply le_of_eq
    field_simp
  · rw [abs_of_pos (div_pos hR hK)]
    change K * (p.R / K) ≤ p.R
    rw [mul_div_cancel₀ _ hK.ne']
  · exact hD
  · simp only [Nat.cast_add, Nat.cast_one]
    dsimp [K]
    linarith
  · exact hk
  · exact hT
  · have he : p.R / (p.R / (8 * K ^ 2) / 4) = 32 * K ^ 2 := by
      field_simp
      ring
    rw [he]
    change 32 * (budget p 0 + 1 : ℕ) * ((k + 1 : ℕ) : ℝ) * (32 * K ^ 2) ≤ (p.d : ℝ) - K
    have heK : ((k + 1 : ℕ) : ℝ) = K := by simp [K]
    rw [heK]
    nlinarith [hdim]
  · have he : 23 * (p.L * (p.R / K) ^ 2 / (16 * ((k : ℝ) + 1) * p.n)) =
        23 * p.L * p.R ^ 2 / (16 * p.n * K ^ 3) := by
      change 23 * (p.L * (p.R / K) ^ 2 / (16 * K * p.n)) = _
      field_simp
    rw [he]
    apply (lt_div_iff₀ (by positivity : 0 < 16 * (p.n : ℝ) * K ^ 3)).mpr
    have hs := mul_lt_mul_of_pos_left hε (by norm_num : (0 : ℝ) < 16)
    change 16 * (32 * p.n * K ^ 3 * p.ε) < 16 * (p.L * p.R ^ 2) at hs
    nlinarith [mul_pos hL (sq_pos_of_pos hR)]

end LongTails.Proofs.FiniteSumNondualLowerBound
