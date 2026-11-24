import LongTails.Proofs.NcConcaveEmbed

open scoped BigOperators

namespace LongTails.Proofs.NcConcaveStage

open LongTails.Proofs.NcConcaveInstance LongTails.Proofs.NcConcaveModel
open LongTails.Proofs.NcConcaveLocality LongTails.Proofs.NcConcaveChainGrad
open LongTails.Proofs.NcConcaveEmbed

variable {n m : ℕ}

noncomputable def famSup {ι : Type*} [Fintype ι] (θ : ℝ) (r : ℕ) (pos : ι → ℕ) (val : ι → ℝ) : ℕ :=
  Finset.univ.sup fun i => if pos i < r ∧ θ < |val i| then pos i + 1 else 0

lemma famSup_le {ι : Type*} [Fintype ι] (θ : ℝ) (r : ℕ) (pos : ι → ℕ) (val : ι → ℝ) :
    famSup θ r pos val ≤ r := by
  apply Finset.sup_le; intro i _; split_ifs with h <;> omega

lemma famSup_small {ι : Type*} [Fintype ι] (θ : ℝ) (r : ℕ) (pos : ι → ℕ) (val : ι → ℝ) (s : ℕ)
    (hs : famSup θ r pos val ≤ s) (i : ι) (hi : s ≤ pos i) (hr : pos i < r) : |val i| ≤ θ := by
  by_contra h
  push Not at h
  have hle : (if pos i < r ∧ θ < |val i| then pos i + 1 else 0) ≤ famSup θ r pos val :=
    Finset.le_sup (f := fun i => if pos i < r ∧ θ < |val i| then pos i + 1 else 0) (Finset.mem_univ i)
  rw [ite_eq_left ⟨hr, h⟩] at hle
  omega

lemma famSup_congr {ι : Type*} [Fintype ι] (θ : ℝ) (r : ℕ) (pos : ι → ℕ) (val val' : ι → ℝ)
    (h : ∀ i, pos i < r → val i = val' i) : famSup θ r pos val = famSup θ r pos val' := by
  unfold famSup
  congr 1; funext i
  by_cases hi : pos i < r
  · rw [h i hi]
  · simp only [hi, false_and, ite_false]

lemma famSup_eq_of_small {ι : Type*} [Fintype ι] (θ : ℝ) (r r' : ℕ) (pos : ι → ℕ) (val : ι → ℝ)
    (hrr : r ≤ r') (h : ∀ i, r ≤ pos i → |val i| ≤ θ) : famSup θ r' pos val = famSup θ r pos val := by
  unfold famSup
  congr 1; funext i
  by_cases hi : pos i < r
  · simp only [hi, show pos i < r' by omega, true_and]
  · have := h i (by omega)
    simp only [hi, ite_false, show ¬ (θ < |val i|) by linarith, and_false]

noncomputable def stageUpTo (θ : ℝ) (r : ℕ) (c : CS n m) : ℕ :=
  max (max (famSup θ r (fun j : Fin (n + 1) => pU m j) c.1) (famSup θ r (fun i : Fin n => pA m i) c.2.1))
    (max (famSup θ r (fun i : Fin n => pB m i) c.2.2.1)
      (famSup θ r (fun p : Fin n × Fin (m + 1) => pY m p.1 p.2) (fun p => c.2.2.2 p.1 p.2)))

noncomputable def stage (θ : ℝ) (c : CS n m) : ℕ := stageUpTo θ (K n m) c

lemma stageUpTo_le (θ : ℝ) (r : ℕ) (c : CS n m) : stageUpTo θ r c ≤ r := by
  unfold stageUpTo
  simp only [max_le_iff]
  exact ⟨⟨famSup_le _ _ _ _, famSup_le _ _ _ _⟩, famSup_le _ _ _ _, famSup_le _ _ _ _⟩

lemma stage_le (θ : ℝ) (c : CS n m) : stage θ c ≤ K n m := stageUpTo_le θ _ c

lemma smallFrom_stageUpTo (θ : ℝ) (r : ℕ) (c : CS n m) (s : ℕ) (hs : stageUpTo θ r c ≤ s) :
    (∀ j : Fin (n + 1), s ≤ pU m j → pU m j < r → |c.1 j| ≤ θ) ∧
    (∀ i : Fin n, s ≤ pA m i → pA m i < r → |c.2.1 i| ≤ θ) ∧
    (∀ i : Fin n, s ≤ pB m i → pB m i < r → |c.2.2.1 i| ≤ θ) ∧
    (∀ (i : Fin n) (k : Fin (m + 1)), s ≤ pY m i k → pY m i k < r → |c.2.2.2 i k| ≤ θ) := by
  unfold stageUpTo at hs
  simp only [max_le_iff] at hs
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hs
  exact ⟨fun j hj hr => famSup_small _ _ _ _ _ h1 j hj hr,
    fun i hi hr => famSup_small _ _ _ _ _ h2 i hi hr,
    fun i hi hr => famSup_small _ _ _ _ _ h3 i hi hr,
    fun i k hk hr => famSup_small θ r (fun p : Fin n × Fin (m + 1) => pY m p.1 p.2)
      (fun p => c.2.2.2 p.1 p.2) s h4 (i, k) hk hr⟩

lemma smallFrom_stage {θ : ℝ} (c : CS n m) (s : ℕ) (hs : stage θ c ≤ s) :
    SmallFrom θ s c := by
  obtain ⟨h1, h2, h3, h4⟩ := smallFrom_stageUpTo θ (K n m) c s hs
  exact ⟨fun j hj => h1 j hj (pU_lt j), fun i hi => h2 i hi (pA_lt i),
    fun i hi => h3 i hi (pB_lt i), fun i k hk => h4 i k hk (pY_lt i k)⟩

lemma stageUpTo_eq_stage {θ : ℝ} (r : ℕ) (c : CS n m) (hr : r ≤ K n m) (h : SmallFrom θ r c) :
    stageUpTo θ r c = stage θ c := by
  unfold stage stageUpTo
  rw [famSup_eq_of_small θ r (K n m) _ _ hr h.hu, famSup_eq_of_small θ r (K n m) _ _ hr h.ha,
    famSup_eq_of_small θ r (K n m) _ _ hr h.hb,
    famSup_eq_of_small θ r (K n m) (fun p : Fin n × Fin (m + 1) => pY m p.1 p.2)
      (fun p => c.2.2.2 p.1 p.2) hr (fun p hp => h.hy p.1 p.2 hp)]

lemma stageUpTo_congr {θ : ℝ} (r : ℕ) (c c' : CS n m)
    (h1 : ∀ j : Fin (n + 1), pU m j < r → c.1 j = c'.1 j)
    (h2 : ∀ i : Fin n, pA m i < r → c.2.1 i = c'.2.1 i)
    (h3 : ∀ i : Fin n, pB m i < r → c.2.2.1 i = c'.2.2.1 i)
    (h4 : ∀ (i : Fin n) (k : Fin (m + 1)), pY m i k < r → c.2.2.2 i k = c'.2.2.2 i k) :
    stageUpTo θ r c = stageUpTo θ r c' := by
  unfold stageUpTo
  rw [famSup_congr θ r _ _ _ h1, famSup_congr θ r _ _ _ h2, famSup_congr θ r _ _ _ h3,
    famSup_congr θ r (fun p : Fin n × Fin (m + 1) => pY m p.1 p.2) (fun p => c.2.2.2 p.1 p.2)
      (fun p => c'.2.2.2 p.1 p.2) (fun p hp => h4 p.1 p.2 hp)]

def maskedPos (m n : ℕ) (p : ℕ) : Prop := ∃ i : Fin n, ∃ k : Fin (m + 1), pY m i k = p

instance (p : ℕ) : Decidable (maskedPos m n p) := by unfold maskedPos; infer_instance

lemma not_masked_K : ¬ maskedPos m n (K n m) := by
  rintro ⟨i, k, h⟩
  have := pY_lt (m := m) i k
  omega

end LongTails.Proofs.NcConcaveStage
