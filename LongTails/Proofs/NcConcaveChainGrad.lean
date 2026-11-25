import LongTails.Proofs.NcConcaveLocality
import LongTails.Proofs.NcConcaveAnalysis

open scoped BigOperators Topology

namespace LongTails.Proofs.NcConcaveChainGrad

open LongTails.Proofs.NcConcaveScalars LongTails.Proofs.NcConcaveTransitions
open LongTails.Proofs.NcConcaveTransitionBounds LongTails.Proofs.NcConcaveInstance
open LongTails.Proofs.NcConcaveModel LongTails.Proofs.NcConcaveLocality
open LongTails.Proofs.NcConcaveAnalysis

variable {n m : ℕ}

abbrev CS (n m : ℕ) :=
  (Fin (n + 1) → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → Fin (m + 1) → ℝ)

noncomputable def Fc (θ τ : ℝ) (c : CS n m) : ℝ := robF θ τ c.1 c.2.1 c.2.2.1 c.2.2.2

noncomputable def DFl (θ τ : ℝ) (c : CS n m) : CS n m →ₗ[ℝ] ℝ where
  toFun v := dF θ τ c.1 c.2.1 c.2.2.1 c.2.2.2 v.1 v.2.1 v.2.2.1 v.2.2.2
  map_add' v w := dF_add θ τ c.1 c.2.1 c.2.2.1 c.2.2.2 v.1 w.1 v.2.1 w.2.1 v.2.2.1 w.2.2.1 v.2.2.2 w.2.2.2
  map_smul' r v := dF_smul θ τ c.1 c.2.1 c.2.2.1 c.2.2.2 r v.1 v.2.1 v.2.2.1 v.2.2.2

noncomputable def DFc (θ τ : ℝ) (c : CS n m) : CS n m →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (DFl θ τ c)

lemma DFc_apply (θ τ : ℝ) (c v : CS n m) :
    DFc θ τ c v = dF θ τ c.1 c.2.1 c.2.2.1 c.2.2.2 v.1 v.2.1 v.2.2.1 v.2.2.2 := rfl

def NC (n m : ℕ) : ℝ := (n + 1 : ℕ) + n + n + n * (m + 1 : ℕ)

lemma coord_sq_le (v : CS n m) :
    (∀ j, v.1 j ^ 2 ≤ ‖v‖ ^ 2) ∧ (∀ i, v.2.1 i ^ 2 ≤ ‖v‖ ^ 2) ∧ (∀ i, v.2.2.1 i ^ 2 ≤ ‖v‖ ^ 2) ∧
      (∀ i k, v.2.2.2 i k ^ 2 ≤ ‖v‖ ^ 2) := by
  have hsq : ∀ (t : ℝ) (B : ℝ), ‖t‖ ≤ B → t ^ 2 ≤ B ^ 2 := by
    intro t B h
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (by rwa [Real.norm_eq_abs] at h) 2
  have h1 : ‖v.1‖ ≤ ‖v‖ := norm_fst_le v
  have h2 : ‖v.2‖ ≤ ‖v‖ := norm_snd_le v
  have h21 : ‖v.2.1‖ ≤ ‖v‖ := (norm_fst_le v.2).trans h2
  have h22 : ‖v.2.2‖ ≤ ‖v‖ := (norm_snd_le v.2).trans h2
  have h221 : ‖v.2.2.1‖ ≤ ‖v‖ := (norm_fst_le v.2.2).trans h22
  have h222 : ‖v.2.2.2‖ ≤ ‖v‖ := (norm_snd_le v.2.2).trans h22
  refine ⟨fun j => hsq _ _ ((norm_le_pi_norm v.1 j).trans h1),
    fun i => hsq _ _ ((norm_le_pi_norm v.2.1 i).trans h21),
    fun i => hsq _ _ ((norm_le_pi_norm v.2.2.1 i).trans h221),
    fun i k => hsq _ _ (((norm_le_pi_norm (v.2.2.2 i) k).trans (norm_le_pi_norm v.2.2.2 i)).trans h222)⟩

lemma nsq_le (v : CS n m) : nsq v.1 v.2.1 v.2.2.1 v.2.2.2 ≤ NC n m * ‖v‖ ^ 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := coord_sq_le v
  have s1 : sq1 v.1 ≤ (n + 1 : ℕ) * ‖v‖ ^ 2 := by
    unfold sq1
    calc _ ≤ ∑ _j : Fin (n + 1), ‖v‖ ^ 2 := Finset.sum_le_sum fun j _ => h1 j
      _ = _ := by simp
  have s2 : sq2 v.2.1 ≤ n * ‖v‖ ^ 2 := by
    unfold sq2
    calc _ ≤ ∑ _i : Fin n, ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ => h2 i
      _ = _ := by simp
  have s3 : sq2 v.2.2.1 ≤ n * ‖v‖ ^ 2 := by
    unfold sq2
    calc _ ≤ ∑ _i : Fin n, ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ => h3 i
      _ = _ := by simp
  have s4 : sqY v.2.2.2 ≤ (n * (m + 1 : ℕ)) * ‖v‖ ^ 2 := by
    unfold sqY
    calc _ ≤ ∑ _i : Fin n, ∑ _k : Fin (m + 1), ‖v‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => h4 i k
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  unfold nsq NC
  nlinarith

noncomputable def baseB (c : CS n m) : ℝ := (n + 1) * ‖c‖

lemma baseB_nonneg (c : CS n m) : 0 ≤ baseB c := by unfold baseB; positivity

lemma base_a (c : CS n m) : sq2 c.2.1 ≤ baseB c ^ 2 := by
  obtain ⟨-, h2, -, -⟩ := coord_sq_le c
  unfold sq2 baseB
  calc _ ≤ ∑ _i : Fin n, ‖c‖ ^ 2 := Finset.sum_le_sum fun i _ => h2 i
    _ = n * ‖c‖ ^ 2 := by simp
    _ ≤ _ := by
      have := norm_nonneg c
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith [sq_nonneg ‖c‖]

lemma base_b (c : CS n m) (i : Fin n) : |c.2.2.1 i| ≤ baseB c := by
  have h1 : ‖c.2.2.1 i‖ ≤ ‖c‖ :=
    (norm_le_pi_norm c.2.2.1 i).trans ((norm_fst_le c.2.2).trans ((norm_snd_le c.2).trans (norm_snd_le c)))
  rw [Real.norm_eq_abs] at h1
  unfold baseB
  have := norm_nonneg c
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

theorem Fc_model {θ τ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτ : 0 < τ) (B : ℝ) (hB : 0 ≤ B)
    (c w : CS n m) (ha : sq2 c.2.1 ≤ B ^ 2) (hb : ∀ i, |c.2.2.1 i| ≤ B) :
    |Fc θ τ w - Fc θ τ c - DFc θ τ c (w - c)| ≤
      cF B * nsq (w - c).1 (w - c).2.1 (w - c).2.2.1 (w - c).2.2.2 := by
  have h := robF_model hθ hθ1 hτ B hB c.1 w.1 c.2.1 w.2.1 c.2.2.1 w.2.2.1 c.2.2.2 w.2.2.2 ha hb
  have e1 : (fun j => w.1 j - c.1 j) = (w - c).1 := by funext j; simp
  have e2 : (fun i => w.2.1 i - c.2.1 i) = (w - c).2.1 := by funext j; simp
  have e3 : (fun i => w.2.2.1 i - c.2.2.1 i) = (w - c).2.2.1 := by funext j; simp
  have e4 : (fun i k => w.2.2.2 i k - c.2.2.2 i k) = (w - c).2.2.2 := by funext i k; simp
  rw [e1, e2, e3, e4] at h
  exact h

theorem hasFDerivAt_Fc {θ τ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτ : 0 < τ) (c : CS n m) :
    HasFDerivAt (Fc θ τ) (DFc θ τ c) c := by
  apply hasFDerivAt_of_model (C := cF (baseB c) * NC n m)
  intro w
  have h := Fc_model hθ hθ1 hτ (baseB c) (baseB_nonneg c) c w (base_a c) (base_b c)
  have h2 := nsq_le (w - c)
  have hc : 0 ≤ cF (baseB c) := by
    unfold cF cP; have := baseB_nonneg c; linarith
  calc _ ≤ _ := h
    _ ≤ cF (baseB c) * (NC n m * ‖w - c‖ ^ 2) := mul_le_mul_of_nonneg_left h2 hc
    _ = _ := by ring

noncomputable def prL (r : ℕ) : CS n m →ₗ[ℝ] CS n m where
  toFun v := (prU (m := m) r v.1, prA (m := m) r v.2.1, prB (m := m) r v.2.2.1, prY r v.2.2.2)
  map_add' v w := by
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · funext j; simp only [prU, Prod.fst_add, Pi.add_apply]; split_ifs <;> simp
    · funext j; simp only [prA, Prod.fst_add, Prod.snd_add, Pi.add_apply]; split_ifs <;> simp
    · funext j; simp only [prB, Prod.fst_add, Prod.snd_add, Pi.add_apply]; split_ifs <;> simp
    · funext j k; simp only [prY, Prod.snd_add, Pi.add_apply]; split_ifs <;> simp
  map_smul' c v := by
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · funext j; simp only [prU, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      split_ifs <;> simp
    · funext j; simp only [prA, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply]
      split_ifs <;> simp
    · funext j; simp only [prB, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply]
      split_ifs <;> simp
    · funext j k; simp only [prY, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      split_ifs <;> simp

noncomputable def prC (r : ℕ) : CS n m →L[ℝ] CS n m := LinearMap.toContinuousLinearMap (prL r)

lemma prC_apply (r : ℕ) (v : CS n m) :
    prC r v = (prU (m := m) r v.1, prA (m := m) r v.2.1, prB (m := m) r v.2.2.1, prY r v.2.2.2) := rfl

structure SmallFrom (θ : ℝ) (s : ℕ) (c : CS n m) : Prop where
  hu : ∀ j : Fin (n + 1), s ≤ pU m j → |c.1 j| ≤ θ
  ha : ∀ i : Fin n, s ≤ pA m i → |c.2.1 i| ≤ θ
  hb : ∀ i : Fin n, s ≤ pB m i → |c.2.2.1 i| ≤ θ
  hy : ∀ (i : Fin n) (k : Fin (m + 1)), s ≤ pY m i k → |c.2.2.2 i k| ≤ θ

lemma dead_of_near {θ : ℝ} {s : ℕ} {c w : CS n m} (hc : SmallFrom (θ / 2) s c)
    (hw : ‖w - c‖ < θ / 2) : Dead (m := m) θ s w.1 w.2.1 w.2.2.1 w.2.2.2 := by
  obtain ⟨h1, h2, h3, h4⟩ := coord_sq_le (w - c)
  have hb : ∀ t : ℝ, t ^ 2 ≤ ‖w - c‖ ^ 2 → |t| < θ / 2 := by
    intro t ht
    have : |t| ≤ ‖w - c‖ := by
      rw [← Real.sqrt_sq (abs_nonneg t), ← Real.sqrt_sq (norm_nonneg (w - c)), sq_abs]
      exact Real.sqrt_le_sqrt ht
    linarith
  refine ⟨fun j hj => ?_, fun i hi => ?_, fun i hi => ?_, fun i k hk => ?_⟩
  · have := hb _ (h1 j); have := hc.hu j hj
    simp only [Prod.fst_sub, Pi.sub_apply] at *
    calc |w.1 j| = |(w.1 j - c.1 j) + c.1 j| := by rw [sub_add_cancel]
      _ ≤ |w.1 j - c.1 j| + |c.1 j| := abs_add_le _ _
      _ < θ := by linarith
  · have := hb _ (h2 i); have := hc.ha i hi
    simp only [Prod.fst_sub, Prod.snd_sub, Pi.sub_apply] at *
    calc |w.2.1 i| = |(w.2.1 i - c.2.1 i) + c.2.1 i| := by rw [sub_add_cancel]
      _ ≤ |w.2.1 i - c.2.1 i| + |c.2.1 i| := abs_add_le _ _
      _ < θ := by linarith
  · have := hb _ (h3 i); have := hc.hb i hi
    simp only [Prod.fst_sub, Prod.snd_sub, Pi.sub_apply] at *
    calc |w.2.2.1 i| = |(w.2.2.1 i - c.2.2.1 i) + c.2.2.1 i| := by rw [sub_add_cancel]
      _ ≤ |w.2.2.1 i - c.2.2.1 i| + |c.2.2.1 i| := abs_add_le _ _
      _ < θ := by linarith
  · have := hb _ (h4 i k); have := hc.hy i k hk
    simp only [Prod.snd_sub, Pi.sub_apply] at *
    calc |w.2.2.2 i k| = |(w.2.2.2 i k - c.2.2.2 i k) + c.2.2.2 i k| := by rw [sub_add_cancel]
      _ ≤ |w.2.2.2 i k - c.2.2.2 i k| + |c.2.2.2 i k| := abs_add_le _ _
      _ < θ := by linarith

theorem DFc_local {θ τ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτ : 0 < τ) {s : ℕ} (c : CS n m)
    (hc : SmallFrom (θ / 2) s c) :
    DFc θ τ c = (DFc θ τ (prC (s + 1) c)).comp (prC (s + 1)) := by
  have h1 := hasFDerivAt_Fc hθ hθ1 hτ c
  have h2 : HasFDerivAt (fun w => Fc θ τ (prC (s + 1) w))
      ((DFc θ τ (prC (s + 1) c)).comp (prC (s + 1))) c :=
    (hasFDerivAt_Fc hθ hθ1 hτ (prC (s + 1) c)).comp c (prC (s + 1)).hasFDerivAt
  have heq : (fun w => Fc θ τ (prC (s + 1) w)) =ᶠ[𝓝 c] Fc θ τ := by
    filter_upwards [Metric.ball_mem_nhds c (by linarith : (0 : ℝ) < θ / 2)] with w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hd := dead_of_near hc hw
    simp only [Fc, prC_apply]
    exact (robF_pr (τ := τ) hθ hd).symm
  exact h1.unique (h2.congr_of_eventuallyEq heq.symm)

end LongTails.Proofs.NcConcaveChainGrad
