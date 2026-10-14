import LongTails.Proofs.HeavyTailedMarkovMixing

open MeasureTheory ProbabilityTheory
open Set Function Preorder

namespace OracleTemplate.HeavyTailedMarkovGradient

open LongTails.Setups.HeavyTailedMarkovSmoothAndConvex

variable {Ω : Type} [MeasurableSpace Ω]

noncomputable def historyKernel (κ : Kernel Ω Ω) (n : ℕ) : Kernel (Finset.Iic n → Ω) Ω :=
  κ.comap (fun z => z ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (by fun_prop)

instance historyKernel_markov (κ : Kernel Ω Ω) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (historyKernel κ n) := inferInstanceAs (IsMarkovKernel (κ.comap _ _))

lemma comp_comap_eq_comp_map {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (κ : Kernel Ω Ω) {f : X → Ω} (hf : Measurable f) :
    (κ.comap f hf) ∘ₘ μ = κ ∘ₘ μ.map f := by
  rw [← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map]

lemma pathLaw_map_zero (κ : Kernel Ω Ω) [IsMarkovKernel κ] (π : ProbabilityMeasure Ω) :
    (pathLaw κ π : Measure (ℕ → Ω)).map (fun ξ => ξ 0) = (π : Measure Ω) := by
  change (Kernel.trajMeasure (X := fun _ : ℕ => Ω) (π : Measure Ω) (historyKernel κ)).map (fun ξ => ξ 0) = _
  have hprefix : (Kernel.trajMeasure (X := fun _ : ℕ => Ω) (π : Measure Ω) (historyKernel κ)).map (frestrictLe 0) =
      (π : Measure Ω).map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Ω)).symm := by
    rw [Kernel.trajMeasure, Measure.map_comp _ _ (by fun_prop),
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
  have he : (fun ξ : ℕ → Ω => ξ 0) =
      (fun ξ : Finset.Iic 0 → Ω => ξ ⟨0, by simp⟩) ∘ frestrictLe 0 := rfl
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop), hprefix,
    Measure.map_map (by fun_prop) (by fun_prop)]
  convert Measure.map_id (μ := (π : Measure Ω)) using 1
  congr 1

lemma pathLaw_map_succ (κ : Kernel Ω Ω) [IsMarkovKernel κ] (π : ProbabilityMeasure Ω) (k : ℕ) :
    (pathLaw κ π : Measure (ℕ → Ω)).map (fun ξ => ξ (k + 1)) =
      κ ∘ₘ (pathLaw κ π : Measure (ℕ → Ω)).map (fun ξ => ξ k) := by
  let P : Measure (ℕ → Ω) := pathLaw κ π
  have hj := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ : ℕ => Ω) (μ₀ := (π : Measure Ω)) (κ := historyKernel κ) (a := k)
  have hh := congrArg (fun μ : Measure ((Finset.Iic k → Ω) × Ω) => μ.map Prod.snd) hj
  change (P.map (frestrictLe k) ⊗ₘ historyKernel κ k).map Prod.snd =
    (P.map (fun ξ => (frestrictLe k ξ, ξ (k + 1)))).map Prod.snd at hh
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at hh
  have he : (P.map (frestrictLe k) ⊗ₘ historyKernel κ k).map Prod.snd =
      κ ∘ₘ P.map (fun ξ => ξ k) := by
    rw [show (P.map (frestrictLe k) ⊗ₘ historyKernel κ k).map Prod.snd =
        (P.map (frestrictLe k) ⊗ₘ historyKernel κ k).snd from rfl,
      Measure.snd_compProd, historyKernel, comp_comap_eq_comp_map,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [he] at hh
  exact hh.symm

lemma pathLaw_stationary_marginal (κ : Kernel Ω Ω) [IsMarkovKernel κ] (π : ProbabilityMeasure Ω)
    (hπ : κ ∘ₘ (π : Measure Ω) = (π : Measure Ω)) (k : ℕ) :
    (pathLaw κ π : Measure (ℕ → Ω)).map (fun ξ => ξ k) = (π : Measure Ω) := by
  induction k with
  | zero => exact pathLaw_map_zero κ π
  | succ k ih => rw [pathLaw_map_succ, ih, hπ]

lemma traj_map_time (κ : Kernel Ω Ω) [IsMarkovKernel κ] (k t : ℕ) :
    (Kernel.traj (X := fun _ : ℕ => Ω) (historyKernel κ) k).map (fun ξ => ξ (k + t)) =
      (κ ^ t).comap (fun ξ : Finset.Iic k → Ω => ξ ⟨k, Finset.mem_Iic.mpr le_rfl⟩) (by fun_prop) := by
  have hprefix (j : ℕ) :
      (Kernel.partialTraj (X := fun _ : ℕ => Ω) (historyKernel κ) k j).map
        (fun ξ : Finset.Iic j → Ω => ξ ⟨j, Finset.mem_Iic.mpr le_rfl⟩) =
      (Kernel.traj (X := fun _ : ℕ => Ω) (historyKernel κ) k).map (fun ξ => ξ j) := by
    rw [← Kernel.traj_map_frestrictLe, ← Kernel.map_comp_right _ (by fun_prop) (by fun_prop)]
    rfl
  induction t with
  | zero =>
    simp only [Nat.add_zero, pow_zero]
    rw [← hprefix k, Kernel.partialTraj_self]
    change Kernel.id.map _ = Kernel.id.comap _ _
    rw [Kernel.id_map, Kernel.id_comap]
  | succ t ih =>
    rw [show k + (t + 1) = (k + t) + 1 by omega]
    have htraj := Kernel.traj_comp_partialTraj (X := fun _ : ℕ => Ω) (κ := historyKernel κ) (show k ≤ k + t by omega)
    calc
      _ = ((Kernel.traj (X := fun _ : ℕ => Ω) (historyKernel κ) (k + t)) ∘ₖ
          Kernel.partialTraj (X := fun _ : ℕ => Ω) (historyKernel κ) k (k + t)).map (fun ξ => ξ ((k + t) + 1)) := by rw [htraj]
      _ = historyKernel κ (k + t) ∘ₖ Kernel.partialTraj (X := fun _ : ℕ => Ω) (historyKernel κ) k (k + t) := by
        rw [Kernel.map_comp, Kernel.map_traj_succ_self]
      _ = κ ∘ₖ (Kernel.traj (X := fun _ : ℕ => Ω) (historyKernel κ) k).map (fun ξ => ξ (k + t)) := by
        rw [historyKernel, ← Kernel.comp_map, hprefix]
      _ = κ ∘ₖ (κ ^ t).comap (fun ξ : Finset.Iic k → Ω => ξ ⟨k, Finset.mem_Iic.mpr le_rfl⟩) (by fun_prop) := by rw [ih]
      _ = _ := by
        rw [← Kernel.comp_deterministic_eq_comap, ← Kernel.comp_assoc]
        change ((κ * κ ^ t) ∘ₖ _) = _
        rw [← pow_succ', Kernel.comp_deterministic_eq_comap]

lemma pathLaw_prefix_traj (κ : Kernel Ω Ω) [IsMarkovKernel κ]
    (π : ProbabilityMeasure Ω) (k : ℕ) :
    (pathLaw κ π : Measure (ℕ → Ω)).map (frestrictLe k) ⊗ₘ
      Kernel.traj (X := fun _ : ℕ => Ω) (historyKernel κ) k =
    (pathLaw κ π : Measure (ℕ → Ω)).map (fun ξ => (frestrictLe k ξ, ξ)) := by
  change (Kernel.trajMeasure (X := fun _ : ℕ => Ω) (π : Measure Ω) (historyKernel κ)).map _ ⊗ₘ _ =
    (Kernel.trajMeasure (X := fun _ : ℕ => Ω) (π : Measure Ω) (historyKernel κ)).map _
  rw [Measure.compProd_eq_comp_prod, Kernel.trajMeasure,
    Measure.map_comp _ _ (by fun_prop), Kernel.traj_map_frestrictLe,
    Measure.comp_assoc, Measure.map_comp _ _ (by fun_prop)]
  congr with x₀ : 1
  rw [Kernel.comp_apply, ← Measure.compProd_eq_comp_prod,
    Kernel.map_apply _ (by fun_prop), Kernel.partialTraj_compProd_traj (Nat.zero_le k)]

lemma pathLaw_prefix_future (κ : Kernel Ω Ω) [IsMarkovKernel κ]
    (π : ProbabilityMeasure Ω) (k t : ℕ) :
    (pathLaw κ π : Measure (ℕ → Ω)).map (frestrictLe k) ⊗ₘ
      (κ ^ t).comap (fun ξ : Finset.Iic k → Ω => ξ ⟨k, Finset.mem_Iic.mpr le_rfl⟩) (by fun_prop) =
    (pathLaw κ π : Measure (ℕ → Ω)).map (fun ξ => (frestrictLe k ξ, ξ (k + t))) := by
  rw [← traj_map_time, Measure.compProd_map (by fun_prop), pathLaw_prefix_traj,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma pathLaw_integral_future (κ : Kernel Ω Ω) [IsMarkovKernel κ]
    (π : ProbabilityMeasure Ω) (k t : ℕ)
    {W : (Finset.Iic k → Ω) → Ω → ℝ} (hW : Measurable (Function.uncurry W))
    {B : ℝ} (hbound : ∀ h y, |W h y| ≤ B) :
    (∫ ξ, W (frestrictLe k ξ) (ξ (k + t)) ∂(pathLaw κ π : Measure (ℕ → Ω))) =
    ∫ h, ∫ y, W h y ∂(κ ^ t) (h ⟨k, Finset.mem_Iic.mpr le_rfl⟩)
      ∂((pathLaw κ π : Measure (ℕ → Ω)).map (frestrictLe k)) := by
  let ρ := (pathLaw κ π : Measure (ℕ → Ω)).map (frestrictLe k)
  let K : Kernel (Finset.Iic k → Ω) Ω :=
    (κ ^ t).comap (fun h => h ⟨k, Finset.mem_Iic.mpr le_rfl⟩) (by fun_prop)
  have : IsProbabilityMeasure ρ := inferInstance
  have hi : Integrable (Function.uncurry W) (ρ ⊗ₘ K) :=
    Integrable.of_bound hW.aestronglyMeasurable B
      (Filter.Eventually.of_forall (fun z => hbound z.1 z.2))
  have hj := pathLaw_prefix_future κ π k t
  change ρ ⊗ₘ K = _ at hj
  have hi' := hi
  rw [hj] at hi'
  have he := Measure.integral_compProd hi
  rw [hj, integral_map (by fun_prop) hi'.aestronglyMeasurable] at he
  simpa only [Function.uncurry_apply_pair, K, Kernel.comap_apply, ρ] using he

lemma pathLaw_averaged_mixing_bound (κ : Kernel Ω Ω) [IsMarkovKernel κ]
    (π : ProbabilityMeasure Ω) (hπ : κ ∘ₘ (π : Measure Ω) = (π : Measure Ω))
    (k t : ℕ) (hd : Integrable (mixingDistance κ π t) (π : Measure Ω))
    {W : (Finset.Iic k → Ω) → Ω → ℝ} (hW : Measurable (Function.uncurry W))
    {B δ : ℝ} (hB : 0 ≤ B) (hbound : ∀ h y, |W h y| ≤ B)
    (hmix : (∫ y, mixingDistance κ π t y ∂(π : Measure Ω)) ≤ δ) :
    |(∫ ξ, W (frestrictLe k ξ) (ξ (k + t)) ∂(pathLaw κ π : Measure (ℕ → Ω))) -
      ∫ h, ∫ y, W h y ∂(π : Measure Ω)
        ∂((pathLaw κ π : Measure (ℕ → Ω)).map (frestrictLe k))| ≤ 2 * B * δ := by
  rw [pathLaw_integral_future κ π k t hW hbound]
  have : IsProbabilityMeasure ((pathLaw κ π : Measure (ℕ → Ω)).map (frestrictLe k)) :=
    inferInstance
  apply averaged_mixing_bound κ π (by fun_prop) _ t hd hW hB hbound hmix
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  exact pathLaw_stationary_marginal κ π hπ k

end OracleTemplate.HeavyTailedMarkovGradient
