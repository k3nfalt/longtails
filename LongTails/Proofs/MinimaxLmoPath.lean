import LongTails.Setups.MinimaxLmo
import LongTails.Proofs.LmoOutput

open MeasureTheory

namespace OracleTemplate.MinimaxLmo

open LongTails.Setups.UscgConstant (Space)
open LongTails.Setups.MinimaxLmo (GdaState lmoGda clip)

variable {d₁ d₂ : ℕ} {Ω : Type}

noncomputable def gpath (lmo : Space d₁ → Space d₁) (γ α β δ : ℕ → ℝ) (x₁ : Space d₁) (y₁ : Space d₂)
    (ox : Space d₁ → Space d₂ → Ω → Space d₁) (oy : Space d₁ → Space d₂ → Ω → Space d₂) (ξ : ℕ → Ω) :
    ℕ → Space d₁ × Space d₂ × Space d₁
  | 0 => (x₁, y₁, 0)
  | k + 1 =>
      ((gpath lmo γ α β δ x₁ y₁ ox oy ξ k).1 + γ (k + 1) • lmo (α (k + 1) •
          ox (gpath lmo γ α β δ x₁ y₁ ox oy ξ k).1 (gpath lmo γ α β δ x₁ y₁ ox oy ξ k).2.1 (ξ k) +
          (1 - α (k + 1)) • (gpath lmo γ α β δ x₁ y₁ ox oy ξ k).2.2),
        (gpath lmo γ α β δ x₁ y₁ ox oy ξ k).2.1 + β (k + 1) • clip (δ (k + 1))
          (oy (gpath lmo γ α β δ x₁ y₁ ox oy ξ k).1 (gpath lmo γ α β δ x₁ y₁ ox oy ξ k).2.1 (ξ k)),
        α (k + 1) • ox (gpath lmo γ α β δ x₁ y₁ ox oy ξ k).1 (gpath lmo γ α β δ x₁ y₁ ox oy ξ k).2.1 (ξ k) +
          (1 - α (k + 1)) • (gpath lmo γ α β δ x₁ y₁ ox oy ξ k).2.2)

variable (lmo : Space d₁ → Space d₁) (γ α β δ : ℕ → ℝ) (x₁ : Space d₁) (y₁ : Space d₂)
  (ox : Space d₁ → Space d₂ → Ω → Space d₁) (oy : Space d₁ → Space d₂ → Ω → Space d₂)

lemma gpath_congr {ξ ξ' : ℕ → Ω} :
    ∀ k, (∀ i, i < k → ξ i = ξ' i) →
      gpath lmo γ α β δ x₁ y₁ ox oy ξ k = gpath lmo γ α β δ x₁ y₁ ox oy ξ' k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro h
      simp only [gpath]
      rw [ih (fun i hi => h i (by omega)), h k (by omega)]

lemma clip_measurable {d : ℕ} (c : ℝ) : Measurable (clip (d := d) c) := by
  unfold clip
  refine Measurable.ite (measurableSet_le measurable_norm measurable_const) measurable_id ?_
  exact (measurable_const.div measurable_norm).smul measurable_id

lemma measurable_gpath [MeasurableSpace Ω] (hlmo : Measurable lmo)
    (hox : Measurable (fun z : (Space d₁ × Space d₂) × Ω => ox z.1.1 z.1.2 z.2))
    (hoy : Measurable (fun z : (Space d₁ × Space d₂) × Ω => oy z.1.1 z.1.2 z.2)) :
    ∀ k, Measurable (fun ξ : ℕ → Ω => gpath lmo γ α β δ x₁ y₁ ox oy ξ k) := by
  intro k
  induction k with
  | zero => exact measurable_const
  | succ k hk =>
      have hgx : Measurable (fun ξ : ℕ → Ω =>
          ox (gpath lmo γ α β δ x₁ y₁ ox oy ξ k).1 (gpath lmo γ α β δ x₁ y₁ ox oy ξ k).2.1 (ξ k)) :=
        hox.comp ((hk.fst.prodMk hk.snd.fst).prodMk (measurable_pi_apply k))
      have hgy : Measurable (fun ξ : ℕ → Ω =>
          oy (gpath lmo γ α β δ x₁ y₁ ox oy ξ k).1 (gpath lmo γ α β δ x₁ y₁ ox oy ξ k).2.1 (ξ k)) :=
        hoy.comp ((hk.fst.prodMk hk.snd.fst).prodMk (measurable_pi_apply k))
      have hm : Measurable (fun ξ : ℕ → Ω =>
          α (k + 1) • ox (gpath lmo γ α β δ x₁ y₁ ox oy ξ k).1 (gpath lmo γ α β δ x₁ y₁ ox oy ξ k).2.1 (ξ k) +
            (1 - α (k + 1)) • (gpath lmo γ α β δ x₁ y₁ ox oy ξ k).2.2) :=
        by
          have ha : Measurable (fun ξ : ℕ → Ω => α (k + 1) •
              ox (gpath lmo γ α β δ x₁ y₁ ox oy ξ k).1 (gpath lmo γ α β δ x₁ y₁ ox oy ξ k).2.1 (ξ k)) :=
            hgx.const_smul (α (k + 1))
          have hb : Measurable (fun ξ : ℕ → Ω => (1 - α (k + 1)) • (gpath lmo γ α β δ x₁ y₁ ox oy ξ k).2.2) :=
            hk.snd.snd.const_smul (1 - α (k + 1))
          exact ha.add hb
      simp only [gpath]
      have hl : Measurable (fun ξ : ℕ → Ω => γ (k + 1) • lmo (α (k + 1) •
          ox (gpath lmo γ α β δ x₁ y₁ ox oy ξ k).1 (gpath lmo γ α β δ x₁ y₁ ox oy ξ k).2.1 (ξ k) +
            (1 - α (k + 1)) • (gpath lmo γ α β δ x₁ y₁ ox oy ξ k).2.2)) :=
        (hlmo.comp hm).const_smul (γ (k + 1))
      have hc : Measurable (fun ξ : ℕ → Ω => β (k + 1) • clip (δ (k + 1))
          (oy (gpath lmo γ α β δ x₁ y₁ ox oy ξ k).1 (gpath lmo γ α β δ x₁ y₁ ox oy ξ k).2.1 (ξ k))) :=
        ((clip_measurable (δ (k + 1))).comp hgy).const_smul (β (k + 1))
      exact (hk.fst.add hl).prodMk ((hk.snd.fst.add hc).prodMk hm)

lemma gda_run (T : ℕ) (w : PMF (Fin (T + 1))) (ξ : ℕ → Ω) (j : ℕ) :
    ∀ k, k ≤ j →
      (fun sc : GdaState d₁ d₂ × ℕ =>
          ((lmoGda lmo γ α β δ T w x₁ y₁).update sc.1
            ((fun q (ω : Ω) => (ox q.1 q.2 ω, oy q.1 q.2 ω))
              ((lmoGda lmo γ α β δ T w x₁ y₁).query sc.1).2 (ξ sc.2)),
            sc.2 + 1))^[k] (⟨j, 0, x₁, y₁, 0⟩, 0) =
        (⟨j, k, (gpath lmo γ α β δ x₁ y₁ ox oy ξ k).1, (gpath lmo γ α β δ x₁ y₁ ox oy ξ k).2.1,
          (gpath lmo γ α β δ x₁ y₁ ox oy ξ k).2.2⟩, k) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro h
      rw [Function.iterate_succ_apply', ih (by omega)]
      have hk : k < j := by omega
      simp only [lmoGda, hk, ite_true, gpath]

lemma gda_frozen (T : ℕ) (w : PMF (Fin (T + 1))) (ξ : ℕ → Ω) (j : ℕ) :
    ∀ m, ((fun sc : GdaState d₁ d₂ × ℕ =>
          ((lmoGda lmo γ α β δ T w x₁ y₁).update sc.1
            ((fun q (ω : Ω) => (ox q.1 q.2 ω, oy q.1 q.2 ω))
              ((lmoGda lmo γ α β δ T w x₁ y₁).query sc.1).2 (ξ sc.2)),
            sc.2 + 1))^[j + m] (⟨j, 0, x₁, y₁, 0⟩, 0)).1 =
        ⟨j, j, (gpath lmo γ α β δ x₁ y₁ ox oy ξ j).1, (gpath lmo γ α β δ x₁ y₁ ox oy ξ j).2.1,
          (gpath lmo γ α β δ x₁ y₁ ox oy ξ j).2.2⟩ := by
  intro m
  induction m with
  | zero => exact congrArg Prod.fst (gda_run lmo γ α β δ x₁ y₁ ox oy T w ξ j j le_rfl)
  | succ m ih =>
      rw [show j + (m + 1) = (j + m) + 1 by omega, Function.iterate_succ_apply']
      set sc := (fun sc : GdaState d₁ d₂ × ℕ =>
          ((lmoGda lmo γ α β δ T w x₁ y₁).update sc.1
            ((fun q (ω : Ω) => (ox q.1 q.2 ω, oy q.1 q.2 ω))
              ((lmoGda lmo γ α β δ T w x₁ y₁).query sc.1).2 (ξ sc.2)),
            sc.2 + 1))^[j + m] (⟨j, 0, x₁, y₁, 0⟩, 0)
      obtain ⟨s, c⟩ := sc
      simp only at ih
      subst ih
      simp [lmoGda]

lemma execute_lmoGda [MeasurableSpace Ω] (T : ℕ) (w : PMF (Fin (T + 1))) (P : ProbabilityMeasure (ℕ → Ω)) (K : ℕ) (hK : T ≤ K)
    (j : (lmoGda lmo γ α β δ T w x₁ y₁).Seed) (ξ : ℕ → Ω) :
    execute ({ Seed := fun _ => Ω, law := P, answer := fun _ (_, z) ω => (ox z.1 z.2 ω, oy z.1 z.2 ω) } :
        Oracle (Space d₁ × Space d₂) (Space d₁ × Space d₂))
      (lmoGda lmo γ α β δ T w x₁ y₁) (fun _ => K) j ξ =
      (gpath lmo γ α β δ x₁ y₁ ox oy ξ (j : Fin (T + 1)).val).1 := by
  refine (execute_indexed_of_answer
    ({ Seed := fun _ => Ω, law := P, answer := fun _ (_, z) ω => (ox z.1 z.2 ω, oy z.1 z.2 ω) } :
      Oracle (Space d₁ × Space d₂) (Space d₁ × Space d₂))
    (lmoGda lmo γ α β δ T w x₁ y₁) K j ξ
    (fun k q => (ox q.2.1 q.2.2 (ξ k), oy q.2.1 q.2.2 (ξ k))) (fun _ _ => rfl)).trans ?_
  change Fin (T + 1) at j
  obtain ⟨m, hm⟩ : ∃ m, K = j.val + m := ⟨K - j.val, by have := j.isLt; omega⟩
  subst hm
  have h := gda_frozen lmo γ α β δ x₁ y₁ ox oy T w ξ j.val m
  change (((fun sc : GdaState d₁ d₂ × ℕ =>
          ((lmoGda lmo γ α β δ T w x₁ y₁).update sc.1
            ((fun q (ω : Ω) => (ox q.1 q.2 ω, oy q.1 q.2 ω))
              ((lmoGda lmo γ α β δ T w x₁ y₁).query sc.1).2 (ξ sc.2)),
            sc.2 + 1))^[j.val + m] (⟨j.val, 0, x₁, y₁, 0⟩, 0)).1).x = _
  rw [h]

end OracleTemplate.MinimaxLmo
