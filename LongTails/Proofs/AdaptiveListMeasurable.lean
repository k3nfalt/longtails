import LongTails.Proofs.ScalarSearchMeasurable

open MeasureTheory

namespace OracleTemplate.AdaptiveList

scoped instance instMeasurableSpaceList {E : Type*} [MeasurableSpace E] : MeasurableSpace (List E) :=
  MeasurableSpace.comap List.equivSigmaTuple inferInstance

variable {E Z : Type*} [MeasurableSpace E] [MeasurableSpace Z]

set_option backward.isDefEq.respectTransparency false in
def listEquiv : List E ≃ᵐ Σ n, Fin n → E where
  toEquiv := List.equivSigmaTuple
  measurable_toFun := comap_measurable _
  measurable_invFun := by
    change Measurable[(inferInstance : MeasurableSpace (Σ n, Fin n → E)),
      MeasurableSpace.comap List.equivSigmaTuple (inferInstance : MeasurableSpace (Σ n, Fin n → E))]
      List.equivSigmaTuple.symm
    apply measurable_comap_iff.mpr
    convert (measurable_id : Measurable (id : (Σ n, Fin n → E) → _)) using 1
    exact List.equivSigmaTuple.self_comp_symm

lemma measurable_cases (f : List E → Z)
    (h : ∀ n, Measurable (fun x : Fin n → E => f (List.ofFn x))) : Measurable f := by
  apply listEquiv.symm.measurable_comp_iff.mp
  exact ScalarNoisySearch.measurable_sigma_source _ h

lemma measurable_ofFn (n : ℕ) : Measurable (List.ofFn : (Fin n → E) → List E) :=
  listEquiv.symm.measurable.comp (ScalarNoisySearch.measurable_sigma_mk n)

lemma measurable_length : Measurable (List.length : List E → ℕ) := by
  apply measurable_cases
  intro n
  simpa only [List.length_ofFn] using
    (measurable_const : Measurable (fun _ : Fin n → E => n))

lemma measurable_getD (i : ℕ) (fallback : E) :
    Measurable (fun l : List E => l[i]?.getD fallback) := by
  apply measurable_cases
  intro n
  by_cases hi : i < n
  · have he : (fun x : Fin n → E => (List.ofFn x)[i]?.getD fallback) =
        fun x => x ⟨i, hi⟩ := by
      funext x
      rw [List.getElem?_eq_getElem (by simpa using hi)]
      simp
    rw [he]
    exact measurable_pi_apply _
  · have he : (fun x : Fin n → E => (List.ofFn x)[i]?.getD fallback) = fun _ => fallback := by
      funext x
      rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi)]
      rfl
    rw [he]
    exact measurable_const

lemma measurable_cons (fallback : E) : Measurable (fun w : E × List E => w.1 :: w.2) := by
  let family : ℕ → E × List E → List E := fun n w =>
    List.ofFn (Fin.cons w.1 (fun i : Fin n => w.2[i.val]?.getD fallback))
  apply ScalarNoisySearch.measurable_nat_selection _ (fun w : E × List E => w.2.length)
    (measurable_length.comp measurable_snd) family
  · intro n
    apply (measurable_ofFn (n + 1)).comp
    apply measurable_pi_iff.mpr
    intro i
    cases i using Fin.cases with
    | zero => exact measurable_fst
    | succ i => exact (measurable_getD i.val fallback).comp measurable_snd
  · intro w
    dsimp only [family]
    rw [List.ofFn_succ]
    congr 1
    have he : (fun i : Fin w.2.length => w.2[i.val]?.getD fallback) = w.2.get := by
      funext i
      rw [List.getElem?_eq_getElem i.isLt]
      rfl
    rw [he]
    simp only [Fin.cons_succ, List.ofFn_get]

lemma measurable_map {F : Type*} [MeasurableSpace F] (f : E → F) (hf : Measurable f) :
    Measurable (List.map f : List E → List F) := by
  apply measurable_cases
  intro n
  simp only [List.map_ofFn]
  exact (measurable_ofFn n).comp (measurable_pi_iff.mpr (fun i => hf.comp (measurable_pi_apply i)))

lemma measurable_take (n : ℕ) : Measurable (List.take n : List E → List E) := by
  apply measurable_cases
  intro m
  have he : (fun x : Fin m → E => (List.ofFn x).take n) =
      fun x => List.ofFn (fun i : Fin (min n m) => x ⟨i.val, lt_of_lt_of_le i.isLt (min_le_right _ _)⟩) := by
    funext x
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  rw [he]
  exact (measurable_ofFn _).comp (measurable_pi_iff.mpr (fun _ => measurable_pi_apply _))

end OracleTemplate.AdaptiveList
