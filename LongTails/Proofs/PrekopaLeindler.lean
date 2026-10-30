/-
Adapted from https://github.com/hojonathanho/isoperimetric at 29768f8beeaf17295cdf3853d37da35d7e2b0a5f.
Modified for the pinned LongTails Lean/mathlib version and namespaced.


                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace LongTails.Proofs.PrekopaLeindler

lemma biSup_add_biSup
    {ι κ : Sort*}
    {p : ι → Prop} {q : κ → Prop} (hp : ∃ i, p i) (hq : ∃ j, q j)
    {f : ι → ENNReal} {g : κ → ENNReal} :
    (⨆ i, ⨆ _ : p i, f i) + (⨆ j, ⨆ _ : q j, g j) =
    (⨆ i, ⨆ j, ⨆ _ : p i, ⨆ _ : q j, f i + g j) := by
  apply le_antisymm
  · calc
      (⨆ x, ⨆ _ : p x, f x) + (⨆ y, ⨆ _ : q y, g y)
          = ⨆ x, ⨆ _ : p x, (f x + (⨆ y, ⨆ _ : q y, g y)) := by apply ENNReal.biSup_add' hp
      _ ≤ (⨆ x, ⨆ y, ⨆ _ : p x, ⨆ _ : q y, f x + g y) := by
        apply iSup₂_le
        intro x hx
        calc
          f x + (⨆ y, ⨆ _ : q y, g y) = ⨆ y, ⨆ _ : q y, (f x + g y) := by
            apply ENNReal.add_biSup' hq
          _ ≤ ⨆ x, ⨆ _ : p x, (⨆ y, ⨆ _ : q y, (f x + g y)) := by
            apply le_iSup₂ x hx
          _ = ⨆ x, ⨆ y, ⨆ _ : p x, ⨆ _ : q y, (f x + g y) := by
            apply iSup_congr; intro; exact iSup_comm
  simp only [iSup_le_iff]
  intro i j hi hj
  calc
    f i + g j ≤ (⨆ i, ⨆ (_ : p i), f i) + g j := by gcongr; apply le_iSup₂ i hi
    _ ≤ (⨆ i, ⨆ (_ : p i), f i) + ⨆ j, ⨆ (_ : q j), g j := by gcongr; apply le_iSup₂ j hj

lemma iSup_nonzero_of_nonzero {f : ℝ → ENNReal} (hf_nonzero : f ≠ 0) : iSup f ≠ 0 := by
  intro h
  apply hf_nonzero
  ext x
  simpa using le_iSup f x |>.trans_eq h

lemma iSup_min_nat (a : ENNReal) : ⨆ (n : ℕ), min a n = a := by
  apply iSup_eq_of_forall_le_of_forall_lt_exists_gt (by simp)
  intro w hw
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (hw.trans_le le_top).ne
  exact ⟨n, by simp_all⟩

lemma iSup_min_nat_ne_top {ι : Sort*} (n : ℕ) (f : ι → ENNReal) :
    iSup (fun x ↦ min (f x) n) ≠ ⊤ := by
  apply ne_of_lt
  rw [iSup_lt_iff]
  use n
  exact ⟨ENNReal.natCast_lt_top n, fun x ↦ min_le_right (f x) ↑n⟩

lemma iSup_rpow_of_pos {ι : Sort*} {r : ℝ} (hr : r > 0) (f : ι → ENNReal) :
    (⨆ (i : ι), f i) ^ r = ⨆ (i : ι), f i ^ r :=
  (ENNReal.orderIsoRpow r hr).map_iSup f

open MeasureTheory Set
open scoped Pointwise

lemma brunn_minkowski_1d_compact
    {A B C : Set ℝ}
    (h : A + B ⊆ C)
    (hA_nonempty : A.Nonempty) (hA_compact : IsCompact A)
    (hB_nonempty : B.Nonempty) (hB_compact : IsCompact B)
    : volume A + volume B ≤ volume C := by

  let A' := A + {-sSup A}
  let B' := B + {-sInf B}
  have h_inter_zero : A' ∩ B' = {0} := by
    ext x
    simp only [add_singleton, image_add_right, neg_neg, mem_inter_iff, mem_preimage,
      mem_singleton_iff, A', B']
    constructor
    · intro ⟨ha, hb⟩
      exact le_antisymm
        (nonpos_of_add_le_left (le_csSup hA_compact.bddAbove ha))
        (nonneg_of_le_add_left (csInf_le hB_compact.bddBelow hb))
    · intro hx
      simp only [hx, zero_add]
      exact ⟨hA_compact.sSup_mem hA_nonempty, hB_compact.sInf_mem hB_nonempty⟩
  calc
    volume C ≥ volume (A + B) := measure_mono h

    _ = volume (A + B + {-sSup A} + {-sInf B}) := by simp
    _ = volume (A' + B') := by
      congr 1; nth_rw 2 [add_assoc]; nth_rw 3 [add_comm]; rw [← add_assoc]; rw [add_assoc]

    _ ≥ volume (A' ∪ B') := by
      apply measure_mono
      rw [union_subset_iff]
      have h_zero_in_inter : 0 ∈ A' ∩ B' := by simp [h_inter_zero]
      exact ⟨subset_add_left A' h_zero_in_inter.2, subset_add_right B' h_zero_in_inter.1⟩

    _ = volume (A' ∪ B') + volume (A' ∩ B') := by simp [h_inter_zero]
    _ = volume A' + volume B' := by
      rw [measure_union_add_inter]
      exact (hB_compact.add isCompact_singleton).measurableSet
    _ = volume A + volume B := by simp [A', B']

lemma brunn_minkowski_1d_infinite
    {A B C : Set ℝ} (ha : volume A = ⊤) (hb : B.Nonempty) (hc : A + B ⊆ C) :
    volume A + volume B ≤ volume C := calc
  volume A + volume B = volume (A + {hb.some}) := by simp [ha]
  _ ≤ volume (A + B) := measure_mono (add_subset_add_left (singleton_subset_iff.mpr hb.some_mem))
  _ ≤ volume C := measure_mono hc

lemma brunn_minkowski_1d
    {A B C : Set ℝ}
    (h : A + B ⊆ C)
    (hA_nonempty : A.Nonempty) (hA_measurable : MeasurableSet A)
    (hB_nonempty : B.Nonempty) (hB_measurable : MeasurableSet B)
    : volume A + volume B ≤ volume C := by

  by_cases hvolAfinite : volume A = ⊤
  · exact brunn_minkowski_1d_infinite hvolAfinite hB_nonempty h
  by_cases hvolBfinite : volume B = ⊤
  · rw [add_comm] at ⊢ h
    exact brunn_minkowski_1d_infinite hvolBfinite hA_nonempty h

  rw [hA_measurable.measure_eq_iSup_isCompact_of_ne_top hvolAfinite,
    hB_measurable.measure_eq_iSup_isCompact_of_ne_top hvolBfinite]

  have combine_sup_conditions {A : Set ℝ} :
      (⨆ K, ⨆ (_ : K ⊆ A), ⨆ (_ : IsCompact K), volume K) =
      (⨆ K, ⨆ (_ : K ⊆ A ∧ IsCompact K), volume K) := by
    simp only [iSup_and]
  simp only [combine_sup_conditions]

  have sup_vol_eq_sup_nonempty_vol {A : Set ℝ} :
      ⨆ K, ⨆ (_ : K ⊆ A ∧ IsCompact K), volume K =
      ⨆ K, ⨆ (_ : K ⊆ A ∧ IsCompact K ∧ K.Nonempty), volume K := by
    apply le_antisymm
    · apply iSup_le; intro K
      apply iSup_le; intro hK
      by_cases h : K.Nonempty
      · apply le_iSup₂_of_le K (by simp [hK, h])
        exact le_refl (volume K)
      rw [not_nonempty_iff_eq_empty] at h
      simp [h]
    apply iSup_le; intro K
    apply iSup_le; intro hK
    apply le_iSup₂_of_le K
    · exact le_refl (volume K)
    simp [hK]
  simp only [sup_vol_eq_sup_nonempty_vol]

  have combine_sups :
      (⨆ K, ⨆ (_ : K ⊆ A ∧ IsCompact K ∧ K.Nonempty), volume K)
      + (⨆ L, ⨆ (_ : L ⊆ B ∧ IsCompact L ∧ L.Nonempty), volume L)
      = ⨆ K, ⨆ L,
        ⨆ (_ : K ⊆ A ∧ IsCompact K ∧ K.Nonempty),
        ⨆ (_ : L ⊆ B ∧ IsCompact L ∧ L.Nonempty),
        volume K + volume L :=
    biSup_add_biSup
      (by use {hA_nonempty.some}; simp [hA_nonempty.some_mem])
      (by use {hB_nonempty.some}; simp [hB_nonempty.some_mem])
  rw [combine_sups]

  apply iSup_le; intro K; apply iSup_le; intro L
  apply iSup_le; intro ⟨hKsubA, hKcompact, hKnonempty⟩
  apply iSup_le; intro ⟨hLsubA, hLcompact, hLnonempty⟩
  have hKplusLsubC : K + L ⊆ C := calc
    K + L ⊆ A + L := add_subset_add_right hKsubA
    _ ⊆ A + B := add_subset_add_left hLsubA
    _ ⊆ C := h
  exact brunn_minkowski_1d_compact hKplusLsubC hKnonempty hKcompact hLnonempty hLcompact

lemma vol_superlevelset_measurable (f : ℝ → ENNReal)
    : Measurable (fun t : ℝ ↦ volume {x | ENNReal.ofReal t ≤ f x}) := by
  apply Antitone.measurable
  intro a b hab
  apply measure_mono
  simp only [ofPred_subset_ofPred]
  intro z hz
  calc
    ENNReal.ofReal a ≤ ENNReal.ofReal b := ENNReal.ofReal_le_ofReal hab
    _ ≤ f z := hz

lemma layercake {f : ℝ → ENNReal} (hf_measurable : Measurable f) :
    ∫⁻ (x : ℝ), f x = ∫⁻ (t : ℝ) in Ioi 0, volume {x : ℝ | ENNReal.ofReal t ≤ f x} := by
  let ind (x t : ℝ) : ENNReal := if ENNReal.ofReal t ≤ f x then 1 else 0
  calc
    ∫⁻ (x : ℝ), f x = ∫⁻ (x : ℝ), ∫⁻ (t : ℝ) in Ioi 0, ind x t := by
      congr; ext x; symm
      calc
        ∫⁻ (t : ℝ) in Ioi 0, ind x t
            = ∫⁻ (t : ℝ) in Ioi 0, {t : ℝ | ENNReal.ofReal t ≤ f x}.indicator 1 t := by
          simp [ind, indicator]
        _ = ∫⁻ (t : ℝ) in {t : ℝ | ENNReal.ofReal t ≤ f x} ∩ (Ioi 0), 1 := by
          apply setLIntegral_indicator
          exact measurableSet_le ENNReal.measurable_ofReal measurable_const
        _ = volume {t : ℝ | ENNReal.ofReal t ≤ f x ∧ 0 < t} := by apply setLIntegral_one
        _ = f x := by
          by_cases hinf : f x = ⊤
          · simp only [hinf, le_top, true_and]; exact Real.volume_Ioi
          calc
            volume {t | ENNReal.ofReal t ≤ f x ∧ 0 < t}
                = volume {t | t ≤ (f x).toReal ∧ 0 < t} := by
              congr; ext t; simp only [and_congr_left_iff]; intro
              exact ENNReal.ofReal_le_iff_le_toReal hinf
            _ = volume (Ioc 0 (f x).toReal) := by congr; aesop
            _ = ENNReal.ofReal (f x).toReal := by simp
            _ = f x := ENNReal.ofReal_toReal_eq_iff.mpr hinf
    _ = ∫⁻ (t : ℝ) in Ioi 0, ∫⁻ (x : ℝ), ind x t := by
      apply lintegral_lintegral_swap
      exact Measurable.aemeasurable <|
        Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) (by fun_prop) (by fun_prop)
    _ = ∫⁻ (t : ℝ) in Ioi 0, volume {x : ℝ | ENNReal.ofReal t ≤ f x} := by
      congr; ext t
      calc
        ∫⁻ (x : ℝ), ind x t = ∫⁻ (x : ℝ), {x : ℝ | ENNReal.ofReal t ≤ f x}.indicator 1 x := by
          simp [ind, indicator]
        _ = ∫⁻ (x : ℝ) in {x : ℝ | ENNReal.ofReal t ≤ f x}, 1 := by
          apply lintegral_indicator
          exact measurableSet_le measurable_const hf_measurable
        _ = volume {x | ENNReal.ofReal t ≤ f x} := by apply setLIntegral_one

lemma lintegral_eq_vol_superlevelset_lintegral_01
    {f : ℝ → ENNReal} (hf_bound : f ≤ 1) (hf_measurable : Measurable f)
    : ∫⁻ x, f x = ∫⁻ t in Ioo 0 1, (fun t ↦ volume {x | ENNReal.ofReal t ≤ f x}) t := by
  let vf := fun t : ℝ ↦ volume {x | ENNReal.ofReal t ≤ f x}
  calc
    ∫⁻ x, f x = ∫⁻ t in Ioi 0, vf t := layercake hf_measurable
    _ = ∫⁻ t in (Ioo 0 1 ∪ Ici 1), vf t := by simp
    _ = (∫⁻ t in Ioo 0 1, vf t) + (∫⁻ t in Ici 1, vf t) :=
      lintegral_union measurableSet_Ici (by simp [disjoint_left])
    _ = ∫⁻ t in Ioo 0 1, vf t := by
      suffices ∫⁻ t in Ici 1, vf t = 0 by simp [this]
      rw [setLIntegral_eq_zero_iff measurableSet_Ici (vol_superlevelset_measurable f)]
      suffices ∀ x : ℝ, x ∈ Ioi 1 → volume {x_1 | ENNReal.ofReal x ≤ f x_1} = 0 by
        apply ae_of_mem_of_ae_of_mem_inter_Ioo; intros; filter_upwards; intro c _
        simp_all only [mem_Ioi, mem_Ici, mem_inter_iff, mem_Ioo]
        exact this c (by linarith)
      intro a ha
      suffices {x | ENNReal.ofReal a ≤ f x} = ∅ by rw [this]; exact measure_empty
      apply eq_empty_of_forall_notMem
      intro x hx
      have : 1 < f x := calc
        1 < ENNReal.ofReal a := ENNReal.one_lt_ofReal.mpr ha
        _ ≤ f x := hx
      exact absurd this (not_lt.mpr (hf_bound x))

lemma weighted_amgm {θ a b : ℝ} (hθ : 0 < θ ∧ θ < 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    : ((1-θ)^(1-θ) * θ^θ)⁻¹ * a^(1-θ) * b^θ ≤ a + b := calc
  ((1-θ)^(1-θ) * θ^θ)⁻¹ * a^(1-θ) * b^θ = ((1-θ)^(1-θ))⁻¹ * a^(1-θ) * (θ^θ)⁻¹ * b^θ := by grind
  _ = ((1-θ)⁻¹)^(1-θ) * a^(1-θ) * (θ⁻¹)^θ * b^θ := by
    rw [Real.inv_rpow (by linarith), Real.inv_rpow (by linarith)]
  _ = ((1-θ)⁻¹*a)^(1-θ) * (θ⁻¹*b)^θ := by
    rw [Real.mul_rpow (by simp only [inv_nonneg, sub_nonneg]; linarith) ha,
      Real.mul_rpow (by simp only [inv_nonneg]; linarith) hb]
    ring
  _ ≤ (1-θ)*((1-θ)⁻¹*a) + θ*(θ⁻¹*b) :=
    Real.geom_mean_le_arith_mean2_weighted
      (by linarith) (by linarith) (by simp [hθ.2, ha]) (by simp [hθ.1, hb]) (by ring)
  _ = a + b := by grind

lemma prekopa_leindler_1d_normalized
    {θ : ℝ} {f g h : ℝ → ENNReal}
    (hθ : 0 < θ ∧ θ < 1)
    (hf_measurable : Measurable f) (hf_sup1 : iSup f = 1)
    (hg_measurable : Measurable g) (hg_sup1 : iSup g = 1)
    (hh_measurable : Measurable h)
    (hfgh : ∀ x y, (f x) ^ (1 - θ) * (g y) ^ θ ≤ h (x + y))
    : ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹) * (∫⁻ x, f x)^(1-θ) * (∫⁻ x, g x)^θ ≤ (∫⁻ x, h x) := by

  have h_superlevelset_incl : ∀ t : ℝ, 0 < t →
      {x | ENNReal.ofReal t ≤ f x} + {x | ENNReal.ofReal t ≤ g x}
      ⊆ {x | ENNReal.ofReal t ≤ h x} := by
    intro t ht
    rw [add_subset_iff]
    intro x hx y hy
    simp only [mem_ofPred_eq] at hx hy ⊢
    calc
      ENNReal.ofReal t = (ENNReal.ofReal t) ^ (1 - θ) * (ENNReal.ofReal t) ^ θ := by
        rw [← ENNReal.rpow_add (1-θ) θ (ne_of_gt (ENNReal.ofReal_pos.mpr ht)) ENNReal.ofReal_ne_top]
        simp
      _ ≤ f x ^ (1 - θ) * g y ^ θ := by
        gcongr
        · linarith
        linarith
      _ ≤ h (x + y) := hfgh x y

  let vf : ℝ → ENNReal := fun t : ℝ ↦ volume {x | ENNReal.ofReal t ≤ f x}
  let vg : ℝ → ENNReal := fun t : ℝ ↦ volume {x | ENNReal.ofReal t ≤ g x}
  let vh : ℝ → ENNReal := fun t : ℝ ↦ volume {x | ENNReal.ofReal t ≤ h x}

  have h_vol_ineq : ∀ t : ℝ, 0 < t ∧ t < 1 → vf t + vg t ≤ vh t := by
    intro t ht
    have superlevelset_nonempty {f : ℝ → ENNReal} (hf_sup1 : iSup f = 1)
        : {x | ENNReal.ofReal t ≤ f x}.Nonempty := by
      apply nonempty_def.mpr
      suffices ∃ x, x ∈ {x | ENNReal.ofReal t < f x} by
        simp only [mem_ofPred_eq] at this ⊢
        rcases this with ⟨x, hx⟩
        use x
        exact le_of_lt hx
      simp only [mem_ofPred_eq]
      apply exists_lt_of_lt_ciSup
      simp only [hf_sup1, ENNReal.ofReal_lt_one, ht.2]
    exact brunn_minkowski_1d
      (h_superlevelset_incl t ht.1)
      (superlevelset_nonempty hf_sup1) (measurableSet_le measurable_const hf_measurable)
      (superlevelset_nonempty hg_sup1) (measurableSet_le measurable_const hg_measurable)

  have h_vol_ineq_integral :
      (∫⁻ t in Ioo 0 1, vf t) + (∫⁻ t in Ioo 0 1, vg t) ≤ ∫⁻ t in Ioi 0, vh t := calc
    (∫⁻ t in Ioo 0 1, vf t) + (∫⁻ t in Ioo 0 1, vg t)
        = ∫⁻ t in Ioo 0 1, (vf t + vg t) := by
      rw [lintegral_add_left (vol_superlevelset_measurable f)]
    _ ≤ ∫⁻ t in Ioo 0 1, vh t := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact h_vol_ineq t ht
    _ ≤ ∫⁻ t in Ioi 0, vh t := by apply lintegral_mono_set; grind

  let fint : ENNReal := ∫⁻ x, f x
  let gint : ENNReal := ∫⁻ x, g x
  let hint : ENNReal := ∫⁻ x, h x
  have hfint : fint = ∫⁻ t in Ioo 0 1, vf t :=
    have hf_bound : f ≤ 1 := by
      intro x; simp only [Pi.one_apply]; rw [← hf_sup1]; exact le_iSup_iff.mpr fun _ a ↦ a x
    lintegral_eq_vol_superlevelset_lintegral_01 hf_bound hf_measurable
  have hgint : gint = ∫⁻ t in Ioo 0 1, vg t :=
    have hg_bound : g ≤ 1 := by
      intro x; simp only [Pi.one_apply]; rw [← hg_sup1]; exact le_iSup_iff.mpr fun _ a ↦ a x
    lintegral_eq_vol_superlevelset_lintegral_01 hg_bound hg_measurable
  have hhint : hint = ∫⁻ t in Ioi 0, vh t := layercake hh_measurable

  have h_ineq_integral : fint + gint ≤ hint := by
    rw [← hhint, ← hfint, ← hgint] at h_vol_ineq_integral
    exact h_vol_ineq_integral

  by_cases h_fint_eq_top : fint = ⊤
  · simp only [h_fint_eq_top, top_add, top_le_iff] at h_ineq_integral
    unfold fint at h_fint_eq_top; unfold hint at h_ineq_integral
    simp [h_fint_eq_top, h_ineq_integral]
  by_cases h_gint_eq_top : gint = ⊤
  · simp only [h_gint_eq_top, add_top, top_le_iff] at h_ineq_integral
    unfold gint at h_gint_eq_top; unfold hint at h_ineq_integral
    simp [h_gint_eq_top, h_ineq_integral]

  have weighted_amgm_factor_nonneg : 0 ≤ ((1-θ)^(1-θ) * θ^θ)⁻¹ := by
    rw [inv_nonneg]
    exact mul_nonneg (Real.rpow_nonneg (by linarith) (1 - θ)) (Real.rpow_nonneg (by linarith) θ)

  calc
    ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹) * fint^(1-θ) * gint^θ =
        ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹) * ENNReal.ofReal ((fint^(1-θ)).toReal) * gint^θ := by
      congr; rw [ENNReal.ofReal_toReal]
      exact ENNReal.rpow_ne_top_of_nonneg (by linarith) h_fint_eq_top
    _ = ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹) * ENNReal.ofReal (fint.toReal^(1-θ)) * gint^θ := by
      rw [← ENNReal.toReal_rpow]
    _ = ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹ * fint.toReal^(1-θ)) * gint^θ := by
      rw [← ENNReal.ofReal_mul]; exact weighted_amgm_factor_nonneg
    _ = ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹ * fint.toReal^(1-θ))
        * ENNReal.ofReal ((gint^θ).toReal) := by
      congr; rw [ENNReal.ofReal_toReal]
      exact ENNReal.rpow_ne_top_of_nonneg (by linarith) h_gint_eq_top
    _ = ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹ * fint.toReal^(1-θ))
        * ENNReal.ofReal (gint.toReal^θ) := by
      rw [← ENNReal.toReal_rpow]
    _ = ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹ * fint.toReal^(1-θ) * gint.toReal^θ) := by
      rw [← ENNReal.ofReal_mul]
      exact mul_nonneg weighted_amgm_factor_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg (1-θ))
    _ ≤ ENNReal.ofReal (fint.toReal + gint.toReal) :=
      ENNReal.ofReal_le_ofReal (weighted_amgm hθ ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    _ = ENNReal.ofReal (fint.toReal) + ENNReal.ofReal (gint.toReal) :=
      ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    _ = fint + gint := by simp [h_fint_eq_top, h_gint_eq_top]
    _ ≤ hint := by exact h_ineq_integral

lemma prekopa_leindler_1d_bounded {θ : ℝ} {f g h : ℝ → ENNReal}
    (hθ : 0 < θ ∧ θ < 1)
    (hf_measurable : Measurable f) (hf_bounded : iSup f ≠ ⊤)
    (hg_measurable : Measurable g) (hg_bounded : iSup g ≠ ⊤)
    (hh_measurable : Measurable h)
    (hfgh : ∀ x y, (f x) ^ (1 - θ) * (g y) ^ θ ≤ h (x + y))
    : ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹) * (∫⁻ x, f x)^(1-θ) * (∫⁻ x, g x)^θ ≤ ∫⁻ x, h x := by

  by_cases hf_zero : f = 0
  · aesop
  by_cases hg_zero : g = 0
  · aesop

  let f' := fun x ↦ (f x) * (iSup f)⁻¹
  let g' := fun x ↦ (g x) * (iSup g)⁻¹
  let h' := fun x ↦ (h x) * ((iSup f)⁻¹)^(1-θ) * ((iSup g)⁻¹)^θ
  let fint := ∫⁻ x, f x
  let gint := ∫⁻ x, g x
  let hint := ∫⁻ x, h x
  let f'int := ∫⁻ x, f' x
  let g'int := ∫⁻ x, g' x
  let h'int := ∫⁻ x, h' x
  let factor : ENNReal := ENNReal.ofReal ((1-θ)^(1-θ) * θ^θ)⁻¹

  have iSupf_ne_zero : iSup f ≠ 0 := iSup_nonzero_of_nonzero hf_zero
  have iSupg_ne_zero : iSup g ≠ 0 := iSup_nonzero_of_nonzero hg_zero
  have iSupf_pos : 0 < iSup f := pos_of_ne_zero iSupf_ne_zero
  have iSupg_pos : 0 < iSup g := pos_of_ne_zero iSupg_ne_zero
  have iSupf_pow_ne_zero : (iSup f)^(1-θ) ≠ 0 :=
    (ne_of_lt (ENNReal.rpow_pos_of_nonneg iSupf_pos (by linarith))).symm
  have iSupg_pow_ne_zero : (iSup g)^θ ≠ 0 :=
    (ne_of_lt (ENNReal.rpow_pos_of_nonneg iSupg_pos (by linarith))).symm
  have iSupf_pow_ne_top : (iSup f)^(1-θ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg' iSupf_pos hf_bounded
  have iSupg_pow_ne_top : (iSup g)^θ ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg' iSupg_pos hg_bounded

  have normalized_result : factor * f'int^(1-θ) * g'int^θ ≤ h'int :=
    have f'_isup1 : iSup f' = 1 := by
      rw [← ENNReal.iSup_mul, ENNReal.mul_inv_cancel iSupf_ne_zero hf_bounded]
    have g'_isup1 : iSup g' = 1 := by
      rw [← ENNReal.iSup_mul, ENNReal.mul_inv_cancel iSupg_ne_zero hg_bounded]
    have hf'g'h' : ∀ x y, (f' x)^(1-θ) * (g' y)^θ ≤ h' (x + y) := by
      unfold f' g' h'
      intro x y
      calc
        (f x * (iSup f)⁻¹) ^ (1 - θ) * (g y * (iSup g)⁻¹) ^ θ
            = (f x)^(1 - θ) * ((iSup f)⁻¹) ^ (1 - θ) * (g y) ^ θ * ((iSup g)⁻¹)^θ := by
          rw [ENNReal.mul_rpow_of_nonneg, ENNReal.mul_rpow_of_nonneg]
          · ring
          · linarith
          linarith
        _ = (f x)^(1 - θ) * (g y) ^ θ * ((iSup f)⁻¹) ^ (1 - θ) * ((iSup g)⁻¹)^θ := by ring
        _ ≤ h' (x + y) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hfgh x y) (by apply zero_le)) (by apply zero_le)
    prekopa_leindler_1d_normalized
      hθ
      (by fun_prop) f'_isup1
      (by fun_prop) g'_isup1
      (by fun_prop)
      hf'g'h'

  have f'int_to_fint : f'int = fint * (iSup f)⁻¹ := lintegral_mul_const (iSup f)⁻¹ hf_measurable
  have g'int_to_gint : g'int = gint * (iSup g)⁻¹ := lintegral_mul_const (iSup g)⁻¹ hg_measurable
  have h'int_to_hint : h'int = hint * (iSup f)⁻¹^(1-θ) * (iSup g)⁻¹^θ := calc
    h'int = ∫⁻ x, ((h x) * (iSup f)⁻¹^(1-θ) * (iSup g)⁻¹^θ) := by rfl
    _ = ∫⁻ x, ((h x) * ((iSup f)⁻¹^(1-θ) * (iSup g)⁻¹^θ)) := by congr; ext x; ring
    _ = hint * ((iSup f)⁻¹^(1-θ) * (iSup g)⁻¹^θ) := by rw [lintegral_mul_const]; exact hh_measurable
    _ = hint * (iSup f)⁻¹^(1-θ) * (iSup g)⁻¹^θ := by ring

  change factor * fint^(1-θ) * gint^θ ≤ hint
  calc
    factor * fint^(1-θ) * gint^θ = factor * (f'int * iSup f)^(1-θ) * (g'int * iSup g)^θ := by
      rw [f'int_to_fint, g'int_to_gint]
      congr
      · exact (ENNReal.inv_mul_cancel_right iSupf_ne_zero hf_bounded).symm
      exact (ENNReal.inv_mul_cancel_right iSupg_ne_zero hg_bounded).symm
    _ = (factor * f'int^(1-θ) * g'int^θ) * ((iSup f)^(1-θ) * (iSup g)^θ) := by
      rw [ENNReal.mul_rpow_of_nonneg, ENNReal.mul_rpow_of_nonneg]
      · ring
      · linarith
      linarith
    _ ≤ h'int * ((iSup f)^(1-θ) * (iSup g)^θ) := by
      rw [ENNReal.mul_le_mul_iff_left]
      · exact normalized_result
      · rw [← pos_iff_ne_zero]; exact ENNReal.mul_pos iSupf_pow_ne_zero iSupg_pow_ne_zero
      · exact ENNReal.mul_ne_top iSupf_pow_ne_top iSupg_pow_ne_top
    _ = (hint * (iSup f)⁻¹^(1-θ) * (iSup g)⁻¹^θ) * ((iSup f)^(1-θ) * (iSup g)^θ) := by
      rw [h'int_to_hint]
    _ = hint * ((iSup f)⁻¹^(1-θ) * (iSup f)^(1-θ)) * ((iSup g)⁻¹^θ * (iSup g)^θ) := by ring
    _ = hint * (((iSup f)^(1-θ))⁻¹ * (iSup f)^(1-θ)) * (((iSup g)^θ)⁻¹ * (iSup g)^θ) := by
      congr
      · rw [ENNReal.inv_rpow]
      rw [ENNReal.inv_rpow]
    _ = hint * 1 * 1 := by
      congr
      · exact ENNReal.inv_mul_cancel iSupf_pow_ne_zero iSupf_pow_ne_top
      exact ENNReal.inv_mul_cancel iSupg_pow_ne_zero iSupg_pow_ne_top
    _ = hint := by ring

lemma prekopa_leindler_1d {θ : ℝ} {f g h : ℝ → ENNReal}
    (hθ : 0 < θ ∧ θ < 1)
    (hf_measurable : Measurable f)
    (hg_measurable : Measurable g)
    (hh_measurable : Measurable h)
    (hfgh : ∀ x y, (f x) ^ (1 - θ) * (g y) ^ θ ≤ h (x + y))
    : ENNReal.ofReal ((1-θ)^(1-θ) * θ^θ)⁻¹ * (∫⁻ x, f x)^(1-θ) * (∫⁻ x, g x)^θ ≤ ∫⁻ x, h x := by
  let c : ENNReal := ENNReal.ofReal ((1-θ)^(1-θ) * θ^θ)⁻¹
  let f_bounded (n : ℕ) : ℝ → ENNReal := fun x ↦ min (f x) n
  let g_bounded (n : ℕ) : ℝ → ENNReal := fun x ↦ min (g x) n

  have f_bounded_mono : Monotone f_bounded := by
    intro _ _ hab; rw [Pi.le_def]; intro x; exact min_le_min_left (f x) (by simp [hab])
  have g_bounded_mono : Monotone g_bounded := by
    intro _ _ hab; rw [Pi.le_def]; intro x; exact min_le_min_left (g x) (by simp [hab])

  have f_as_sup : ∫⁻ x, f x = ⨆ n, ∫⁻ x, f_bounded n x := calc
    _ = ∫⁻ x, ⨆ n, f_bounded n x := by congr; ext; symm; apply iSup_min_nat
    _ = _ := lintegral_iSup (by fun_prop) f_bounded_mono
  have g_as_sup : ∫⁻ x, g x = ⨆ n, ∫⁻ x, g_bounded n x := calc
    _ = ∫⁻ x, ⨆ n, g_bounded n x := by congr; ext; symm; apply iSup_min_nat
    _ = _ := lintegral_iSup (by fun_prop) g_bounded_mono

  have result_for_bounded : ∀ n m,
      c * (∫⁻ x, f_bounded n x)^(1-θ) * (∫⁻ x, g_bounded m x)^θ ≤ ∫⁻ x, h x := by
    intro n m
    apply prekopa_leindler_1d_bounded hθ (by fun_prop) (iSup_min_nat_ne_top n _)
      (by fun_prop) (iSup_min_nat_ne_top m _) hh_measurable
    intro x y
    calc
      (f_bounded n x)^(1-θ) * (g_bounded m y)^θ ≤ (f x)^(1-θ) * (g y)^θ := by
        gcongr
        · linarith
        · aesop
        · linarith
        aesop
      _ ≤ h (x + y) := hfgh x y

  calc
    c * (∫⁻ x, f x)^(1-θ) * (∫⁻ x, g x)^θ
        = c * (⨆ n, ∫⁻ x, f_bounded n x)^(1-θ) * (⨆ m, ∫⁻ x, g_bounded m x)^θ := by
      rw [f_as_sup, g_as_sup]
    _ = ⨆ n, c * (∫⁻ x, f_bounded n x)^(1-θ) * (⨆ m, ∫⁻ x, g_bounded m x)^θ := by
      rw [← ENNReal.iSup_mul, ← ENNReal.mul_iSup, iSup_rpow_of_pos (by linarith)]
    _ = ⨆ n, ⨆ m, c * (∫⁻ x, f_bounded n x)^(1-θ) * (∫⁻ x, g_bounded m x)^θ := by
      congr; ext; rw [← ENNReal.mul_iSup, iSup_rpow_of_pos hθ.1]
    _ ≤ ∫⁻ x, h x := by apply iSup₂_le; exact result_for_bounded

lemma lintegral_fin1 (F : (Fin 1 → ℝ) → ENNReal) :
    ∫⁻ v : (Fin 1 → ℝ), F v = ∫⁻ x : ℝ, F (fun _ ↦ x) := by
  exact MeasurePreserving.lintegral_map_equiv F
    (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
    ((volume_preserving_funUnique (Fin 1) ℝ).symm _)


def append {d : ℕ} (x : Fin d → ℝ) (t : Fin 1 → ℝ) : Fin (d + 1) → ℝ :=
  fun i ↦ if h : i.val < d then x ⟨i.val, h⟩ else t default

@[fun_prop]
lemma append_measurable {d : ℕ} (x : Fin d → ℝ) : Measurable (append x) := by
  unfold append
  apply Measurable.of_eval
  intro
  split
  · fun_prop
  fun_prop

@[fun_prop]
lemma append_measurable' {d : ℕ} (t : Fin 1 → ℝ) : Measurable (fun x : Fin d → ℝ ↦ append x t) := by
  unfold append
  apply Measurable.of_eval
  intro
  split
  · fun_prop
  fun_prop

lemma append_linear {d : ℕ} (x1 y1 : Fin (d + 1) → ℝ) (x y : Fin 1 → ℝ)
    : append x1 x + append y1 y = append (x1 + y1) (x + y) := by
  unfold append
  aesop

def fix {d : ℕ} (F : (Fin (d + 1) → ℝ) → ENNReal) (x : Fin d → ℝ) : (Fin 1 → ℝ) → ENNReal :=
  F ∘ (append x)

@[fun_prop]
lemma fix_measurable {d : ℕ} {F : (Fin (d + 1) → ℝ) → ENNReal} (hF : Measurable F) (x : Fin d → ℝ)
    : Measurable (fix F x) := by
  unfold fix
  fun_prop

lemma fix_apply {d : ℕ} (F : (Fin (d + 1) → ℝ) → ENNReal) (x : Fin d → ℝ) (y : Fin 1 → ℝ)
    : fix F x y = F (append x y) := by
  rfl

lemma lintegral_fix_eq_lmarginal {d : ℕ}
    (F : (Fin (d + 2) → ℝ) → ENNReal) (x1 : Fin (d + 1) → ℝ)
    : ∫⁻ y : Fin 1 → ℝ, (fix F x1) y = (∫⋯∫⁻_{⟨d+1, by simp⟩}, F) (append x1 default) := by
  have h_lmarginal_singleton := lmarginal_singleton F ⟨d+1, by simp⟩ (μ := fun _ ↦ volume)
  suffices ∫⁻ (y : ℝ), F (Function.update (append x1 default) ⟨d + 1, by simp⟩ y)
      = ∫⁻ (y : Fin 1 → ℝ), fix F x1 y by
    rw [congrFun h_lmarginal_singleton (append x1 default), this]
  rw [lintegral_fin1]
  unfold fix append Function.update
  simp_all only [Pi.default_def, eq_rec_constant, Fin.default_eq_zero, Fin.isValue, dite_eq_ite,
    Function.comp_apply]
  congr; ext; congr; ext i; split
  case e_f.isTrue => simp_all
  case e_f.isFalse h => simp [Fin.val_lt_last h]

lemma lintegral_fix_lintegral_eq_lintegral
    {d : ℕ} {f : (Fin (d + 2) → ℝ) → ENNReal} (hf_measurable : Measurable f) :
    ∫⁻ (x : Fin (d + 1) → ℝ), ∫⁻ (t : Fin 1 → ℝ), (fix f x) t
    = ∫⁻ (x : Fin (d + 2) → ℝ), f x := by

  have : ∫⁻ (x : Fin (d + 1) → ℝ), ∫⁻ (t : Fin 1 → ℝ), (fix f x) t
      = ∫⁻ (x : Fin (d + 1) → ℝ), ∫⁻ (t : ℝ), f (append x (fun _ ↦ t)) := by
    congr; ext; rw [lintegral_fin1]; rfl
  rw [this]

  let equiv : (Fin (d + 2) → ℝ) ≃ᵐ ℝ × (Fin (d + 1) → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 2) ↦ ℝ) (Fin.last (d + 1))
  let g : ℝ × (Fin (d + 1) → ℝ) → (Fin (d + 2) → ℝ) := fun tx ↦ (append tx.2 fun _ ↦ tx.1)
  have hg_eq_equiv_invFun : g = equiv.invFun := by aesop
  have hg_measurable : Measurable g := by rw [hg_eq_equiv_invFun]; exact equiv.measurable_invFun
  let f' : (ℝ × (Fin (d + 1) → ℝ)) → ENNReal := fun tx ↦ f (append tx.2 fun x ↦ tx.1)
  have hf'_measurable : Measurable f' := by
    apply Measurable.comp hf_measurable; unfold g at hg_measurable; exact hg_measurable
  rw [← MeasureTheory.lintegral_prod_symm' f' hf'_measurable]

  have : ∫⁻ (z : ℝ × (Fin (d + 1) → ℝ)), f' z ∂volume.prod volume
    = ∫⁻ (z : ℝ × (Fin (d + 1) → ℝ)), f' z := by rfl
  rw [this]

  rw [← MeasureTheory.lintegral_map hf_measurable hg_measurable]

  congr
  rw [hg_eq_equiv_invFun]
  exact (MeasureTheory.volume_preserving_piFinSuccAbove
    (fun _ : Fin (d + 2) ↦ ℝ) (Fin.last (d + 1))).symm.map_eq

def PLConditions (n : ℕ) (θ : ℝ) (f g h : (Fin n → ℝ) → ENNReal) : Prop :=
  0 < θ ∧ θ < 1 ∧
  Measurable f ∧ Measurable g ∧ Measurable h ∧
  (∀ x y, (f x)^(1-θ) * (g y)^θ ≤ h (x + y))

lemma prekopa_leindler_1d_fin1
    {θ : ℝ} {f g h : (Fin 1 → ℝ) → ENNReal} (hθfgh : PLConditions 1 θ f g h)
    : ENNReal.ofReal ((1-θ)^(1-θ) * θ^θ)⁻¹ * (∫⁻ x, f x)^(1-θ) * (∫⁻ x, g x)^θ ≤ ∫⁻ x, h x := by
  let ⟨hθ0, hθ1, hf_measurable, hg_measurable, hh_measurable, hfgh⟩ := hθfgh
  rw [lintegral_fin1 f, lintegral_fin1 g, lintegral_fin1 h]
  exact prekopa_leindler_1d
    ⟨hθ0, hθ1⟩
    (by fun_prop)
    (by fun_prop)
    (by fun_prop)
    (fun x y ↦ hfgh (fun _ ↦ x) (fun _ ↦ y))

lemma prekopa_leindler
    {d : ℕ} {θ : ℝ} {f g h : (Fin (d + 1) → ℝ) → ENNReal} (hθfgh : PLConditions (d + 1) θ f g h)
    : ENNReal.ofReal ((1 - θ) ^ ((d + 1) * (1 - θ)) * θ ^ ((d + 1) * θ))⁻¹
      * (∫⁻ x, f x) ^ (1 - θ) * (∫⁻ x, g x) ^ θ ≤ ∫⁻ x, h x := by

  induction d using Nat.case_strong_induction_on with
  | hz => simpa using (prekopa_leindler_1d_fin1 hθfgh)
  | hi d hd =>

  let ⟨hθ0, hθ1, hf_measurable, hg_measurable, hh_measurable, hfgh⟩ := hθfgh

  have hyp_0 : ∀ {f g h : (Fin 1 → ℝ) → ENNReal}, PLConditions 1 θ f g h →
      ENNReal.ofReal ((1-θ)^(1-θ) * θ^θ)⁻¹
      * (∫⁻ (x : Fin 1 → ℝ), f x)^(1-θ) * (∫⁻ (x : Fin 1 → ℝ), g x)^θ
      ≤ ∫⁻ (x : Fin 1 → ℝ), h x := by
    have := hd 0
    simp_all
  have hyp_d : ∀ {f g h : (Fin (d + 1) → ℝ) → ENNReal}, PLConditions (d + 1) θ f g h →
      ENNReal.ofReal ((1-θ)^((d+1)*(1-θ)) * θ^((d+1)*θ))⁻¹
      * (∫⁻ (x : Fin (d + 1) → ℝ), f x)^(1-θ) * (∫⁻ (x : Fin (d + 1) → ℝ), g x)^θ
      ≤ ∫⁻ (x : Fin (d + 1) → ℝ), h x := by
    have := hd d
    simp_all

  let F : (Fin (d + 1) → ℝ) → ENNReal := fun x1 ↦ ∫⁻ x, (fix f x1) x
  let G : (Fin (d + 1) → ℝ) → ENNReal := fun x1 ↦ ∫⁻ x, (fix g x1) x
  let H : (Fin (d + 1) → ℝ) → ENNReal :=
    fun x1 ↦ ENNReal.ofReal ((1-θ)^(1-θ) * θ^θ) * ∫⁻ x, (fix h x1) x

  let F' : (Fin (d + 1) → ℝ) → ENNReal :=
    fun x1 ↦ (∫⋯∫⁻_{⟨d + 1, by simp⟩}, f ∂fun _ ↦ volume) (append x1 default)
  let G' : (Fin (d + 1) → ℝ) → ENNReal :=
    fun x1 ↦ (∫⋯∫⁻_{⟨d + 1, by simp⟩}, g ∂fun _ ↦ volume) (append x1 default)
  let H' : (Fin (d + 1) → ℝ) → ENNReal :=
    fun x1 ↦ ENNReal.ofReal ((1-θ)^(1-θ) * θ^θ)
      * (∫⋯∫⁻_{⟨d + 1, by simp⟩}, h ∂fun _ ↦ volume) (append x1 default)
  have h_F_eq_F' : F = F' := by unfold F F'; ext; rw [lintegral_fix_eq_lmarginal]
  have h_G_eq_G' : G = G' := by unfold G G'; ext; rw [lintegral_fix_eq_lmarginal]
  have h_H_eq_H' : H = H' := by unfold H H'; ext; rw [lintegral_fix_eq_lmarginal]

  have hF_measurable : Measurable F := by
    rw [h_F_eq_F']; unfold F'
    exact (hf_measurable.lmarginal (fun _ => volume)).comp (by fun_prop)
  have hG_measurable : Measurable G := by
    rw [h_G_eq_G']; unfold G'
    exact (hg_measurable.lmarginal (fun _ => volume)).comp (by fun_prop)
  have hH_measurable : Measurable H := by
    rw [h_H_eq_H']; unfold H'
    exact measurable_const.mul
      ((hh_measurable.lmarginal (fun _ => volume)).comp (by fun_prop))
  have factor_pos : 0 < (1-θ)^(1-θ)*θ^θ :=
    mul_pos (Real.rpow_pos_of_pos (by linarith) (1-θ)) (Real.rpow_pos_of_pos (by linarith) θ)
  have fix_plconditions : ∀ x1 y1 : Fin (d + 1) → ℝ,
      PLConditions 1 θ (fix f x1) (fix g y1) (fix h (x1 + y1)) := by
    intro x1 y1
    exact ⟨
      hθ0, hθ1, by fun_prop, by fun_prop, by fun_prop, by
        intro x y
        rw [fix_apply, fix_apply, fix_apply]
        have h_result : f (append x1 x)^(1-θ) * g (append y1 y)^θ ≤ h (append x1 x + append y1 y) :=
          hfgh (append x1 x) (append y1 y)
        rw [append_linear x1 y1 x y] at h_result
        exact h_result
    ⟩
  have marginal_pl_condition : ∀ x1 y1 : Fin (d + 1) → ℝ,
      (F x1)^(1-θ) * (G y1)^θ ≤ H (x1 + y1) := by
    intro x1 y1
    calc
      (F x1)^(1-θ) * (G y1)^θ = 1 * (F x1)^(1-θ) * (G y1)^θ := by ring
      _ = (ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ) * (ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ))⁻¹)
          * (F x1)^(1-θ) * (G y1)^θ := by
        congr
        symm
        exact ENNReal.mul_inv_cancel
          (ENNReal.ofReal_ne_zero_iff.mpr factor_pos) (Ne.symm ENNReal.top_ne_ofReal)
      _ = (ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ) * ENNReal.ofReal ((1 - θ)^(1-θ)*θ^θ)⁻¹)
          * (F x1)^(1-θ) * (G y1)^θ := by
        congr
        rw [ENNReal.ofReal_inv_of_pos (by linarith)]
      _ = ENNReal.ofReal ((1-θ)^(1-θ) * θ^θ)
          * (ENNReal.ofReal ((1 - θ)^(1-θ)*θ^θ)⁻¹ * (F x1)^(1-θ) * (G y1)^θ) := by
        ring
      _ ≤ H (x1 + y1) := by
        rw [ENNReal.mul_le_mul_iff_right
          (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith)
          (by simp only [ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true])]
        exact hyp_0 (fix_plconditions x1 y1)
  have result_d : ENNReal.ofReal ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ))⁻¹
      * (∫⁻ (x : Fin (d + 1) → ℝ), F x)^(1-θ)
      * (∫⁻ (x : Fin (d + 1) → ℝ), G x)^θ
      ≤ ∫⁻ (x : Fin (d + 1) → ℝ), H x :=
    hyp_d ⟨hθ0, hθ1, hF_measurable, hG_measurable, hH_measurable, marginal_pl_condition⟩

  have result_d_2 : (ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ))⁻¹ *
      (ENNReal.ofReal ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ))⁻¹
      * (∫⁻ (x : Fin (d + 2) → ℝ), f x)^(1-θ) *
      (∫⁻ (x : Fin (d + 2) → ℝ), g x)^θ) ≤ ∫⁻ (x : Fin (d + 2) → ℝ), h x := by
    unfold F G H at result_d
    have extract_constant :
        ∫⁻ (x : Fin (d + 1) → ℝ), ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ) * ∫⁻ t, (fix h x) t
        = ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ) * ∫⁻ (x : Fin (d + 1) → ℝ), ∫⁻ t, (fix h x) t := by
      rw [lintegral_const_mul']
      exact Ne.symm ENNReal.top_ne_ofReal
    rw [lintegral_fix_lintegral_eq_lintegral hf_measurable,
      lintegral_fix_lintegral_eq_lintegral hg_measurable,
      extract_constant,
      lintegral_fix_lintegral_eq_lintegral hh_measurable,
      ← ENNReal.inv_mul_le_iff
        (ENNReal.ofReal_ne_zero_iff.mpr factor_pos) (Ne.symm ENNReal.top_ne_ofReal)] at result_d
    exact result_d
  have rewrite_lhs_of_result_d_2 :
      (ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ))⁻¹ * (ENNReal.ofReal ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ))⁻¹
      * (∫⁻ (x : Fin (d + 2) → ℝ), f x)^(1-θ) * (∫⁻ (x : Fin (d + 2) → ℝ), g x)^θ)
      = (ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ))⁻¹ * ENNReal.ofReal ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ))⁻¹
      * (∫⁻ (x : Fin (d + 2) → ℝ), f x)^(1-θ) * (∫⁻ (x : Fin (d + 2) → ℝ), g x)^θ := by ring
  have combine_consts_of_result_d_2 : (ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ))⁻¹
      * ENNReal.ofReal ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ))⁻¹ =
      ENNReal.ofReal ((1-θ)^((d+2)*(1-θ))*θ^((d+2)*θ))⁻¹ := calc
    _ = ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ)⁻¹
        * ENNReal.ofReal ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ))⁻¹ := by
      congr; exact Eq.symm (ENNReal.ofReal_inv_of_pos factor_pos)
    _ = ENNReal.ofReal (((1-θ)^(1-θ)*θ^θ)⁻¹ * ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ))⁻¹) :=
      Eq.symm (ENNReal.ofReal_mul (inv_nonneg.mpr (le_of_lt factor_pos)))
    _ = ENNReal.ofReal (((1-θ)^(1-θ)*(1-θ)^((d+1)*(1-θ))) * (θ^θ * θ^((d+1)*θ)))⁻¹ := by grind
    _ = ENNReal.ofReal ((1-θ)^((d+2)*(1-θ))*θ^((d+2)*θ))⁻¹ := by
      congr
      · exact Eq.symm <| Real.rpow_of_add_eq
          (by linarith) (ne_of_gt <| mul_pos (by linarith) (by linarith)) (by grind)
      exact Eq.symm <| Real.rpow_of_add_eq
        (by linarith) (ne_of_gt <| mul_pos (by linarith) (by linarith)) (by grind)
  have result_d_3 : ENNReal.ofReal ((1-θ)^((d+2)*(1-θ))*θ^((d+2)*θ))⁻¹
      * (∫⁻ (x : Fin (d + 2) → ℝ), f x) ^ (1 - θ) * (∫⁻ (x : Fin (d + 2) → ℝ), g x) ^ θ ≤
      ∫⁻ (x : Fin (d + 2) → ℝ), h x := by
    rw [rewrite_lhs_of_result_d_2, combine_consts_of_result_d_2] at result_d_2
    exact result_d_2
  have rewrite_const_of_result_d_3 :
      ENNReal.ofReal ((1-θ)^((d+2)*(1-θ))*θ^((d+2)*θ))⁻¹ =
      ENNReal.ofReal ((1-θ)^((↑(d+1)+1)*(1-θ))*θ^((↑(d+1)+1)*θ))⁻¹ := by
    congr 5
    · simp only [Nat.cast_add, Nat.cast_one]
      ring
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  change ENNReal.ofReal ((1-θ)^((↑(d+1)+1)*(1-θ))*θ^((↑(d+1)+1)*θ))⁻¹
    * (∫⁻ (x : Fin (d + 2) → ℝ), f x)^(1-θ) * (∫⁻ (x : Fin (d + 2) → ℝ), g x)^θ
    ≤ ∫⁻ (x : Fin (d + 2) → ℝ), h x
  rw [rewrite_const_of_result_d_3] at result_d_3
  exact result_d_3
lemma lintegral_comp_inv_smul {d : ℕ} (c : ℝ) (hc : 0 < c)
    (f : (Fin d → ℝ) → ENNReal) (hf : Measurable f) :
    (∫⁻ x, f (c⁻¹ • x)) = ENNReal.ofReal (c ^ d) * ∫⁻ x, f x := by
  rw [← lintegral_map hf (by fun_prop : Measurable (fun x : Fin d → ℝ => c⁻¹ • x)),
    Measure.map_addHaar_smul volume (inv_ne_zero hc.ne'), lintegral_smul_measure]
  simp [inv_pow, abs_of_nonneg (pow_nonneg hc.le d), smul_eq_mul]

lemma scaled_power_cancel (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) (F G : ENNReal) :
    ENNReal.ofReal ((a ^ ((n : ℝ) * (1 - t)) * b ^ ((n : ℝ) * t))⁻¹) *
      (ENNReal.ofReal (a ^ n) * F) ^ (1 - t) *
      (ENNReal.ofReal (b ^ n) * G) ^ t = F ^ (1 - t) * G ^ t := by
  have ha' := Real.rpow_pos_of_pos ha ((n : ℝ) * (1 - t))
  have hb' := Real.rpow_pos_of_pos hb ((n : ℝ) * t)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (sub_nonneg.mpr ht'),
    ENNReal.mul_rpow_of_nonneg _ _ ht,
    ENNReal.ofReal_rpow_of_pos (pow_pos ha n),
    ENNReal.ofReal_rpow_of_pos (pow_pos hb n),
    ← Real.rpow_natCast_mul ha.le, ← Real.rpow_natCast_mul hb.le]
  let A := ENNReal.ofReal (a ^ ((n : ℝ) * (1 - t)))
  let B := ENNReal.ofReal (b ^ ((n : ℝ) * t))
  rw [ENNReal.ofReal_inv_of_pos (mul_pos ha' hb'), ENNReal.ofReal_mul ha'.le]
  change (A * B)⁻¹ * (A * F ^ (1 - t)) * (B * G ^ t) = _
  calc
    (A * B)⁻¹ * (A * F ^ (1 - t)) * (B * G ^ t) =
        ((A * B)⁻¹ * (A * B)) * (F ^ (1 - t) * G ^ t) := by ac_rfl
    _ = F ^ (1 - t) * G ^ t := by
      rw [ENNReal.inv_mul_cancel (by positivity : A * B ≠ 0)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top), one_mul]

lemma prekopa_leindler_weighted {d : ℕ} {t : ℝ}
    {f g h : (Fin (d + 1) → ℝ) → ENNReal}
    (ht : 0 < t) (ht' : t < 1) (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h)
    (hfg : ∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y)) :
    (∫⁻ x, f x) ^ (1 - t) * (∫⁻ x, g x) ^ t ≤ ∫⁻ x, h x := by
  have ha : 0 < 1 - t := sub_pos.mpr ht'
  have hscaled := prekopa_leindler (d := d) (f := fun x => f ((1 - t)⁻¹ • x))
    (g := fun x => g (t⁻¹ • x)) (h := h)
    ⟨ht, ht', hf.comp (by fun_prop), hg.comp (by fun_prop), hh, by
      intro x y
      simpa only [smul_smul, mul_inv_cancel₀ ha.ne', mul_inv_cancel₀ ht.ne', one_smul]
        using hfg ((1 - t)⁻¹ • x) (t⁻¹ • y)⟩
  rw [lintegral_comp_inv_smul (1 - t) ha f hf,
    lintegral_comp_inv_smul t ht g hg] at hscaled
  have hc := scaled_power_cancel (1 - t) t ha ht (d + 1) t ht.le ht'.le
    (∫⁻ x, f x) (∫⁻ x, g x)
  simp only [Nat.cast_add, Nat.cast_one] at hc
  rwa [hc] at hscaled

lemma prekopa_leindler_euclidean {d : ℕ} {t : ℝ}
    {f g h : EuclideanSpace ℝ (Fin (d + 1)) → ENNReal}
    (ht : 0 < t) (ht' : t < 1) (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h)
    (hfg : ∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y)) :
    (∫⁻ x, f x) ^ (1 - t) * (∫⁻ x, g x) ^ t ≤ ∫⁻ x, h x := by
  have hp := PiLp.volume_preserving_toLp (Fin (d + 1))
  rw [← hp.lintegral_comp hf, ← hp.lintegral_comp hg, ← hp.lintegral_comp hh]
  apply prekopa_leindler_weighted ht ht' (hf.comp hp.measurable)
    (hg.comp hp.measurable) (hh.comp hp.measurable)
  intro x y
  simpa only [Function.comp_apply, WithLp.toLp_add, WithLp.toLp_smul] using
    hfg (WithLp.toLp 2 x) (WithLp.toLp 2 y)

end LongTails.Proofs.PrekopaLeindler
