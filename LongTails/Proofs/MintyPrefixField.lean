import LongTails.Proofs.MintyPrefixSphere
import Mathlib.Analysis.Real.Pi.Bounds
import LongTails.Proofs.MintyPrefixSearch

open scoped RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.MintyPrefixField

open MintyChainGeometry MintyPrefixSphere MintyPrefixSearch

variable {k d m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

def offsets (π : Fin (k+1) ↪ Fin d) (s : ℝ) (x : E) (w : Word (k+1) m) (i : Fin (k+1)) :=
  x (π i) / s - 4 * (w i : ℕ)

def field (π : Fin (k+1) ↪ Fin d) (s a : ℝ) (w : Word (k+1) m) (x : E) : E :=
  a • lift π (fun j => sphere (offsets π s x w) j.castSucc)

def root (π : Fin (k+1) ↪ Fin d) (s : ℝ) (w : Word (k+1) m) : E :=
  s • lift π (fun j => 4 * (w j : ℕ))

lemma root_coord (π : Fin (k+1) ↪ Fin d) (s : ℝ) (w : Word (k+1) m) (i : Fin (k+1)) :
    root π s w (π i) = s * (4 * (w i : ℕ)) := by
  change s * lift π _ (π i) = _
  rw [lift_apply]

lemma field_root (π : Fin (k+1) ↪ Fin d) {s : ℝ} (hs : 0 < s) (a : ℝ) (w : Word (k+1) m) :
    field π s a w (root π s w) = 0 := by
  have he : offsets π s (root π s w) w = fun _ => 0 := by
    funext i
    rw [offsets, root_coord, mul_div_cancel_left₀ _ hs.ne', sub_self]
  ext i
  change a * (∑ j, if π j = i then sphere (offsets π s (root π s w) w) j.castSucc else 0) = 0
  simp [he, sphere_origin]

lemma norm_root (π : Fin (k+1) ↪ Fin d) {s : ℝ} (hs : 0 < s) (w : Word (k+1) m) :
    ‖root π s w‖ ≤ 4 * s * m * Real.sqrt (k+1) := by
  have h (j : Fin (k+1)) : (4 * ((w j : ℕ) : ℝ)) ^ 2 ≤ (4 * (m : ℝ)) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    have := (w j).isLt
    gcongr
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
  have hv : 0 ≤ (k : ℝ) + 1 := by positivity
  have ht : ‖lift π (fun j => 4 * ((w j : ℕ) : ℝ))‖ ≤ 4 * m * Real.sqrt (k+1) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [norm_lift_sq, mul_pow, Real.sq_sqrt hv]
    simpa [mul_comm] using hb
  rw [root, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  nlinarith [mul_le_mul_of_nonneg_left ht hs.le]

lemma field_minty (π : Fin (k+1) ↪ Fin d) {s a : ℝ} (hs : 0 < s) (ha : 0 ≤ a)
    (w : Word (k+1) m) (x : E) : 0 ≤ ⟪field π s a w x, x - root π s w⟫ := by
  rw [field, real_inner_smul_left, inner_lift]
  apply mul_nonneg ha
  apply Finset.sum_nonneg
  intro i _
  have he : (x - root π s w) (π i) = offsets π s x w i * s := by
    change x (π i) - root π s w (π i) = _
    rw [root_coord, offsets, sub_mul, div_mul_cancel₀ _ hs.ne']
    ring
  rw [he, ← mul_assoc]
  exact mul_nonneg (sphere_sign _ i) hs.le

lemma field_lip (π : Fin (k+1) ↪ Fin d) {s a : ℝ} (hs : 0 < s) (ha : 0 ≤ a)
    (w : Word (k+1) m) (x y : E) :
    ‖field π s a w x - field π s a w y‖ ≤ (2 * a / s) * ‖x - y‖ := by
  let u := offsets π s x w
  let v := offsets π s y w
  have hδ (i) : u i - v i = (x-y) (π i) / s := by
    change _ / s - _ - (_ / s - _) = (x (π i) - y (π i)) / s
    ring
  have h := sphere_chord u v
  rw [Fin.sum_univ_castSucc (f := fun i => (sphere u i - sphere v i)^2)] at h
  simp_rw [hδ, div_pow] at h
  rw [← Finset.sum_div] at h
  have hb := coordinate_sq_sum π (x-y)
  have hh : ‖lift π (fun j => sphere u j.castSucc - sphere v j.castSucc)‖ ≤
      2 * ‖x-y‖ / s := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [norm_lift_sq, div_pow, mul_pow]
    apply le_trans _ (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb
      (by norm_num : (0:ℝ) ≤ 2^2)) (sq_nonneg s))
    nlinarith [sq_nonneg (sphere u (Fin.last (k+1)) - sphere v (Fin.last (k+1))),
      div_nonneg (Finset.sum_nonneg (s := Finset.univ) (fun j _ => sq_nonneg ((x-y) (π j)))) (sq_nonneg s),
      show (2:ℝ)^2 * (∑ j, (x-y) (π j)^2) / s^2 =
        4 * ((∑ j, (x-y) (π j)^2) / s^2) by ring]
  rw [field, field, ← smul_sub, lift_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  calc
    _ ≤ a * (2 * ‖x-y‖ / s) := mul_le_mul_of_nonneg_left hh ha
    _ = _ := by ring

def side (q : ℝ) (v : Fin m) : Ordering :=
  if q - 4 * (v : ℕ) ≤ -(Real.pi / 2) then .lt
  else if Real.pi / 2 ≤ q - 4 * (v : ℕ) then .gt else .eq

lemma side_near {q : ℝ} {v : Fin m} (h : side q v = .eq) :
    -(Real.pi/2) < q - 4 * (v : ℕ) ∧ q - 4 * (v : ℕ) < Real.pi/2 := by
  unfold side at h
  split_ifs at h with h1 h2
  exact ⟨lt_of_not_ge h1, lt_of_not_ge h2⟩

lemma near_unique (q : ℝ) (u v : Fin m) (hu : side q u = .eq) (hv : side q v = .eq) :
    u = v := by
  obtain ⟨ha, hb⟩ := side_near hu
  obtain ⟨hc, hd⟩ := side_near hv
  apply Fin.ext
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · have he : ((u : ℕ) : ℝ) + 1 ≤ (v : ℕ) := by exact_mod_cast h
    linarith [Real.pi_lt_four]
  · have he : ((v : ℕ) : ℝ) + 1 ≤ (u : ℕ) := by exact_mod_cast h
    linarith [Real.pi_lt_four]

lemma side_far {q : ℝ} {u v : Fin m} (h : side q u ≠ .eq) (he : side q u = side q v) :
    angle (q - 4 * (u : ℕ)) = angle (q - 4 * (v : ℕ)) ∧
    Real.pi / 2 ≤ |q - 4 * (u : ℕ)| := by
  unfold side at h he
  split_ifs at h he with h1 h2 h3 h4 <;> try contradiction
  · exact ⟨by simp [angle, max_eq_right h1, max_eq_right h2], le_abs.mpr (Or.inr (by linarith))⟩
  · rename_i hv
    exact ⟨by simp [angle, min_eq_left (h4.trans (le_max_left _ _)),
      min_eq_left (hv.trans (le_max_left _ _))], le_abs.mpr (Or.inl h4)⟩

lemma same_reply (π : Fin (k+1) ↪ Fin d) (s a : ℝ) (x : E) (i : Fin (k+1))
    (w v : Word (k+1) m) (hp : ∀ j : Fin (k+1), j.val < i.val → w j = v j)
    (h : side (x (π i) / s) (w i) ≠ .eq)
    (he : side (x (π i) / s) (w i) = side (x (π i) / s) (v i)) :
    field π s a w x = field π s a v x := by
  obtain ⟨ht, hz⟩ := side_far h he
  have heq := sphere_prefix (offsets π s x w) (offsets π s x v) i
    (fun j hj => by simp [offsets, hp j hj]) ht (cos_angle_eq_zero hz)
  simp only [field, heq]

lemma far_norm (π : Fin (k+1) ↪ Fin d) (s : ℝ) {a : ℝ} (ha : 0 ≤ a)
    (x : E) (i : Fin (k+1)) (w : Word (k+1) m) (h : side (x (π i) / s) (w i) ≠ .eq) :
    ‖field π s a w x‖ = a := by
  have hz := (side_far h rfl).2
  have he := saturated_norm (offsets π s x w) i hz
  have hn : ‖lift π (fun j => sphere (offsets π s x w) j.castSucc)‖ = 1 := by
    have hh := norm_lift_sq π (fun j => sphere (offsets π s x w) j.castSucc)
    nlinarith [norm_nonneg (lift π (fun j => sphere (offsets π s x w) j.castSucc))]
  simp [field, norm_smul, abs_of_nonneg ha, hn]

end LongTails.Proofs.MintyPrefixField
