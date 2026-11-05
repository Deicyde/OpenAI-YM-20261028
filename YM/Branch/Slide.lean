import YM.Branch.Uniform
import YM.Lattice.Foliation

/-!
# Compare planes in the axial gauge

but instead recurse on slabs. Keep all cover sites and faces.
No restriction on curvature, root chosen existentially for a specified order.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Axial

open Function Filter Set NormedSpace Submodule Lattice Wilson
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

variable {G : Gauge}

/-- sum over all internal positive links. -/
def perEdge (X : Finset Cover) (U : CoverConfig G) (x : Cover) (i : Axis) : ℝ :=
    if x+step i ∈ X then G.chord (U (x,i)) else 0

def edges (X : Finset Cover) (U : CoverConfig G) : ℝ := ∑ x ∈ X, ∑ i, perEdge X U x i

/-- faces fully inside. -/
def face (X : Finset Cover) (U : CoverConfig G) (x : Cover) (p : PlaqAxes) :=
    if ∀ y ∈ visits x (square p.val.1 p.val.2), y ∈ X then G.chord (faceValue U (x,p)) else 0

def field (X : Finset Cover) (U : CoverConfig G) (x : Cover) := ∑ p, face X U x p

def faces (X : Finset Cover) (U : CoverConfig G) := ∑ x ∈ X, field X U x

lemma face_nonneg (X : Finset Cover) (U : CoverConfig G) (x p) : 0 ≤ face X U x p := by
  unfold face; split
  · exact G.chord_nonneg _
  rfl

lemma field_nonneg (X : Finset Cover) (U : CoverConfig G) (x) : 0 ≤ field X U x := Finset.sum_nonneg fun _ _ ↦ face_nonneg ..

lemma faces_nonneg (X : Finset Cover) (U : CoverConfig G) : 0 ≤ faces X U := Finset.sum_nonneg fun _ _ ↦ field_nonneg ..

@[simp] lemma face_gauge_symm (t : Cover → G.El) (X : Finset Cover) (U x p) :
    face X (gauge t U) x p = face X U x p := by simp only [face,face_gauge,G.chord_conj]

@[simp] lemma faces_gauge_symm (t : Cover → G.El) (X : Finset Cover) (U) :
    faces X (gauge t U) = faces X U := by simp_rw [faces,field,face_gauge_symm]

lemma faces_pins {r o l j} (hj : j ∉ l) (U : CoverConfig G) :
    ∑ z ∈ layers r, faces (slab r (update o j z) l) U ≤ faces (slab r o (l++[j])) U := by
  unfold faces
  rw [slab_sum r o hj]
  refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun p hp => ?_
  unfold face; split_ifs with h h' h'
  · rfl
  · exact False.elim <| h' <| fun y hy => ((lower_pin hj _).mp (h _ hy)).1
  · exact G.chord_nonneg _
  rfl

lemma squares (U : CoverConfig G) {x i j} (hne : i ≠ j) (X : Finset Cover) (hx : x ∈ X)
    (hi : x+step i ∈ X) (hj : x+step j ∈ X) (hij : x+step i+step j ∈ X) :
    G.chord (travel U x (square i j)) ≤ field X U x := by
  let p := PlaqAxes.ordered i j hne
  have he := Finset.single_le_sum (f := fun f => face X U x f) (fun k _ => face_nonneg ..) (Finset.mem_univ p)
  refine le_trans (le_of_eq ?_) he
  rcases lt_or_gt_of_ne hne with h|h
  · simp [face,p, PlaqAxes.ordered,h.le, square_corners,hx,hi,hj,hij,faceValue]
  have hh : x+step j+step i ∈ X := by rw [add_right_comm]; exact hij
  have ha : travel U x (square j i) = (travel U x (square i j))⁻¹ := oriented_swap (posDir i) (posDir j) x U
  simp [face,p,PlaqAxes.ordered,h.le,square_corners,hh,hx,hi,hj,faceValue,ha]

lemma variation (U : CoverConfig G) {x i j} (h : U (x,j)=1) (h' : U (x+step i,j)=1) :
    |G.chord (U (x+step j,i)) - G.chord (U (x,i))| ≤ G.chord (travel U x (square i j)) := by
  have hi : x+step i+step j-step i=x+step j := by abel
  have hj : x+step i+step j+-step i=x+step j := by abel
  simp only [square,travel,Step.vec_pos,Step.vec_neg,Step.pos_read,Step.neg_read,h,h',hi,hj, add_sub_cancel_right, inv_one,mul_one,one_mul]
  let a := U (x,i)
  let b := U (x+step j,i)
  have he := G.chord_triangle (a*b⁻¹) b
  rw [inv_mul_cancel_right] at he
  have hh := G.chord_triangle (a*b⁻¹)⁻¹ a
  rw [G.chord_inv,show (a*b⁻¹)⁻¹*a=b by group] at hh
  apply abs_le.mpr
  change _ ≤ G.chord b - G.chord a ∧ G.chord b - G.chord a ≤ G.chord (a*b⁻¹)
  exact ⟨by change - G.chord (a*b⁻¹) ≤ _; linarith, by linarith⟩

lemma slide_le (r : ℕ) (o : Cover) {l j} (hj : j ∉ l) (U : CoverConfig G)
    (hs : ∀ x ∈ slab r o (l++[j]), x+step j ∈ slab r o (l++[j]) → U (x,j) = 1)
    {z : ℤ} (hz : z ∈ layers r) (ht : z+1 ∈ layers r) :
    |edges (slab r (update o j (z+1)) l) U-edges (slab r (update o j z) l) U|
      ≤ 4*∑ x ∈ slab r (update o j z) l, field (slab r o (l++[j])) U x := by
  let X := slab r o (l++[j])
  let P := slab r (update o j z) l
  let Q := slab r (update o j (z+1)) l
  have he : P.image (·+step j)=Q := by
    simpa only [add_sub_cancel_left, one_smul] using
      (slab_update_image (r:=r) (o:=o) hj _ _ hz ht)
  have hh (x : Cover) : x ∈ P ↔ x+step j ∈ Q := by rw [← he]; simp
  have hp : P ⊆ X := fun i hi => ((lower_pin hj _).mp hi).1
  have hq : Q ⊆ X := fun i hi => ((lower_pin hj _).mp hi).1
  have sum (f : Cover → ℝ) : (∑ x ∈ Q, f x)=∑ x ∈ P, f (x+step j) := by
    rw [← he, Finset.sum_image]; simp
  have hs' (x) (hx : x ∈ P) (i : Axis) : |perEdge Q U (x+step j) i-perEdge P U x i| ≤ field X U x := by
    have ha : x+step j ∈ Q := (hh x).mp hx
    by_cases h0 : x+step i ∈ P
    · have h1 := (hh (x+step i)).mp h0
      have h2 : x+step j+step i∈ Q := by rw [add_right_comm]; exact h1
      unfold perEdge; rw [if_pos h2,if_pos h0]; exact (variation U (hs _ (hp hx) (hq ha)) (hs _ (hp h0) (hq h1))).trans
        (squares U (axis_orthogonal hx h0 hj rfl) _ (hp hx) (hp h0) (hq ha) (hq h1))
    have h1 : x+step j+step i ∉ Q := by rw [add_right_comm,← hh]; exact h0
    simp only [perEdge,if_neg h0,if_neg h1,sub_zero,abs_zero]; exact field_nonneg ..
  change |edges Q U-edges P U| ≤ _
  unfold edges; rw [sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply le_trans (Finset.sum_le_sum fun i _ ↦ hs' x hx i)
  simp [Axis,X]

lemma window_le {r o l j} (hj : j ∉ l) (U : CoverConfig G)
    (hs : ∀ x ∈ slab r o (l++[j]), x+step j ∈ slab r o (l++[j]) → U (x,j) = 1)
    {z u : ℤ} (hz : z ∈ layers r) (hu : u ∈ layers r) :
    |edges (slab r (update o j z) l) U-edges (slab r (update o j u) l) U|
      ≤ 4*faces (slab r o (l++[j])) U := by
  let X := slab r o (l++[j])
  let C z := slab r (update o j z) l
  let E z := edges (C z) U
  let f (z) := 4*∑ i ∈ C z, field X U i
  have ha (z u : ℤ) (hz : z ∈ layers r) (hu : u ∈ layers r) (h : z ≤ u) :
      |E z-E u| ≤ 4*faces X U := by
    have hy : Finset.Ico z u ⊆ layers r := by
      intro i hi; obtain ⟨ha,hb⟩ := Finset.mem_Ico.mp hi
      exact Finset.mem_Icc.mpr ⟨le_trans (Finset.mem_Icc.mp hz).1 ha, le_trans hb.le (Finset.mem_Icc.mp hu).2⟩
    have he : |E z-E u| ≤ ∑ k ∈ Finset.Ico z u, f k := by
      -- reuse successor inequality
      have ht : (∑ k ∈ Finset.Ico z u,(E k-E (k+1))) = E z-E u := by
        clear hu hy hs
        induction u,h using Int.leInduction with
        | base => simp
        | succ k hx ih =>
          rw [show Finset.Ico z (k+1) = insert k (Finset.Ico z k) by
                ext; simp; omega, Finset.sum_insert (by simp),ih]
          abel
      rw [← ht]; apply (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
      rw [abs_sub_comm]; apply slide_le r o hj U hs (hy hi)
      unfold layers; have H := hy hi; simp only [layers,Finset.mem_Icc, Finset.mem_Ico] at H hu hi ⊢; omega
    have hsum : faces X U = ∑ i ∈ layers r, ∑ x ∈ C i, field X U x := slab_sum _ _ hj _
    rw [hsum,Finset.mul_sum]; apply he.trans; exact Finset.sum_le_sum_of_subset_of_nonneg hy fun i _ _ => mul_nonneg (by linarith) (Finset.sum_nonneg fun k _ => field_nonneg ..)
  change |E z-E u|≤_
  rcases le_total z u with h|h
  · exact ha z u hz hu h
  rw [abs_sub_comm]; exact ha u z hu hz h
end YM.Axial
