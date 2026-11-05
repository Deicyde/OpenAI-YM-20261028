import YM.Branch.Slide


/-!
# Density of coordinate-routed pairs. Native multiplicities.

Independently exchange slots by a permutation of Endpoint PAIRS; avoids
counting intersections multiple times. Valid on the whole box.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Pressure
open Function Lattice RG RG.Patch Axial Wilson Finset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators NNReal
variable {G : Gauge}

lemma per_nn (X : Finset Cover) (U : CoverConfig G) (x i) : 0≤perEdge X U x i := by
  unfold perEdge; split
  · exact G.chord_nonneg _
  rfl

section
variable (r : ℕ)
abbrev Place (r : ℕ) := ↥(box r)
abbrev Height (r : ℕ) := ↥(layers r)
variable (j : Axis)
def slide (x : Place r) (w : Height r) : Place r := ⟨update x.val j w.val, update_box x.property w.property _⟩

def discord (p : List Axis) (x y : Place r) : Place r := ⟨fun i => if i ∈ p then y.val i else x.val i, by
  rw [box_iff_layers]; intro i; split
  · exact (box_iff_layers ..).mp y.property i
  exact (box_iff_layers ..).mp x.property i⟩

def permute (p : List Axis) : Equiv.Perm (Place r × Place r) where
  toFun t := (discord r p t.1 t.2, discord r p t.2 t.1)
  invFun t := (discord r p t.1 t.2, discord r p t.2 t.1)
  left_inv := by
    intro t; apply Prod.ext <;> apply Subtype.ext <;> funext i <;> simp only [discord] <;> split <;> simp_all
  right_inv := by
    intro t; apply Prod.ext <;> apply Subtype.ext <;> funext i <;> simp only [discord] <;> split <;> simp_all

def translateHeight : Equiv.Perm (Place r × Height r) where
  toFun z := (slide r j z.1 z.2,⟨_,(box_iff_layers ..).mp z.1.property j⟩)
  invFun z := (slide r j z.1 z.2,⟨_,(box_iff_layers ..).mp z.1.property j⟩)
  left_inv := by
    intro z; apply Prod.ext <;> apply Subtype.ext <;> simp only [slide,update_self,update_idem,update_eq_self]
  right_inv := by
    intro z; apply Prod.ext <;> apply Subtype.ext <;> simp only [slide,update_self,update_idem,update_eq_self]

lemma marginal (p : List Axis) (f : Place r → ℝ) : ∑ x : Place r, ∑ y : Place r, f (discord r p x y) =
    (box r).card * ∑ x : Place r, f x := by
  rw [← show ∑ a : Place r×Place r,f ((permute r p a).1)=∑ x, ∑ y, f (discord r p x y) from Fintype.sum_prod_type _]
  rw [Equiv.sum_comp (permute r p) (fun z => f z.1),Fintype.sum_prod_type]
  simp [Place, Finset.mul_sum]

lemma slidings (f : Place r → ℝ) : (∑ x : Place r, ∑ i : Height r, f (slide r j x i)) =
    (2*r+1:ℝ)*∑ x : Place r, f x := by
  rw [← show ∑ a : Place r × Height r, f ((translateHeight r j a).1)=∑ x, ∑ y, f (slide r j x y) from Fintype.sum_prod_type _]
  rw [Equiv.sum_comp (translateHeight r j) (fun z => f z.1), Fintype.sum_prod_type]
  simp [Height, Place, Finset.mul_sum, card_layers]

variable (U : CoverConfig G)

lemma positive_step (j : Axis) (x : Cover) (d : ℕ) (h : ∀ k : ℕ, k≤d → x+k • step j ∈ box r) :
    G.chord (travel U x (straight j (d:ℤ))) ≤ ∑ k ∈ range d, perEdge (box r) U (x+k • step j) j := by
  induction d with
  | zero => simp [straight,travel]
  | succ d ih =>
    rw [Nat.cast_add_one,carry_succ, Finset.sum_range_succ, perEdge, if_pos (by rw [add_assoc,show d • step j+step j=(d+1) • (step j:Cover) from (succ_nsmul ..).symm]; exact h _ le_rfl)]
    simp only [natCast_zsmul]
    exact (G.chord_triangle _ _).trans (add_le_add_left (ih (fun k hk => h k (by omega))) _)

lemma upstream (x : Place r) (z : Height r) (hz : x.val j ≤ z.val) : G.chord (travel U x.val (straight j (z.val-x.val j))) ≤
    ∑ w : Height r, perEdge (box r) U (slide r j x w).val j := by
  let d := (z.val-x.val j).natAbs
  have he : (d:ℤ)=z.val-x.val j := by unfold d; omega
  have h (k : ℕ) (hk : k ≤ d) : (x.val j + (k:ℤ)) ∈ layers r := by
    obtain ⟨hq,hy⟩ := Finset.mem_Icc.mp ((box_iff_layers ..).mp x.property j)
    have H := Finset.mem_Icc.mp z.property
    apply Finset.mem_Icc.mpr; omega
  have hl (k : ℕ) : x.val+k • step j = update x.val j (x.val j + (k:ℤ)) := by
    ext i; by_cases hk : i=j <;> simp [*]
  rw [← he]
  apply (positive_step r U j _ d (fun k hk => by rw [hl]; exact update_box x.property (h k hk) _)).trans
  let b (e : ↥(Finset.range d)) : Height r := ⟨x.val j + (e.val:ℤ), h e.val (Finset.mem_range.mp e.property).le⟩
  have hi : Injective b := fun i k he => by
    have hh := congr_arg Subtype.val he; dsimp only [b] at hh; apply Subtype.ext; omega
  rw [← Finset.sum_coe_sort]; simp_rw [hl]
  calc
    _ = ∑ i ∈ (Finset.univ.image b), perEdge (box r) U (slide r j x i).val j := by rw [sum_image hi.injOn]; rfl
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => per_nn ..)

lemma step_cost (x : Place r) (z : Height r) : G.chord (travel U x.val (straight j (z.val-x.val j))) ≤
    ∑ w : Height r, perEdge (box r) U (slide r j x w).val j := by
  by_cases he : x.val j ≤ z.val
  · exact upstream r j U x z he
  let y := slide r j x z
  have hy : y.val j=z.val := update_self ..
  have hb : stop y.val (straight j (x.val j - y.val j))=x.val := by
    rw [straight_stop]; unfold y slide; ext i; by_cases hx : i=j <;> simp [*]
  rw [show travel U x.val (straight j (z.val-x.val j))=(travel U y.val (straight j (x.val j-y.val j)))⁻¹ from by
    rw [← travel_reverse _ U, hb, reverse_straight, hy, neg_sub],G.chord_inv]
  exact (upstream r j U y (⟨x.val j,(box_iff_layers ..).mp x.property j⟩:Height r)
    (by dsimp only; rw [hy]; exact le_of_not_ge (fun h => he h)
    )).trans (by simp only [y,slide,update_idem]; rfl)

lemma route_sum (p : List Axis) (h : p.Nodup) :
    (∑ x : Place r, ∑ y : Place r, G.chord (travel U x.val (axisRoute x.val y.val p))) ≤
      p.length*((box r).card:ℝ)*(2*r+1)*edges (box r) U := by
  induction p using List.reverseRecOn with
  | nil => simp [axisRoute,travel]
  | append_singleton p j ih =>
    rw [List.nodup_append] at h
    have hj : j ∉ p := fun hh => h.2.2 j hh j (by simp) rfl
    have he (x y : Place r) : stop x.val (axisRoute x.val y.val p) = (discord r p x y).val := by rw [axisRoute_end x.val y.val x.val p h.1]; funext i; simp only [discord]; split <;> rename_i hi <;> simp_all
    have hb (x y : Place r) : (discord r p x y).val j=x.val j := if_neg hj
    let F j (u : Place r) := ∑ i : Height r, perEdge (box r) U (slide r j u i).val j
    have ha (x y : Place r) : G.chord (travel U x.val (axisRoute x.val y.val (p++[j]))) ≤ G.chord (travel U x.val (axisRoute x.val y.val p))+F j (discord r p x y) := by
      rw [axisRoute_append,travel_append,he]; apply (G.chord_triangle _ _).trans
      apply add_le_add_right; have hi := step_cost r j U (discord r p x y) (⟨y.val j,(box_iff_layers ..).mp y.property j⟩ : Height r)
      rw [hb] at hi; simp only [axisRoute,List.flatMap_singleton]; exact hi
    apply le_trans (sum_le_sum fun i _ => sum_le_sum fun j _ => ha i j)
    simp_rw [sum_add_distrib]
    rw [marginal r p (F j)]
    have hx : (∑ x : Place r, F j x) ≤ (2*r+1:ℝ)*edges (box r) U := by
      unfold F; rw [slidings r j (fun i => perEdge (box r) U i.val j),edges,← Finset.sum_coe_sort (box r)]
      gcongr
      exact Finset.single_le_sum (f:=fun k : Axis => perEdge (box r) U _ k) (fun k _ => per_nn ..) (Finset.mem_univ j)
    refine (add_le_add (ih h.1) (mul_le_mul_of_nonneg_left hx (by positivity))).trans_eq ?_
    simp only [List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one]; ring
end
end YM.Pressure
