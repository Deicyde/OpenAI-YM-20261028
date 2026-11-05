import YM.Branch.Slide

/-!
# Pre-patch fallback and universal branches
-/

set_option autoImplicit false
noncomputable section
namespace YM

open Lattice Wilson Function Finset
open scoped Matrix.Norms.Frobenius BigOperators
namespace Axial
variable {G : Gauge}

def traveller (l : List Axis) (U : CoverConfig G) (p x : Cover) := travel U p (axisRoute p x l)

lemma endpoint (p x : Cover) (l : List Axis) (h : l.Nodup) (he : ∀ i ∉ l, p i=x i) :
    stop p (axisRoute p x l)=x := by
  rw [axisRoute_end p x p l h]; ext i; by_cases H : i ∈ l <;> simp [*, he i]

lemma vertical {r o x p l j z} (hj : j ∉ l) (hl : List.Nodup l)
    (hx : x ∈ slab r o (l++[j])) (hp : p ∈ slab r (update o j z) l)
    (U : CoverConfig G) : gauge (traveller (l++[j]) U p) U (x,j) = 1 := by
  let u := update x j z
  have h0 (y w : Cover) (i : Axis) : axisRoute y w [i] = straight i (w i-y i) := by simp [axisRoute]
  have hh (i : Axis) (hi : i ∈ l) : i ≠ j := by rintro rfl; exact hj hi
  have he : axisRoute p x l = axisRoute p u l := axis_route_support _ _ _ l fun i hi => by simp [u,hh i hi]
  have hq : axisRoute p (x+step j) l = axisRoute p u l := axis_route_support _ _ _ l fun i hi => by simp [u,hh i hi]
  have hd : stop p (axisRoute p u l)=u := endpoint p u l hl fun i hi => by
    rw [(slab_iff.mp hp).2 _ hi]; by_cases H : i=j
    · simp [H,u]
    have hg := (slab_iff.mp hx).2 i (by simp [hi,H]); simp [*,u]
  have hh' := ((lower_pin hj _).mp hp).2
  have hk : u+(x j-p j) • step j=x := by ext i; by_cases h : i=j <;> simp [*,u]
  unfold Lattice.gauge traveller
  rw [axisRoute_append, axisRoute_append,he,hq,h0, h0,travel_append,travel_append,hd]
  dsimp only
  have hh1 : (x+step j : Cover) j-p j=x j-p j+1 := by simp [add_sub_right_comm]
  rw [hh1,carry_succ,hk]
  group

lemma total_slab {r o l j z} {U : CoverConfig G} (hj : j ∉ l) (hl : List.Nodup l)
    {p} (hp : p ∈ slab r (update o j z) l) (hz : z ∈ layers r) :
    edges (slab r o (l++[j])) (gauge (traveller (l++[j]) U p) U) ≤
      ((layers r).card:ℝ)*(edges (slab r (update o j z) l) (gauge (traveller l U p) U)+4*faces (slab r o (l++[j])) U) := by
  let X := slab r o (l++[j])
  let C u := slab r (update o j u) l
  let V := gauge (traveller (l++[j]) U p) U
  have hv (x) (hx : x∈X) (_ : x+step j∈X) : V (x,j)=1 := vertical hj hl hx hp U
  have slice (x i z) (hx : x ∈ C z) : perEdge X V x i = perEdge (C z) V x i := by
    unfold perEdge; split_ifs with h h' h'
    · rfl
    · have ha := (lower_pin hj _).mp hx
      by_cases hy : i=j
      · subst i; rw [hv _ ha.1 h, G.chord_one]
      exact False.elim (h' ((lower_pin hj _).mpr ⟨h,by simp [Ne.symm hy,ha.2]⟩))
    exact False.elim (h ((lower_pin hj _).mp h').1)
    rfl
  have eq : edges X V=∑ i ∈ layers r, edges (C i) V := by
    unfold edges X
    rw [slab_sum r o hj]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun x hx ↦ sum_congr rfl fun k _ ↦ slice x k i hx
  have eq' : edges (C z) V=edges (C z) (gauge (traveller l U p) U) := by
    have h (i) (hi : i ∈ C z) : traveller (l++[j]) U p i=traveller l U p i := by
      rw [traveller,axisRoute_append]; simp only [axisRoute,List.flatMap_cons,List.flatMap_nil,List.append_nil]
      rw [((lower_pin hj _).mp hi).2, ((lower_pin hj _).mp hp).2,sub_self]; simp [straight,traveller,axisRoute]
    refine sum_congr rfl fun i hi ↦ sum_congr rfl fun a _ ↦ ?_
    unfold perEdge; split_ifs with ha
    · simp only [V,Lattice.gauge,h i hi,h _ ha]
    rfl
  have H (i) (hi : i ∈ layers r) : edges (C i) V ≤ edges (C z) V +4 * faces X U := by
    have hx := (abs_le.mp <| window_le hj V hv hi hz).2
    rw [show faces X U= faces X V from (faces_gauge_symm ..).symm]
    linarith [show edges (C i) V-edges (C z) V ≤ 4*faces X V from hx]
  change edges X V≤_
  rw [eq,← eq']
  exact (sum_le_sum fun i hi => H i hi).trans (by simp [C,X,mul_add])

lemma existence (l : List Axis) (r : ℕ) (o : Cover) (U : CoverConfig G) (hl : l.Nodup) (ho : o ∈ box r) :
    ∃ x ∈ slab r o l, edges (slab r o l) (gauge (traveller l U x) U) ≤
      4*(l.length:ℝ)*(layers r).card*faces (slab r o l) U := by
  induction l using List.reverseRecOn generalizing o with
  | nil =>
    have eq : slab r o []={o} := by ext i; simp only [slab_iff,List.not_mem_nil,not_false_eq_true,true_imp_iff, mem_singleton]; exact ⟨fun h => funext h.2,fun h => ⟨h.symm ▸ ho, congr_fun h⟩⟩
    refine ⟨o, by simp [eq], ?_⟩
    have H (i : Axis) : o+step i≠o := fun h => by have he := congr_fun h i; simp at he
    simp [edges, eq, perEdge,H]
  | append_singleton l j ih =>
    rw [List.nodup_append] at hl
    have hj : j ∉ l := fun h => hl.2.2 j h j (by simp) rfl
    let f z := faces (slab r (update o j z) l) U
    obtain ⟨z,hz,h⟩ := exists_min_image (layers r) f ⟨0,by simp [layers]⟩
    have he := faces_pins hj U (r:=r) (o:=o)
    have ht : (layers r).card*f z ≤ faces (slab r o (l++[j])) U := le_trans (by simp [f,nsmul_eq_mul])
      (le_trans (sum_le_sum (f:=fun _ => f z) fun i hi => h i hi) he)
    obtain ⟨p,hp,hs⟩ := ih (update o j z) hl.1 (update_box ho hz j)
    refine ⟨p, ((lower_pin hj _).mp hp).1, (total_slab hj hl.1 hp hz).trans ?_⟩
    calc
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add_left hs (4*faces (slab r o (l++[j])) U)) (Nat.cast_nonneg _)
      _ ≤ _ := ?_
    simp only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add,Nat.cast_add,Nat.cast_one]
    have hh := mul_le_mul_of_nonneg_left ht (show 0 ≤ 4*(l.length:ℝ)*(layers r).card from by positivity)
    unfold f at hh
    linarith only [hh]

lemma edge_cost (P : RG.Patch) (U : CoverConfig G) (x : P.FrameTag) : P.axialCost U x =
    edges (box P.radius) (gauge (traveller (allAxes x.2) U x.1.val) U) := by
  unfold RG.Patch.axialCost edges
  rw [← Finset.sum_coe_sort (box P.radius)]; apply Finset.sum_congr rfl
  intro i _; refine Finset.sum_congr rfl fun j _ ↦ ?_
  change (if h : _ then _ else _) = perEdge P.sites _ _ j
  unfold perEdge; split_ifs <;> rfl

lemma face_cost (P : RG.Patch) (U : CoverConfig G) : P.facesum U = faces (box P.radius) U := by
  unfold faces RG.Patch.facesum
  rw [← Finset.sum_coe_sort (box P.radius)]; rfl

lemma eligible (P : RG.Patch) (U : CoverConfig G) (C : RG.KernelChoices) (hc : 16 ≤ C.axial_factor) (o : Lattice.Order) :
    ∃ x : P.Points, (x,o)∈ P.eligible C U := by
  let l := allAxes o
  let R := P.radius
  have he := existence l R 0 U ((List.nodup_finRange _).map o.injective) (center_box _)
  have ha (i : Axis) : i ∈ l := List.mem_map.mpr ⟨_,List.mem_finRange _,o.apply_symm_apply i⟩
  rw [show slab R 0 l = box R by ext i; simp only [slab_iff,ha,not_true,false_imp_iff,forall_const,and_true]] at he
  obtain ⟨x,hx,H⟩ := he
  refine ⟨⟨x,hx⟩,?_⟩
  unfold RG.Patch.eligible
  simp only [mem_filter,mem_univ,true_and, edge_cost,face_cost]
  apply H.trans
  rw [card_layers,show l.length=4 by simp [l,allAxes]]
  push_cast
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) ?_) (faces_nonneg ..)
  positivity

/-- All thresholds independent of P,L,J. -/
lemma viable (G : Gauge) (κ : ℝ) (hn : 0 < κ) : ∃ C : RG.KernelChoices, C.penalty=κ ∧
    ∀ P : RG.Patch, P.Branches C G := by
  obtain ⟨δ,h,H⟩ := RG.frame_unique G
  obtain ⟨ε,w,W⟩ := RG.predictor_unique G
  refine ⟨⟨κ,δ,ε,16,hn,h,w,by norm_num⟩,rfl,fun P => ⟨H _ le_rfl _, W _ le_rfl _, fun U => ?_⟩⟩
  obtain ⟨x,hx⟩ := eligible P U ⟨κ,δ,ε,16,hn,h,w,by norm_num⟩ le_rfl 1; exact ⟨_,hx⟩
end Axial
end YM
