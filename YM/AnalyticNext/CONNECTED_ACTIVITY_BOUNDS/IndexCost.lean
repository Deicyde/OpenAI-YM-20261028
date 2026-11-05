import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Speed
import YM.Push.ABSOLUTE_SUMS.Footprint


/-!
# Complete positional and Schur footprints of the counted array

(Not yet clamp, branch or record extension work.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Turn
open Matrix Work.F03 Progress.StationaryScenes Push.AbsoluteSums Tree
open Win  Animals
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

section sites
variable {ι κ : Type*} [Fintype ι] [Fintype κ] (d : ι → Site c) {P Q : ℝ}
open Finset Corona

lemma population_copy (hd : governs d P) :
    governs (fun i : ι×κ => d i.1) (P*Fintype.card κ) := by
  intro x r
  let E : ι → Prop := fun i => separation x (d i) ≤ r
  have he : ((univ : Finset (ι×κ)).filter fun i => separation x (d i.1) ≤ r) ⊆
      (univ.filter fun i => separation x (d i) ≤ r) ×ˢ univ := fun i hi => mem_product.mpr
    ⟨mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2⟩,mem_univ _⟩
  have ht := card_le_card he
  apply (Nat.cast_le (α:=ℝ).mpr ht).trans; rw [card_product,card_univ,Nat.cast_mul]; apply le_trans
    (mul_le_mul_of_nonneg_right (hd x r) (by positivity)) (le_of_eq (by ring))

lemma population_signed (hd : governs d P) :
    governs (fun i : Signed × ι => i.1.act (d i.2)) (Fintype.card Signed*P) := by
  intro x r
  let Y := univ.filter fun i : Signed×ι => separation x (i.1.act (d i.2)) ≤ r
  have hs (p : Signed) : (((Y.filter fun i => i.1=p).card:ℕ):ℝ) ≤ P * (1+(r:ℝ))^4 := by
    let V := Y.filter (fun i => i.1=p)
    let W := univ.filter fun i => separation (p⁻¹.act x) (d i) ≤ r
    have he : V ⊆ ({p} ×ˢ W) := by
      rintro ⟨s,i⟩ h; obtain ⟨hn,h⟩ := mem_filter.mp h
      change s=p at h; subst p; refine mem_product.mpr ⟨by simp,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
      rw [← separation_signed (s⁻¹.act x) (d i) s, s.act_inv]; exact (mem_filter.mp hn).2
    have hp := card_le_card he; rw [card_product,card_singleton,one_mul] at hp
    exact (Nat.cast_le.mpr hp).trans (hd _ _)
  change (Y.card:ℝ) ≤ _
  calc
    _ = ∑ p : Signed, (((Y.filter fun i => i.1=p).card:ℕ):ℝ) := by
      simpa using (sum_fiberwise_of_maps_to (g:=Prod.fst) (t:=univ) (s:=Y) (fun _ _ => mem_univ _) (fun _ => (1:ℝ))).symm
    _ ≤ ∑ _ : Signed,P*(1+(r:ℝ))^4 := sum_le_sum fun i _ => hs i
    _ = _ := by simp [mul_assoc]

lemma population_add (q : κ→Site c) (h : governs d P) (he : governs q Q) : governs (Sum.elim d q) (P+Q) := by
  intro x r
  let s := univ.filter (fun i=> separation x (d i) ≤ r); let t := univ.filter (fun i=> separation x (q i) ≤ r)
  have hi : (univ.filter (fun i : ι⊕κ => separation x (Sum.elim d q i)≤r))⊆s.disjSum t := by
    rintro (i|i) hi
    · exact inl_mem_disjSum.mpr (Finset.mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩)
    exact inr_mem_disjSum.mpr (mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩)
  apply (Nat.cast_le.mpr (card_le_card hi)).trans
  rw [card_disjSum,Nat.cast_add,add_mul]; exact add_le_add (h _ _) (he _ _)

lemma population_physical (c : Side) : governs (id:Site c → Site c) 16 := by
  intro x r
  have he : (univ.filter (fun i=>separation x i≤r)) ⊆ neighbors r x := fun i hi =>
    (neighbors_mem ..).mpr (mem_filter.mp hi).2
  apply (Nat.cast_le (α:=ℝ).mpr ((card_le_card he).trans (neighbors_card ..))).trans
  unfold ballCost; push_cast; rw [show (16:ℝ) = 2^4 by norm_num, ← mul_pow]; gcongr; linarith

lemma population_parent (q : Ratio c f) : governs q.parent ((q.count.val:ℝ)^4*16) := by
  intro x r
  have he : (univ.filter (fun i=> separation x (q.parent i)≤r)) ⊆
      univ.filter (fun i=> q.parent i∈univ.filter (fun i : Site c => separation x i ≤ r)) := fun i hi =>
    mem_filter.mpr ⟨mem_univ _,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩⟩
  apply (Nat.cast_le (α:=ℝ).mpr ((card_le_card he).trans (Footprint.crowd q _))).trans
  rw [Nat.cast_mul,Nat.cast_pow]; exact (mul_le_mul_of_nonneg_right (population_physical c x r) (by positivity)).trans_eq
    (by ring)
end sites

def density_home (L : Side) : ℝ := ((L.val:ℝ)^4*16)*Fintype.card Axis
def density_variables (G : Gauge) (L : Side) : ℝ := density_home L*Fintype.card G.ColorIndex

def density_item (L : Side) : ℝ := (Fintype.card Signed:ℝ) *
    ((((L.val:ℝ)^4*16)*Fintype.card PlaqAxes)*Fintype.card Bool + 16*Fintype.card Axis)

def density_orbit (G : Gauge) (L : Side) : ℝ := density_item L*Fintype.card G.ColorIndex

lemma governs_home (S : StepData c f) : governs (home S) (density_home S.patch.L) :=
    population_copy (κ:=Axis) S.ratio.parent (population_parent _)

lemma governs_vars (S : StepData c f) : governs (fun i : Vars G f => home S i.1) (density_variables G S.patch.L) :=
  population_copy (home S) (governs_home S)

lemma governs_item (S : StepData c f) : governs (base S) (density_item S.patch.L) :=
  population_signed (center S)
    (population_add _ _
      (population_copy (κ:=Bool) (fun i : Cell f => S.ratio.parent i.1) (population_copy
        (κ:=PlaqAxes) S.ratio.parent (population_parent S.ratio)))
      (population_copy (κ:=Axis) (id:Site c → Site c) (population_physical c)))

lemma governs_Ix (S : StepData c f) : governs (fun i : Ix G S => base S i.1) (density_orbit G S.patch.L) :=
  population_copy (base S) (governs_item S)

def drow (S : StepData c f) (i : Ix G S) := base S i.1
def dcol (S : StepData c f) (i : Vars G f) := home S i.1

section receipts

-- Prices doesn't imply direction gap.
open Green
variable (S : StepData c f) (T : Tube G S) (F : Forest S.ratio) (A : Stores S) (V : Config G c) (x : ℝ)

structure GramCost (ν C : ℝ) : Prop where
  unmasked : Both (drow S) (dcol S) (scale T x V) ν C C
  affine : Both (drow S) (dcol S) (Dmat T F x A V) ν C C
  price : Both (dcol S) (dcol S) (gram T F x A V) ν (C^2+1) (C^2+1)
  rangeB (i j : Vars G f) : gram T F x A V i j≠0 → separation (dcol S i) (dcol S j) ≤ 2*stencilD S.patch (till x)

lemma stencil (P : Teller G) (hT : P.Funds S T) (η ν C : ℝ) (hC : 0 ≤ C) (hn : 0≤ν) (hη : ν<η)
    (hc : ∀ i j, Green.wt η (drow S i) (dcol S j) * |scale T x V i j| ≤ C) :
    let Y := max (density_orbit G S.patch.L) (density_variables G S.patch.L)
    GramCost S T F A V x ν (planePrice Y (η-ν)*C) := by
  intro Y
  have hp : 0 ≤ Y := le_max_of_le_left (by unfold density_orbit density_item; positivity)
  have h1 : governs (dcol (G:=G) S) Y := fun a b => (governs_vars (G:=G) S a b).trans
    (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity))
  have h2 : governs (drow (G:=G) S) Y := fun a b => (governs_Ix (G:=G) S a b).trans
    (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity))
  let L := planePrice Y (η-ν)*C
  have hg : 0 ≤ L := mul_nonneg (Win.planePrice_nn hp (sub_pos.mpr hη)) hC
  have hs i j : |Dmat T F x A V i j| ≤ |scale T x V i j| := by unfold Dmat; rw [Matrix.of_apply]; split <;> simp
  have ht : Both (drow S) (dcol S) (Dmat T F x A V) ν L L :=
    point_both h1 h2 hp hp hη hC fun i j => ((mul_le_mul_of_nonneg_left (hs i j) (wt_pos ..).le).trans
      (hc i j))
  refine ⟨point_both h1 h2 hp hp hη hC hc, ht, ?_, ?_⟩
  · unfold gram
    simp_rw [pow_two]
    apply plusBoth (timesBoth hn (both_transpose ht) ht hg hg)
    let M := Matrix.diagonal (fun j : Vars G f => if j.1 ∉ activeB A F (radiusB x) then (1:ℝ) else 0)
    have hy : Rows (dcol S) (dcol S) M ν 1 := by
      intro i; dsimp only [M]; rw [Finset.sum_eq_single i (fun j _ hj => ?_) (by simp), diagonal_apply_eq]
      · split <;> simp [wt]
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hj),abs_zero,mul_zero]
    exact ⟨hy,by change Rows (dcol S) (dcol S) M.transpose ν 1; rw [show M.transpose = M from Matrix.isSymm_diagonal _]; exact hy⟩
  intro i j hi; contrapose! hi; unfold gram
  rw [Matrix.add_apply, Matrix.diagonal_apply_ne _ ?_,add_zero,Matrix.mul_apply]; swap
  · rintro e; simp [e] at hi
  apply Finset.sum_eq_zero
  intro q _; rw [Matrix.transpose_apply]
  have hx l (he : stencilD S.patch (till x)<separation (drow S q) (dcol S l)) : Dmat T F x A V q l=0 := by
    have hi := hs q l
    rw [tangent_support T hT x V q l he, abs_zero] at hi
    exact abs_eq_zero.mp (le_antisymm hi (abs_nonneg _))
  by_cases h : stencilD S.patch (till x)<separation (drow S q) (dcol S i)
  · rw [hx i h,zero_mul]
  have hh := separation_triangle (dcol S i) (drow S q) (dcol S j)
  rw [separation_comm _ (drow S q)] at hh
  rw [hx j (by omega),mul_zero]

end receipts

open Green

theorem gram_budget (P : Teller G) (D : Patch) (h : D.Branches P.bind G) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), P.Funds S T → S.patch=D →
    ∀ (F : Forest S.ratio) (A : Stores S) (V : Config G c) (x : ℝ), GramCost S T F A V x (P.top.width/2) C := by
  obtain ⟨C,hC,H⟩ := received P D h
  let Y := max (density_orbit G D.L) (density_variables G D.L)
  let s := P.top.width; let T := planePrice Y (s-s/2)*C
  have hs : 0 < s := P.top.width_pos
  have hv : 0 ≤ Y := le_max_of_le_left (by unfold density_orbit density_item; positivity)
  have hy : 0 ≤ T := mul_nonneg (planePrice_nn hv (by linarith)) hC.le
  refine ⟨1+T,by positivity,fun c f S K hk hS F A V x => ?_⟩
  obtain ⟨h1,h2,h3,h4⟩ := stencil S K F A V x P hk s (s/2) C hC.le (by positivity)
    (half_lt_self hs) (H c f S K hk hS x V)
  have hl : T=planePrice (max (density_orbit G S.patch.L) (density_variables G S.patch.L)) (s-s/2)*C := by simp [T,Y,hS]
  rw [← hl] at h1 h2 h3
  have hq : T ≤ 1+T := le_add_of_nonneg_left zero_le_one
  exact ⟨monoBoth h1 le_rfl hq hq,monoBoth h2 le_rfl hq hq,monoBoth h3 le_rfl (by gcongr) (by gcongr),h4⟩
end YM.AnalyticNext.ConnectedActivity.Aff
