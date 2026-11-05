import YM.Next.RANK.Sky



/-!
# The physical tree stencil for making marks

Literal ordered axial gauge path (from tagged center). Each internal link in
that gauge has an exact expression as a product of oriented positive faces
inside, with their actual transport to that same tree frame. FaceEach data
reused in all linear cochain tests at the beginning k stage. This tree is in
a lifted, fitting box and has *different purpose* from the global torus
elimination in Axial.lean. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Spindle
open Lattice Wilson RG Beamer MeasureTheory Set Function
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side} {R : ℕ}

-- tree path recurrence. rank of last nonzero entry determines next vertical

def north (x : Cover) := (Finset.univ.filter fun i => x i ≠ 0)
private lemma at_north (x : Cover) (h : x ≠ 0) : (north x).Nonempty := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp h; exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩

def last (x : Cover) (h : x ≠ 0) : Axis := Finset.max' _ (at_north x h)
lemma last_has (x : Cover) (h : x ≠ 0) : x (last x h)≠0 := (Finset.mem_filter.mp (show last x h ∈ north x from (Finset.max'_mem _ _))).2
lemma last_le (x : Cover) (h : x ≠ 0) (i : Axis) (hx : x i ≠ 0) : i≤last x h := Finset.le_max' (north x) i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩)
lemma last_clear (x : Cover) (h : x ≠ 0) (i : Axis) (he : last x h < i) : x i=0 := not_not.mp fun hx => not_lt_of_ge (last_le x h i hx) he
lemma tail {x : Cover} (h : x≠0) {i : Axis} (hp : x i≠0) (hx : ∀ j>i,x j=0) : last x h=i := by
  have he := last_le x h i hp
  by_contra hh
  exact last_has x h (hx _ (lt_of_le_of_ne he (Ne.symm hh)))
private lemma opposite (x : Cover) {i : Axis} (h : x i<0) : street (x+step i)+1=street x := by
  rw [← mirror_road x, ← mirror_road (x+_), neg_add, ← sub_eq_add_neg]; exact once_road _ (by exact neg_pos.mpr h)

private lemma keeps_sub {x : Cover} (h : x∈box R) {i : Axis} (hi : 0<x i) : x-step i ∈ box R := by
  rw [box_test] at *; constructor <;> intro j <;> have hj:=h.1 j <;> have hg:=h.2 j <;> (by_cases hp : j=i <;> simp only [Pi.sub_apply, step_apply, hp,↓reduceIte] <;> first | omega | grind)
private lemma keeps_add {x : Cover} (h : x∈box R) {i : Axis} (hi : x i<0) : x+step i ∈ box R := by
  rw [box_test] at *; constructor <;> intro j <;> have hj:=h.1 j <;> have hg:=h.2 j <;> (by_cases hp : j=i <;> simp only [Pi.add_apply, step_apply, hp,↓reduceIte] <;> first | omega | grind)

private def up (x : Cover) (h : x≠0) := if x (last x h)<0 then x+step (last x h) else x-step (last x h)
private def letsWalk (x : Cover) (h : x≠0) := if x (last x h)<0 then negDir (last x h) else posDir (last x h)
private lemma uphill {x : Cover} (h : x≠0) : street (up x h)+1=street x := by
  unfold up; split
  · exact opposite x (by assumption)
  exact once_road x (by have h := last_has x h; omega)
private lemma up_box {x : Cover} (h : x≠0) (he : x∈box R) : up x h∈box R := by
  unfold up; split
  · exact keeps_add he (by assumption)
  exact keeps_sub he (by have hi := last_has x h; omega)
private lemma up_end {x : Cover} (h : x≠0) : up x h+(letsWalk x h).vec=x := by unfold up letsWalk; split<;> simp [*,sub_eq_add_neg]

def paths (x : Cover) : Walk := if h : x≠0 then paths (up x h)++[letsWalk x h] else []
  termination_by street x
  decreasing_by have hx := uphill h; omega

@[simp] lemma paths_zero : paths 0=[] := by rw [paths]; simp
lemma stops (x : Cover) : stop (0 : Cover) (paths x)=x := by
  rcases eq_or_ne x 0 with hx|hx
  · subst x; simp [stop]
  rw [paths,dif_pos hx,stop_append,stops (up x hx)]; exact up_end _
  termination_by street x
  decreasing_by have hx:= uphill hx; omega
lemma lengths (x : Cover) : (paths x).length=street x := by
  rcases eq_or_ne x 0 with hx|hx
  · subst x; simp [empty_road]
  rw [paths,dif_pos hx,List.length_append,lengths (up x hx)]; exact uphill _
  termination_by street x
  decreasing_by have hx:= uphill hx; omega
lemma bounded {x : Cover} (h : x ∈ box R) : street x ≤ 4*R := by
  obtain ⟨he,hp⟩ := box_test.mp h
  calc
    _ ≤ ∑ _ : Axis, R := Finset.sum_le_sum fun i _ => (show (x i).natAbs ≤ R from by have := he i; have := hp i; omega)
    _ = _ := by simp [Axis]
private lemma visit_append {x y : Cover} (a b : Walk) (h : y ∈ visits x (a++b)) : y∈visits x a ∨ y∈visits (stop x a) b := by
  induction a generalizing x with
  | nil => exact Or.inr h
  | cons i l H =>
    change y∈_ ∨ y∈visits (stop (x+i.vec) l) b
    change y∈x::visits (x+i.vec) (l++b) at h
    rcases List.mem_cons.mp h with h|h
    · exact Or.inl (List.mem_cons.mpr (Or.inl h))
    exact (H h).imp_left fun a => List.mem_cons.mpr (Or.inr a)
lemma village (x : Cover) (h : x∈box R) (y) (hy : y∈visits 0 (paths x)) : y ∈ box R := by
  rcases eq_or_ne x 0 with hx|hx
  · subst x; simp only [paths_zero,visits,List.mem_singleton] at hy; exact hy ▸ h
  rw [paths,dif_pos hx] at hy
  obtain he|he := visit_append _ _ hy
  · exact village (up x hx) (up_box hx h) _ he
  rw [stops] at he; simp only [visits,List.mem_cons,up_end,List.not_mem_nil,or_false] at he
  exact he.elim (fun e => e ▸ up_box hx h) fun e => e ▸ h
  termination_by street x
  decreasing_by have hx':= uphill hx; omega

section field
variable (U : CoverConfig G)

def leaves (x : Cover) : G.El := travel U 0 (paths x)
def central := gauge (leaves U) U

lemma climbing (x : Cover) (h : x≠0) : leaves U x=leaves U (up x h)*(letsWalk x h).read U (up x h) := by
  conv_lhs => unfold leaves; rw [paths,dif_pos h,travel_append,stops]; simp only [travel,mul_one]
  rfl

def trunk (x : Cover) (i : Axis) := ∀ j, i< j → x j=0
lemma vertical (x : Cover) (i : Axis) (h : trunk x i) : central U (x,i)=1 := by
  by_cases hi : x i < 0
  · have he : x≠0 := fun H => hi.not_ge (by simp [H])
    have hl := tail he (ne_of_lt hi) h
    have hp := climbing U x he
    simp only [letsWalk,up,hl,if_pos hi,Step.neg_read, add_sub_cancel_right] at hp
    change leaves U x * U (x,i) * (leaves U (x+step i))⁻¹=_; rw [hp]; group
  let y:= x+ step i
  have hJ : 0 < y i := by simp only [y,Pi.add_apply,step_apply,↓reduceIte]; omega
  have he : y≠0 := fun H => hJ.not_ge (by simp [H])
  have hl := tail he (ne_of_gt hJ) (by intro j hj; simp only [y,Pi.add_apply,step_apply,if_neg (ne_of_gt hj),add_zero,h _ hj])
  have hp := climbing U y he
  simp only [letsWalk,up,hl,if_neg (not_lt_of_ge hJ.le)] at hp
  change leaves U x* U (x,i)*(leaves U y)⁻¹=_; rw [hp]; simp [y]
end field

-- positive canonical face list; signs remain exact in all products

def Device (R : ℕ) := Finset.filter (fun (p : Cover × PlaqAxes) => ∀ z∈ visits p.1 (square p.2.val.1 p.2.val.2), z ∈ box R) (box R ×ˢ Finset.univ)
abbrev Turn (R : ℕ) := ↥(Device R)
abbrev Word (R : ℕ) := List (Turn R × Bool)
lemma allowed (z : Cover × PlaqAxes) (h : ∀ x∈ visits z.1 (square z.2.val.1 z.2.val.2), x∈box R) : z ∈ Device R :=
  Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h _ (List.mem_cons_self),Finset.mem_univ _⟩,h⟩
lemma faceOrigin (p : Turn R) : p.val.1 ∈ box R := (Finset.mem_product.mp (Finset.mem_filter.mp p.property).1).1
lemma face_patch (p : Turn R) (x) (h : x∈visits p.val.1 (square p.val.2.val.1 p.val.2.val.2)) : x∈box R := (Finset.mem_filter.mp p.property).2 x h

-- words recorded at cover. unknown using Cov projection.
def played (u : Turn R → G.El) (p : Word R) : G.El := List.prod (p.map fun a => if a.2 then (u a.1)⁻¹ else u a.1)
def used (U : CoverConfig G) (x : Turn R) : G.El := faceValue (central U) x.val

private lemma shifted {x : Cover} {i j : Axis} (h : i<j) (U : CoverConfig G) (hp : trunk x j) :
    faceValue (central U) (x,⟨(i,j),h⟩)=central U (x,i)*(central U (x+step j,i))⁻¹ := by
  have he : trunk (x+step i) j := by intro k hk; have H := ne_of_gt (lt_trans h hk); simp [H,hp k hk]
  unfold faceValue; simp only [square,travel,Step.vec_pos,Step.vec_neg,Step.pos_read,Step.neg_read,show x+step i+step j-step i=x+step j by abel, show x+step i+step j+-step i=x+step j by abel, add_sub_cancel_right,vertical U x j hp,vertical U _ j he,inv_one,mul_one,one_mul]
private def tile (x : Cover) {i j : Axis} (h : i < j) (hx : x ∈ box R) (hi : x+step i ∈ box R) (hj : x+step j ∈ box R) (hk : x+step j+step i∈box R) : Turn R := by
  refine ⟨(x,⟨(i,j),h⟩),allowed _ ?_⟩; intro z hz
  simp only [square_corners, List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with hh|hh|hh|hh|hh
  all_goals subst z
  all_goals first | assumption | rwa [add_right_comm]

theorem rolled (G : Gauge) (x : Cover) (i : Axis) (hx : x∈box R) (hs : x+step i ∈ box R) :
    ∃ p : Word R, p.length ≤ street x ∧ ∀ U : CoverConfig G, central U (x,i)=played (used U) p := by
  by_cases hh : trunk x i
  · exact ⟨[], Nat.zero_le _,fun U => vertical U x i hh⟩
  have ht : x≠0 := fun H => hh (by intro j h; rw [H]; rfl)
  let j:= last x ht
  have he : i<j := lt_of_not_ge fun H => hh (fun k h => last_clear x ht k (lt_of_le_of_lt H h))
  have hg : trunk x j := last_clear x ht
  obtain h|h := lt_or_gt_of_ne (show x j≠0 from last_has x ht); swap
  · let y:= x-step j; have hy : y+step j=x := sub_add_cancel x _
    have hv := keeps_sub hx h
    have h1 : y+step i ∈ box R := by
      rw [show y+step i=x+step i-step j by dsimp [y]; abel]; exact keeps_sub hs (by simp only [Pi.add_apply,step_apply, if_neg (ne_of_gt he),add_zero]; exact h)
    have h2 : trunk y j := by intro k hk; simp [y,ne_of_gt hk,hg k hk]
    obtain ⟨p,hp,H⟩ := rolled G y i hv h1
    let a := tile y he hv h1 (by rwa [hy]) (by rwa [hy])
    refine ⟨(a,true)::p,show p.length+1≤street x from (Nat.succ_le_succ hp).trans_eq (once_road x h),fun U => ?_⟩
    simp only [played,List.map_cons,↓reduceIte,List.prod_cons]
    change central U (x,i)=(used U a)⁻¹*played (used U) p
    rw [← show central U (y,i)=_ from H U,used,show a.val=(y,⟨(i,j),he⟩) from rfl,show faceValue (central U) (y,⟨_,he⟩) = _ from shifted he U h2,hy]; group
  let y := x+step j
  have hv := keeps_add hx h
  have h1 : y+step i ∈ box R := by
    rw [show y+step i=x+step i+step j by dsimp [y]; abel]; exact keeps_add hs (by simp only [Pi.add_apply,step_apply,if_neg (ne_of_gt he),add_zero]; exact h)
  obtain ⟨p,hp,H⟩ := rolled G y i hv h1
  let a:= tile x he hx hs hv h1
  refine ⟨(a,false)::p,show p.length+1≤street x from (Nat.succ_le_succ hp).trans_eq (opposite x h),fun U => ?_⟩
  simp only [played,List.map_cons,Bool.false_eq_true,↓reduceIte,List.prod_cons]; change central U (x,i)=(used U a)*played (used U) p; rw [← show central U (y,i)= _ from H U, used,show a.val=(x,⟨(i,j),he⟩) from rfl,show faceValue (central U) _= _ from shifted he U hg]; dsimp [y]; group
  termination_by street x
  decreasing_by
    all_goals first | (have he' := once_road x h; change street (x-step j)<_; omega) | (have he' := opposite x h; change street (x+step j)<_; omega)
end YM.Next.Rank.Spindle
