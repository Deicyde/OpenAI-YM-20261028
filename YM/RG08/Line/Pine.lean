import YM.RG08.Line.Golden
import YM.RG08.Rows.Fund

/-!
# A standard repeated-block forest

Independent tree on each centered residue cell, repeated exactly on all periods. Not assumed of
the forest choices on actual Mercies. All walks in a tree's paths are true fine-link paths.
-/
noncomputable section
namespace YM.RG08.Line
open Stationary Function Matrix Lattice Exterior Precision RG Tree Wilson Laurent Bloch
open scoped Matrix BigOperators Topology Classical
set_option autoImplicit false
variable (S : Patch)

def parentDir (x : Cover) : Step := if h:x=0 then posDir 0 else
    have hh : ∃ i,x i≠0 := by contrapose! h; exact funext h
    let i:=hh.choose
    if x i < 0 then posDir i else negDir i

lemma crawl (x : Cover) (he:x≠0) :
    size (x+(parentDir x).vec) < size x ∧ ∀ r,x∈box r → x+(parentDir x).vec ∈ box r := by
  unfold parentDir; rw [dif_neg he]
  let h : ∃ i,x i≠0 := by contrapose! he; exact funext he
  let i:= Classical.choose h
  have hi := Classical.choose_spec h
  change x i ≠ 0 at hi
  let w : Step:= if x i < 0 then posDir i else negDir i
  have ht (j : Axis) (hj:j≠i) : (x+w.vec:Cover) j=x j := by unfold w; split <;> simp [hj]
  have hv : ((x+w.vec:Cover) i).natAbs < (x i).natAbs := by unfold w; split <;> simp <;> omega
  change size (x+w.vec) < size x ∧ ∀ r, x∈box r → x+w.vec∈box r
  constructor
  · refine Finset.sum_lt_sum (s:=Finset.univ) (f:=fun i:Axis=>((x+w.vec:Cover) i).natAbs) (g:=fun i:Axis=>(x i).natAbs) ?_ ⟨i,Finset.mem_univ _,hv⟩
    intro j _
    by_cases hh:j=i
    · subst j; exact hv.le
    rw [ht _ hh]
  intro r hr
  rw [box_iff_layers]; intro j; have hz:=(box_iff_layers ..).mp hr j
  by_cases hh : j=i
  · subst j
    unfold Lattice.layers at *
    simp only [Finset.mem_Icc] at *
    omega
  rw [ht j hh]; exact hz

def walkTree (x : Cover) : Walk := if h:x=0 then [] else
    parentDir x :: walkTree (x+(parentDir x).vec)
termination_by size x
decreasing_by apply (crawl ..).1; exact h

def green {c f : Side} (T : StepData c f) : Forest T.ratio where
  up x:=parentDir (lift (T.ratio.residue x))
  height x:= size (lift (T.ratio.residue x))
  bound x:= by
    let y:=lift (T.ratio.residue x)
    have hk:=T.ratio.half_box T.patch.odd_side (T.ratio.residue x)
    have he(i:Axis): (y i).natAbs ≤ T.ratio.count.val := by
      have h:=(box_iff_layers ..).mp hk i
      unfold Lattice.layers at h; rw [Finset.mem_Icc] at h
      change -( (T.ratio.count.val/2:ℕ):ℤ ) ≤ y i ∧ y i ≤ _ at h
      omega
    apply (Finset.sum_le_sum (fun i (_:i∈Finset.univ)=> he i)).trans
    simp
  rise x hx:= by
    let p:=T.ratio.residue x; let y:=lift p
    have h : y≠0:= by
      intro hv; apply hx; apply (T.ratio.root_id x).2; have ht:= wrap_lift p; change wrap _ y=p at ht; rw [hv,map_zero] at ht; exact ht.symm
    have he:=T.ratio.internal (x:=x) (i:=parentDir y) T.patch.odd_side ((crawl y h).2 _ (T.ratio.half_box T.patch.odd_side p))
    rw [he.1]; exact (crawl y h).1
  stays x hx:= by
    let p:=T.ratio.residue x; let y:=lift p
    have h : y≠0:= by
      intro hv; apply hx; apply (T.ratio.root_id x).2
      have hh:=wrap_lift p
      change wrap _ y=p at hh; rw [hv,map_zero] at hh; exact hh.symm
    exact (T.ratio.internal T.patch.odd_side ((crawl y h).2 _ (T.ratio.half_box T.patch.odd_side p))).2

theorem repeat_tree {c f:Side} (T:StepData c f) (x:Site f):
    (green T).hike x=walkTree (lift (T.ratio.residue x)) := by
  induction x using Forest.hike.induct (green T) with
  | case1 x h he =>
    let P:=T.ratio.residue x; let y:=lift P
    have h0 : y≠0 := by intro hv; apply h; apply (T.ratio.root_id x).2; have ht:= wrap_lift P; change wrap _ y=P at ht; rw [hv,map_zero] at ht; exact ht.symm
    have hv:=T.ratio.internal (x:=x) (i:=parentDir y) T.patch.odd_side ((crawl y h0).2 _ (T.ratio.half_box T.patch.odd_side P))
    rw [Forest.hike,dif_pos h, walkTree,dif_neg h0,he]; exact congr_arg _ (congr_arg walkTree hv.1)
  | case2 x h =>
    have he:= (T.ratio.root_id x).mp (Classical.not_not.mp h)
    rw [Forest.hike,dif_neg h,he,walkTree]; simp
end YM.RG08.Line
