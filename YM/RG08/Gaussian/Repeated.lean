import YM.RG08.Gaussian.TreeInverse

/-! # The fixed, repeated tree used for the formal conditional expansion.
Admit any internal tree of bounded block height paid post-L. Provide a
canonical one, always adjusting the least nonzero axis. The in-block test
prevents accidental crossing due to modulo of a one-cell period. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Function Filter Lattice Wilson RG Precision Bloch Laurent Work.F08 Tree Finset
open Stationary
open scoped Topology BigOperators

variable {L c f : Side}

structure Repeated (L : Side) where
  up : Site L → Step
  height : Site L → ℕ
  bound x : height x ≤ 4*L.val
  rise x : x ≠ 0 → height (arrives x (up x).vec) < height x
  stays x : x ≠ 0 → carry x (up x).vec = 0

namespace Repeated
variable (r : Ratio c f)

def forest (X : Repeated r.count) : Forest r where
  up x := X.up (r.residue x)
  height x := X.height (r.residue x)
  bound x := X.bound _
  rise x h := by
    obtain hh := mt (r.root_id x).2 h
    rw [← wrap_vec f, moves_residue]
    exact X.rise _ hh
  stays x h := by
    obtain hh := mt (r.root_id x).2 h
    rw [← wrap_vec f, moves_parent, X.stays _ hh, map_zero,add_zero]

def path (X : Repeated L) (x : Site L) : Walk :=
    if _h : x≠0 then X.up x :: X.path (arrives x (X.up x).vec) else []
termination_by X.height x
decreasing_by exact X.rise x _h

lemma branches (X : Repeated r.count) (x : Site f) : (X.forest r).hike x=X.path (r.residue x) := by
  induction x using Forest.hike.induct (X.forest r) with
  | case1 x h IH =>
    rw [Forest.hike,dif_pos h,path,dif_pos (mt (r.root_id x).2 h), IH]
    change X.up (r.residue x) :: X.path (_) = X.up (r.residue x) :: _
    rw [← wrap_vec f, moves_residue]; rfl
  | case2 x hx =>
    have he : r.residue x=0 := (r.root_id x).1 (Classical.not_not.mp hx)
    rw [Forest.hike,dif_neg hx,path,dif_neg (not_not.mpr he)]

/-- Positive edges at residues *occupied* (at the actual edge-start, not
    necessarily the child). -/
def logs (X : Repeated L) := Finset.image (fun x : Site L => (X.up x).used x) (Finset.univ.erase 0)
lemma arrives_step (x : Site L) (s : Step) : arrives x s.vec = x+s.vec := by rw [Work.F08.arrives,map_add,wrap_lift,wrap_vec]
lemma leaf_places (X : Repeated r.count) {x : Site f} (h : leaf r x) :
    let i := X.forest r|>.up x
    let j := i.used x; let k := i.used (r.residue x)
    r.residue j.1=k.1 ∧ r.parent j.1=r.parent x ∧ j.2=k.2 := by
  intro i j k
  have hh : r.residue x ≠ 0 := mt (r.root_id x).2 h
  have ht : r.parent (x+i.vec)=r.parent x := (X.forest r).stays x h
  have hc : r.residue (x+i.vec)=r.residue x+i.vec := by rw [← wrap_vec f i,moves_residue,arrives_step]
  unfold j k; cases hi : i with
  | mk a b => cases b <;> simp only [Step.used] <;> first
    | exact ⟨rfl,rfl,rfl⟩
    | (rw [hi] at ht hc; simp only [Step.vec,↓reduceIte,← sub_eq_add_neg] at ht hc; exact ⟨hc,ht,rfl⟩)
lemma trunks (X : Repeated r.count) (x : Edge (Site f)) :
    x ∈ (X.forest r).trunks ↔ (r.residue x.1,x.2)∈ X.logs := by
  rw [Forest.trunk_mem_iff,logs,mem_image]
  constructor
  · rintro ⟨i,h,rfl⟩; obtain ⟨hh,_,hy⟩ := leaf_places r X h
    exact ⟨_,mem_erase.mpr ⟨mt (r.root_id i).2 h,mem_univ _⟩,Prod.ext hh.symm hy.symm⟩
  rintro ⟨i,hi,h⟩; let b := r.assemble (r.parent x.1,i)
  have hb : r.residue b=i := r.assemble_res _
  have hx : (X.forest r).up b=X.up i := congr_arg X.up hb
  have hv : leaf r b := by
    refine mt (r.root_id b).1 ?_; rw [hb]; exact (mem_erase.mp hi).1
  refine ⟨b,hv,?_⟩
  obtain ⟨hi,hg,hm⟩ := leaf_places r X hv
  rw [hx,hb,h] at hi hm; rw [hx] at hg
  rw [hx]; apply Prod.ext _ hm
  have he := congr_arg r.assemble (show (r.parent ((X.up i).used b).1, r.residue ((X.up i).used b).1)=(r.parent x.1,r.residue x.1) from Prod.ext (hg.trans (r.assemble_parent _)) hi)
  simpa [Ratio.assemble,r.unpack_at] using he

section order

def candidates (x : Site L) := Finset.univ.filter fun i => (lift x i)≠0
lemma candidates_ne {x : Site L} (h : x≠0) : (candidates x).Nonempty := by
  obtain ⟨i,hi⟩ : ∃ i,lift x i≠0 := by
    by_contra! H
    have hv : lift x=0 := funext H
    exact h ((wrap_lift x).symm.trans ((congr_arg (wrap L) hv).trans (map_zero _)))
  exact ⟨i,mem_filter.mpr ⟨mem_univ _, hi⟩⟩
def orderStep (x : Site L) :=
    if h : (candidates x).Nonempty then
      let i := (candidates x).min' h
      if lift x i < 0 then posDir i else negDir i
    else posDir 0
lemma order_cost (hp : Odd L.val) (x : Site L) (h : x≠0) :
    let a := (orderStep x).vec (R:=ℤ)
    carry x a=0 ∧ size (lift (arrives x a))<size (lift x) := by
  intro a
  have hc := candidates_ne h; let i := (candidates x).min' hc
  have hx : lift x i ≠ 0 := (mem_filter.mp (min'_mem _ hc)).2
  have hi j (hj : j≠i) : a j=0 := by unfold a; rw [orderStep,dif_pos hc]; dsimp only; split <;> simp [*, ← show i=(candidates x).min' hc from rfl]
  have hu : ((lift x+a) i).natAbs < (lift x i).natAbs := by
    rw [Pi.add_apply]; unfold a; rw [orderStep, dif_pos hc]; change (lift x i+(Step.vec (if lift x i < 0 then posDir i else negDir i) : Cover) i).natAbs<_; split <;> simp_all <;> omega
  let v := lift x + a
  have he : lift (arrives x a)=v := by
    apply lift_eq_iff.mpr
    obtain ⟨d,hd⟩ := hp
    refine ⟨rfl,fun j => ?_⟩
    have hs := lift_centers x j
    rcases eq_or_ne j i with H|H
    · subst j; change (v i).natAbs < _ at hu; omega
    simpa [v,hi j H] using hs
  have hW := carry_spec x a
  constructor
  · rw [he] at hW
    have hr : L.val • carry x a=0 := by change v=v+ _ at hW; exact (left_eq_add.mp hW)
    funext j; have hJ := congr_fun hr j
    simp only [Pi.smul_apply,Pi.zero_apply,nsmul_eq_mul] at hJ
    exact (mul_eq_zero.mp hJ).resolve_left (by positivity)
  rw [he]
  refine sum_lt_sum ?_ ⟨i,mem_univ _, hu⟩
  intro j _; rcases eq_or_ne j i with H|H
  · subst j; exact hu.le
  unfold v; simp [hi j H]

/-- Nearest-root path ordered by standard axes, even at one-cell periods. -/
def axisRule (L : Side) (ho : Odd L.val) : Repeated L where
    up := orderStep
    height x := size (lift x)
    stays x hx := (order_cost ho x hx).1
    rise x hx := (order_cost ho x hx).2
    bound x := le_trans (sum_le_sum (g:=fun _ : Axis => L.val)
      (fun i _ => by have h := lift_centers x i; omega)) (by simp [Axis])
end order
end Repeated
end YM.RG08
