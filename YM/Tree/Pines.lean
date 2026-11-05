import YM.Lattice.Crossing
import YM.Exterior.Complex

/-!
# Slices over actual centered roots

Chosen independently per physical coarse site in applications. Branches can
prove for arbitrary Forest; for integration over choices must bind before
reusing addresses. Parent/projection is part of the scale data, not inferred
from a user's arbitrary tree. Heights ≤ 4L. Frame patch minimizing may
not be any of these trees. `within` later takes statement on residual gauges
constant on each tree slice block. No ambiguity on crossing when c>1.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Tree
open Lattice Filter MeasureTheory Laurent
open scoped Matrix.Norms.Frobenius Topology BigOperators
variable {c f : Side} {g : Ratio c f}

def leaf (g : Ratio c f) (x : Site f) : Prop := g.parent x |> fun i => x≠g.embed i
instance (g : Ratio c f) : DecidablePred (leaf g) := by intro x; unfold leaf; infer_instance

structure Forest (g : Ratio c f) where
  up : Site f → Step
  height : Site f → ℕ
  bound i : height i ≤ 4*g.count.val
  rise i : leaf g i → height (i+(up i).vec)<height i
  stays i : leaf g i → g.parent (i+(up i).vec)=g.parent i

/-- local potential existence: use first misplaced coordinate per vertex (later
may randomize independently per patch) -/
theorem select (g : Ratio c f) (hp : Odd g.count.val) : Nonempty (Forest g) := by
  let q (i : Site f) := Lattice.lift (g.residue i)
  let m (i : Site f) := Laurent.size (q i)
  let L := g.count.val/2
  have hb (x : Site f) : m x ≤ 4*g.count.val := by
    have h (i : Axis) := (box_iff_layers ..).mp (g.half_box hp (g.residue x)) i
    apply le_trans (b:=∑ _ : Axis, g.count.val) (Finset.sum_le_sum fun i _ ↦ ?_) (by simp [Axis])
    have hi : q x i ∈ Finset.Icc (-(L:ℤ)) L := h i
    rw [Finset.mem_Icc] at hi
    change (q x i).natAbs ≤ g.count.val
    unfold L at hi; omega
  have he (x : Site f) : ∃ i : Step, leaf g x →
      m (x+i.vec)<m x ∧ g.parent (x+i.vec)=g.parent x := by
    by_cases hx : leaf g x
    · obtain ⟨a,ha⟩ : ∃ a : Axis, q x a≠0 := by
        by_contra! h
        have hi : q x=0 := funext h
        apply hx; apply (g.root_id x).mpr
        rw [← wrap_lift (g.residue x)]; change wrap _ (q x)=0; rw [hi,map_zero]
      let d := if q x a < 0 then posDir a else negDir a
      refine ⟨d, fun _ ↦ ?_⟩
      have hh (i : Axis) (hi : i ≠ a) : (q x + d.vec : Cover) i=q x i := by unfold d; split <;> simp [hi]
      have hz : (q x + d.vec : Cover)∈box L := by
        rw [box_iff_layers]; intro i
        have hk := (box_iff_layers ..).mp (g.half_box hp (g.residue x)) i
        by_cases H : i=a
        · subst i
          change q x a∈ Finset.Icc (-(L:ℤ)) L at hk
          unfold d layers; split <;> simp at * <;> omega
        rw [hh i H]; exact hk
      obtain ⟨e1,e2⟩ := g.internal hp hz; refine ⟨?_,e2⟩
      unfold m; rw [show q (x+d.vec)=_ from e1]; change Laurent.size (q x+d.vec)<Laurent.size (q x)
      have h : ((q x+d.vec:Cover) a).natAbs<(q x a).natAbs := by unfold d; split <;> simp <;> omega
      unfold Laurent.size; refine Finset.sum_lt_sum (fun i _ ↦ ?_) ⟨a,Finset.mem_univ _,h⟩
      by_cases H : i=a
      · exact H.symm ▸ h.le
      rw [hh i H]
    exact ⟨posDir 0, fun h => False.elim (hx h)⟩
  choose u H using he
  exact ⟨⟨u,m,hb,fun x hx ↦ (H x hx).1,fun x hx ↦ (H x hx).2⟩⟩

namespace Forest
variable (A : Forest g)

def trunks := (Finset.univ.filter (leaf g)).image (fun i => (A.up i).used i)

lemma trunk_mem_iff (e : Edge (Site f)) : e∈A.trunks ↔ ∃ i, leaf g i ∧ (A.up i).used i=e := by simp [trunks]

lemma trunk_internal {x : Site f} {i} (h : (x,i)∈A.trunks) :
    g.parent (x+step i)=g.parent x := by
  obtain ⟨k,hk,H⟩ := (trunk_mem_iff A _).mp h
  have hp := A.stays k hk
  cases he : A.up k with
  | mk j val =>
    rw [he] at H hp
    cases val <;> simp only [Step.used,Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at H
    · rw [← H.1, ← H.2]; exact hp
    rw [← H.1, ← H.2,sub_add_cancel]; simpa [Step.vec,sub_eq_add_neg] using hp.symm

/-- path child-to-root -/
def hike (A : Forest g) (x : Site f) : Walk := if h : leaf g x then A.up x :: A.hike (x+(A.up x).vec) else []
termination_by A.height x
decreasing_by exact A.rise x h

lemma hike_root (x : Site f) : stop x (A.hike x)=g.embed (g.parent x) := by
  induction x using hike.induct A with
  | case1 i hi ih => rw [hike,dif_pos hi, stop,ih,A.stays i hi]
  | case2 i hi => rw [hike, dif_neg hi]; exact Classical.not_not.mp hi

lemma hike_lower (x : Site f) : (A.hike x).length ≤ A.height x := by
  induction x using hike.induct A with
  | case1 i hi ih => rw [hike,dif_pos hi,List.length_cons]; exact lt_of_le_of_lt ih (A.rise i hi)
  | case2 i hi => rw [hike,dif_neg hi]; simp

end Forest
end YM.Tree
