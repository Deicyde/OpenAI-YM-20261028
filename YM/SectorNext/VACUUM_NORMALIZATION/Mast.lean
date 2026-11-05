import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import YM.Analysis.Polydisc
import YM.Pressure.Seeds

/-!
# Full tree and triangular plaquette elimination (periodic)

Highest active dimension first. For each dimension spend FIRST on
wrapping vertical variables leaf-to-root within the horizontal base;
only THEN on horizontal links slice-by-slice top toward base. This
accumulates only four global-direction slots instead of surface-size
entropy, even with torus links and the fixed positive-orientation
convention. Selection independent of β/p. Tree slice uses ratio
1:n so root-fixed; can eliminate plaquettes even without gauge fixing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Vacuum.Masts
open Lattice Tree RG Wilson Filter Finset Function
open scoped Matrix.Norms.Frobenius BigOperators Topology Classical
variable (n : Side)

private abbrev tower := Ratio (1:Side) n

def spire : tower n := ⟨n,by simp⟩

abbrev Link (n : Side) := Edge (Site n)

variable {n}

def highest (x : Site n) : Axis := ((univ : Finset Axis).filter fun i=>x i≠0).sup id

lemma realm (x : Site n) (j : Axis) (h : x j ≠ 0) : j≤highest x := Finset.le_sup (f:=id) (mem_filter.mpr ⟨mem_univ _,h⟩)
lemma above (x : Site n) {i : Axis} (h : highest x< i) : x i=0 := by by_contra H; exact h.not_ge (realm _ _ H)
lemma highest_on (x : Site n) (h : x≠0) : x (highest x)≠0 := by
  let v := (univ : Finset Axis).filter fun i=>x i≠0
  have hv : v.Nonempty := by
    contrapose! h
    have he := h
    funext i; by_contra hh; have hg : i∈v := mem_filter.mpr ⟨mem_univ _,hh⟩; rw [he] at hg; exact notMem_empty _ hg
  have he : v.max' hv ∈ v := v.max'_mem hv
  have hl : v.max' hv=highest x := le_antisymm (Finset.le_sup (s:=v) (f:=id) he) (Finset.sup_le (fun i hi => le_max' v i hi))
  exact hl ▸ (mem_filter.mp he).2
lemma upto (x : Site n) (i : Axis) (h : ∀ j, i<j → x j=0) : highest x ≤ i := Finset.sup_le fun j hj=> le_of_not_gt fun he=> (mem_filter.mp (show j∈Finset.univ.filter (fun k=>x k≠0) from hj)).2 (h _ he)

def depth (x : Site n) := ∑ i,(x i).val
lemma shorten (hl : 1<n.val) (x : Site n) (q : Axis) (hx : x q≠0) :
    depth (x - step q)+1=depth x := by
  have he := Ne.symm ((ZMod.val_eq_zero _).not.mpr hx)
  have hv : ((x-step q:Site n) q).val+1=(x q).val := by
    simp only [Pi.sub_apply,step_apply,if_pos]; rw [ZMod.val_sub,ZMod.val_one'' (by omega)]; omega
    rw [ZMod.val_one'' (by omega)]; omega
  have hh (i : Axis) : ((x-step q:Site n) i).val+(if i=q then 1 else 0)=(x i).val := by
    by_cases h : i=q; subst i; simpa using hv
    simp [h]
  simpa [Finset.sum_add_distrib,depth] using! Finset.sum_congr (s₁:=(univ:Finset Axis)) rfl (fun i _=>hh i)

private lemma lonely (x : Site (1:Side)) : x=0 := by funext i; exact Subsingleton.elim (α:=ZMod 1) _ _
private lemma basement (x : Site (1:Side)) : (spire n).embed x = 0 := by rw [lonely x,← Ratio.root_embed, map_zero]
lemma reachable (x : Site n) : leaf (spire n) x ↔ x≠0 := by unfold leaf; dsimp only; rw [basement]

def main (n : Side) (h : 1<n.val) : Forest (spire n) where
  up x := negDir (highest x)
  height := depth
  bound i := by
    apply le_trans (Finset.sum_le_sum (fun j (_ : j∈Finset.univ)=> Nat.le_of_lt (ZMod.val_lt (i j))))
    simp [spire,Axis]
  rise i hi := by simp only [Step.vec_neg,← sub_eq_add_neg]; have he := shorten h i (highest i) (highest_on i ((reachable _).mp hi)); omega
  stays _ _ := (lonely _).trans (lonely _).symm



/-- Parts of a Link's location ticket. Only test coordinates above current
axis for all-zero. -/
def top (e : Link n) := ∀ i, e.2 < i → e.1 i=0
lemma top_le (e : Link n) : top e ↔ highest e.1 ≤ e.2 :=
  ⟨upto _ _,fun h _ hi=>above _ (h.trans_lt hi)⟩

def wraps (e : Link n) := e.1 e.2= -1



/-- One wrapping variable per axis retained globally. -/
def mast (n : Side) (i : Axis) : Link n := (-step i,i)
def Active (e : Link n) := ¬ (top e ∧ ¬ wraps e) ∧ e≠mast n e.2
abbrev Tor (n : Side) := {e : Link n // Active e}



end YM.SectorNext.Vacuum.Masts
