import YM.RG08.Rudder.Loop.Kinetic
import YM.AnalyticNext.QUARTIC_MATCH.Cells.Per
import YM.RG08.Isles.Launch

/-!
# Periodizing Laurent curvature lifts: agreement between descriptor conventions
-/
noncomputable section
namespace YM.RG08.Anchor
open Forms Rudder Packets Isles Finset Function Lattice Laurent Pert.Bulk Exterior Filter Bloch
open AnalyticNext.QuarticMatch.BoxChain hiding sway
open scoped Topology BigOperators Classical ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
local notation "Box"=> YM.AnalyticNext.QuarticMatch.BoxChain.Cell -- clashes?
variable {I : Type}{n:ℕ}{P:Side}{σ C:ℝ}{F:Raw I n}

def herald (x:Tape n (Box (Per P)))(y:Tape n I):Tape n (Cove P (Tone I)):=fun i=>( (x i).1,(x i).2,y i)
variable (i:Fin n) (x:Tape n (Box (Per P)))(y:Tape n I)
private def escort(v:sheets P i):Tape n (Market (Tone I)):=fun j=> (Lattice.lift (x j).1+v.val j, (x j).2,y j)
private lemma ready(v:sheets P i):escort i x y v∈ lantern i (herald x y):=by
 refine ⟨?_,funext fun j=> ?_⟩
 · change (Lattice.lift _+ v.val i,_)=_;rw [sheet_here,add_zero];rfl
 change ((wrap P) (_+v.val j),_)=_;rw [map_add,sheet_wrap,add_zero,wrap_lift];rfl
private def sheetsTake (v:↥(lantern i (herald x y))) : sheets P i := ⟨fun j=> (v.val j).1 - Lattice.lift (x j).1,fun j=> by
 have h:=congr_arg Prod.fst (Isles.found v.property j)
 change wrap P _ = (x j).1 at h
 rw [map_sub,h,wrap_lift,sub_self],by
 have he:= congr_arg Prod.fst ((Set.mem_setOf.mp v.property).1)
 change (v.val i).1=Lattice.lift (x i).1 at he;dsimp only;rw [he,sub_self]⟩

private def santa : (↥(sheets P i)) ≃ ↥(lantern i (herald x y)) where
 toFun v:=⟨_,ready i x y v⟩
 invFun:=sheetsTake i x y
 left_inv v:=by apply Subtype.ext;ext1 j;change Lattice.lift _+v.val j -_= _;abel
 right_inv v:=by
   apply Subtype.ext; funext j
   have H:=congr_arg Prod.snd (Isles.found v.property j)
   change (Lattice.lift _+((v.val j).1-Lattice.lift _),_,_) = v.val j
   ext1
   · dsimp only;abel
   exact H.symm

/- `i` is ANY anchor. -/
lemma landing : pour (P:=P) F i (herald x y) = scene P i (hum F y) x:=by
 rw [pour_at,← (santa i x y).tsum_eq];rfl

/-- Exact, including all paths/frequencies. No Wick closed cycles here. -/
lemma turns (F: Raw I n)(hp:NextTo F σ C)(x:Tape n (Box (Per P)))(y:Tape n I):
 pour (picture I n F) i (herald x y)=
      YM.AnalyticNext.QuarticMatch.BoxChain.solve (List.finRange n) (fun v=>pour F i (herald v y)) x:=by
 simp_rw [landing,picture,patch_eval, descend_list P i (hp y)]
end YM.RG08.Anchor
