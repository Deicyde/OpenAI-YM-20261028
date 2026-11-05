import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Festal
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Turbine
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sward.Greenbelt
/-! # Actual per-site Forest and tag uniform probabilities under cover. No appeal
 to coframe partition outside these patches.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Deck
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter  Shingle Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F:Side} {P : Patch} {M D' : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} (hC : C.val=c.val*M) (he:2 ≤ c.val)
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "Y" => stepped Q H
variable (x : Site C)
local notation "W" => Deck.reverts hC x
local notation "rA" => decreed h
local notation "P'" => decreed H

-- Q shadow etc
section roles
abbrev climbF (i:Site f): Site F:= (L).R.assemble (W ((L).r.parent i), (L).r.residue i)
include hC he
lemma course (i:Site f): (L).high.cut (climbF (h:=h) (H:=H) hC he x i)=i := by unfold climbF; rw [Lace.regions, show (L).low.cut _= _ from Deck.reverted hC x ((L).r.parent i)]; exact Ratio.unpack_at ..
lemma ascend (i:Site f): (P').parent (climbF (h:=h) (H:=H) hC he x i)=W ((rA).parent i):= Ratio.assemble_parent ..
lemma hereagain {z:Site C} (hp : z∈Set.range W) (i : Site F) (hi : (P').parent i=z): climbF (h:=h) (H:=H) hC he x ((L).high.cut i)=i:= by
  obtain ⟨y,rfl⟩:= hp; apply (Deck.footing (h:=h) (H:=H) hC he).firm _ _ (course ..); rw [ascend]; change W ((L).r.parent ((L).high.cut i))=(L).R.parent i; rw [Lace.position,show (L).R.parent i=_ from hi, show (L).low.cut (W y)=y from Deck.reverted hC x _]
variable (R : Forest (decreed H))
def dismount : Forest (decreed h) where
  up i := R.up (Deck.climbF (h:=h) (H:=H) hC he x i)
  height i:= R.height (Deck.climbF (h:=h) (H:=H) hC he x i)
  bound i:= R.bound _
  rise i hi:= by
    let p':= climbF (h:=h) (H:=H) hC he x i; let n:=R.up p'
    have hx := (L).fork p'; have hp: (L).high.cut p'=i:= course ..; rw [hp] at hx
    have hg:= R.rise p' (hx.2 hi); have ht:=R.stays p' (hx.2 hi)
    change R.height (climbF (h:=h) (H:=H) hC he x (i+n.vec))<_
    have hv: (L).high.cut (p'+n.vec)=i+n.vec:= by rw [Macrame.Window.uniform,hp]
    rw [← hv, Deck.hereagain hC he x (Set.mem_range_self _) (p'+n.vec) (ht.trans (ascend hC he x i))]; exact hg
  stays i hi:= by
    let p':=climbF (h:=h) (H:=H) hC he x i
    have hx := (L).fork p'; have hp:(L).high.cut p'=i:= course ..; rw [hp] at hx
    have he:= R.stays p' (hx.2 hi); have hh:= ((L).strolls p' (R.up p')).1 he; rw [hp] at hh; exact hh

variable {R}
-- Override large Forest ON blocks picked for all small coarse sites (Rank padding retained). Generic matchup.
def mountForest (R : Forest (decreed H)) (T : Forest (decreed h)) : Forest (decreed H):= Greenbelt.allot (S:=stepped Q H) (fun p => if p∈Set.range W then (L).repeater T else R)
-- Q argument include
include Q
def countingF : Matchup (dismount (H:=H) (h:=h) hC he x) where
  put:=Deck.mountForest (Q:=Q) hC he x
  put_get R T:= by
    apply Greenbelt.identityF _ _; all_goals funext i; let i':= climbF (h:=h) (H:=H) hC he x i; have hp:(P').parent i' ∈ Set.range W:= (ascend hC he x i).symm ▸ Set.mem_range_self _; unfold Deck.dismount Deck.mountForest Greenbelt.allot; dsimp only; rw [if_pos (show (Y).ratio.parent (climbF (h:=h) (H:=H) hC he x i) ∈ Set.range W from hp)]; first | exact congr_arg T.up (course (h:=h) (H:=H) hC he x i) | exact congr_arg T.height (course (h:=h) (H:=H) hC he x i)
  birth R:= by
    apply Greenbelt.identityF _ _; all_goals funext i; unfold Deck.mountForest Greenbelt.allot; dsimp only; split; next hp=> first| exact congr_arg R.up (hereagain hC he x hp _ (show (P').parent i=_ from rfl)) | exact congr_arg R.height (hereagain hC he x hp _ (show (P').parent i=_ from rfl))
    all_goals rfl
  back _x _y _z:= by
    apply Greenbelt.identityF _ _; all_goals funext i; unfold Deck.mountForest Greenbelt.allot; dsimp only; split
    all_goals first | rfl | (dsimp only; rw [if_neg (by assumption)])
end roles
end YM.PhysicalNext.Repeat.Deck
