import YM.AnalyticNext.GRID_STOP_ATTENUATION.Coarrival.Core
import YM.MergeProof.Badlands
import YM.MergeProof.Coast
import YM.Next.RANK.HomeSync
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.RibbonRise
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Graces.Eagles


set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Next.Rank Edition Baler Value Glyph Thirst Alarm Push GridApprox.Nil Motion Spindle Atlas Cells
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V]
-- generate chess-copies all polynomials. factor across every occurrence no collapse.
lemma logged (R:Rep G n)(X:Tiling n) (f:V → Config G n→ℂ) (β:ℝ)(hr:R.eval=bare β): Array.stamp X β (fun U=> Glyph.raw (fun i=> f i U)) = birth (Stock.census (X.Cell × V)) R (fun t=>X.copy t.1 (f t.2)):=by
   let Y:=X.Cell; let σ:=X.Cell × V; let F(i:σ):= X.copy i.1 (f i.2)
   funext U; ext i; rw [Array.stamp_part]; unfold birth; rw [Poly.part_smul,hr]; unfold Mach; rw [Extra.Trajectories.pass_fire]
   congr 1; simp_rw [Glyph.expand]
   have he(t:Y)(s:Finset V):X.copy t (fun U=>∏ j∈s,f j U) U=∏ j∈s,F (t,j) U:=by unfold F Tiling.copy; split_ifs; rw [star_prod]; rfl -- check
   change (∏ t:Y,_)= ∏ j∈i.val, F j U; simp_rw [he]; unfold fibre; dsimp only [scene]; rw [show ∏ j∈i.val,F j U=∏ j:σ, if j∈ i.val then F j U else 1 from by rw [← Finset.prod_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]]; rw [Fintype.prod_prod_type]; exact prod_congr rfl (fun _ _=> Finset.prod_filter ..)
variable (C:Family G)(h:C.Makes)(N k p d m:ℕ) (v:Fin m→ C.label d) (b:ℝ)(Y:Points m)(hk:k≤N)
local notation "T"=> Ship.yard C b hk p
local notation "Q"=> C.path.rep N p N
set_option quotPrecheck false
def plum (j:Listens C b (v:=m) hk p):= dye (hand C b hk p j) (fp C b hk p j)
def hops (i:ℕ)(j:Listens C b hk p (v:=m)): Site (C.side i p):= Mix.camp C p k i (seats C b Y hk p j)
local notation "L"=> Listens C b (v:=m) hk p
local notation "v'"=> hops C N k p m b Y hk
local notation "g'"=> plum C N k p m b hk
local notation "P"=> Issued C b Y hk p v
include h
lemma wound : Issued C b Y hk p v=birth (Stock.census (Listens C b (v:=m) hk p)) Q (fun i=> item C d N p (v i.2) (fun j=> hops C N k p m b Y hk j i) (plum C N k p m b hk i)):=by
    let J:= origin C b Y k N p v
    have hv := logged Q T J (C.beta N p) (h.wilson.starts N p|>.2)
    have hV:P= birth (Stock.census _) Q (fun i=>(T).copy i.1 (J i.2)):= hv
    rw [hV]; congr 1; funext i U
    have hx:= congr_fun (stamp_single C b Y hk p v i) U
    change (Issued _ _ _ _ _ _ _).part _ = _ at hx; rw [hV,boot,(h.wilson.starts N p).2] at hx
    let z:= v' N i; have he:z=(C.S.toDepth hk p).embed (seats C b Y hk p i):= by unfold z hops Mix.camp; rw [dif_pos hk]
    unfold item; change _= scalar (g' i) ((C.O N p (v i.2) 0) (pull (g' i).1 z U)); rw [he]; simp only [plum,calling]; unfold singleP at hx; dsimp only [Function.comp_apply] at hx; rw [bare_pull,dot_move] at hx
    exact mul_left_cancel₀ (show (bare (C.beta N p) U:ℂ)≠0 from Complex.ofReal_ne_zero.mpr (bare_pos ..|>.ne')) hx
end YM.MergeProof.Accent
