import YM.MergeProof.SkyProbe

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Guard Next.Foundations Local Next.Rank Edition Spindle Extra.Multi Motion
open PhysicalNext.Repeat.Legato.Bandage Cells Extraction Extraction.Lease Exponential Bid Next.Extract RelayDifference Opening
open Labels
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}(H:C.Makes)(B:Stock.Tabs C.path.levels)
variable {f:Extraction.Order}{N p d:ℕ}(V:SectionData (C.labels.level d)) (R : Mark.Weave G)
    (hV: Mark.Portfolio C.params V (R d)) {ζ:ℕ→ℕ→ℝ}{E:ℕ→ℝ}(P:ℕ→ℕ→(C.label d≃ₗ[ℂ] C.label d)){U:ℕ→ℕ→(C.labels.level d).Index→ C.label d}
    (h:Hearth V ζ E P U)
set_option quotPrecheck false
local notation "F"=> C.labels.level d
local notation "T"=> C.localSection d
local notation "Φ"=> C.path
local notation "Z"=> (C.factory d N p).terminal
-- at bin C choose. preR. Raw construction, follows org.L.Rep.Active. shim not invoking R on C.S actual.
open Mark (Weave theta Active Portfolio)
def Astar (C:Family G)(d N p)(V:C.label d≃ₗ[ℂ] C.label d) := (((C.factory d N p).terminal.symm).trans V).trans (C.factory d N p).terminal
def bindP (C : Family G) (R : Weave G) (d N p : ℕ) (V:C.label d≃ₗ[ℂ] C.label d): Label G d≃ₗ[ℂ] C.label d:= (Mark.embedTo C R d N p).trans (Astar C d N p V)
def catalog (C : Family G) (R : Weave G) (d N p : ℕ)(V:C.label d≃ₗ[ℂ] C.label d) := (Maxwell.equationIdeal G d).map (bindP C R d N p V).toLinearMap
include h H hV
set_option maxRecDepth 8000 in
lemma catalog_symm : ∀ᶠ i:ℕ in atTop,∀ p:ℕ, (∀ (x:Label G d), bindP C R d i p (P i p) (realBar x) = star (bindP C R d i p (P i p) x)) ∧ ∀ x s,bindP C R d i p (P i p) (theta s x)=(F).act s.ortho (bindP C R d i p (P i p) x):=by
   filter_upwards [h.stamped,eventually_ge_atTop (C.ref d)] with i hi ht p; have hg : ∀ j,P i p j= decor F (U i p) j:= (hi p).1; have he:= H.calibrated d i p ht
   have hd(j: (F).Coeff): decor F (U i p) j = repaint F (U i p) j:=by simp only [decor, LinearMap.coe_mk,AddHom.coe_mk]
   constructor
   · intro x; simp only [bindP,Mark.embedTo,Astar, LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply, hV.truly]
     have hp : (F).coords (realBar ((R d) x))= star ((F).coords ((R d) x)):= funext fun i=>by have hy:= (F).conj_basis ((F).coords ((R d) x)) i; rw [LinearEquiv.symm_apply_apply] at hy; exact hy
     rw [hp]; have hb (v:(F).Coeff) : Mark.tied C d i (star v)=star (Mark.tied C d i v):=by
         funext j; change (F).scaled _ (star v) j=star ((F).scaled _ v j); simp [mul_comm]
     rw [hb,hg,hg,hd,hd,← repainted_star,he.realForm]
   intro x s; simp only [bindP,Mark.embedTo, Astar,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply,hV.inter]; unfold Mark.theta
   rw [← Frame.act_coords,show ∀ w:C.label d, Mark.tied C d i ((F).act s.ortho w)= _ from fun w=> Frame.scaling _ _ s.ortho w,hg,hg,hd,hd,← repainted_H,he.orients]; rfl
-- kernel.Purchase.Dark.
include B
set_option maxHeartbeats 200000 in
lemma marshal (x:Rowe C d) (hv:dollar C f x) (hp:∀ j,x j∈ catalog C R d j.1 j.2 (P j.1 j.2)) :
    ∃ z,sober C z f ∧ exactOnSep C f z ∧ Bid.close C f (upper C x-z):= by
   let Z'(i : Cutoffs):= (C.factory d i.1 i.2).terminal; let y:Rowe C d := fun i=> (P i.1 i.2).symm ((Z' i).symm (x i))
   have he(i) : Z' i (P i.1 i.2 (y i))=x i:=by unfold y; rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
   have hx(i): Z' i (y i) ∈ Mark.carrier C R d i.1 i.2:=by
      obtain ⟨v,hv,hw⟩:= hp i; change bindP C R d i.1 i.2 _ v = x i at hw; unfold Z' y; rw [← hw,bindP,Astar,LinearEquiv.trans_apply,LinearEquiv.trans_apply, LinearEquiv.trans_apply]; simp only [Z', LinearEquiv.symm_apply_apply,LinearEquiv.apply_symm_apply]; exact Mark.entry_mem C R d i.1 i.2 _ hv
   have hc:= (dollar_slow _).1 hv
   have hy : Slow C f y:=by
     apply ((Slow.const (C:=C) (f:=f) (2:ℝ)).mul (coords_slow _ hc)).reduce
     filter_upwards [(cutoff_grows f).eventually h.stamped] with i hi; exact ((Size.norm_le _ _).trans ((hi i.2).2.1 ((Z' i).symm (x i)))).trans (Real.le_norm_self _)
   refine ⟨hallmarks V y,(region V hV.valid y).sober,?_,?_⟩
   · intro n q i t ht
     have h := Mark.skyprobes R V hV t ht n (fun j=> (q j).1); unfold Order.late; exact Eventually.of_forall (fun l=> (f.mesh.cofinal.eventually h).mono (fun j ht p hp=> ht (f.per l) ((show 0 < C.beta (f.mesh j) (f.per l) from Overlay.beta_positive H.wilson (le_refl (f.mesh j))).ne') y (hx (f.mesh j,f.per l)) q (fun _=> rfl) i p (fun j he=> hp j i he)))
   have hV:= embark H B V hV.valid h y hy; change Bid.close C f (upper C _-hallmarks V y) at hV; change Bid.close C f (upper C (fun i=>Z' i (P i.1 i.2 (y i)))-hallmarks V y) at hV; rw [show (fun i:Cutoffs=>Z' i (P i.1 i.2 (y i)))=x from funext he] at hV; exact hV
end YM.MergeProof
