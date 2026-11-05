import YM.RG08.Weald.Growth
import YM.RG08.Hatch.Rill

/-!
# Integrating a cofinal Gauge mark. Part I. Formula for the rescaled
`Slate.certify` at each fine density sector. Uses ACTUAL ψ credentials, no
custom measure. Includes endpoint colors even at tree bonds. qS^0
is linear in the rescaled coordinates; ∴ Ward applies to gauge
change at neighboring level without a stationarity limit.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Weald
open Jetty Skiff Lattice Isles Forms Pert.Bulk Function Finset Laurent Filter Packets Steam Mount
open Room Gallery Camera MvPolynomial Glyph Hatch Quarry
open RG Wilson Stationary Precision Tack Tree Prism Slate Work.F05
open scoped Topology BigOperators ENNReal Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {c n:Side}{G:Gauge}(S:StepData c n)(F:Forest S.ratio)(A B:Bed)
variable (Z:ChartRatio G)(hZ:LocalRatio Z)(d:G.El)
abbrev RoomX (G:Gauge)(c:Side):= Cove c (cuff G)
abbrev podium:=Lex F G (RoomX G c)
def Operandi : Prism.Bore S F A B (Quarry.badge c) id Z:= Slate.certify _ _ A B _ _ _ _ (Quarry.route S F (Quarry.badge (G:=G) c) (raise c d)) Z hZ
abbrev firstF (x : podium (G:=G) S F): Bid.Dir G n:= Prism.tone F A B (Quarry.badge c) x
abbrev secondF (x:podium (G:=G) S F):Bid.Dir G n:=Prism.tone F A B id (Camera.roll (Operandi S F A B Z hZ d).map x)
abbrev currentF (x:podium (G:=G) S F)(i:Site n):G.Color:=Quarry.spear (S.ratio.parent i) (Slate.envar x)
-- on all links, no hc
lemma corrected (x:podium (G:=G) S F)(y:Site n)(i:Axis):
 secondF S F A B Z hZ d x (y,Exterior.coord i)=tub (raise c d) (envar x) (firstF S F A B x (y,Exterior.coord i)) (S.ratio.parent y) (S.ratio.parent (y+step i)):=by
 let v:=Quarry.badge (G:=G) c; let V:=raise c d
 let L:= Operandi S F A B Z hZ d
 by_cases he:(y,i) ∈ F.trunks
 · rw [show secondF S F A B Z hZ d x (y,Exterior.coord i)=0 from tone_trunk F A B id _ (y,i) he,show firstF S F A B x (y,Exterior.coord i)=0 from tone_trunk F A B _ _ (y,i) he,F.trunk_internal he]; unfold tub siteBox; simp only [Gauge.mat_lieExp_zero,mul_one,mul_inv_cancel,Gauge.mat_one,Gauge.plog_one]
 let a:F.Free:=⟨(y,i),he⟩
 have ht:=congrFun (Slate.paid S F A B v (wheel S F V) id (arch v V) x) a
 exact ht

abbrev boltF (x:podium (G:=G) S F)(i:Lines G n 1):G.Color:=flourish d (firstF S F A B x (i.1,i.2.1)) (currentF S F x i.1) (currentF S F x (i.1+step (Quarry.back i.2.1)))
lemma salute (i:Lines G n 1):∀ᶠ x:podium (G:=G) S F in 𝓝 0, secondF S F A B Z hZ d x (i.1,i.2.1)=boltF S F A B d x i:=by
 let j:=i.2.1;let y:=i.1
 let a:=Quarry.back j; let w:=y+step (a:Axis)
 let H(x:podium (G:=G) S F):Trip G:=(firstF S F A B x (y,j),currentF S F x y,currentF S F x w)
 have he(k:Site n): ContinuousAt (fun x:podium (G:=G) S F=>currentF S F x k) 0:= (Quarry.spear _).continuous.continuousAt.comp Slate.smooth2.continuous.continuousAt
 have hR: H 0=0:=by
    unfold H firstF Prism.tone currentF; rw [seated,map_zero,show envar (0:podium (G:=G) S F)=(0:Cellar (RoomX G c)) from rfl,map_zero,map_zero];rfl
 have hH:ContinuousAt H 0:= (((continuous_apply (y,j)).continuousAt.comp (tone_pace F A B (Quarry.badge (G:=G) c)).continuousAt).prodMk ((he y).prodMk (he w)))
 have hy:Tendsto H (𝓝 0) (𝓝 0):=by rw [←hR]; exact hH.tendsto
 filter_upwards [hy.eventually (Quarry.colored d)] with x hx
 change secondF _ _ _ _ _ _ _ x (y,j)=flourish d (H x).1 (H x).2.1 (H x).2.2
 have hh : Exterior.coord a=j:= YM.Exterior.axisEquiv.apply_symm_apply j
 rw [←hx,←hh,corrected S F A B Z hZ d]
 unfold tub;congr 2
 unfold H; dsimp only; rw [hh]; unfold siteBox gaugeIn Quarry.raise w currentF
 simp only [_root_.mul_inv_rev,Work.F03.exp_neg_color,inv_inv];group

end YM.RG08.Weald
