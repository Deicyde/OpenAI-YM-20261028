import YM.FullVolume.Auvi.Orleans
/- point of departure -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lark
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Beacon Stationary.Shade Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c f:Side}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}
open Rain Pane Roof ConnectedActivityE6.Lim FullVolume.Shadow
variable {m:ℕ}{Z:f.val=c.val*(A.B.a.S.block m).val}{W:Listing G f}{N:ℕ}
local notation "K"=> A.B.kin
local notation "B"=> A.B.a
local notation "Q"=> A.B.a.budget m
local notation "Ω"=> A.B.a.budget (m+1)
variable {p:ℕ}
namespace Pith
variable (hG:G.Simple){t v:ℝ}{u v':ℕ→ℕ}(h:Artes.Cadre A.post A.B.kin)(hk:Next.Free.Amplify A.B.M)(hu:Tendsto u atTop atTop)(hh:Tendsto v' atTop atTop)(hx:Near A m u)(hy:Near A m v')(H:∀ n,Chord R (u n) m p t v)(T:∀ n, Chord R (v' n) m p t v)
    (M:∀ n,Chord.Flight A (u n) m p)(L:∀ n,Chord.Flight A (v' n) m p)
set_option quotPrecheck false
local notation "P'"=> A.B.a.S.side m p
local notation "f'"=>A.B.a.S.side (m+1) p
set_option quotPrecheck false
local notation "γ"=> fun n=> A.B.kin.alpha (u n) m
local notation "δ"=> fun n=> A.B.kin.alpha (v' n) m
local notation "V"=>fun n=> (M n).val
local notation "V'"=>fun n=>(L n).val
local notation "W"=> FullVolume.Urns.layout G (f') Ω -- replace
variable (hZ:Jams.Wild R.shape A.delay) (hP:∀ n,listIn (M n).val=FullVolume.Urns.layout G (A.B.a.S.side (m+1) p) (A.B.a.budget (m+1)))(hP':∀ n,listIn (L n).val=FullVolume.Urns.layout G (A.B.a.S.side (m+1) p) (A.B.a.budget (m+1))) (hE:Angel (fun n=> (M n).val.activities.regularOccurrence (A.B.a.budget (m+1))) (fun n=> (L n).val.activities.regularOccurrence (A.B.a.budget (m+1))))(hK:Angel (fun n=>(M n).val.activities.K) (fun n=>(L n).val.activities.K)) (hB:Glints atTop (fun n=>(M n).val.beta) (fun n=>(L n).val.beta))
open Accout
include hx hy H T hE hK hB hP hP' hZ h hk hu hh
local notation "Ξ"=>fun i=>H i|>.moment (M i)
local notation "Θ"=>fun i=>T i|>.moment (L i)
include hG
lemma rises : Tendsto (fun n=>(Ξ n).beta-(Θ n).beta) atTop (𝓝 0)∧ Canopy Q (drawer G P').reg (fun n=> (Ξ n|>.activities.E)) (fun n=>(Θ n|>.activities.E)) ∧ Angel (fun n=> (Ξ n|>.activities.K)) (fun n=> (Θ n|>.activities.K)):=by
    obtain ⟨X,hA,hC,hD,hF⟩:=ballad h hk hu hh hx hy H T M L hZ hP hP' hE hK hB
    let D n:= (H n).source (M n); let F n:= (T n).source (L n); have h' := landhold h hu hh (m:=m)
    constructor
    · simp_rw [fun n=> (show (Ξ n).beta=(V n).beta+γ n+Averaging.delta (X.read (D n)) by rw [← hA n]; rfl),fun n=> (show (Θ n).beta=(V' n).beta+δ n+Averaging.delta (X.read (F n)) by rw [← hC n]; rfl)]
      have ht:= (hB.shrank.add h'.shrank).add (Ledgers.incomes (F:=D) (H:=F) hG hD hF|>.goes); simp only [add_zero] at ht; exact ht.congr' (Eventually.of_forall fun i=>by dsimp only; ring)
    let K' n:= Cad.pure (K|>.path (u n) m); let Var n:= Cad.pure (K|>.path (v' n) m) -- V' reserved
    let z:= ((B).params m).clip
    let F' n:= finish (K' n|>.path) z Q (shelves X (K' n|>.path) Q) (branch X (K' n|>.path) z Q (D n) (γ n)) 0 0; let G' n:=finish (Var n|>.path) z Q (shelves X (Var n|>.path) Q) (branch X (Var n|>.path) z Q (F n) (δ n)) 0 0
    have he n:(Ξ n).activities=(F' n).activities:=by unfold F'; rw [← hA n,show (K' n).path=A.B.kin.path _ _ from (hx n).2.1]; exact Apse.writtenN ..
    have hg n:(Θ n).activities=(G' n).activities:=by unfold G'; rw [← hC n,show (Var n).path=A.B.kin.path _ _ from (hy n).2.1]; exact Apse.writtenN ..
    have ha:=Roof.coating (H 0).earns.conducts (H 0).paid (R:=fun _=>(M 0).val) (s:=Set.univ) (fun _ _=>(M 0).property.2)
    have hp:Soul atTop K' Var:= souls (slots h m) hu hh; have hf: Canopy Q (drawer G P').reg (fun n=> (F' n).activities.E) (fun n=> (G' n).activities.E)∧ Angel (fun n=>(F' n).activities.K) (fun n=>(G' n).activities.K):= Ledgers.uniforms («p»:=Q) («F»:=D) (T:=F) hG (nearby hx) (nearby hy) hp ha.width ha.decent ⟨treasury h',h'.shrank⟩ hD hF (fun _=>0) (fun _=>0) (fun _=>0) (fun _=>0)
    simp_rw [he,hg]; exact hf
end Pith
end YM.PhysicalNext.Repeat.Lark
