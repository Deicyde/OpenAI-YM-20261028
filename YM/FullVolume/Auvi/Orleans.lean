import YM.FullVolume.Auvi.Lands
import YM.FullVolume.Table.Vola
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
local notation "Qx"=>R.target ((B).clock.J (m+1)) ((B).clock.J m)
local notation "C"=> R.shape.c ((B).clock.J (m+1)) ((B).clock.J m)
local notation "s'"=> R.walls ((B).clock.J (m+1)) ((B).clock.J m)
local notation "q"=> R.shape.μ ((B).clock.J (m+1)) ((B).clock.J m)
local notation "x₀"=> ((B).clock.hatBeta m)
local notation "b"=>R.shape.o ((B).clock.J (m+1)) ((B).clock.J m)
local notation "D'"=> D.L ((B).clock.J (m+1))
local notation "Z'"=> (X.p.profile ((B).clock.J m)).order
local notation "k"=> Trio.base (Rain.lint R.target A m) (radiusB x₀)
open Slide
variable (R)
lemma billiard {P:f.val=c.val*((B).S.block m).val}{S S': Rep G f} {V T: Tube G (panel A m P)} {g:Cash s' x₀ q D' Qx b C V S} {F:Cash s' x₀ q D' Qx b C T S'} (ht:V=T)(he:S=S')(hp:HEq g F) (i:ℕ)(w:ℝ)(D:∀ s:Stars, Trio.Offer G (Rain.moor R.target A m s)): Beam.marquee g Q=Beam.marquee F Q∧ Marlin.bison (Meadow.timbres (χ:=Chi.canonical) (staple (H:=g) (J:=g) rfl rfl rfl) w i) (Trio.ornament (Rain.screens R.target A m) D) (Trio.insight Q (staple (H:=g) (J:=g) rfl rfl rfl) w i (Rain.screens R.target A m) k D)= Marlin.bison (Meadow.timbres (χ:=Chi.canonical) (staple (H:=F) (J:=F) rfl rfl rfl) w i) (Trio.ornament (Rain.screens R.target A m) D) (Trio.insight Q (staple (H:=F) (J:=F) rfl rfl rfl) w i (Rain.screens R.target A m) k D):=by subst T; subst S'; rw [eq_of_heq hp]; exact ⟨rfl,rfl⟩
variable {R}
local notation "P"=> ((B).S.oneStep m p).exact_size
local notation "P'"=>A.B.a.S.side m p
local notation "f'"=>A.B.a.S.side (m+1) p
set_option quotPrecheck false
local notation "γ"=> fun n=> A.B.kin.alpha (u n) m
local notation "δ"=> fun n=> A.B.kin.alpha (v' n) m
local notation "V"=>fun n=> (M n).val
local notation "V'"=>fun n=>(L n).val
local notation "W"=> FullVolume.Urns.layout G (f') Ω -- replace
lemma upright (F:Chord.Flight A N m p): F.val.path=A.B.kin.path N (m+1):= F.property.1.path.trans (congr_fun (congr_fun A.B.bases N) _)
variable (hZ:Jams.Wild R.shape A.delay) (hP:∀ n,listIn (M n).val=FullVolume.Urns.layout G (A.B.a.S.side (m+1) p) (A.B.a.budget (m+1)))(hP':∀ n,listIn (L n).val=FullVolume.Urns.layout G (A.B.a.S.side (m+1) p) (A.B.a.budget (m+1))) (hE:Angel (fun n=> (M n).val.activities.regularOccurrence (A.B.a.budget (m+1))) (fun n=> (L n).val.activities.regularOccurrence (A.B.a.budget (m+1))))(hK:Angel (fun n=>(M n).val.activities.K) (fun n=>(L n).val.activities.K)) (hB:Glints atTop (fun n=>(M n).val.beta) (fun n=>(L n).val.beta))
open Accout
include hx hy H T hE hK hB hP hP' hZ h hk hu hh
set_option maxHeartbeats 650000 in
lemma ballad : ∃ X:Listing G P', (∀ n,(H n).listing (M n)=X)∧ (∀ n,(T n).listing (L n)=X)∧ Canopy Q X.reg (fun n=> (H n|>.source (M n)).logRead) (fun n=> (T n|>.source (L n)).logRead)∧ Angel (fun n=>(H n|>.source (M n)).hardRead) (fun n=> (T n|>.source (L n)).hardRead):=by
    let A' n:= book m (A:=A) P (W) (u n) (V n) -- specify
    let E n:= book m (A:=A) P (W) (v' n) (V' n)
    have he n: (A' n).kin=V n:= reads m P W (u n) (hx n).2 (hP n) (M n).property.1.point (M n).property.1.clip (upright _)
    have hf n: (E n).kin=V' n:= reads m P W (v' n) (hy n).2 (hP' n) (L n).property.1.point (L n).property.1.clip (upright _)
    have h' n: (A' n).tubes=Pane.orchestra A (u n) P:= seats m P W (u n) (hx n).2 _
    have h'' n:(E n).tubes=Pane.orchestra A (v' n) P:= seats m P W (v' n) (hy n).2 _
    let I n:= safeTrans R P (A' n) (h' n) (he n) ((H n).sight (M n)); let Y n:= safeTrans R P (E n) (h'' n) (hf n) ((T n).sight (L n)); obtain ⟨b',hv⟩:= quarters hZ m
    have hg:= (H 0).earns.conducts.full; let K'n n:= deposits R b' hv (V n) (h' n) (hx n).1 hg (I n); let K'T n:= deposits R b' hv (V' n) (h'' n) (hy n).1 hg (Y n)
    have hd:= (Roof.coating (H 0).earns.conducts (H 0).paid (R:=fun _=> (M 0).val) (s:= Set.univ) (fun _ _=>(M 0).property.2)).decent
    let f₀ n:= (H n).pitch (M n); let f₁ n:= (T n).pitch (L n); let D₀ i:= (H i).rates (M i); let D₁ i:= (T i).rates (L i)
    have h0 :Tendsto f₀ atTop atTop:= tendsto_atTop_mono (f:=u) (fun i=>(H i).towards _) hu; have h1 : Tendsto f₁ atTop atTop:= tendsto_atTop_mono (f:=v') (fun i=>(T i).towards _) hh; have ha := allies h hk hu hh hx hy hd P W V V' he hf hE hK hB
    have hp :∀ i j, Yard.Loom Q 0 Finset.univ (fun n=>D₀ n i j) (fun n=> D₁ n i j):= swaths R h hk hu hh hx hy hd hZ (fun i=>(H i).tone) (fun i=>(T i).tone) h0 h1 (fun i=>⟨(V i).beta,(M i).property.2⟩) (fun i=>⟨(V' i).beta,(L i).property.2⟩) hB hg
    obtain ⟨hL,hG⟩:= ambit I Y K'n K'T ha rfl ((Rain.jersey (A:=A) (m:=m)).1.le) h0 h1 (Rain.screens R.target A m) hp (show _≤ k by unfold Trio.base; omega)
    let X' := Marlin.lodge (Beam.marquee (I 0) Q) k (2*k)
    let DH n:= Marlin.bison (Meadow.timbres (χ:=Chi.canonical) (clav (I n)) (γ n) (f₀ n)) (Trio.ornament (Rain.screens R.target A m) (D₀ n)) (Trio.insight Q (clav (I n)) (γ n) (f₀ n) (Rain.screens R.target A m) k (D₀ n))
    let DK n:= Marlin.bison (Meadow.timbres (χ:=Chi.canonical) (clav (Y n)) (δ n) (f₁ n)) (Trio.ornament (Rain.screens R.target A m) (D₁ n)) (Trio.insight Q (clav (Y n)) (δ n) (f₁ n) (Rain.screens R.target A m) k (D₁ n))
    have hz n: Beam.marquee (I n) Q=(H n).crewD (M n) ∧ DH n=(H n).offerT (M n):= billiard R (g:=I n) (F:=(H n).sight (M n)) (h' n) (he n) (bank R P _ _ _ _) (f₀ n) (γ n) (D₀ n)
    have hz' n:Beam.marquee (Y n) Q=(T n).crewD (L n) ∧ DK n=(T n).offerT (L n):=billiard R (g:=Y n) (F:=(T n).sight (L n)) (h'' n) (hf n) (bank R P _ _ _ _) (f₁ n) (δ n) (D₁ n)
    have hr n:(H n).lens (M n)=X':=by unfold Chord.lens; rw [← (hz n).1]; rfl
    have hF n:(T n).lens (L n)=X':=by unfold Chord.lens; rw [←(hz' n).1]; rfl
    have hpp n:(H n).source (M n)= Marlin.poursP Q X' (DH n):=by unfold Chord.source; rw [hr n,←(hz n).2]
    have hpp' n:(T n).source (L n)= Marlin.poursP Q X' (DK n):=by unfold Chord.source; rw [hF n,←(hz' n).2]
    refine ⟨Marlin.pluck Q X',fun n=>congr_arg (Marlin.pluck Q) (hr n),fun n=>congr_arg (Marlin.pluck Q) (hF n),?_,?_⟩
    · simp_rw [hpp,hpp']; exact hL
    simp_rw [hpp,hpp']; exact hG
end Pith
end YM.PhysicalNext.Repeat.Lark
