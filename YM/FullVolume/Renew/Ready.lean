import YM.FullVolume.Renew.Widen
/-! E6 Layout steps full volume.Epoch. Keep Records by exact tags.Canvas.Read.F. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
open Matrix Window Progress.StationaryScenes Green Census Control Flux FullVolume.Shadow
open Gate Frond Vine Mask
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{J: Ultrafilter ℕ}{Q:ConnectedActivityE6.Target G P}{W x μ C₀ a b e ℓ v :ℝ}{o:Target.Order G W}
    {Λ: Era G S}{U:ℕ→ E→ Config G c}{Z: Draft F G} {K H:ℕ→ Epoch Λ}{j:ℕ}{p:E}
open FullVolume.Neptune Flux Shield Eider Packets Polar
namespace Ledgers
open Geo WilsonStartup
variable {K H: ℕ→ Cad G} {σ C A:ℝ}{p:BudgetPoint}{b:Clip}{α κ v v':ℕ→ℝ} {X : Listing G c}{F T:ℕ→ Collection.Source G c}
open Ovens Residual Rack
variable (h:G.Simple)(h1:∀ n,(K n).path.Bounds b σ C A)(h2:∀ n,(H n).path.Bounds b σ C A)(hv:Soul atTop K H)(hk:Geo.Width p b σ)(hd: Decent b p) (he: Twin α κ)
variable (hE: Canopy p X.reg (fun i=>(F i).logRead) (fun i=>(T i).logRead))(hK: Angel (fun i=> (F i).hardRead) (fun i=>(T i).hardRead))
lemma skins (V W:Cad G) : shelves X V.path p=shelves X W.path p :=by
     have hv: lowEntry (n:=c) G V.path p= lowEntry G W.path p := rfl
     have hh: highEntry (n:=c) G V.path=highEntry G W.path:=by
        funext i; rcases i with ⟨v,i|i⟩
        · change Seat.reg v ((V.path.cubic i).footprint 0) _=Seat.reg v ((W.path.cubic i).footprint 0) _; rfl
        change Seat.reg v ((V.path.quartic i).footprint 0) _=Seat.reg v ((W.path.quartic i).footprint 0) _; rfl
     have he: Collection.incoming X V.path p=Collection.incoming X W.path p:=by unfold Collection.incoming; rw [hv,hh]
     have vs {p q:Pipes G c}(h:p.reg=q.reg)(hh:p.kernel=q.kernel)(hf:p.softer=q.softer): p=q:= by rcases p; rcases q; congr
     exact vs (congr_arg (· ∘ (numbering (EKey c))) he) rfl rfl
include h h1 h2 hv hk hd he hE hK
lemma uniforms (a a' t t':ℕ→ ℝ):
        let F n:= Progress.DirectedRecipe.finish (K n|>.path) b p (shelves X (K n).path p) (branch X (K n).path b p (F n) (α n)) (a n) (t n)
        let G' n:= Progress.DirectedRecipe.finish (H n|>.path) b p (shelves X (H n).path p) (branch X (H n).path b p (T n) (κ n)) (a' n) (t' n)
        Canopy p (drawer G c).reg (fun n=> F n|>.activities.E) (fun n=>G' n|>.activities.E)∧ Angel (fun i=> (F i).activities.K) (fun i=> (G' i).activities.K):=by
    intro W V; obtain ⟨hE,h⟩:= tapu h h1 h2 hv hk hd he hE hK; let P:= shelves X (K 0).path p
    unfold W V; simp_rw [show ∀ n,shelves X (K n).path p=P from fun n=> skins ..,show ∀ n,shelves X (H n).path p=P from fun n=> skins ..]; let U n:=branch X (K n).path b p (F n) (α n); let X' n:=branch X (H n).path b p (T n) (κ n); exact ⟨consume P hE (U:=U) (V:=X'),entire P (U:=U) (V:=X') h hK⟩
end Ledgers
end YM.ConnectedActivityE6.Lim
