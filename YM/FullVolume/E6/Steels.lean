import YM.FullVolume.E6.Witness
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
open Pressure.Stores Tags
namespace Draft
variable (H₀:∀ n,Cash W x μ L Q o C₀ (K n).tubes (K n).kin)(H₁:∀ n,Cash W x μ L Q o C₀ (H n).tubes (H n).kin)(hQ:∀ n, Promo Q o j x v ℓ a Z.χ (K n).tubes)
   (hz:Z.Paid Q o x) (h:Finish J K H)(hv:0≤v)
   (U₀:ℕ→ Config G c)(he:∀ᶠ i in (J:Filter ℕ), Z.Viable (U₀ i))
set_option quotPrecheck false
local notation "D"=> fun n => Z.paints (K n) (U₀ n)
local notation "D'"=> fun n=> Z.paints (H n) (U₀ n)
local notation "Hn" => (fun n (_:ℝ)=>U₀ n)
include H₀ hz
lemma febrile : 0 < Pressure.temp Z.x:= Work.E09.temp_pos (show 0< Z.x from hz.1.symm ▸ (H₀ 0).laws.data.room.signs)
lemma fitsX : Room P S (K 0).tubes Z.x:= hz.1.symm ▸ (H₀ 0).laws.data.room
omit H₀ hz
include hv
lemma haloV : ∀ᶠ i in (J:Filter ℕ),Mode (Hn i) 0 j v:= Eventually.of_forall fun i=> ⟨hv,fun q=>a_oneB _ _ hv⟩ -- syntax
include H₀ H₁ hz h he hv hQ
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
lemma oxcart {F Hx:ℕ→ ℝ→ Directions G f}(hk:Frill J j 0 F Hx)(s:Signed)(q:Spot c f): Glints J (fun n=> (D n).extracted (F n 0) s q) (fun n=>(D' n).extracted (Hx n 0) s q) :=by
    exact (portico hQ hz h (haloV hv U₀) he hk s q).crest.carve (he.mono fun i hi=>((Polar.cotton (D i) (hz.1.symm ▸ (H₀ i).laws.data.room) hi _ s q)).symm) (he.mono fun i hi=> ((Polar.cotton (D' i) (hz.1.symm ▸ (H₁ i).laws.data.room) hi _ s q)).symm)
lemma exhaust (s:Signed)(q:Spot c f): Glints J (fun n=> (D n).extracted (D n|>.μ) s q) (fun n=>(D' n).extracted (D' n|>.μ) s q):=by
    exact (oxcart H₀ H₁ hQ hz h hv U₀ he (levied H₀ hQ hz h (haloV hv U₀) he) s q).carve (he.mono fun i hi=> congr_arg (fun u=> (D i).extracted u s q) (Vine.agrees_all (hz.1.symm ▸ (H₀ i).laws.data.room) (X:=D i) hi).symm) (he.mono fun i hi=> congr_arg (fun u=> (D' i).extracted u s q) (Vine.agrees_all (hz.1.symm ▸ (H₁ i).laws.data.room) (X:=D' i) hi).symm)
local notation "t" => fiery G Z.x S.patch.L
local notation "a₀"=> o.a
lemma daw (A:Stores S)(u:Directions G f)(l:Finset ℕ) : Glints J (fun n=> (D n).Pack (K n).kin Q.table l W a₀ A u) (fun n=> (D' n).Pack (H n).kin Q.table l W a₀ A u):=by
    let V n := (D n).input u; let k:=Z.k
    have hg:= haloV hv U₀ (J:=J) (j:=j)
    have hu (s:Signed)(q:Spot c f) : Glints J (fun n=> (D n).debit u s q) (fun n=>(D' n).debit u s q):= (h.whole (fun n=>pull s 0 (U₀ n)) (fun n=>pull s 0 (V n)) (fun n=>S.prediction (pull s 0 (V n)) (Oriented.choice s k)) Z.x q (febrile (Z:=Z) H₀ hz)).prods (oxcart H₀ H₁ hQ hz h hv U₀ he (Frill.still (x:=(0:ℝ)) u) s q) (Q:=fun x y:ℝ=> x-y) (continuous_fst.sub continuous_snd)
    let z:=radiusB Z.x; let P(s:Signed) := posted (turnStore s A) (200*z)
    have hU : Frill J j (0:ℝ) (fun n _=> (D n).quoteNear A u) (fun n _=> (D' n).quoteNear A u):=(Frill.still _).times (Frill.buds Finset.univ fun i _=> Frill.buds (P i) fun j _=>Frill.bare (hu i j))
    have hV : Frill J j (0:ℝ) (fun n _=>(D n).far_bills A) (fun n _=>(D' n).far_bills A):=(Frill.still _).times (Frill.buds Finset.univ fun i _=> Frill.buds (P i) fun j _=>Frill.bare (exhaust H₀ H₁ hQ hz h hv U₀ he i j)); let H':=(D 0).pens A
    have he': Frill J j (0:ℝ) (fun n _=>(D n).steamLog (K n).kin Q.table a₀ A u) (fun n _=>(D' n).steamLog (H n).kin Q.table a₀ A u):= ((((Frill.bare h.beta).neg.times (hU.add hV)).add (Frill.buds (visit A (200*z)) fun i _=> Draft.charges H₀ hz h hg he i)).add (Frill.still (∑ i∈ (D 0).plaza (A.dome (304*z)), (D 0).gentry Q.table a₀ u i))).sub ((Frill.still (H'.card:ℝ)).times (harms h H₀))
    let I:=300*z; let F':=A.dome I
    have hF: Frill J j (0:ℝ) (fun n _=> Mask.tickets A I (V n) k) (fun n _=>Mask.tickets A I (V n) k):=by
          unfold Mask.tickets; exact (Frill.pears F' (fun i _=> canto (F:=fun n=>siteMass (V n) k i) (fun n=>⟨site_nn _ _ _,site_cap _ _ _⟩))).times (Frill.pears (Mask.readBonds F') (fun i _=>canto (F:=fun n=>pinMass (V n) k i) (fun n=>⟨pin_nn ..,pin_cap ..⟩)))
    let L':=(D 0).plaza (A.dome (304*z)); have hx : Frill J j (0:ℝ) (fun n _=> (D n).steam (K n).kin Q.table l W a₀ A u) (fun n _=> (D' n).steam (H n).kin Q.table l W a₀ A u):= (((((he'.via Real.contDiff_exp).times (canto (F:=fun n=> Contract.order ((K n).kin) l (vias S A I) (V n)) (fun n=> Contract.valid_pay ..))).times hF).times (canto (F:=fun n=> profiles A Z.χ I Z.x W (V n) k (U₀ n)) fun n=> Mask.profiles_range ..)).times (Frill.still ((D 0).enforce a₀ u L')))
    exact switch hx.crest ⟨_,tendsto_const_nhds,tendsto_const_nhds⟩ (fun n=> (D n).existSeeds A 300)
end Draft
end YM.ConnectedActivityE6.Lim
