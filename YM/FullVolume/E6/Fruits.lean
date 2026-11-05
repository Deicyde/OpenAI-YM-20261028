import YM.FullVolume.E6.Reform
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
open Polar
variable [FiniteDimensional ℝ E]
open Pressure.Stores Packets Tags
namespace Draft
variable (H₀:∀ n,Cash W x μ L Q o C₀ (K n).tubes (K n).kin)(hQ:∀ n, Promo Q o j x v ℓ a Z.χ (K n).tubes)
   (hz:Z.Paid Q o x) (h:Finish J K H)(he:∀ᶠ i in (J:Filter ℕ), Mode (U i) p j v)(ht:∀ᶠ i in (J:Filter ℕ), Z.Viable (U i p))
set_option quotPrecheck false
local notation "D" => fun n y=> (Z.paints (K n) (U n y))
local notation "D'" => fun n y=> (Z.paints (H n) (U n y))
local notation "t" => Pressure.fiery G Z.x S.patch.L
local notation "R"=> radiusB Z.x
variable (V:ℕ→ Config G f) {w w':ℕ→ E→Directions G f}{z z':ℕ→ E→Air f G}(u:Frill J j p w w')(r:Frill J j p z z')
include H₀ hz h he ht u
include hQ
lemma stoked (A:Stores S) (k: Finset ℕ) : Frill J j p (fun n y=> stock (D n y) o.a (K n).kin W Q.table (w n y) (V n) k A) (fun n y=> stock (D' n y) o.a (H n).kin W Q.table (w' n y) (V n) k A):=by
   let Y:=300*R; let I:= (D 0 p).plaza (A.dome (304*R)); let X':= A.dome Y
   unfold Polar.stock; change Frill _ _ _ (fun n y=> if A.place ⊆ Z.store.place ∧ A.flags=∅ then _ else _) (fun n y=> if A.place ⊆ Z.store.place ∧ A.flags=∅ then _ else _)
   split
   · have hp:Frill J j p (fun n y=> profiles A Z.χ Y Z.x W (V n) Z.k (U n y)) (fun n y=> profiles A Z.χ Y Z.x W (V n) Z.k (U n y)):=
       (Frill.pears (Mask.readFine X' S) (fun i _=> canto (fun n=>Mask.fine_range A Z.χ i t (V n)))).times (Frill.pears (Mask.readBonds X') (fun i _=> hifi Z.χ W V (scaleG he) i A t Z.k))
     have ht': Frill J j p (fun n _=> tickets A Y (V n) Z.k) (fun n _=> tickets A Y (V n) Z.k):=by
        unfold Mask.tickets; exact (Frill.pears X' (fun i _=> canto (F:=fun n=>siteMass (V n) Z.k i) (fun n =>⟨site_nn _ _ _, site_cap _ _ _⟩))).times (Frill.pears (Mask.readBonds X') (fun i _=> canto (F:=fun n=> pinMass (V n) Z.k i) (fun n=>⟨pin_nn ..,pin_cap ..⟩)))
     exact (((((flowing H₀ hQ hz h he ht u V A).via Real.contDiff_exp).times (canto (F:=fun n=>Contract.order (K n|>.kin) k (vias S A Y) (V n)) (fun n=> Contract.valid_pay ..))).times ht').times hp).times (mantle (K:=K) (H:=H) (Z:=Z) (U:=U) u I o.a)
   exact Frill.still _
include r
lemma petals (i: LogIndex c f) : Frill J j p (fun n y=> Polar.logMoment (D n y) o.a (K n).kin Q.table (w n y) (V n) (z n y) i) (fun n y=> Polar.logMoment (D' n y) o.a (H n).kin Q.table (w' n y) (V n) (z' n y) i):=by
    let pA:= D 0 p; have hk I:= mantle (K:=K) (H:=H) (Z:=Z) (U:=U) u I (2*o.a)
    rcases i with i|i|i
    · exact (h.ridge (scaleG he) V Z.x i).times (hk (pA.plaza (Raw.space (K 0).tubes 0 R (K 0).kin i)))
    · rcases i with i|i|i
      · change Frill _ _ _ (fun n y=> hover _ _ _ _ _ _) (fun n y=>hover _ _ _ _ _ _)
        unfold hover; change Frill _ _ _ (fun n y=> if Inside (rowSite S i) Z.store (200*R) then _ else _) (fun n y=> if Inside (rowSite S i) Z.store (200*R) then _ else _); split
        · exact Frill.still _
        exact (((Frill.bare h.beta).neg).times (Frill.still _)).times (((hk (pA.booth (rowSite S i))).times (rootage hQ hz h he ht u V i.1 i.2 true)).add (portico hQ hz h he ht (levied H₀ hQ hz h he ht) i.1 i.2))
      · change Frill _ _ _ (fun n y=>(D n y).undercurrent _) (fun n y=> (D' n y).undercurrent _); unfold undercurrent; change Frill _ _ _ (fun n y=> if voyage Z.store (200*R) i then _ else _) (fun n y=> if voyage Z.store (200*R) i then _ else _); split
        · exact Frill.still _
        exact charges H₀ hz h he ht i
      change Frill _ _ _ (fun n y=> (D n y).solo (w n y) Q.table o.a i) (fun n y=> (D' n y).solo (w' n y) Q.table o.a i)
      have hf (T':Epoch Λ)(V:Config G c)(b:Directions G f): (Z.paints T' V).solo b Q.table o.a i = if i∉ pA.plaza (Z.store.dome (304*R)) ∧ pA.Hot i then (Z.paints T' V).gentry Q.table o.a b i else 0:= rfl
      simp_rw [hf]; split; · exact gears H₀ hz u i
      exact Frill.still _
    exact rowsP H₀ hQ hz h he ht u r i
omit r h ht hz H₀ hQ in
lemma minor (i:WarningAt c f) (k:Finset ℕ): Frill J j p (fun n y=> Polar.sprinkle (D n y) o.a (K n).kin W (w n y) (V n) k i) (fun n y=> Polar.sprinkle (D' n y) o.a (H n).kin W (w' n y) (V n) k i):=by
    let pA:=D 0 p; rcases i with i|i
    · change Frill _ _ _ (fun n y=> Polar.flare _ _ _ _ _ _ _ _) (fun n y=> Polar.flare _ _ _ _ _ _ _ _)
      unfold Polar.flare; change Frill _ _ _ (fun n y=> if mandatory Z.store R i then _ else _) (fun n y=> if mandatory Z.store R i then _ else _); split
      · exact Frill.still _
      apply Frill.times (mantle (K:=K) (H:=H) (Z:=Z) (U:=U) u (pA.plaza (halo R (districts S i))) (2*o.a)); refine Frill.sub ?_ (Frill.still _); rcases i with i|i|i|i|i
      · exact canto (F:=fun n=> Mask.fine Z.store Z.χ i t (V n)) fun n=> fine_range ..
      · exact hifi Z.χ W V (scaleG he) i Z.store t Z.k
      · exact canto (F:=fun n=> pinMass (V n) Z.k i) (b:=Fintype.card S.patch.Points) fun n=>⟨pin_nn .., pin_cap ..⟩
      · exact canto (F:=fun n=>siteMass (V n) Z.k i) (b:=Fintype.card S.patch.FrameTag) fun n=>⟨site_nn ..,site_cap ..⟩
      exact canto (F:=fun n=> Contract.charges (K n).kin k (V n) i) (b:=1) fun n=> by rcases Contract.ordinary (K n).kin k (V n) i with h|h <;> rw [h] <;> simp
    change Frill _ _ _ (fun n y=> (D n y).aura _ _ _) (fun n y=> (D' n y).aura _ _ _)
    have hf(T':Epoch Λ)(V:Config G c)(b:Directions G f): (Z.paints T' V).aura b o.a i = if pA.Hot i ∧ i∉pA.plaza (Z.store.dome (304*R)) then pA.cone o.a b i-1 else 0:=rfl
    simp_rw [hf]; split; · exact ((lamps (Z:=Z) (K:=K) (H:=H) (U:=U) i u o.a).sub (Frill.still _))
    exact Frill.still _
lemma hero (i:Head S)(k:Finset ℕ)(l:ℕ): Frill J j p (fun n y=> Polar.ember (D n y) o.a (K n).kin W Q.table (w n y) (V n) (z n y) k l i) (fun n y=> Polar.ember (D' n y) o.a (H n).kin W Q.table (w' n y) (V n) (z' n y) k l i):=by
    rcases i with i|i|i|i
    · unfold Polar.ember; dsimp only [Sum.elim]; change Frill _ _ _ (fun n y=> if Packets.connected S l R i then _ else _) (fun n y=> if Packets.connected S l R i then _ else _); split; · exact stoked H₀ hQ hz h he ht V u i k
      exact Frill.still _
    · exact (Frill.bare (h.grant i V)).times (mantle (Z:=Z) (K:=K) (H:=H) (U:=U) u ((D 0 p).plaza (Raw.forcedFoot S.ratio 0 R (K 0).kin i)) (2*o.a))
    · exact ((petals H₀ hQ hz h he ht V u r i).via Real.contDiff_exp).sub (Frill.still _)
    exact minor he V u i k
end Draft
end YM.ConnectedActivityE6.Lim
