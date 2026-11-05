import YM.FullVolume.Poesy.Fits
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
open Yard Accout Slide Trio Meadow
variable {A:Stars→Side}{l z:ℕ}
variable {M: Bank}(I:Depot Q o x μ L C₀ K)(T:Depot Q o x μ L C₀ H){v v':ℕ→ℝ}
variable (R:∀ n,Station M Chi.canonical (I n) j)(P':∀ n,Station M Chi.canonical (T n) j){B:BudgetPoint}(h:Accord K H B v v') (hp:B.threshold=Pressure.temp x) (he:B.order≤ j)
    {f₀ f₁:ℕ→ℕ}(hv:Tendsto f₀ atTop atTop)(hk:Tendsto f₁ atTop atTop)
variable {fa ga: ℕ→∀ i:Stars, Trio.Offer G (A i)}(hd:∀ i,(A i).val=2*(l+i.val))(hP:∀ i j,Loom B 0 Finset.univ (fun n=>fa n i j) (fun n=>ga n i j))(hl:l+4≤z)
set_option quotPrecheck false
local notation "L'"=> Beam.marquee (I 0) B
local notation "pl"=> fun n=> plusone (I n) (clav (I n)) Chi.canonical (v n)
local notation "pl'"=>fun n=> plusone (T n) (clav (T n)) Chi.canonical (v' n)
include I T R P' h hp he hv hk hd hP hl
lemma nocturnal (u:Site c): Solo (fun n=> insight B (clav (I n)) (v n) (f₀ n) hd z (fa n) u) (fun n=>insight B (clav (T n)) (v' n) (f₁ n) hd z (ga n) u):=by
    have hh:= bannersL I T R P' h hp he hv hk u u
    have ht: Solo (fun n (_:Config G c)=>Meadow.barony (I n) Chi.canonical (f₀ n) (v n) u 1) (fun n _=>Meadow.barony (T n) Chi.canonical (f₁ n) (v' n) u 1):=by
         have he := (Solo.born hh).still 1
         simp_rw [masked_eq B.threshold _ _ 1 (CouplingShape.clear_one B _)] at he; exact he
    have hV:=pallor I T R P' h hp he; let S n:= Meadow.panel (I n) (f₀ n); let X n:= Meadow.panel (T n) (f₁ n)
    let f n i (U:Config G c):= Meadow.garnerAt (I n) B u i*(((Beam.marquee (I n) B).read (pl n)).regularOccurrence B i U)
    let g n i (U:Config G c):= Meadow.garnerAt (T n) B u i*(((Beam.marquee (T n) B).read (pl' n)).regularOccurrence B i U)
    have hg i : Solo (fun n=> f n i) (fun n=>g n i):= (Solo.born (Yard.many hV i)).coins (Meadow.garnerAt (I 0) B u i)
    refine (Solo.minus (Solo.minus (F:=fun n U=> ∑ i∈ S n,f n i U) (H:=fun n U=>∑ i∈ X n,g n i U) ?_ ht) (unearnedF hd hP hl u)); obtain ⟨U,hS,hX⟩:= Epoch.vistaP (I 0)
    have hz n:S n⊆U:= (Epoch.sparks (I 0) (I n) B _).2.subset.trans (hS _); have he' n: X n ⊆ U:= (Epoch.sparks (I 0) (T n) B _).2.subset.trans (hS _)
    have hh n V (F:ℕ→ℕ→ Config G c→ℝ) (x:Finset ℕ) (hp:x⊆U): (∑ i∈x,F n i V)=∑ i∈U,if i ∈x then F n i V else 0:=by rw [← Finset.sum_filter, show U.filter (· ∈ x)= x from ?_]; ext i; rw [mem_filter]; exact ⟨And.right,fun h=>⟨hp h,h⟩⟩
    simp_rw [fun n V=> hh n V f (S n) (hz n),fun n V=>hh n V g (X n) (he' n)]; refine Solo.total U fun i _=>?_ ; exact Solo.stitching (hg i) (fun n=> i∈ S n) (fun n=> i∈ X n) ((climbers I T hv hk).mono fun n (h:S n=X n)=> by rw [h])
end YM.ConnectedActivityE6.Lim
