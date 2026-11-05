import YM.FullVolume.Poesy.Xylo
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
open Geo Yard Accout Meadow
variable {M: Bank}(I:Depot Q o x μ L C₀ K)(T:Depot Q o x μ L C₀ H){v v':ℕ→ℝ}
variable (R:∀ n,Station M Chi.canonical (I n) j)(P':∀ n,Station M Chi.canonical (T n) j){B:BudgetPoint}(h:Accord K H B v v') (hp:B.threshold=Pressure.temp x) (he:B.order≤ j)
set_option quotPrecheck false
local notation "L'"=> Beam.marquee (I 0) B
local notation "pl"=> fun n=> plusone (I n) (clav (I n)) Chi.canonical (v n)
local notation "pl'"=>fun n=> plusone (T n) (clav (T n)) Chi.canonical (v' n)
open Epoch
variable {f₀ f₁:ℕ→ℕ}(hv:Tendsto f₀ atTop atTop)(hk:Tendsto f₁ atTop atTop)
include hv hk I T
lemma climbers : ∀ᶠ i in atTop, Meadow.panel (I i) (f₀ i)= Meadow.panel (T i) (f₁ i):=by
   obtain ⟨U,_,h⟩:=vistaP (I 0); have B:BudgetPoint:=Λ.p
   filter_upwards [hv.eventually h,hk.eventually h] with i hi ht; exact (sparks (I 0) (I i) B (f₀ i)).2.trans (hi.trans (ht.symm.trans (sparks (I 0) (T i) B _).2.symm))
include R P' h hp he
lemma bincase : Canopy B (L').reg (fun i=> (Meadow.timbres (χ:=Chi.canonical) (clav (I i)) (v i) (f₀ i)).logRead) (fun i=> (Meadow.timbres (χ:=Chi.canonical) (clav (T i)) (v' i) (f₁ i)).logRead):=by
    let g n:= pl n|>.logRead; let w n:=pl' n|>.logRead; let m n (i:ℕ):Prop:=i∉Meadow.panel (I n) (f₀ n); let u n (i:ℕ):Prop:=i∉ Meadow.panel (T n) (f₁ n)
    have hx:= pallor I T R P' h hp he
    have hp {g:ℕ→ℕ→ Config G c→ℝ}(h:PulseWise B (L').reg g) (m:ℕ→ℕ→Prop) (hp:∀ i j,Decidable (m i j)): PulseWise B (L').reg fun n i=>@ite _ (m n i) (hp n i) (g n i) 0:=by
        constructor; · intro n i; split; exact h.chart ..; exact CouplingShape.reg_const _
        obtain ⟨v,hv,V⟩:=h.sup; refine ⟨v,hv,fun n i=>?_⟩; split; exact V ..; exact CouplingShape.sup_larger (CouplingShape.sup_const 0) (by simpa using hv.value n i)
    have hz: Canopy B (L').reg (fun i j=> if m i j then g i j else 0) (fun i j=> if u i j then w i j else 0):= by
        refine ⟨hp hx.a m (fun i j=>inferInstance),hp hx.b u (fun i j=>inferInstance),fun i b hb=>?_⟩; filter_upwards [hx.sails i b hb,climbers I T hv hk] with n hn he; unfold m u; rw [he]; split; · exact hn
        rw [sub_zero]; exact CouplingShape.sup_larger (CouplingShape.sup_const 0) (by simpa using hb.le)
    convert! hz using 1
    · ext i k V; unfold m g; simp_rw [Meadow.compass,Meadow.petaled,ite_not]
    ext i k V; unfold u w; simp_rw [Meadow.compass,Meadow.petaled,ite_not]
-- finite comparisons.Ship sum proof equivalence.Maps ALL p univ wide regardless .hd.
lemma bannersL (p: Site c)(u:Site c) : Loom B u Finset.univ (fun n=> Meadow.barony (I n) Chi.canonical (f₀ n) (v n) p) (fun n=> Meadow.barony (T n) Chi.canonical (f₁ n) (v' n) p) :=by
     let f n i:= Meadow.garnerAt (I 0) B p i • (pl n).logRead i; let g n i:= Meadow.garnerAt (I 0) B p i • (pl' n).logRead i
     have hv' n: Meadow.barony (I n) Chi.canonical (f₀ n) (v n) p=∑ i ∈ Meadow.panel (I n) (f₀ n), f n i:=by exact Meadow.aster Chi.canonical B (clav (I n)) rfl rfl rfl ..
     have hp' n : Meadow.barony (T n) Chi.canonical (f₁ n) (v' n) p=∑ i∈ Meadow.panel (T n) (f₁ n),g n i:= Meadow.aster Chi.canonical B (clav (T n)) rfl rfl rfl ..
     obtain ⟨U,hU,H⟩:= Epoch.vistaP (I 0); let S n:=Meadow.panel (I n) (f₀ n); let V n:= Meadow.panel (T n) (f₁ n); have he' n:S n⊆U:= (Epoch.sparks (I 0) (I n) B _).2 |>.subset.trans (hU _) ; have ht n: V n⊆U:=(Epoch.sparks (I 0) (T n) B _).2 |>.subset.trans (hU _)
     let f'(n i:ℕ):= if i∈S n then f n i else 0; let g'(n i:ℕ):= if i∈ V n then g n i else 0
     have hL : Loom B u Finset.univ (fun n=>∑ i∈ U,f' n i) (fun n=>∑ i∈U,g' n i) :=by
        refine Loom.tall U (F:=f') (H:=g') fun i _=>?_ ; have H:Loom B u Finset.univ (fun n=> f n i) (fun n=> g n i):= ((Yard.many (pallor I T R P' h hp he) i).moves u Finset.univ (subset_univ _)).seats (garnerAt (I 0) B p i)
        have H':= Loom.shirt H (fun n=>i∈ S n) (fun n=> i∈ V n) ((climbers I T hv hk).mono fun n (hn:S n=V n)=> by rw [hn])
        convert! H' using 1 <;> funext n <;> by_cases he:i∈S n <;> by_cases hh:i∈V n <;> simp [f',g',he,hh]
     have ht' (g:ℕ→ Config G c→ℝ) (x:Finset ℕ) (h:x⊆U) : (∑ i∈x,g i)=∑ i∈U,if i∈x then g i else 0 :=by
         rw [← sum_filter,show (U.filter (·∈x))=x from ?_]; ext i; rw [mem_filter]; exact ⟨And.right,fun hi=>⟨h hi,hi⟩⟩
     simp_rw [hv',hp']; convert! hL using 1
     · exact funext fun i=>ht' (f i) (S i) (he' i)
     exact funext fun i=>ht' (g i) (V i) (ht i)
end YM.ConnectedActivityE6.Lim
