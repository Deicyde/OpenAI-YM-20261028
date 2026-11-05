import YM.UVExtension.Wren.Mesa
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Duet
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wren
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze March Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι} {P:BudgetPoint}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a g u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}
open Matrix MeasureTheory WithLp Shield
open Span Oriented Vine PhysicalNext.Repeat PhysicalNext.Repeat.Match PhysicalNext.Repeat.Greenbelt Wick
open Polar Silica Shield Score Flux Matter Ursell Gas Trees Multiple Refrain

-- Captain leases come together with Score width for all L large and at any calendar.
open AnalyticBridge VerifiedReset Collection Quotes WilsonStartup Extra.Iteration Next.Scheduling
open Song Strata Gala Concert Geo
open Badge Chains
namespace Choir
variable {H:∀ i:ι,Cash w s q L Q U C (T i) (R i)} (p:Choir v T H k χ)(h:StableR v R)
variable (j:ι)(P:BudgetPoint)
variable [NeBot v][v.IsCountablyGenerated]
open Meadow
include h p j
lemma verses (n): Deck.Mint.verse (R n).path (c:=c) (f:=f)=Deck.Mint.verse (R j).path:=by
   rw [(p.laws.upR n).1,(p.laws.upR j).1]; unfold Deck.Mint.verse Raw.atomCharge Atom.length; obtain ⟨u,B,hb⟩:=p.laws.views.cap
   simp_rw [(hb.layout n).1, (hb.layout n).2.1,(hb.layout n).2.2,(hb.layout j).1,(hb.layout j).2.1,(hb.layout j).2.2]
lemma seeding (a: Park c f)(n:ι): Seed (H n) a ↔ Seed (H j) a :=by
    have he : (H j).supportP=(H n).supportP:=p.laws.zones h.toKept j n Q.halo (radiusB s)
    have hx:=(p.verses h j n)
    constructor
    · intro h; refine ⟨he.symm ▸ h.hot,h.sizes,?_⟩; intro i hi; rw [←hx]; exact h.earns _ hi
    intro h; refine ⟨he ▸ h.hot,h.sizes,?_⟩; intro i hi; rw [hx]; exact h.earns _ hi
lemma sons (n:ι)(z): Stir (H j) z ↔ Stir (H n) z:=by
   have hx: Meadow.ground (H n)= Meadow.ground (H j):= by unfold Meadow.ground; rw [p.stirs h]
   exact ⟨fun x=>⟨x.small,(fun i=> (seeding p h j _ n).2 (x.each i)),hx.symm ▸ x.moves⟩,fun x=>⟨x.small, (fun i=>(seeding p h j _ n).1 (x.each i)),hx ▸ x.moves⟩⟩
def tuners n : Poet (H j)≃ Poet (H n):=Equiv.subtypeEquiv (Equiv.refl _) (p.sons h j n)
lemma yokes n q i : i ∈ Meadow.calendar (H j) q ↔ tuners p h j n i∈ Meadow.calendar (H n) q:= by rw [Meadow.tunes,Meadow.tunes]; rfl
lemma stalls (n:ι) (i:Poet (H j)): p.casts h j n (booths (H j) i)=booths (H n) (p.tuners h j n i):= by
   obtain ⟨⟨i,k⟩,hp⟩:= i; change Sigma.mk i _= Sigma.mk i _; congr 1
-- melody hymn size.
lemma ripened (n i): Meadow.ripened (T j).down (radiusB s) i=Meadow.ripened (T n).down (radiusB s) i:=by
    obtain ⟨u,R,hR⟩:= p.laws.views.cap'; have hp n: Meadow.melody (T n).down= Meadow.melody R:=by unfold Meadow.melody Atom.length; simp_rw [Ski.bases hR, (hR.layout n).1,(hR.layout n).2.1,(hR.layout n).2.2]
    unfold Meadow.ripened; rw [hp j,hp n] -- hp n
omit p h j in
lemma unionBallads {A B X Y Z:Type}(T:Finset A)(U:Finset B)(d:Finset Z)(R:A≃B)(P:X≃Y)(L:A↪X)(N:B↪Y)(he:∀ i,i∈T↔ R i∈ U)(ht:∀ i,P (L i)= N (R i))(i:X⊕Z): i∈(T.map L).disjSum d ↔ Equiv.sumCongr P (Equiv.refl Z) i∈ (U.map N).disjSum d:=by
   cases i with
   | inl i=>
    change _↔ Sum.inl (P i)∈_; simp only [inl_mem_disjSum,Finset.mem_map]; constructor
    · rintro ⟨a,hx,hv⟩; exact ⟨_,(he _).1 hx,(ht a).symm.trans (congr_arg P hv)⟩
    rintro ⟨b,hb,h⟩; obtain ⟨a,rfl⟩:= R.surjective b; exact ⟨a,(he _).2 hb,P.injective ((ht a).trans h)⟩
   | inr i=> change Sum.inr i∈_ ↔ Sum.inr i∈_; simp
lemma blossoms (n:ι)(i:Magazine (H j))(q:ℕ) : i∈Meadow.bouquet (H j) q ↔ (p.ballads h j n i) ∈ Meadow.bouquet (H n) q:=by
    unfold Meadow.bouquet; rw [ripened p h j n]; exact unionBallads _ _ _ (p.tuners h j n) (p.casts h j n) _ _ (p.yokes h j n q) (p.stalls h j n) i
lemma in_panel (n i) : Meadow.panel (H j) i = Meadow.panel (H n) i :=by
   ext k; rw [Meadow.petaled,Meadow.petaled,birthday (p.stirs h j n)]; exact p.blossoms h j ..

lemma shareIn (n:ι) (x:Site c)(i): Meadow.share (H j) P x i=Meadow.share (H n) P x (ballads p h j n i) :=by
   refine Sum.rec (motive:=fun i:Magazine (H j)=> Meadow.share (H j) P x i = Meadow.share (H n) P x (p.ballads h j n i)) ?_ ?_ i
   · intro i; change (if x∈_ then _ else (0:ℝ))=(if x∈perf (H n) (p.casts h j n i) then (↑(perf (H n) (p.casts h j n i)).card:ℝ)⁻¹ else 0); rw [p.landscapes h]
   intro i; obtain ⟨u,R,hR⟩:=p.laws.views.cap'; change _=if (strings (T n).down P i).site=x then (1:ℝ) else 0; unfold Meadow.share; simp only [Sum.elim_inr,strings_v hR]
omit h p j in
lemma talents {A B K: Type}(X: A≃B)(f:Site c→A→K)(g:Site c→ B→K)(x: Seat c ×A)(y:Seat c× B)(o:Site c)(he:y= (Equiv.prodCongr (Equiv.refl _) X x))(hp:∀ i j,f i j=g i (X j)): g ((Meadow.spin y.1).symm o) y.2=f ((Meadow.spin x.1).symm o) x.2:=by rw [he]; exact Eq.symm (hp _ _)
lemma tiles (n i y): Meadow.garnerAt (H n) P y i= Meadow.garnerAt (H j) P y i:=talents (p.ballads h j n) (Meadow.share _ _) (Meadow.share _ _) _ _ y (birthday (p.stirs h j n) i) (shareIn p h j P n)

end Choir
end YM.UVExtension.Wren
