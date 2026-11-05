import YM.UVExtension.Wren.Candor
import YM.UVExtension.Wren.Pods
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

/- One unpermuted lock, actual Berry Works. -/
open AnalyticBridge VerifiedReset Collection Quotes WilsonStartup Extra.Iteration Next.Scheduling
open Song Strata Gala Concert Geo
namespace Chains
-- use four Path width actual via concerted cap `cops`. h.cops Bounds W where W not clip C; Bounds only widths etc; sufficient for `.Invariant` and `.gap` with actual clip unaffected.
variable {P:BudgetPoint}{R:ι→ PathData G}{S:PathData G} (h:Revenues v u R S)
include h
variable [NeBot v]
lemma songsL : Flo v u (fun n=> (R n).cubic) S.cubic:= ⟨h.pos,fun i=>(h.layout i).2.1,fun i=> let ⟨_,_,_,H⟩:=h.cops i; fun j=> (H.invariant j).2.1, h.parked₂.1,h.parked₂.2⟩
lemma songsH : Flo v u (fun n=> (R n).quartic) S.quartic:=⟨h.pos,fun i=>(h.layout i).2.2,fun i=> let ⟨_,_,_,H⟩:=h.cops i; fun j=> (H.invariant j).2.2, h.parked₃.1,h.parked₃.2⟩
lemma songsK: Flo v u (fun n=>(R n).loop) S.loop:=⟨h.pos,fun i=>(h.layout i).1,fun i=> let ⟨_,_,_,H⟩:=h.cops i; fun j=> (H.invariant j).1, h.parked₁.1,h.parked₁.2⟩
lemma strings_v (P:BudgetPoint)(i): strings (n:=c) (R i) P=strings S P:=by
    funext x; rcases x with x|x|x|x; exact congr_fun (Ski.foots h P i) x
    · exact ((songsL h).landsH i x).symm
    · exact ((songsH h).landsH i x).symm
    exact ((songsK h).landsH i x).symm
lemma cashYears {C:Clip}{P:BudgetPoint}(he:Decent C P) {β γ:ι→ℝ}(hb:∃ a,Tendsto β v (𝓝 a))(hg:∃ a,Tendsto γ v (𝓝 a)): Notes v P (strings S P (n:=c)) (fun n=> sounding (R n) C (β n) (γ n)):=by
    obtain ⟨r,hr⟩:=hb; obtain ⟨a,ha⟩:=hg
    let j:=(songsL h).winds (c:=c) P _ hr.neg ; let p:=(songsH h).winds (c:=c) P _ hr.neg
    let y:=(songsK h).windward (c:=c) P (-1); let g:=Ski.vibes (c:=c) h P he _ ha.neg
    -- functions Σ eliminations are nested Pi fibers definitional? Sum.elim η
    exact g.plucks (j.plucks (p.plucks y))
end Chains
open Chains Badge
namespace Choir
variable {H:∀ i:ι,Cash w s q L Q U C (T i) (R i)} (p:Choir v T H k χ)(h:StableR v R)
variable (j:ι)(P:BudgetPoint)(hp:P.threshold=temp s)(hu:P.order ≤ k)
variable [NeBot v][v.IsCountablyGenerated]

abbrev ballads n: Magazine (H j) ≃ Magazine (H n) := Equiv.sumCongr (p.casts h j n) (Equiv.refl _)
def potents (β:ι→ℝ) n m:= Song.opus (H n) (helm (H:=H) n) χ (β n) (p.ballads h j n m)
include p h
lemma registers (n:ι)(m): Beam.contents (H n) P (ballads p h j n m) = Beam.contents (H j) P m:= by
    obtain ⟨u,V,hR⟩:=p.laws.views.cap'; let v:=p.ballads h j n
    have ht (i: Songbook c):Beam.contents (H n) P (v (.inr i))=Beam.contents (H j) P (.inr i):= congr_fun (show strings (n:=c) (T n).down P=strings (T j).down P from Eq.trans (strings_v hR P n) (strings_v hR P j).symm) i
    exact Sum.rec (motive:= fun i=> Beam.contents (H n) P (v i)= Beam.contents (H j) P i) (fun i=> (Badge.dashboard (p.stirs h j n) i ((h.labels j n).2)).symm) ht m
omit p h in
lemma extPose {X Y: Listing G c}(h:X.reg=Y.reg)(hx:X.hard=Y.hard): X=Y:=by rcases X with ⟨a,b⟩; rcases Y with ⟨c,d⟩; exact congr_arg₂ Listing.mk h hx
omit p h in
lemma extendsT {U V:Type}(x:U≃V)(F:V→ RegularAddress c)(z: Seat c×U)(g:U→ RegularAddress c)(he:∀ i,F (x i)=g i): revolve F (Equiv.prodCongr (Equiv.refl _) x z)= revolve g z:= congr_arg (fun t=> Song.line t z.1) (he _)
lemma siteR (n i): (Beam.marquee (H n) P).hard i=(Beam.marquee (H j) P).hard i:=Eq.trans (congr_arg (Refrain.reserve _) (seats (p.stirs h j n) i)) (addrZ ..)
lemma siteD (n i): (Beam.marquee (H n) P).reg i=(Beam.marquee (H j) P).reg i:= (congr_arg (revolve (Beam.contents (H n) P)) (birthday (p.stirs h j n) i)).trans (extendsT (p.ballads h j n) _ (pennant (H j) i) _ (registers p h j P n))
lemma versed (n:ι): Beam.marquee (H n) P=Beam.marquee (H j) P:= extPose (funext (siteD p h j P n)) (funext (siteR p h j P n))
omit h p in
lemma uncast (t:ι)(b : (H t).fragrances): (helm (H:=H) t).furrow b=b:= grass_self _ _
omit h p in
lemma versity (t:ι)(m:(H t).fragrances): sequence (H t) (helm (H:=H) t) χ m=(-1:ℝ) • (fun x=> stream (H t) χ x m):=by unfold Song.sequence; rw [uncast]
omit p h in
lemma orga {X Y Z W:Type}(f:X≃Y)(L:Y→ W)(C:Z→W)(u:X→W)(h: L∘f=u):
    (fun (i:X⊕Z)=> Sum.elim L C (Equiv.sumCongr f (Equiv.refl _) i))=Sum.elim u C:= by subst u; funext i; cases i <;> rfl
lemma royalty (n d): p.potents h j d n=
      Sum.elim (fun i=> (-1:ℝ) • p.rings h j n i) (sounding (T n).down (T n).low (R n).beta (d n)):= orga (p.casts h j n) (Song.sequence (H n) (helm (H:=H) n) χ) _ _ (funext fun i=> versity (H:=H) (χ:=χ) n (p.casts h j n i))
-- Choir composed natural batch.
omit h p in
lemma chorus_label {A B:Type} (V:A≃B)(f:B→ Config G c→ℝ) (i:Seat c×A): Song.choir f (Equiv.prodCongr (Equiv.refl _) V i)=Song.choir (f ∘ V) i:= rfl
lemma taxes (n i d):(plusone (H n) (helm (H:=H) n) χ (d n)).logRead i= Song.choir (potents p h j d n) (pennant (H j) i):=(congr_arg (Song.choir (Song.opus (H n) (helm (H:=H) n) χ (d n))) (birthday (p.stirs h j n) i)).trans (chorus_label (p.ballads h j n) _ (pennant (H j) i))
include hp hu
lemma ranches (d:ι→ℝ)(hf:∃ t,Tendsto d v (𝓝 t))(hC: Decent (T j).low P) : Notes v P (Beam.contents (H j) P) (p.potents h j d) :=by
    let A (n:ι) (i:(H j).fragrances):= (-1:ℝ) • p.rings h j n i
    have hA: Notes v P (Beam.dashboard (H j)) A := (p.sonnets h j _ (fun i=> Beam.see ..) P hp hu).swells _ tendsto_const_nhds
    let b n:= (R n).beta; let V n:=sounding (n:=c) (T n).down (T n).low (b n) (d n)
    have hv:Notes v P (strings (T j).down P) V:=by
       obtain ⟨σ,B,hQ⟩:= p.laws.views.cap'; rw [strings_v hQ P]; obtain ⟨C,hK⟩:=p.laws.views.low
       unfold V; simp_rw [hK]; exact cashYears hQ (hK j ▸ hC) h.beta hf
    exact (show p.potents h j d = (fun n=> Sum.elim (A n) (V n)) from funext fun n=> p.royalty h j n d) ▸ hA.plucks hv
lemma armory (d:ι→ℝ)(hf:∃ t,Tendsto d v (𝓝 t))(hC:Decent (T j).low P): Notes v P (Beam.marquee (H j) P).reg (fun n=> (plusone (H n) (helm (H:=H) n) χ (d n)).logRead) :=by
    have hU := ((ranches p h j P hp hu d hf hC).rotary).draws (pennant (H j)) (pennant _).injective
    let F n:= choir (potents p h j d n) ∘ pennant (H j)
    have ht:(fun n=> (plusone (H n) (helm (H:=H) n) χ (d n)).logRead)=F:=by
       exact funext (fun n=> funext (fun i=> taxes p h j n i d))
    rw [ht]; exact hU
end Choir
end YM.UVExtension.Wren
#print axioms YM.UVExtension.Wren.Choir.armory
