import YM.UVExtension.Linden.Ranch
import YM.UVExtension.Linden.Life
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Blush.Wind
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Bud
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost Wick PhysicalNext.Repeat Lantern Marlin Song Animals Slide Meadow MeasureTheory Set Filter
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {x y W μ γ a b e: ℝ} {χ:Chi} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
   {R R' P₀ P' : Rep G f}{H:Cash W x μ L Q o a T R} {H':Cash W x μ L Q o a T R'} {J:Cash W x μ L Q o a T P₀}{J':Cash W x μ L Q o a T P'}
   (p:BudgetPoint) (k:ℕ) (γ:ℝ)

open Linden Willow Guild Refrain Ovens Progress.DirectedRecipe Lotus Concert Daisy Daisy.Charity Match
variable {M:Lotus.Leaf P₀} {N:Lotus.Leaf P'}
structure Mate {G:Gauge}{n:Side}{P P':RG.Rep G n} (M:Lotus.Leaf P)(N:Lotus.Leaf P'):Prop where
    cousins : Cousin P P'
    turn : M.turn=N.turn
    payload : M.ingredient=N.ingredient -- DOES NOT depend on weight or any proofs info. -/
variable (pay:Mate M N)
include pay

variable (h: KinBase R R') (Y : Match.Alliance H J 1 0)(Y' : Match.Alliance H' J' 1 0)(hY:Y.units=Equiv.refl _)(hY':Y'.units=Equiv.refl _)

include hY hY'
-- ambient base H may differ.H-to-H' independent of J! stanza compares future lookups.
variable (tH: Match.Alliance H H' 1 0)(hT:tH.units=Equiv.refl _)
include h hT
lemma mate_ar (i:H.fragrances) : matin M J (Y.furrow i) χ=matin N J' (Y'.furrow (tH.furrow i)) χ:=by
   obtain ⟨a,b1,⟨c,d,e,f⟩,p,q,t⟩:= R; obtain ⟨A,B,⟨C,D,E,F⟩,P,Q,T0⟩:=R'; obtain ⟨he,hp,hq,hg,hH⟩:=h; dsimp only at he hp hq hg hH; subst_vars
   obtain ⟨a,b1,⟨c,d,e,f⟩,p,q,t⟩:= P₀; obtain ⟨A,B,⟨C,D,E,F⟩,P,Q,T0⟩:=P'; obtain ⟨⟨⟨hY0,hY1,hP,hV,hL⟩,hR',hk,hβ⟩,hr,h⟩:=pay
   dsimp only at hY0 hY1 hP hV hL hR' hk hβ; subst_vars
   rcases Y with ⟨Y,hv,hk⟩; rcases Y' with ⟨Z,hz,ht⟩; rcases tH with ⟨W,hw,hF⟩; dsimp only at hY hY' hT; subst_vars
   rcases i with ⟨k,v⟩; rcases M with ⟨F,f0,ha,hb,hc,W,hw',hp,Hv⟩; rcases N with ⟨Y,m0,h'a,h'pay,h'c,h',h'_V,h1,h2⟩; dsimp only at hr h; subst_vars; rfl
omit hT
lemma pollenV : Daisy.Charity.veranda M J χ H Y= Daisy.Charity.veranda N J' χ H' Y':=by
   obtain ⟨a,b1,⟨c,d,e,f⟩,p,q,t⟩:= R; obtain ⟨A,B,⟨C,D,E,F⟩,P,Q,T0⟩:=R'; obtain ⟨he,hp,hq,hg,hH⟩:=h; dsimp only at he hp hq hg hH; subst_vars
   obtain ⟨a,b1,⟨c,d,e,f⟩,p,q,t⟩:= P₀; obtain ⟨A,B,⟨C,D,E,F⟩,P,Q,T0⟩:=P'; obtain ⟨⟨⟨hY0,hY1,hP,hV,hL⟩,hR',hk,hβ⟩,hr,h⟩:=pay
   dsimp only at hY0 hY1 hP hV hL hR' hk hβ; subst_vars
   rcases Y with ⟨Y,hv,hk⟩; rcases Y' with ⟨Z,hz,ht⟩; dsimp only at hY hY'; subst_vars
   rcases M with ⟨F,f0,ha,hb,hc,W,hw',hp,Hv⟩; rcases N with ⟨Y,m0,h'a,h'pay,h'c,h',h'_V,h1,h2⟩; dsimp only at hr h; subst_vars; rfl
omit pay
lemma opusSame (hc:Cousin P₀ P') {q w:ℕ} {V:Stars→Side} (hq:∀ i:Stars,(V i).val=2*(q+i.val)) (O:∀ i,Trio.Offer G (V i)):
    bison (Meadow.timbres Y (χ:=Chi.canonical) γ k) (Trio.ornament hq O) (Trio.insight p Y γ k hq w O) = bison (Meadow.timbres Y' (χ:=Chi.canonical) γ k) (Trio.ornament hq O) (Trio.insight p Y' γ k hq w O):= by
   have hs : Trio.insight p Y γ k hq w O= Trio.insight p Y' γ k hq w O := by
    funext i y
    unfold Trio.insight Trio.earned; rw [samePanel (H:=H) (H':=H') k h, samePrint (χ:=Chi.canonical) (J:=J) (J':=J') p k γ hc, samePlus (χ:=Chi.canonical) γ h Y Y' hY hY' hc, samePoster (H:=H) (H':=H') p h,sameGarner (H:=H) (H':=H') p h]
   rw [hs, sameBook k γ h Y Y' hY hY' hc]
-- structural support doesn't need mate.cousin
omit h hY hY'
lemma loci (Y:Match.Alliance J J' 1 0)(h:KinBase P₀ P')(hv:Y.units=Equiv.refl _)(hp:M.turn=N.turn) (p:J.fragrances) (y:Site c): locus M J y p=locus N J' y (Y.furrow p):=by
   obtain ⟨a,b,⟨c,d,e,f⟩,p0,q,t⟩:= P₀; obtain ⟨A,B,⟨C,D,E,F⟩,P,Q,T⟩:=P'; obtain ⟨hY,hp',hq,hg,hH⟩:=h; dsimp only at hY hp' hq hg hH; subst_vars
   rcases Y with ⟨Y,hx,he⟩; dsimp only at hv; subst_vars; rcases p with ⟨n,f⟩; unfold locus speaks; rw [hp]; rfl
lemma slotsP (Y:Match.Alliance J J' 1 0)(h:KinBase P₀ P')(hv:Y.units=Equiv.refl _)(p:J.fragrances) : Blush.enter J' (Y.furrow p)= Blush.enter J p:=by
   obtain ⟨a,b,⟨c,d,e,f⟩,p0,q,t⟩:= P₀; obtain ⟨A,B,⟨C,D,E,F⟩,P,Q,T⟩:=P'; obtain ⟨hY,hp',hq,hg,hH⟩:=h; dsimp only at hY hp' hq hg hH; subst_vars
   rcases Y with ⟨Y,hx,he⟩; dsimp only at hv; subst_vars; rcases p with ⟨n,f⟩; rfl
end YM.UVExtension.Bud
