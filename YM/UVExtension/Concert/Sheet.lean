import YM.UVExtension.Concert.Hearth
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Concert
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
structure KinBase (R R' : Rep G f) : Prop where
  reg : R.activities.reg=R'.activities.reg
  forced : R.activities.forced=R'.activities.forced
  point : R.p=R'.p
  path : R.path=R'.path
  clip : R.clip=R'.clip
structure Cousin (R R':Rep G f):Prop extends KinBase R R' where
  E : R.activities.E=R'.activities.E
  K : R.activities.K=R'.activities.K
  beta : R.beta=R'.beta
variable (h: KinBase R R') (Y : Match.Alliance H J 1 0)(Y' : Match.Alliance H' J' 1 0)(hY:Y.units=Equiv.refl _)(hY':Y'.units=Equiv.refl _)
include h
lemma samePoster : Beam.marquee H p=Beam.marquee H' p:=by
  obtain ⟨a,b,⟨c,d,e,f⟩,p,q,t⟩:= R; obtain ⟨A,B,⟨C,D,E,F⟩,P,Q,T⟩:=R'; obtain ⟨he,hp,hq,hg,hH⟩:=h; dsimp only at he hp hq hg hH; subst_vars; rfl
lemma samePosting: posting p H=posting p H' := by
  obtain ⟨a,b,⟨c,d,e,f⟩,p,q,t⟩:= R; obtain ⟨A,B,⟨C,D,E,F⟩,P,Q,T⟩:=R'; obtain ⟨he,hp,hq,hg,hH⟩:=h; dsimp only at he hp hq hg hH; subst_vars; rfl
lemma sameGarner (i:Site c) : Meadow.garnerAt H p i=Meadow.garnerAt H' p i:=by
  obtain ⟨a,b,⟨c,d,e,f⟩,p,q,t⟩:= R; obtain ⟨A,B,⟨C,D,E,F⟩,P,Q,T⟩:=R'; obtain ⟨he,hp,hq,hg,hH⟩:=h; dsimp only at he hp hq hg hH; subst_vars; rfl

def parallel := Match.staple (H:=H) (J:=H') h.path h.reg h.forced
def rollM := Equiv.sumCongr (parallel (H:=H) (H':=H') h).furrow (Equiv.refl (Songbook c))
lemma sameDash (i:ℕ) : (Song.pennant H' i).2 = rollM (H':=H') h (Song.pennant H i).2:= by
  obtain ⟨a,b,⟨c,d,e,f⟩,p,q,t⟩:= R; obtain ⟨A,B,⟨C,D,E,F⟩,P,Q,T⟩:=R'; obtain ⟨he,hp,hq,hg,hH⟩:=h; dsimp only at he hp hq hg hH; subst_vars
  generalize e: (Song.pennant H i).2=m
  rw [show (Song.pennant H' i).2=(Song.pennant H i).2 from rfl,e]
  rcases m with z|z; · obtain ⟨k,t⟩:= z; apply congr_arg Sum.inl; rfl
  rfl
lemma samePods (i : Magazine H):i∈Meadow.bouquet H k ↔ rollM (H':=H') h i∈ Meadow.bouquet H' k := by
  rcases i with i|i
  · let K:= parallel (H:=H) (H':=H') h; let hh:= Match.same_area (H:=H) (J:=H') h.path h.reg h.forced
    let f:= Meadow.firstBatch h.path hh; change Sum.inl i∈Meadow.bouquet H k ↔ Sum.inl (K.furrow i) ∈ Meadow.bouquet H' k
    simp only [Meadow.bouquet,Finset.inl_mem_disjSum,Finset.mem_map]
    have he i : i∈Meadow.calendar H k ↔ f i∈ Meadow.calendar H' k:= by rw [Meadow.tunes,Meadow.tunes]; rfl
    constructor
    · rintro ⟨u,hu,hΔ⟩; exact ⟨f u,(he _).1 hu,(Meadow.identifies K h.path rfl hh u).symm.trans (congr_arg _ hΔ)⟩
    rintro ⟨u,hu,hΔ⟩; obtain ⟨j,rfl⟩:= f.surjective u; exact ⟨j,(he _).2 hu,K.furrow.injective ((Meadow.identifies K h.path rfl hh j).trans hΔ)⟩
  change Sum.inr i∈_ ↔ Sum.inr i ∈_; rw [Meadow.bouquet, Meadow.bouquet]; simp only [Finset.inr_mem_disjSum]
lemma samePanel : Meadow.panel H k=Meadow.panel H' k:=by
  ext i; rw [petaled,petaled,sameDash (H:=H) h,samePods (H':=H') k h]
include hY hY'
lemma samePlus (he:Cousin P₀ P') : (plusone H Y χ γ)=plusone H' Y' χ γ:= by
  obtain ⟨a,b,⟨c,d,e,f⟩,p,q,t⟩:= R; obtain ⟨A,B,⟨C,D,E,F⟩,P,Q,T⟩:=R'; obtain ⟨hg,hp,hq,hh,hH⟩:=h; dsimp only at hg hp hq hh hH; subst_vars
  obtain ⟨a,b,⟨c,d,e,f⟩,p,q,t⟩:= P₀; obtain ⟨A,B,⟨C,D,E,F⟩,P,Q,T⟩:=P'; obtain ⟨⟨hg,hp,hq,hh,hH⟩,hz,hV,hv⟩:=he; dsimp only at hg hp hq hh hH hz hV hv; subst_vars
  rcases Y with ⟨Y,hX,hL⟩; rcases Y' with ⟨Y',ha,hK⟩; dsimp only at hY hY'; subst_vars
  rfl
lemma sameBook (he:Cousin P₀ P') : Meadow.timbres Y (χ:=χ) γ k=Meadow.timbres Y' (χ:=χ) γ k:=by
  have hh:=samePlus (χ:=χ) γ h Y Y' hY hY' he
  have hx : (Meadow.timbres Y (χ:=χ) γ k).logRead=(Meadow.timbres Y' (χ:=χ) γ k).logRead:=by
    funext i
    have hp: (Song.pennant H i).2∈ Meadow.bouquet H k ↔ (Song.pennant H' i).2∈ Meadow.bouquet H' k:= by rw [sameDash (H':=H') (H:=H) h]; exact samePods k h _
    rw [Meadow.compass,Meadow.compass,hh]; split; next h=> exact (if_pos (hp.mp h)).symm
    next h=> exact (if_neg (hp.not.mp h)).symm
  have hb:= congr_arg Collection.Source.hardRead hh
  exact (show ∀ (x y:Collection.Source G c), x.logRead=y.logRead→ x.hardRead=y.hardRead→x=y from by rintro ⟨x,y⟩ ⟨a,b⟩ he he'; exact congr_arg₂ _ he he') _ _ hx hb
omit h hY hY'
include p
lemma samePrint (he:Cousin P₀ P') : Meadow.barony J χ k γ= Meadow.barony J' χ k γ:= by
  let X:=parallel (H:=J) (H':=J') he.toKinBase; let Y:Match.Alliance J J 1 0:= Match.staple rfl rfl rfl
  have hv:= samePlus (χ:=χ) γ (H:=J) (H':=J) ⟨rfl,rfl,rfl,rfl,rfl⟩ Y X rfl rfl he
  funext i; rw [Meadow.aster χ p Y rfl rfl rfl,Meadow.aster χ p X he.path (Match.same_area he.path he.reg he.forced) rfl,hv]
include h hY hY'
lemma sameArts {q w:ℕ} {V:Stars→Side} (hq:∀ i:Stars,(V i).val=2*(q+i.val)) (O:∀ i,Trio.Offer G (V i))
   (he:Cousin P₀ P') : shapeP H Y hq k w p O γ = shapeP H' Y' hq k w p O γ:=by
  have hs : Trio.insight p Y γ k hq w O= Trio.insight p Y' γ k hq w O := by
    funext i y
    unfold Trio.insight Trio.earned; rw [samePanel (H:=H) (H':=H') k h, samePrint (χ:=Chi.canonical) (J:=J) (J':=J') p k γ he, samePlus (χ:=Chi.canonical) γ h Y Y' hY hY' he, samePoster (H:=H) (H':=H') p h,sameGarner (H:=H) (H':=H') p h]
  unfold shapeP; rw [hs, samePoster (H:=H) (H':=H') p h,sameBook k γ h Y Y' hY hY' he]
end YM.UVExtension.Concert
