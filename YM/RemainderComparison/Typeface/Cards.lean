import YM.RemainderComparison.Serif.Stage

/-!
# Holding all test/future kernel costs in the activity norm

This is naturality of costs across *all* maker instantiations P.Portal.Lit: use to avoid pointwise-in-X angle sup failing to pay after intersections. Slot registration uses a summons for each α in a ball (or arbitrary type); physical interpretation of multilinear witness separate. Uses no continuity in α.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Typeface
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι β : Type} {α:Type*}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J I:ℕ}(χ:Chi)
open Lyric Mosaic Muse Sleet Serif

structure Portrait (R:Rep G f)(α:Type*) where
  wing : Wing
  weight : ℝ
  angle : α→ Leaf R
  turned j: (angle j).turn=wing
  budget j: (angle j).weight=weight
variable (M:ι→Portrait R α) (x y:α) (l:ι→ℝ)

def brand (i : ι) : Lotus.Leaf R where
   turn:=(M i).wing
   ingredient:= ((M i).angle x).ingredient
   weight:=(M i).weight
   glows:=Leaf.glows _
   borel:=Leaf.borel _
   scopedR:=(M i).turned x ▸ ((M i).angle x).scopedR
   grant:=fun U hu=> (M i).turned x ▸ ((M i).angle x).grant U hu
   blank:=(M i).turned x ▸ ((M i).angle x).blank
   earn:= fun U=> (M i).budget x ▸ ((M i).angle x).earn U
lemma photo (i:ι): brand M x i= (M i).angle x:=by
   have h:∀ (a b:Leaf R),a.turn=b.turn→a.ingredient=b.ingredient→a.weight=b.weight→ a=b:=by rintro ⟨u,v,w,a,b,c,d,e,h⟩ ⟨x,y,z,r,s,t,v1,h1,h2⟩ hu hx ht; subst_vars; rfl
   exact h _ _ ((M i).turned x|>.symm) rfl ((M i).budget x|>.symm)
local notation "Vx"=> brand M x
local notation "Vy" => brand M y

lemma earn (i:Drums Vx S) : (team (Vx) i).weight=(team (Vy) i).weight:=by simp_rw [Palette.worth];rfl
lemma notes (U : Pad H j χ)(i:Sleet.Staff Vx H): Muse.toll Vx H l (Lyric.floats Vx H χ U.S.N) j J i=Muse.toll Vy H l (Lyric.floats Vy H χ U.S.N) j J i:=by
    unfold Muse.toll Lyric.Bill; refine congr_arg ((invests Vx H i.1 i.2 l)*·) ?_; unfold Lyric.dividend Lyric.adjectives; refine congr_arg (_ * ·) (congr_arg (_ * ·) (Finset.prod_congr rfl fun a _=>congr_arg ((2:ℝ)^j*·) ?_))
    unfold floats; rw [Typeface.earn M x y]; rfl
lemma vision (Q:Brake H j χ)(E:Set ℕ)(w:ℕ→ℝ)(J:ℕ) (i:Sleet.Staff Vx H): Muse.toll Vx H l (Muse.song Vx H χ Q E w) j J i = Muse.toll Vy H l (Muse.song Vy H χ Q E w) j J i:=by
    unfold Muse.toll Lyric.Bill; refine congr_arg ((invests Vx H i.1 i.2 l)*·) ?_; unfold Lyric.dividend Lyric.adjectives; refine congr_arg (_ * ·) (congr_arg (_ * ·) (Finset.prod_congr rfl fun a _=> congr_arg ((2:ℝ)^j* ·) ?_))
    unfold Muse.song Halo.melod; rw [Typeface.earn M x y]; rfl

variable (Z:Set ι)(δ:ℝ)
lemma feed (i:Muse.Flak Vx H) : Muse.pitch Vx H χ Z l δ i=Muse.pitch Vy H χ Z l δ i:=by
    -- check defeq
    have hh(p:H.Chapter)(w:Mosaic.Stone Vx H p) : (panel Vx H χ p w).letters=(panel Vy H χ p w).letters:=by cases p<;>rfl
    have ht : (Mosaic.parade Vx H χ i.1 i.2).letters=(Mosaic.parade Vy H χ i.1 i.2).letters:= Finset.sum_congr rfl (fun a _=> Finset.sum_congr rfl fun k _=> hh _ _)
    have hF(p:H.Chapter)(l:ι→ℝ) (w:Mosaic.Stone Vx H p) : Mosaic.pay Vx H l p w=Mosaic.pay Vy H l p w:=by cases p<;>rfl
    unfold Muse.pitch Mosaic.Bank; rw [ht]; split; next h => exact congr_arg (_*·) (Finset.prod_congr rfl fun a _=> congr_arg (·/_) (Finset.prod_congr rfl fun j _=>hF _ _ _))
    next=>rfl
lemma along (i:Muse.Flak Vx H) : Muse.within Vx H χ Z k i↔ Muse.within Vy H χ Z k i:=by
    unfold Muse.within; suffices h: (parade Vx H χ i.1 i.2).letters=(parade Vy H χ i.1 i.2).letters by rw [h]
    have hh(p:H.Chapter)(w:Mosaic.Stone Vx H p) : (panel Vx H χ p w).letters=(panel Vy H χ p w).letters:=by cases p<;>rfl
    exact Finset.sum_congr rfl (fun a _=> Finset.sum_congr rfl fun k _=> hh _ _ )
end YM.RemainderComparison.Typeface
