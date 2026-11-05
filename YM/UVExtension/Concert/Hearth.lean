import YM.UVExtension.Concert.Finale
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Concert
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost Wick PhysicalNext.Repeat Lantern Marlin Song Animals Slide MeasureTheory Set Filter
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {x y W μ γ a b e: ℝ} {χ:Chi} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
   {R:Rep G f}{H:Cash W x μ L Q o a T R} {Y D : Type} [NormedAddCommGroup Y] [NormedSpace ℂ Y] {M:Opening D Y}
    {p:BudgetPoint} (k:ℕ)
open Trio
variable {q w : ℕ} {V:Stars→Side} (hq:∀ i:Stars,(V i).val=2*(q+i.val)) (hw:q+5≤w)
    (U:D→Rep G f) (J:(i:D)→ Cash W x μ L Q o a T (U i)) (F:∀ d, Match.Alliance H (J d) 1 0)
    (fa:D→∀ i:Stars, Trio.Offer G (V i)) (Hq:∀ d,(F d).units=Equiv.refl _)
    (hp:∀ i,R.path=(U i).path) (ha:∀ i,H.supportP=(J i).supportP)
    (hK:p.B=radiusB x)
local notation "O"=> Chi.canonical
-- beacons cert survives cutoff retirement; Amount h when V only. τ excluded here.
def arenaE (p:BudgetPoint)(w:ℕ)(V:Stars→Side)(f:Stars→ℝ): ℝ:= ∑ i:Stars, |ray i| *((Fintype.card (Site (V i)):ℝ)*(2*Trio.tilt p w*(f i+f i)))
def arenaK (V:Stars→Side)(f:Stars→ℝ):ℝ:= ∑ i:Stars, |ray i| *((Fintype.card (Site (V i)):ℝ)*(f i+f i))

variable {A f' v κ e' : ℝ} {g: Stars→ℝ}
    (r:ticketR M p (Beam.marquee H p).reg (preExponent p) (fun d=> (plusone H (F d) Chi.canonical γ).logRead) (fun _=>b)) (hr:∀ d,smoothP p (Beam.marquee H p).reg (plusone H (F d) Chi.canonical γ).logRead)
    (h:Atlas (bell (Beam.marquee H p).hard p.B (p.supportExponent+1+1)) M (fun d i V=> (plusone H (F d) Chi.canonical γ).hardRead i V) (fun _=> e'))
    (hy:∀ i,0≤g i)(hg:∀ i j (u:Fly G (V i) p), Charm M (g i) (fun d=>u.reel (fa d i j))) (hh:∀ i j d, p.Regular univ (fa d i j)) (hb:0≤ b)
    (hE:∀ i:Site c,(coverNumber p.B (neighbors w i):ℝ) ≤ A) (hC:∀ i:Site c,(coverNumber p.B (neighbors (2*w) i):ℝ) ≤ A) (hX:tithe (2*w) (((Animals.ballCost (Meadow.studio Q.halo (radiusB x)):ℝ)*b+(Animals.ballCost (Meadow.studio Q.halo (radiusB x)):ℝ)*b)+arenaK V g) p A≤ f')
    (hn:Progress.DirectedRecipe.Payments.Rates p.B v e' f' κ)

include hw hg hh hy hK hX hn hE hC h r hr Hq hp ha hb

def bookA {G:Gauge}{n:Side}(V:Listing G n) (w:ℕ)(p:BudgetPoint):Listing G n:= pluck p (lodge V w (2*w))
def shapeP (H:Cash W x μ L Q o a T R) {R':Rep G f} {H':Cash W x μ L Q o a T R'}
    (X: Match.Alliance H H' 1 0) {q:ℕ} {V:Stars→Side}(F:∀ i:Stars,(V i).val=2*(q+i.val))(k w:ℕ)(p:BudgetPoint) (u:∀ i,Trio.Offer G (V i))(γ:ℝ):= poursP p (lodge (Beam.marquee H p) w (2*w)) (bison (Meadow.timbres X γ k (χ:=Chi.canonical)) (Trio.ornament F u) (Trio.insight p X γ k F w u))
lemma celebration : ∃ E:D→ Collection.Source G c, E=(fun i=> shapeP H (F i) hq k w p (fa i) γ)∧
    let C:= bookA (Beam.marquee H p) w p
    (∀ i,smoothP p C.reg (E i).logRead) ∧ Nonempty (ticketR M p C.reg (preExponent p) (fun d=>(E d).logRead) (fun _=>b+4*turnFee p*(Real.exp (preExponent p*A)*arenaE p w V g))) ∧
    Nonempty (Atlas (bell C.hard p.B (p.supportExponent+1)) M (fun d i V=> (E d).hardRead i V) (fun _=>v)) := by
  let Y d:= shapeP H (F d) hq k w p (fa d) γ; let B:= Beam.marquee H p
  refine ⟨Y,rfl,?_⟩; intro C'
  let T d:=Trio.ornament (c:=c) hq (fa d); let L d:= Trio.insight p (F d) γ k hq w (fa d); let K d:= bison (Meadow.timbres (F d) (χ:=Chi.canonical) γ k) (T d) (L d)
  have hg' d: smoothP p (leap w) (T d):=by
    intro i; rw [show T d i= _ from Trio.orchard ..]; apply Meadow.regularA; intro j _; apply CouplingShape.reg_scale
    have he (d): p.Regular univ (Trio.froth (fa d j)) := by rw [show Trio.froth (fa d j)=∑ i,fa d j i from funext fun i=> (Finset.sum_apply ..).symm]; exact Meadow.regularA _ fun i _=> hh ..
    exact Slide.regular _ _ (CouplingShape.reg_sub (he d) (CouplingShape.reg_const _)) (fun v=> (neighbors_mem ..).2 ((Slide.village (hq j).ge i v).trans (by have hx:=j.isLt; omega)))
  have hA : 0≤ arenaE p w V g:=sum_nonneg (fun i _=>by unfold Trio.tilt; have h:=hy i; positivity)
  let f:= (pennant H); let X':=Meadow.bouquet H k; obtain ⟨hr',⟨hP⟩⟩:= blackout (C:=B) (fun i=> plusone H (F i) Chi.canonical γ) r (fun i=> (f i).2∈X') (Y':=fun i=> Meadow.timbres (F i) γ k (χ:=Chi.canonical)) (fun i j=> by rw [Meadow.compass]; split <;> rfl) hr
  obtain ⟨hq'⟩:= tribute T (fun u v=> spired hq u hw fa g hh hg hy v) hE hA
  obtain ⟨hp',hY⟩:= blastoff (Beam.marquee H p) _ T L hr' hg' hP hq' (mul_nonneg (Real.exp_pos _).le hA) (2*w)
  refine ⟨hp',hY,?_⟩
  let e:=(Animals.ballCost (Meadow.studio Q.halo (radiusB x)):ℝ)*b; have hz: 0≤arenaK V g:= sum_nonneg (fun i _=> by have h:=hy i; positivity)
  have hx:0≤e:= mul_nonneg (Nat.cast_nonneg _) hb
  have he (o:Site c)(u:Config G c): Charm M (e+e+arenaK V g) (fun i=>L i o u):=by
    have he:= glow H k _ o hK r u
    have hV:= sherbet H k _ o hK r (Fly.star G p _) hr
    unfold L Trio.insight; apply Charm.apart (Charm.apart he ?_) (unearns hq o hw fa g hh hg hy u); simp_rw [Meadow.aster Chi.canonical p _ (hp _) (ha _) (Hq _) γ]; exact hV
  obtain ⟨hκ⟩:= rough L B (fun d=> Meadow.timbres (F d) γ k (χ:=Chi.canonical)) hC T he (add_nonneg (add_nonneg hx hx) hz) hX
  exact brittle (p:=Marlin.raiser p) K (hak (lodge B w (2*w))) h hκ hn
end YM.UVExtension.Concert
