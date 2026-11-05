import YM.UVExtension.Concert.Sheet
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
open Deck Mint
variable (h: KinBase R R') (he : R.beta=R'.beta)
include h he
lemma rlike :∀ (n q:ℕ), areas R T n q=areas R' T n q ∧ troupe T R n q=troupe T R' n q:=by
  obtain ⟨a,b,⟨c,d,e,f⟩,p,q,t⟩:= R; obtain ⟨A,B,⟨C,D,E,F⟩,P,P',T⟩:=R'; obtain ⟨hY,hp,hq,hg,hH⟩:=h; dsimp only at hY hp hq hg hH he; subst_vars
  exact fun n q=> ⟨rfl,rfl⟩
lemma legacy (Y: Mint.Music c f){F:Tree.Forest S.ratio}(v:Coat T F)(A: Directions G f)(U: Config G f)(Z: Air f G)(ff:Finset ℕ) : Polar.ember v a R W Q.table A U Z ff Q.halo (Mint.disc S Y)= Polar.ember v a R' W Q.table A U Z ff Q.halo (Mint.disc S Y):=by
  obtain ⟨a,b,⟨c,d,e,f⟩,p,q,t⟩:= R; obtain ⟨A,B,⟨C,D,E,F⟩,P,P',T⟩:=R'; obtain ⟨hY,hp,hq,hg,hH⟩:=h; dsimp only at hY hp hq hg hH he; subst_vars
  rcases Y with a|a|a|a
  all_goals rfl
lemma purified (X:Molecule S)(hk:∀ i∈ X,i ∈ Set.range (Mint.disc S)) {F: Tree.Forest S.ratio} (v: Coat T F) : Stained.fringe v W o.a X R Q.table Q.halo= Stained.fringe v W o.a X R' Q.table Q.halo := by
  unfold Stained.fringe; apply integral_congr_ae; filter_upwards with d
  let H:= rlike (T:=T) h he Q.halo (v.rinse d).B
  unfold shelter; rw [H.1, H.2]; split; next hX=>
    unfold seating; rw [show Matter.ground R T Q.halo _ X=Matter.ground R' T Q.halo (v.rinse d).B X from congr_arg (X.biUnion ·) H.1]
    apply congr_arg likely; funext i; unfold bars; apply integral_congr_ae; filter_upwards with w; apply integral_congr_ae; filter_upwards with z
    unfold Polar.floating; rw [he]; refine congr_arg₂ HMul.hMul rfl ?_; refine Finset.prod_congr rfl fun n hn=> ?_ ; obtain ⟨u,rfl⟩:= hk n hn; exact legacy h he u _ _ _ _ _
  rfl
omit h he
open March Greenbelt
variable (H)(Y:Match.Alliance H J 1 0)(Y':Match.Alliance H J' 1 0)(hY:Y.units=Equiv.refl _)(hY':Y'.units=Equiv.refl _)
variable (h2:KinBase P₀ P')(he2:P₀.beta=P'.beta)
include Y Y' hY hY' h2 he2
lemma agedPetal (i:H.ThinP) (hP:∀ j∈i.val,j∈ Set.range (Mint.disc S)) (U: Config G c):leaflet J χ U (Y.bearing i)=leaflet J' χ U (Y'.bearing i):=by
  have ht: (Y.bearing i).val=i.val:= by change Y.units _=_; rw [hY]; rfl
  have hv: (Y'.bearing i).val=i.val:= by change Y'.units _=_; rw [hY']; rfl
  unfold March.leaflet; rw [ht,hv]; apply congr_arg likely; funext X; exact purified h2 he2 _ hP _
lemma podium_both (i:H.fragrances) (hP:∀ j (v),v∈ (i.2 j).val → v∈Set.range (Mint.disc S)) : sequence H Y χ i= sequence H Y' χ i:=by
  funext U; change (-1:ℝ)*Blaze.March.stream J χ U (Y.furrow i) =(-1:ℝ)* Blaze.March.stream J' χ U (Y'.furrow i)
  let f:= leaflet J χ U ∘ Y.bearing; let g:=leaflet J' χ U ∘ Y'.bearing
  have hx := Match.sale Y.bearing f (leaflet J χ U) Y.sec (fun i=> rfl) i
  have hy := Match.sale Y'.bearing g (leaflet J' χ U) Y'.sec (fun i=> rfl) i
  suffices h : Gas.term H.seam f i=Gas.term H.seam g i from congr_arg ((-1:ℝ)*·) (hx.symm.trans (h.trans hy))
  have hF(v): f (i.snd v)=g (i.snd v):= agedPetal H Y Y' hY hY' h2 he2 (i.snd v) (hP v) U
  unfold Gas.term; simp_rw [hF]
lemma recorded (z: Poet H) : sequence H Y χ (Meadow.booths H z)= sequence H Y' χ (Meadow.booths H z):= by
  apply podium_both H Y Y' hY hY' h2 he2; intro t j hj
  change j ∈ Mint.hatch S (z.val.snd t) at hj; obtain ⟨u,hu,hv⟩:=Finset.mem_map.mp hj; exact ⟨u,hv⟩
lemma ages (i:ℕ) (ht: Meadow.debris H k i) : (plusone H Y χ γ).logRead i=(plusone H Y' χ γ).logRead i:=by
  let T := pennant H; let o:= T i; suffices hh:opus H Y χ γ o.2=opus H Y' χ γ o.2 by
    change Rim c • (_ ∘ o.1.view)= Rim c • (_ ∘ o.1.view); rw [hh]
  have hg:= ht.1; change ¬Meadow.keep H o.2 at hg
  rcases hx:o.2 with i|i
  · rw [hx] at hg; change ¬i∉ Set.range (Meadow.booths H) at hg; obtain ⟨z,rfl⟩:= not_not.mp hg; let v:= Meadow.booths H z
    exact recorded H Y Y' hY hY' h2 he2 z
  change sounding _ _ P₀.beta _ _= sounding _ _ P'.beta _ _; rw [he2]
end YM.UVExtension.Concert
