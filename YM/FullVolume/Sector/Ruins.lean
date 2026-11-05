import YM.FullVolume.Sector.Clout
/-! Quantified release, coordinate.Eyrie. Both Omega and broad. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Empire
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Alabaster FullVolume.Ray
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}
    {x₀ μ C:ℝ} {H : Cash W x₀ μ L Q o C T R} -- implicit v
    {v s t b δ A n B : ℝ} {j k : ℕ}
variable {F : Tree.Forest S.ratio} {i η r q u d L' A' f':ℝ} {K:ℕ} {χ:Chi}
open Blaze.March Tune Lyre
variable {U:Tune H v δ} (hQ: Q.rate ≤ -(7/16:ℝ))
-- output currencies targeted. Usable by Monadic curves at Fixed.Can.
abbrev pottery (G:Gauge) (L:Side) (x:ℝ):= betaF G x L ^ (-(3/8):ℝ)
structure Candy (U:Tune H v δ)(O:Chi) (e S:ℝ) (P:BudgetPoint) : Prop where
  high : 2≤v
  phases : ∃ f:H.fragrances→ℝ, Ac.Hit (Captain.reachability (H:=H)) (radiusB x₀) f e S ∧
       ∀ i:H.fragrances,∀ z∈ Captain.reachability i, ∀ (w:Rung) (η:ℝ), (∀ i:ℕ, ‖FullVolume.Ray.trace w (fun x=>(x/(v/2))^i)‖ ≤ η)→
         P.supBounds z (Captain.reachability i) (fun V => FullVolume.Ray.trace w (fun t=> Lyre.stamina (χ:=O) (U:=U) i t V)) (f i*η)
  loans : ∃ f:H.Chainbook→ℝ,Ac.Hit H.library (radiusB x₀) f e (softW Q L μ x₀) ∧ ∀ i:H.Chainbook,∀ V, Scout (v/2) (U.fellows O V i) (f i)
  -- Mark.Curve can assume supplier via independent Permit
private lemma degreeW {A : ℝ→ℝ}(hp:Rate G L v A) (u:ℝ) : Rate G L v (fun x=> Trees.degreePrice (radiusB x) (A x) u) := by
  have ht:= width_rate G L 1 0; simp only [one_mul,add_zero] at ht
  simpa only [Trees.degreePrice,Trees.stretch, zero_add, div_eq_mul_inv] using! ((((ht.mul hp).mul_right u⁻¹).mul_left 4))
private lemma beaconK (r b v : ℝ→ℝ) (hr:Rate G L 0 r)(hp:Rate G L 0 b)(hv:Rate G L 0 v) (j k:ℕ) : Rate G L 0 (fun x=> spicesF G (r x) (b x) (v x) k j):=by
  have ht:= Rate.const (G:=G) (L:=L) 1; unfold spicesF
  simpa only [zero_mul,zero_add] using! (((ht.add ((hp.mul_right (2^k:ℝ)).add (hr.mul_left 2))).pow j).mul_left (FullVolume.Ray.Fold.charge j * FullVolume.Ray.Weigh.pattern j)).mul (ht.add (hv.compare (v:=fun x=> |v x|) (Eventually.of_forall fun x=>(abs_abs _).le)))
-- purchases H(turn) pre-L for this Query Q. Any compatible H. not populated tuples.
include hQ
lemma candidates : ∃ N:ℕ,∀ (L:Side),N≤L.val→∀ (D:Patch), D.Branches P.bind G→∀ (j m:ℕ) (χ:Chi)(W μ:ℝ),0<W→0<μ→∀ (o:Target.Order G W) (C e:ℝ), 0≤e→ e<Q.exp → ∀ᶠ x in atTop,∀ (c f:Side) (S:StepData c f)(T:Tube G S), S.patch=D→ Stamp T→ ∀ (R:Rep G f) (H:Cash W x μ L Q o C T R), ∀ (U:Tune H (fire G L x) (thaw G L x)) (P:BudgetPoint), P.power=m→ P.threshold=Pressure.temp x → P.order=j →Candy U χ e (pottery G L x) P:=by
  obtain ⟨n,H⟩:= womb P Q
  refine ⟨n,?_⟩; intro L hL D hD i m χ W μ hW hμ o C e he hx
  obtain ⟨d,A,hp⟩:= Eider.weave G; obtain ⟨K,hK,hG⟩:= March.oar G i
  let a x:=2*Pressure.fiery G x L; let f x:= ((i:ℝ)+1)*K*a x
  have hr : Rate G L (-(1/2)) a:= Rate.flame.mul_left _; have hR : Rate G L (-(1/2)) f:=hr.mul_left _
  have hQ' : ∀ᶠ x in atTop,0<a x:= ((Work.E09.betaF_growth G L).eventually_gt_atTop 0).mono fun x h=> mul_pos (by norm_num) (Work.E09.temp_pos h)
  obtain ⟨C',d',r,p,k,hC,hp₁,hK₁,hX⟩:= H L hL D hD i χ W hW μ hμ o d A hp f hR (hQ'.mono fun x h=> by unfold f; positivity)
  obtain ⟨V,t,hv,hF⟩:= Flux.walksW G L (payE o.eta o.gap o.ample (tubularPrice G L)) (k*i*2)
  have hF' : Lake G L (payE o.eta o.gap o.ample (tubularPrice G L)) (k*i*2) V t:=⟨hF⟩
  let α:= (Q.exp-e)/4; have hs : 0<α:= by unfold α; linarith
  have hΛ:e+3*α ≤ Q.exp:=by unfold α; linarith
  let g x:= spicesF G (r x) (p x) (V x) k i; let z x:= Lyre.eureka Q (g x) L μ x i (t+i); let q:= stella Q
  have hA:= beaconK r p V hK₁ hp₁ hv i k
  have hB : Rate G L q.rate z:=by rw [← zero_add q.rate]; exact Rate.mul ((Rate.const 1).add (hA.mul_left (2^i*2:ℝ))) (q.rate_none L hμ 0 (t+i) 0)
  obtain ⟨ν,hν,hz,hα,hT⟩:= crown G L i 0 C'
  obtain ⟨s⟩:= Lyre.signed_signal i; obtain ⟨ν₀,-,hl,h₀,hT'⟩:= crown G L 0 0 C
  obtain ⟨s₀⟩:= Lyre.signed_signal 0 -- nonempty packs invalid
  have hw : Rate G L q.rate (prismD Q L μ):= (q.tempo L hμ 0).mul_left _
  have hz':Rate G L 0 shiftG := (((Rate.radius_price).mul_left 2).add (Rate.const 1)).mul_left 4
  have hP : Rate G L q.rate (fun x=>FullVolume.Ray.Weigh.pattern i*(collars G α x i m *(z x * (1-1/2)⁻¹))) :=by unfold collars; simpa only [zero_mul,zero_add] using! ((((hz'.pow (m*i)).mul_right _).mul (hB.mul_right (1-1/2:ℝ)⁻¹)).mul_left _)
  have hd :∀ᶠ x in atTop, 2≤ fire G L x := ((tendsto_rpow_atTop (show (0:ℝ)<1/256 by norm_num)).comp (Work.E09.betaF_growth G L)).eventually_ge_atTop _
  filter_upwards [hX,hQ',pocketsC G L hs,shows Q L μ hα s hμ hQ, shows Q L μ h₀ s₀ hμ hQ,
    (degreeW hB α).below q.stop (1/2) (by norm_num), hP _ (by change -(2/5:ℝ)< -(3/8); norm_num), hw.below q.stop (1/2) (by norm_num), (degreeW hw α).below q.stop (1/2) (by norm_num),hd] with x ha hp' hσ H H₁ hb' hJ hq hq' hδ c f' S T hS ht R B U P hp₀ hP hI
  let y:=K*a x; have hy:0≤y:= by unfold y; positivity
  let Y:= Lyre.mk (ha c f' S T hS ht R C B).some (fun i hi=>(ha c f' S T hS ht (U.notes i) C (U.beams i hi)).some)
  have hl':Clarity B i C' (thaw G L x) ν:=⟨fun F X m hh hz'=> hT c f' S T F X m x _ _ C' hz le_rfl hh B.laws.data.funds.length_eq hz' U.pole.full.2.2 U.pole.active⟩ -- argument βCost !!! b,v and α= gain
  have ht':Clarity B 0 C (thaw G L x) ν₀:= ⟨fun F X m hh hz=> hT' c f' S T F X m x _ _ C hl le_rfl hh B.laws.data.funds.length_eq hz U.pole.full.2.2 U.pole.active⟩
  have hy':Sailor G P.threshold y i:= by
    refine ⟨fun c v he => hG c (a x) hp'.le v (he.trans ?_)⟩
    have hh := B.laws.data.room.temperatures; rw [B.laws.data.funds.length_eq] at hh; exact hP.trans_le hh
  have hG : ∀ x', B.smallAt x'=B.smallAt x':=fun _=>rfl
  refine ⟨hδ,⟨_,?_,Y.hailed hF' H hl' hσ hδ hP hI.le hy (show ↑i*y≤f x from (by unfold f y; nlinarith only [mul_nonneg hK.le hp'.le])) hy'⟩, _ ,U.clout H₁ hΛ he hs ((le_abs_self _).trans hq) ((le_abs_self _).trans hq'),fun i V=>Tune.stays U χ H₁ ht' hσ hδ V i⟩
  intro j; rw [hp₀]; exact budget_loosen (Y.edition hF' H hσ _ he hΛ ((le_abs_self _).trans hb') j) ((le_abs_self _).trans hJ)
end YM.ConnectedActivityE6.Empire
