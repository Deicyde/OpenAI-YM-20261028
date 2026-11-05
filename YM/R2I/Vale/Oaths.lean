import YM.R2I.Vale.Petals
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Honey
/- Extend Autumn Pane school post-L to meters-dependent threshold and width. Same witness, larger Saints. -/
noncomputable section
set_option autoImplicit false
namespace YM.PhysicalNext.Repeat.Trio
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric  Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera   Lantern
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable (Θ₃:ℕ)
variable {G : Gauge} {c f C' F L:Side} {j i m n W w r k l:ℕ}
-- take more than every meter (incl mapping radius), all offsets.
abbrev tentW (b B:ℕ) := 4*Meadow.studioR Θ₃ b B+ 100*(1+B)
def fenceW (b B :ℕ) (i : Stars): Side := ⟨2*(tentW Θ₃ b B+i.val), by unfold tentW; omega⟩
abbrev baseW (b B: ℕ) := tentW Θ₃ b B+5
lemma highChairW (b B : ℕ) (i:Stars): 4*Meadow.studioR Θ₃ b B+16 ≤ (fenceW Θ₃ b B i).val ∧ 100*(1+B) ≤ (fenceW Θ₃ b B i).val := by change _≤2*(tentW Θ₃ b B+i.val) ∧ _≤2*(tentW Θ₃ b B+i.val); unfold tentW; omega
abbrev maxFixedW (b:ℕ):=2*baseW Θ₃ b 1
lemma roofW (b B:ℕ) (hx:1 ≤ B):2*baseW Θ₃ b B ≤ Trio.maxFixedW Θ₃ b*B:= by unfold baseW tentW Meadow.studioR Meadow.roomSizeR Mint.width Trio.maxFixedW baseW tentW Meadow.studioR Meadow.roomSizeR Mint.width; nlinarith [mul_nonneg (show 0≤(2+Θ₃)^2 from (Nat.zero_le _)) (show 0≤B from (Nat.zero_le _))]
lemma scaleMetersW (b : ℕ) (B : ℕ) (hx:1 ≤ B) (x:Site c) (u:ℕ) (hp:u≤2*baseW Θ₃ b B):
    coverNumber B (neighbors u x) ≤ (Trio.maxFixedW Θ₃ b+Trio.maxFixedW Θ₃ b+1)^4:= by
  apply (Corona.cover_mono ?_ B).trans (Corona.tile x (maxFixedW Θ₃ b) B hx); intro i hi; exact halo_spec.mpr ⟨x,mem_singleton_self _,((neighbors_mem ..).1 hi).trans (hp.trans (Trio.roofW Θ₃ b B hx))⟩

-- Graph costs Quilt universal
lemma rowsW (G : Gauge) (L : Side) (b : ℕ): Bolt G L (fun x => (Meadow.studioR Θ₃ b (radiusB x):ℝ)) ∧ Bolt G L (fun x=> (tentW Θ₃ b (radiusB x):ℝ))∧ Bolt G L (fun x=> (Trio.baseW Θ₃ b (radiusB x):ℝ)) ∧ Bolt G L (fun x=> (2*Trio.baseW Θ₃ b (radiusB x):ℕ)) := by
  have hp : Bolt G L (fun x => (Meadow.studioR Θ₃ b (radiusB x):ℝ)):= by
    unfold Meadow.studioR Meadow.roomSizeR Mint.width; push_cast
    let h:=Bolt.size (G:=G) (L:=L)
    let M:= (((((Bolt.still (b:ℝ)).times h).joins (((Bolt.still 6).times h).joins (Bolt.still 3))).joins h))
    exact (((((((Bolt.still 4).times M).joins (Bolt.still 2)).times (Bolt.still _)).joins ((Bolt.still 2).times M)).joins (Bolt.still 1)).joins ((Bolt.still 2).times h))
  have ht : Bolt G L (fun x=> (tentW Θ₃ b (radiusB x):ℝ)):= by
    unfold tentW; push_cast; push_cast at hp; exact ((Bolt.still 4).times hp).joins ((Bolt.still 100).times ((Bolt.still 1).joins Bolt.size)) -- hp macro expansions simpl
  have he : Bolt G L (fun x=> (Trio.baseW Θ₃ b (radiusB x):ℝ)):= by unfold baseW; push_cast; push_cast at ht; exact ht.joins (Bolt.still 5)
  refine ⟨hp,ht,he,?_⟩; push_cast; push_cast at he; exact (Bolt.still 2).times he
-- choose LARGE: poly
variable (G : Gauge) (L : Side) (b:ℕ) (t:ℝ)
local notation "B" => radiusB t
-- actual crest at top of Aux side
def mostW (b:ℕ) (x:ℝ):=2*(Trio.baseW Θ₃ b (radiusB x))
lemma tallerW (i:Stars): (fenceW Θ₃ b B i).val ≤ mostW Θ₃ b t:= by change 2*(_+i.val)≤ 2*(_+5); have h:= i.isLt; omega
-- Primary f straight counts

def paySideW (G : Gauge) (L:Side) (b:ℕ) (t : ℝ) : ℕ :=
    let u:= mostW Θ₃ b t; let v:=u*L.val; let X:=u^4*Fintype.card (Exterior.TypeFace 1) * Fintype.card G.ColorIndex; let Z:=v^4*4; let y:= Z*Fintype.card G.ColorIndex
    1+X+Z+u+ v^4 + u^4+y+y
lemma circlesW : Bolt G L (fun t=> (paySideW Θ₃ G L b t:ℝ)):= by
  unfold paySideW; push_cast
  let q:=(rowsW Θ₃ G L b).2.2.2
  -- implicit eq cast again
  have h : Bolt G L (fun i=> ((mostW Θ₃ b i):ℝ)):= (rowsW Θ₃ G L b).2.2.2
  let p:= h.times (Bolt.still (L.val:ℝ)); let v:= (p.nod 4); let u:= h.nod 4; let y:= v.times (Bolt.still 4); let X:=y.times (Bolt.still (Fintype.card G.ColorIndex:ℝ))
  exact (((((((Bolt.still 1).joins ((u.times (Bolt.still _)).times (Bolt.still _))).joins y).joins h).joins v).joins u).joins X).joins X
lemma quiltW (S:StepData c f) (T:Tube G S) (W : Forest S.ratio) (hp : c.val ≤ mostW Θ₃ b t) (hL:S.patch.L=L) (h:Bid.Larger (G:=G) S): Quilt T W (paySideW Θ₃ G L b t):= by
  let u:=mostW Θ₃ b t; let z:=u*L.val; let A:= (paySideW Θ₃ G L b t)
  have he:f.val ≤ z:= by rw [S.sizes,hL]; exact Nat.mul_le_mul_right _ hp
  have hC : Fintype.card (Site c) ≤ u^4:= (site_card c).trans_le (pow_le_pow_left' hp 4)
  have hF : Fintype.card (Site f) ≤ z^4:= (site_card f).trans_le (pow_le_pow_left' he 4)
  have hb : Fintype.card (Bond f) ≤ z^4*4:= by rw [Fintype.card_prod]; exact Nat.mul_le_mul_right 4 hF
  have hx : Fintype.card (Uniform.Primary c G) ≤ u^4* Fintype.card (Exterior.TypeFace 1)* Fintype.card G.ColorIndex:= by unfold Uniform.Primary; rw [Fintype.card_prod, Fintype.card_prod]; gcongr
  have hy: Fintype.card W.Free ≤ z^4*4:= (Fintype.card_le_of_injective _ (@Subtype.val_injective _ _ : Injective (fun i:W.Free=>i.val))).trans hb
  have hK: Fintype.card (Tubular f G) ≤ z^4*4*Fintype.card G.ColorIndex:= by rw [Fintype.card_prod]; gcongr
  have hh : paySideW Θ₃ G L b t=1+u^4*Fintype.card (Exterior.TypeFace 1)*Fintype.card G.ColorIndex+z^4*4+u+z^4+u^4+z^4*4*Fintype.card G.ColorIndex+z^4*4*Fintype.card G.ColorIndex:=rfl
  have hT : Fintype.card (Uniform.Joint W G) ≤ A:= by rw [Fintype.card_sum,Fintype.card_prod (α:=W.Free)]; have hz:= Nat.mul_le_mul_right (Fintype.card G.ColorIndex) hy; change _≤ paySideW Θ₃ G L b t; rw [hh]; omega
  have hA:1≤ A:=by unfold A; omega
  refine ⟨h,(by exact_mod_cast hA),(by exact_mod_cast hT),?_,?_,?_,?_,?_⟩ <;> exact_mod_cast (by  omega : _ ≤ paySideW Θ₃ G L b t)
end YM.PhysicalNext.Repeat.Trio

namespace YM.PhysicalNext.Repeat.Trio
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable (Θ₃:ℕ)
variable (G : Gauge) (L:Side) (t:ℝ) (b:ℕ) (σ:RG.Stage) (x:ℝ)
local notation "B" => radiusB x
local notation "h" => (gold G L x)
local notation "c" => fenceW Θ₃ b (radiusB x)
local notation "s" => Height.away σ
local notation "z" => (baseW Θ₃ b B)
-- dues old Local.loose E-turn already included

def heatW := ((ballCost (Meadow.studioR Θ₃ b B)):ℝ)*(s*((betaF G x L)^t+ betaF G x L ^ (-(7/16):ℝ)))
def lossFeeW:= heatW Θ₃ G L t b σ x+heatW Θ₃ G L t b σ x+ ∑ i:Stars, |Slide.ray i| * ((Fintype.card (Site (c i)):ℝ)*(heatW Θ₃ G L t b σ x+heatW Θ₃ G L t b σ x))
def crestFeatW (i:Stars):= (ticket σ.order h+2*((Fintype.card (Site (c i)):ℝ)*(s*(h+h)+h)))
def planksW := ∑ i:Stars, |Slide.ray i| * ((2:ℝ)^σ.order*((1+(z:ℝ))^(σ.power*σ.order))*crestFeatW Θ₃ G L b σ x i)
def coverTicketW (b:ℕ) : ℝ := (((2*maxFixedW Θ₃ b+1)^4:ℕ):ℝ)

lemma losesW (p : BudgetPoint) (ht:p.order=σ.order) (hp:p.power=σ.power): tilt p z=(2:ℝ)^σ.order*((1+(z:ℝ))^(σ.power*σ.order))∧
    Trio.oroW p z (crestFeatW Θ₃ G L b σ x)=planksW Θ₃ G L b σ x:= by simp only [tilt, ht,hp,oroW,planksW]; trivial -- edit orientation

-- rate bundles
lemma feeStarsW (i:Stars): Rate G L 0 (fun x=> (Fintype.card (Site (Trio.fenceW Θ₃ b (radiusB x) i)):ℝ)) := by
  have he:= (rowsW Θ₃ G L b).2.1
  let F x := (tentW Θ₃ b (radiusB x):ℝ)
  let g x:=2*(F x+i.val)
  have hg:Bolt G L g:= (Bolt.still 2).times (he.joins (Bolt.still _))
  refine Rate.congr (Bolt.uses (hg.nod 4)) ?_; filter_upwards with x; rw [site_card]; symm; change (g x)^4= ((↑((2*(tentW Θ₃ b (radiusB x)+i.val))^4:ℕ)):ℝ); unfold g F; norm_cast -- edit
lemma heatsW (ht:t=-(7/16:ℝ)): Rate G L t (heatW Θ₃ G L t b σ):= by
  subst t; exact (balls G L ((rowsW Θ₃ G L b).1)).mul (((Rate.power).add Rate.power).mul_left _) |>.weaken (by rw [zero_add])
lemma twigsW (ht:t=-(7/16:ℝ)): Rate G L t (lossFeeW Θ₃ G L t b σ):= by
  have hx:= Trio.heatsW Θ₃ G L t b σ ht; let hh:= hx.add hx; refine Rate.add hh (sparks G L fun i=> ?_); simpa only [zero_add] using! (((feeStarsW Θ₃ G L b i).mul hh).mul_left |Slide.ray i|)
lemma frostW (i:Stars): Rate G L (-(23/20)) (fun x=> crestFeatW Θ₃ G L b σ x i):= by
  have ht : Rate G L (-(23/20)) (gold G L):= Rate.power; apply Rate.add ((ht.mul_left _).mul_right _); simpa only [zero_add] using! (((feeStarsW Θ₃ G L b i).mul (((ht.add ht).mul_left _).add ht)).mul_left 2)
lemma skywardW : Rate G L (-(23/20)) (fun x=> planksW Θ₃ G L b σ x):= by
  have hb := (rowsW Θ₃ G L b).2.2.1
  apply sparks G L (f:=fun i x=> |Slide.ray i| * (_) ); intro i
  simpa only [zero_add] using! ((((Bolt.still ((2:ℝ)^σ.order)).times (((Bolt.still 1).joins hb).nod (σ.power*σ.order))).uses.mul (Trio.frostW Θ₃ G L b σ i)).mul_left |Slide.ray i|)
-- whole transformation compare/h endpoints. q costs at any θ
lemma cheapW (ht:t=-(7/16:ℝ)): ∀ᶠ x in atTop,Marlin.tithe (2*baseW Θ₃ b (radiusB x)) (lossFeeW Θ₃ G L t b σ x) ⟨σ.power,σ.order, σ.supportExponent,1,1,σ.power_ge,σ.order_ge,σ.price_pos,Nat.zero_lt_one,zero_lt_one,le_rfl⟩ (coverTicketW Θ₃ b) ≤ betaF G x L ^(-(1/8):ℝ):= by
  have ht' := ((balls G L ((rowsW Θ₃ G L b).2.2.2)).mul (twigsW Θ₃ G L t b σ ht)).mul_right (Real.exp ((σ.supportExponent+1+1)*coverTicketW Θ₃ b)) (-(1/8):ℝ) (by rw [ht]; norm_num)
  filter_upwards [ht'] with x hv; exact (le_abs_self _).trans hv
end YM.PhysicalNext.Repeat.Trio

namespace YM.PhysicalNext.Repeat.Roof
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio
open Progress.DirectedRecipe Time
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable (Θ₃:ℕ)
variable {G : Gauge} {c f L:Side} {t u v b:ℝ} {j i m n N:ℕ}
lemma comparW (G : Gauge) (L:Side) (b : ℕ) (P: RG.Stage): ∀ᶠ x in atTop,
    let u:=gold G L x; let z:= Height.away P
    z*u+u+ z*(planksW Θ₃ G L b P x* Real.exp (stout P * coverTicketW Θ₃ b)) ≤ (1/2:ℝ)*(Time.credit G P*δE x):= by
  have ht : Rate G L (-(23/20)) (gold G L) := Rate.power
  have hh := (((ht.mul_left (away P)).add ht).add (((Trio.skywardW Θ₃ G L b P).mul_right (Real.exp (stout P * coverTicketW Θ₃ b))).mul_left (away P)))
  let z:= Height.away P; let A:= Time.credit G P
  have hp: 0<A:=Time.credit_pos ..
  filter_upwards [Sienna.contraction G L (a:=1) (b:=A/2) (by positivity) (show Rate G L (-(23/20)) (fun x=> z*gold G L x+gold G L x+ z*(planksW Θ₃ G L b P x*Real.exp (stout P*coverTicketW Θ₃ b))) from hh) (show -(23/20:ℝ)< -(11/10) by norm_num),Delay.shift_pos G L,eventually_gt_atTop (0:ℝ)] with x ht hx hX u z
  have he : δE (betaF G x L)=betaF G x L ^ (-(11/10):ℝ):= by unfold δE Clock.gap; rw [Real.sqrt_eq_rpow,← Real.rpow_neg hx.le,← Real.rpow_mul hx.le]; norm_num
  have hh : δE (betaF G x L) ≤ δE x:= by
    unfold δE; refine Real.rpow_le_rpow (by unfold Clock.gap; positivity) ?_ (by norm_num)
    have hz : x ≤ betaF G x L:= le_add_of_nonneg_right (Work.E04.shift_nonneg G L)
    exact inv_anti₀ (Real.sqrt_pos.mpr hX) (Real.sqrt_le_sqrt hz)
  rw [one_mul,← he] at ht; refine ht.le.trans ((mul_le_mul_of_nonneg_left hh (by positivity : 0≤A/2)).trans_eq ?_); unfold A; ring

variable {X:Metals G} (D:Rolls X.p) {C : Targets X.p X.K} (Z : Expenses C)
    {F:ℕ→ℕ→Postage} (S : Time.Scouts (F:=F)) {P:Protection D} (W : Delays P)
def panW (j i:ℕ) (x:ℝ):Prop := let L:= D.L j; let t:= (Z j i).wanting; let b:= (C j i).halo; let T:= X.p.profile i; let B:=radiusB x; let h:= Trio.baseW Θ₃ b B
    (Marlin.tithe (2*h) (lossFeeW Θ₃ G L t b T x) ⟨T.power,T.order,T.supportExponent,1,1,T.power_ge,T.order_ge,T.price_pos,Nat.zero_lt_one,zero_lt_one,le_rfl⟩ (coverTicketW Θ₃ b) ≤ betaF G x L ^(-(1/8):ℝ))∧
    (let u:=gold G L x; let z:= Height.away T; z*u+u+ z*(planksW Θ₃ G L b T x* Real.exp (stout T * coverTicketW Θ₃ b)) ≤ (1/2:ℝ)*(Time.credit G T*δE x)) ∧
    (∀ β:ℝ, Next.Scheduling.inBand (betaF G x L) β→∀ a b:ℝ,let v:= (S j i).pair.strong (betaF G x L) β; 0 ≤ a → 0 ≤ b → a ≤ v/8 → b ≤ (betaF G x L) ^ (-(1/8:ℝ)) → ∃ κ, Payments.Rates B v a b κ) ∧
    ∀ P:BudgetPoint,P.threshold ≤2*Pressure.fiery G x L→∀ c f: Side, 2*h<c.val→∀ w:ℕ,w+1≤h→∀ (u:2*w≤f.val) (o:Site c) (V:Config G c), Healthy P.threshold (neighbors h o) V→ ∃ (z:Site f→G.El) (s:Positions (Uniform.Primary f G)), Boulevard.actual s=gauge z (Slide.shape (Slide.cognac u) o V) ∧ ‖s‖+2*Sienna.furl G L x < eaves G L x
lemma dishesW (ht:(Z j i).wanting=-(7/16:ℝ)):∀ᶠ x in atTop, Roof.panW Θ₃ D Z S j i x:=
  let b:= (C j i).halo; let L:=D.L j; let p:= (X.p.profile i)
  (Trio.cheapW Θ₃ G L _ b p ht).and ((Roof.comparW Θ₃ G L b p).and ((Marlin.pricingBuy G L _ (S j i)).and (Trio.pledges G L (fun x=>Trio.baseW Θ₃ b (radiusB x)) (Trio.rowsW Θ₃ G L b|>.2.2.1.uses))))
structure AutumnW : Prop where
  allot j i (h:StepStages j i) x (he:W.betaEntry j≤x) : panW (3+4*j) D Z S j i x
  sizes (j i:ℕ) (h:StepStages j i): 100*Trio.maxFixedW (3+4*j) (C j i).halo ≤ W.shells j ∧ 1 ≤ W.growth j
lemma ensuresW (h : ∀ j i,StepStages j i→(Z j i).wanting=-(7/16:ℝ)) : ∃ V:Delays P,DelayLe W V ∧ ∀ U : Delays P,DelayLe V U → Roof.AutumnW D Z S U:= by
  obtain ⟨x,-,hp,hv⟩:= collect_upper W.betaEntry _ fun j=>eventually_transitions j _ _ fun i (he:StepStages j i)=> dishesW (3+4*j) D Z S (h _ _ he)
  let v j i:= 100*Trio.maxFixedW (3+4*j) (C j i).halo
  refine ⟨{W with betaEntry:=x, shells:=fun i=> W.shells i+ fromMax v i, growth:=fun i=> W.growth i + 1},⟨hp,le_rfl,fun i=> Nat.le_add_right ..,fun i=> Nat.le_succ _⟩,fun U h=>⟨fun j i hi x hx=>hv _ _ ((h.beta _).trans hx) i hi,fun j i hi=>?_⟩⟩
  exact ⟨((le_fromMax v hi).trans (Nat.le_add_left (fromMax _ _) _)).trans (h.shells _),(Nat.le_add_left 1 _).trans (h.growth _)⟩
end YM.PhysicalNext.Repeat.Roof
