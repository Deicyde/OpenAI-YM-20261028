import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Camp
/- Widen verified Meadow Mantel,Nil,Camp proof to arbitrary order Θ. Native radius remains, connectivity & symmetry BOTH. -/
noncomputable section

set_option autoImplicit false
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {Θ₃ : ℕ}
variable {G : Gauge} {c f C F L : Side} {P : Patch} {M D' : ℕ} {K : Teller G}
variable {S : StepData c f} {T : Tube G S} {p : ℝ} {R R' : RG.Rep G f}
    {a v W q K₀ : ℝ} {J : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W} (H : Cash W p a L J o K₀ T R) {χ : Chi}
local notation "B" => radiusB p

variable (Θ₃) in
structure SeedR (p:Park c f) : Prop where
  hot : Ac.Spark H.supportP (Mint.hatch S p)
  sizes : p.card≤ 2+Θ₃
  earns i : i∈p → Mint.verse R.path i≤B -- p rename
variable (Θ₃) in
structure StirR (z:Vines c f) : Prop where
  small : z.fst≤ 1+Θ₃
  each i : SeedR Θ₃ H (z.2 i)
  moves : coefficient (blocked (Meadow.ground H)) z.2≠0
variable {H}
lemma family_neR {x : Park c f} (hq:SeedR Θ₃ H x) : x.Nonempty:= by obtain ⟨p,hp⟩:= hq.hot.1; obtain ⟨i,hi,rfl⟩:=mem_map.mp hp; exact ⟨i,hi⟩
lemma ground_neR {x} (hq:SeedR Θ₃ H x): (Meadow.ground H x).Nonempty:= by
  obtain ⟨i,hi⟩:= family_neR hq; have hz:= Mint.centered J.halo B B (lt_of_lt_of_le (by norm_num) H.laws.data.room.sight.1) i S T R (hq.earns i hi)
  exact ⟨pace S i,Finset.mem_biUnion.mpr ⟨_,mem_map_of_mem _ hi,hz.1⟩⟩
lemma centersR {x} (hq:SeedR Θ₃ H x) {i} (hi:i∈x): pace S i∈Meadow.ground H x:= Finset.mem_biUnion.mpr ⟨Mint.disc S i, mem_map_of_mem _ hi, (Mint.centered J.halo B B (lt_of_lt_of_le (by norm_num) H.laws.data.room.sight.1) i S T R (hq.earns i hi)).1⟩
def HeirR (y : Park c f) (ht : SeedR Θ₃ H y) : H.ThinP := ⟨Mint.hatch S y,ground_neR ht,by rw [Mint.unrostered]⟩
lemma seed_heightR {x y:Park c f} (he:SeedR Θ₃ H x) (hp:SeedR Θ₃ H y) (h:HeirR x he=HeirR y hp): x=y:= Finset.map_injective (Mint.disc S) (congr_arg Subtype.val h)
def vintageR (z:Vines c f) (hz:StirR Θ₃ H z): H.fragrances:= ⟨z.1,fun i=>HeirR (z.2 i) (hz.each i)⟩
lemma enrollmentR : Injective (fun i : {z:Vines c f// StirR Θ₃ H z}=> vintageR i.val i.property):= by
  rintro ⟨⟨i,z⟩,hp⟩ ⟨⟨j,k⟩,hx⟩ he
  change Sigma.mk i _=Sigma.mk j _ at he; obtain rfl : i=j:= congr_arg Sigma.fst he
  injection he with he hh
  have h': z=k:= funext fun i=> seed_heightR (hp.each i) (hx.each i) (congr_fun hh i)
  cases h'; rfl
lemma manaR {p : Vines c f} (h : StirR Θ₃ H p): coefficient (blocked (Meadow.ground H)) p.2=coefficient H.seam (vintageR p h).2:= by
  apply movement; intro i j; apply or_congr _ Iff.rfl
  exact ⟨fun he=> Subtype.ext (congr_arg (Mint.hatch S) he),seed_heightR (h.each i) (h.each j)⟩

local notation "D" => Mint.width J.halo B B
-- diameter via coverNumber, cluster, startup uses R covariance floor
lemma cover_locR {z} (h : SeedR Θ₃ H z): coverNumber D (Meadow.ground H z) ≤ 2+Θ₃:= by
  set A:= Mint.hatch S z
  refine (Ac.cover _ _ h.hot).trans ((sum_le_sum (g:=fun _=>1) (fun i hi=> ?_)).trans ?_)
  · obtain ⟨i,hi,rfl⟩:=mem_map.mp hi; have hx:=h.earns i (by assumption)
    let p:= pace S i
    have he:neighbors D p=halo D ({p}: Finset _):= by ext i; simp only [halo_spec,neighbors_mem]; simp only [mem_singleton]; grind
    have hp : covers D (H.supportP (Mint.disc S i)) {p}:= ⟨he ▸ (Mint.centered J.halo B B (lt_of_lt_of_le (by norm_num) H.laws.data.room.sight.1) i S T R hx).2, Corona.ship_halo _ (fun i hi j hj=> by rw [mem_singleton.mp hi,mem_singleton.mp hj])⟩
    exact (Corona.list_cost _ hp).trans_eq (card_singleton _)
  simp only [sum_const,smul_eq_mul,mul_one,Mint.hatch, Finset.card_map]; exact h.sizes
lemma wagesR {z} (h : StirR Θ₃ H z) : coverNumber D (Meadow.pasture H z) ≤ (2+Θ₃)^2 := by
  let p:=vintageR z h
  have hx:= connected_pay H.seam H.smallAt D H.testS p.2 zero_le_one (show coefficient H.seam p.2≠0 from manaR h ▸ h.moves)
  unfold Trees.currency at hx; simp_rw [one_mul,← Real.exp_sum,Real.exp_le_exp] at hx; have h(i): (coverNumber D (H.smallAt (p.2 i)):ℝ)≤(2+(Θ₃:ℝ)):= by exact_mod_cast cover_locR (h.each i)
  have he:(coverNumber D (Meadow.pasture H z):ℝ)≤(2+(Θ₃:ℝ))^2:= by
    refine le_trans hx ((Finset.sum_le_sum (fun i _=> h i)).trans ?_)
    rw [sum_const,nsmul_eq_mul]; simp only [card_univ,Fintype.card_option,Fintype.card_fin]; have hp : p.fst+1≤ 2+Θ₃:= by linarith [show p.fst≤1+Θ₃ from ‹StirR Θ₃ H z›.small]
    apply le_trans (mul_le_mul_of_nonneg_right (show ((p.fst+1:ℕ):ℝ) ≤ 2+(Θ₃:ℝ) from by exact_mod_cast hp) (by positivity : (0:ℝ)≤(2+(Θ₃:ℝ)))); exact (le_of_eq (by ring))
  exact_mod_cast he

variable (Θ₃) in
def roomSizeR (l b:ℕ) := (4*Mint.width l b b+2)*(2+Θ₃)^2+2*Mint.width l b b + 1
lemma enteredR {z} (h : StirR Θ₃ H z) (x:Site c) (hx:x∈ Meadow.pasture H z): Meadow.pasture H z ⊆ neighbors (roomSizeR Θ₃ J.halo B) x:= by
  intro i hi; apply (neighbors_mem ..).2
  have he := wagesR h; apply (Corona.extent _ D hx hi).trans; unfold roomSizeR; exact (add_le_add_left (Nat.mul_le_mul_right _ he) (2*_)).trans (by simp only [mul_comm ((4:ℕ) * _ +2)]; omega)
end YM.PhysicalNext.Repeat.Meadow

set_option autoImplicit false
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {Θ₃ : ℕ}
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' m: ℕ} {K : Teller G} {p a W U :ℝ}
section sow
variable {S:StepData c f} {T : Tube G S} {R:RG.Rep G f} {X: ConnectedActivityE6.Target G K} {o:Target.Order G W}
    {H : Cash W p a L₀ X o U T R}
variable (Θ₃) in
abbrev PoetR (H:Cash W p a L₀ X o U (c:=c) (f:=f) T R) := {z:Vines _ _ // StirR Θ₃ H z} -- dep
-- lemma equivalence preimage support Labeling
variable (Θ₃) in
lemma bakedR {k:ℕ} : { i: Vines c f| i.fst ≤1+Θ₃∧∀ j, (i.2 j)⊆Meadow.tuck k}.Finite:= by
  let T: Finset (Music c f):= Meadow.tuck k; let a i:=Fintype.piFinset (fun _j : Option (Fin i)=> T.powerset) -- Fintype
  let Y:Finset (Vines c f):= (Finset.range (2+Θ₃)).sigma a
  apply Y.finite_toSet.subset; rintro ⟨i,j⟩ ⟨hv,hj⟩; change (Sigma.mk i j)∈Y
  change i≤1+Θ₃ at hv; apply mem_sigma.mpr; refine ⟨mem_range.mpr (by change i<2+Θ₃; omega),?_⟩; simp_rw [a,Fintype.mem_piFinset]; exact fun i=>mem_powerset.mpr (hj i)
variable (Θ₃) in
lemma tiledR (H : Cash W p a L₀ X o U T R) (k:ℕ): { i : PoetR Θ₃ H | ∀ j,i.val.snd j⊆Meadow.tuck k}.Finite := Set.Finite.subset ((bakedR Θ₃).preimage (show Set.InjOn (fun p:PoetR Θ₃ H=>p.val) _ from Subtype.val_injective.injOn)) (fun i hi=> show i.val.1≤1+Θ₃∧∀ j,i.val.snd j⊆ Meadow.tuck k from ⟨i.property.small,hi⟩)
variable (Θ₃) in
def calendarR (H:Cash W p a L₀ X o U T R) (k:ℕ) := (tiledR Θ₃ H k).toFinset
lemma tunesR (i:PoetR Θ₃ H) (k:ℕ): i∈ Meadow.calendarR Θ₃ H k↔∀ j,i.val.2 j ⊆ Meadow.tuck k:= Set.Finite.mem_toFinset ..
lemma retiresR (i:PoetR Θ₃ H) : ∀ᶠ k in atTop,i ∈ Meadow.calendarR Θ₃ H k:= by
  have hf j : ∀ᶠ k in atTop, i.val.2 j⊆ Meadow.tuck k:= (eventually_all_finset _).mpr fun u _=> (eventually_ge_atTop (held u)).mono (fun _ he=> (pocket ..).mpr he)
  exact (eventually_all.mpr hf).mono fun k h=> (tunesR i k).2 h
end sow
end YM.PhysicalNext.Repeat.Meadow

set_option autoImplicit false
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Reserves
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {Θ₃ : ℕ}
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' j m: ℕ} {K : Teller G} {p a W U V : ℝ} {X : ConnectedActivityE6.Target G K} {o : Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi}
local notation "B" => radiusB p

abbrev ownedR (H : Cash W p a L₀ X o U T R) (i:PoetR Θ₃ H): H.fragrances:= vintageR i.val i.property
variable (Θ₃) in
def boothsR (H : Cash W p a L₀ X o U T R) : PoetR Θ₃ H ↪ H.fragrances:= ⟨ownedR H,enrollmentR⟩
lemma entryR (z: H.ThinP) (hN : Ac.Spark H.supportP z.val)(hk:z.val.card≤2+Θ₃) (hp : ∀ x∈z.val, Beam.Pennies S x) (hv: H.shapeW z.val≤ B):
    ∃ b: Park c f, ∃ X: SeedR Θ₃ H b,z=HeirR b X:= by
  let k := disc S; let b:= z.val.preimage k k.injective.injOn; have hf i:i∈b↔k i∈z.val:=Finset.mem_preimage
  have he: hatch S b=z.val:= by
    ext y; constructor
    · intro hy; obtain ⟨x,hx,rfl⟩:=mem_map.mp hy; exact (hf _).1 hx
    intro hy; obtain ⟨i,rfl⟩:= (penned ..).1 (hp y hy); exact mem_map_of_mem k ((hf _).2 hy)
  refine ⟨b,⟨he.symm ▸ hN,?_,?_⟩, Subtype.ext he.symm⟩
  · have hx:= hk; rw [← he,hatch,card_map] at hx; exact hx
  intro i hi; have hu:= (hf i).1 hi
  refine (Nat.cast_le (α:=ℝ)).mp ?_ -- change
  refine le_trans ?_ hv; change _≤ Finset.sum _ _; apply le_trans _ (Finset.single_le_sum (fun v hv=> ?_) hu)
  swap
  · obtain ⟨w,hw⟩: v∈Set.range (disc S):= (penned ..).1 (hp v hv); subst v; exact add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · change (Mint.verse R.path i:ℝ)≤_ + (exCharge T R (note i):ℝ); rw [Mint.balance T R i]; exact le_add_of_nonneg_left (Nat.cast_nonneg _)
section shape
variable (v: Match.Alliance H I 1 0) (hr : R.path=R'.path) (he:v.units= Equiv.refl _)
-- supportP may differ in reg otherwise, so assume canonical matches from controller
variable (hp : H.supportP=I.supportP)
include hr hp
lemma estateR (z: Park c f): SeedR Θ₃ H z ↔ SeedR Θ₃ I z:= by
  constructor
  · intro h; refine ⟨hp ▸ h.hot,h.sizes,fun i hi=>?_⟩; rw [← hr]; exact h.earns i hi
  intro h; refine ⟨hp.symm ▸ h.hot,h.sizes,fun i hi=>?_⟩; rw [hr]; exact h.earns i hi
lemma universalR (z: Vines c f): StirR Θ₃ H z ↔ StirR Θ₃ I z:= by
  have hx:Meadow.ground H=Meadow.ground I:= funext fun i=> by unfold Meadow.ground Cash.unionP; rw [hp]
  exact ⟨fun h=>⟨h.small,(fun i=> (estateR hr hp _).1 (h.each i)),hx ▸ h.moves⟩,fun h=>⟨h.small,(fun i=>(estateR hr hp _).2 (h.each i)),hx.symm ▸ h.moves⟩⟩
def firstBatchR : PoetR Θ₃ H≃PoetR Θ₃ I:=Equiv.subtypeEquiv (Equiv.refl _) (universalR hr hp)
include he
lemma identifiesR (z:PoetR Θ₃ H): v.furrow (boothsR Θ₃ H z)=boothsR Θ₃ I (firstBatchR hr hp z):= by
  obtain ⟨⟨i,k⟩,hz⟩:=z; change Sigma.mk i _=Sigma.mk i _; congr 1; funext j; apply Subtype.ext; change v.units (hatch S _)= _; rw [he]; rfl
lemma holdingsR (i:H.fragrances): i∈Set.range (boothsR Θ₃ H) ↔ v.furrow i∈Set.range (boothsR Θ₃ I):= by
  let V:= firstBatchR (Θ₃:=Θ₃) hr hp; constructor
  · rintro ⟨u,rfl⟩; exact ⟨V u,(identifiesR v hr he hp u).symm⟩
  rintro ⟨u,hu⟩; obtain ⟨u,rfl⟩:= V.surjective u; exact ⟨u,v.furrow.injective ((identifiesR v hr he hp u).trans hu)⟩
end shape
end YM.PhysicalNext.Repeat.Meadow
