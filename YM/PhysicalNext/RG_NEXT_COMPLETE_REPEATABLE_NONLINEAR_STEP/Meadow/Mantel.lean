import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Detrain
/-! # Low kinetic cap selection, efficiently transferable in arities. Warming.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L : Side} {P : Patch} {M D' : ℕ} {K : Teller G}
variable {S : StepData c f} {T : Tube G S} {p : ℝ} {R R' : RG.Rep G f}
    {a v W q K₀ : ℝ} {J : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W} (H : Cash W p a L J o K₀ T R) {χ : Chi}
local notation "B" => radiusB p

abbrev Park (c f:Side):= Finset (Mint.Music c f)
abbrev Vines (c f:Side) := Ursell.Clusters (Park c f) -- namespace check
abbrev ground (p:Park c f):= H.unionP (Mint.hatch S p)
abbrev pasture (z:Vines c f):= unionOf (Meadow.ground H) z.2 -- check
structure Seed (p:Park c f) : Prop where
  hot : Ac.Spark H.supportP (Mint.hatch S p)
  sizes : p.card≤ 2
  earns i : i∈p → Mint.verse R.path i≤B -- p rename
structure Stir (z:Vines c f) : Prop where
  small : z.fst≤ 1
  each i : Seed H (z.2 i)
  moves : coefficient (blocked (Meadow.ground H)) z.2≠0
variable {H}
lemma family_ne {x : Park c f} (hq:Seed H x) : x.Nonempty:= by obtain ⟨p,hp⟩:= hq.hot.1; obtain ⟨i,hi,rfl⟩:=mem_map.mp hp; exact ⟨i,hi⟩
lemma ground_ne {x} (hq:Seed H x): (Meadow.ground H x).Nonempty:= by
  obtain ⟨i,hi⟩:= family_ne hq; have hz:= Mint.centered J.halo B B (lt_of_lt_of_le (by norm_num) H.laws.data.room.sight.1) i S T R (hq.earns i hi)
  exact ⟨pace S i,Finset.mem_biUnion.mpr ⟨_,mem_map_of_mem _ hi,hz.1⟩⟩
lemma centers {x} (hq:Seed H x) {i} (hi:i∈x): pace S i∈Meadow.ground H x:= Finset.mem_biUnion.mpr ⟨Mint.disc S i, mem_map_of_mem _ hi, (Mint.centered J.halo B B (lt_of_lt_of_le (by norm_num) H.laws.data.room.sight.1) i S T R (hq.earns i hi)).1⟩
def Heir (y : Park c f) (ht : Seed H y) : H.ThinP := ⟨Mint.hatch S y,ground_ne ht,by rw [Mint.unrostered]⟩
lemma seed_height {x y:Park c f} (he:Seed H x) (hp:Seed H y) (h:Heir x he=Heir y hp): x=y:= Finset.map_injective (Mint.disc S) (congr_arg Subtype.val h)
lemma movement {I E X:Type} [DecidableEq E] [Fintype E] (u : I→I→Prop) (v:E→I) (p:X→X→Prop) (q:E→X) (h : ∀ i j,u (v i) (v j)↔p (q i) (q j)) : coefficient u v=coefficient p q:= by
  apply congr_arg Graph.mass; ext i; simp only [potential_mem,h]

def vintage (z:Vines c f) (hz:Stir H z): H.fragrances:= ⟨z.1,fun i=>Heir (z.2 i) (hz.each i)⟩
lemma enrollment : Injective (fun i : {z:Vines c f// Stir H z}=> vintage i.val i.property):= by
  rintro ⟨⟨i,z⟩,hp⟩ ⟨⟨j,k⟩,hx⟩ he
  change Sigma.mk i _=Sigma.mk j _ at he; obtain rfl : i=j:= congr_arg Sigma.fst he
  injection he with he hh
  have h': z=k:= funext fun i=> seed_height (hp.each i) (hx.each i) (congr_fun hh i)
  cases h'; rfl
lemma mana {p : Vines c f} (h : Stir H p): coefficient (blocked (Meadow.ground H)) p.2=coefficient H.seam (vintage p h).2:= by
  apply movement; intro i j; apply or_congr _ Iff.rfl
  exact ⟨fun he=> Subtype.ext (congr_arg (Mint.hatch S) he),seed_height (h.each i) (h.each j)⟩

lemma your {z} (i:Option (Fin z.fst)): Meadow.ground H (z.2 i) ⊆ Meadow.pasture H z:= Finset.subset_biUnion_of_mem (Meadow.ground H ∘ z.2) (mem_univ _)

local notation "D" => Mint.width J.halo B B
-- diameter via coverNumber, cluster, startup uses R covariance floor
lemma cover_loc {z} (h : Seed H z): coverNumber D (Meadow.ground H z) ≤ 2:= by
  set A:= Mint.hatch S z
  refine (Ac.cover _ _ h.hot).trans ((sum_le_sum (g:=fun _=>1) (fun i hi=> ?_)).trans ?_)
  · obtain ⟨i,hi,rfl⟩:=mem_map.mp hi; have hx:=h.earns i (by assumption)
    let p:= pace S i
    have he:neighbors D p=halo D ({p}: Finset _):= by ext i; simp only [halo_spec,neighbors_mem]; simp only [mem_singleton]; grind
    have hp : covers D (H.supportP (Mint.disc S i)) {p}:= ⟨he ▸ (Mint.centered J.halo B B (lt_of_lt_of_le (by norm_num) H.laws.data.room.sight.1) i S T R hx).2, Corona.ship_halo _ (fun i hi j hj=> by rw [mem_singleton.mp hi,mem_singleton.mp hj])⟩
    exact (Corona.list_cost _ hp).trans_eq (card_singleton _)
  simp only [sum_const,smul_eq_mul,mul_one,Mint.hatch, Finset.card_map]; exact h.sizes
lemma wages {z} (h : Stir H z) : coverNumber D (Meadow.pasture H z) ≤ 4 := by
  let p:=vintage z h
  have hx:= connected_pay H.seam H.smallAt D H.testS p.2 zero_le_one (show coefficient H.seam p.2≠0 from mana h ▸ h.moves)
  unfold Trees.currency at hx; simp_rw [one_mul,← Real.exp_sum,Real.exp_le_exp] at hx; have h(i): (coverNumber D (H.smallAt (p.2 i)):ℝ)≤2:= by exact_mod_cast cover_loc (h.each i)
  have he:(coverNumber D (Meadow.pasture H z):ℝ)≤4:= by
    refine le_trans hx ((Finset.sum_le_sum (fun i _=> h i)).trans ?_)
    rw [sum_const,nsmul_eq_mul]; simp only [card_univ,Fintype.card_option,Fintype.card_fin]; have hp : p.fst+1≤ 2:= by linarith [show p.fst≤1 from ‹Stir H z›.small]
    apply le_trans (mul_le_mul_of_nonneg_right (show ((p.fst+1:ℕ):ℝ) ≤ 2 from by exact_mod_cast hp) (by norm_num : (0:ℝ)≤2)); norm_num
  exact_mod_cast he

def roomSize (l b:ℕ) := 18*Mint.width l b b+8
lemma entered {z} (h : Stir H z) (x:Site c) (hx:x∈ Meadow.pasture H z): Meadow.pasture H z ⊆ neighbors (roomSize J.halo B) x:= by
  intro i hi; apply (neighbors_mem ..).2
  have he := wages h; apply (Corona.extent _ D hx hi).trans; unfold roomSize; exact (add_le_add_left (Nat.mul_le_mul_right _ he) (2*_)).trans_eq (by ring)
end YM.PhysicalNext.Repeat.Meadow
