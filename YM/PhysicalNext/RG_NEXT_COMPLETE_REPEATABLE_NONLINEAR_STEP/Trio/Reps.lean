import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Reframe
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sienna.Canvas
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Slide.Dart

/-!
 # Numerical book at χ seams. Uniform in ALL stages. no β trajectory chosen before calendar.
 -/
set_option autoImplicit false
noncomputable section
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
variable {G : Gauge} {c f C' F L:Side} {j i m n W w r k l:ℕ}
-- take more than every meter (incl mapping radius), all offsets.
abbrev tent (b B:ℕ) := 4*Meadow.studio b B+ 100*(1+B)
def fence (b B :ℕ) (i : Stars): Side := ⟨2*(tent b B+i.val), by unfold tent; omega⟩
abbrev base (b B: ℕ) := tent b B+5
lemma highChair (b B : ℕ) (i:Stars): 4*Meadow.studio b B+16 ≤ (fence b B i).val ∧ 100*(1+B) ≤ (fence b B i).val := by change _≤2*(tent b B+i.val) ∧ _≤2*(tent b B+i.val); unfold tent; omega
abbrev maxFixed (b:ℕ):=2*base b 1
lemma roof (b B:ℕ) (hx:1 ≤ B):2*base b B ≤ Trio.maxFixed b*B:= by unfold base tent Meadow.studio Meadow.roomSize Mint.width Trio.maxFixed base tent Meadow.studio Meadow.roomSize Mint.width; nlinarith
lemma scaleMeters (b : ℕ) (B : ℕ) (hx:1 ≤ B) (x:Site c) (u:ℕ) (hp:u≤2*base b B):
    coverNumber B (neighbors u x) ≤ (Trio.maxFixed b+Trio.maxFixed b+1)^4:= by
  apply (Corona.cover_mono ?_ B).trans (Corona.tile x (maxFixed b) B hx); intro i hi; exact halo_spec.mpr ⟨x,mem_singleton_self _,((neighbors_mem ..).1 hi).trans (hp.trans (Trio.roof b B hx))⟩

-- Graph costs Quilt universal
lemma rows (G : Gauge) (L : Side) (b : ℕ): Bolt G L (fun x => (Meadow.studio b (radiusB x):ℝ)) ∧ Bolt G L (fun x=> (tent b (radiusB x):ℝ))∧ Bolt G L (fun x=> (Trio.base b (radiusB x):ℝ)) ∧ Bolt G L (fun x=> (2*Trio.base b (radiusB x):ℕ)) := by
  have hp : Bolt G L (fun x => (Meadow.studio b (radiusB x):ℝ)):= by
    unfold Meadow.studio Meadow.roomSize Mint.width; push_cast
    let h:=Bolt.size (G:=G) (L:=L)
    exact ((Bolt.still 18|>.times (((((Bolt.still (b:ℝ)).times h).joins (((Bolt.still 6).times h).joins (Bolt.still 3))).joins h))).joins (Bolt.still 8)).joins ((Bolt.still 2).times h)
  have ht : Bolt G L (fun x=> (tent b (radiusB x):ℝ)):= by
    unfold tent; push_cast; push_cast at hp; exact ((Bolt.still 4).times hp).joins ((Bolt.still 100).times ((Bolt.still 1).joins Bolt.size)) -- hp macro expansions simpl
  have he : Bolt G L (fun x=> (Trio.base b (radiusB x):ℝ)):= by unfold base; push_cast; push_cast at ht; exact ht.joins (Bolt.still 5)
  refine ⟨hp,ht,he,?_⟩; push_cast; push_cast at he; exact (Bolt.still 2).times he
-- choose LARGE: poly
variable (G : Gauge) (L : Side) (b:ℕ) (t:ℝ)
local notation "B" => radiusB t
-- actual crest at top of Aux side
def most (b:ℕ) (x:ℝ):=2*(Trio.base b (radiusB x))
lemma taller (i:Stars): (fence b B i).val ≤ most b t:= by change 2*(_+i.val)≤ 2*(_+5); have h:= i.isLt; omega
-- Primary f straight counts

def paySide (G : Gauge) (L:Side) (b:ℕ) (t : ℝ) : ℕ :=
    let u:= most b t; let v:=u*L.val; let X:=u^4*Fintype.card (Exterior.TypeFace 1) * Fintype.card G.ColorIndex; let Z:=v^4*4; let y:= Z*Fintype.card G.ColorIndex
    1+X+Z+u+ v^4 + u^4+y+y
lemma circles : Bolt G L (fun t=> (paySide G L b t:ℝ)):= by
  unfold paySide; push_cast
  let q:=(rows G L b).2.2.2
  -- implicit eq cast again
  have h : Bolt G L (fun i=> ((most b i):ℝ)):= (rows G L b).2.2.2
  let p:= h.times (Bolt.still (L.val:ℝ)); let v:= (p.nod 4); let u:= h.nod 4; let y:= v.times (Bolt.still 4); let X:=y.times (Bolt.still (Fintype.card G.ColorIndex:ℝ))
  exact (((((((Bolt.still 1).joins ((u.times (Bolt.still _)).times (Bolt.still _))).joins y).joins h).joins v).joins u).joins X).joins X
lemma quilt (S:StepData c f) (T:Tube G S) (W : Forest S.ratio) (hp : c.val ≤ most b t) (hL:S.patch.L=L) (h:Bid.Larger (G:=G) S): Quilt T W (paySide G L b t):= by
  let u:=most b t; let z:=u*L.val; let A:= (paySide G L b t)
  have he:f.val ≤ z:= by rw [S.sizes,hL]; exact Nat.mul_le_mul_right _ hp
  have hC : Fintype.card (Site c) ≤ u^4:= (site_card c).trans_le (pow_le_pow_left' hp 4)
  have hF : Fintype.card (Site f) ≤ z^4:= (site_card f).trans_le (pow_le_pow_left' he 4)
  have hb : Fintype.card (Bond f) ≤ z^4*4:= by rw [Fintype.card_prod]; exact Nat.mul_le_mul_right 4 hF
  have hx : Fintype.card (Uniform.Primary c G) ≤ u^4* Fintype.card (Exterior.TypeFace 1)* Fintype.card G.ColorIndex:= by unfold Uniform.Primary; rw [Fintype.card_prod, Fintype.card_prod]; gcongr
  have hy: Fintype.card W.Free ≤ z^4*4:= (Fintype.card_le_of_injective _ (@Subtype.val_injective _ _ : Injective (fun i:W.Free=>i.val))).trans hb
  have hK: Fintype.card (Tubular f G) ≤ z^4*4*Fintype.card G.ColorIndex:= by rw [Fintype.card_prod]; gcongr
  have hh : paySide G L b t=1+u^4*Fintype.card (Exterior.TypeFace 1)*Fintype.card G.ColorIndex+z^4*4+u+z^4+u^4+z^4*4*Fintype.card G.ColorIndex+z^4*4*Fintype.card G.ColorIndex:=rfl
  have hT : Fintype.card (Uniform.Joint W G) ≤ A:= by rw [Fintype.card_sum,Fintype.card_prod (α:=W.Free)]; have hz:= Nat.mul_le_mul_right (Fintype.card G.ColorIndex) hy; change _≤ paySide G L b t; rw [hh]; omega
  have hA:1≤ A:=by unfold A; omega
  refine ⟨h,(by exact_mod_cast hA),(by exact_mod_cast hT),?_,?_,?_,?_,?_⟩ <;> exact_mod_cast (by  omega : _ ≤ paySide G L b t)
end YM.PhysicalNext.Repeat.Trio
