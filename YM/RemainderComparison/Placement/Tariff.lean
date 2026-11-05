import YM.RemainderComparison.Placement.Appointment
import YM.RemainderComparison.Musicology.Grounded
/-!
 # Local currencies from reservations
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Placement
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Shell Census Raw Footprint Matter
open PhysicalNext.Repeat Deck Stellar Mint Poll Pond MeasureTheory ProbabilityTheory Greenbelt Lotus Sienna Fare
open Further.PhysicalPeriodLimitF933 Macrame
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Gas Ursell Trees Blaze March Lyric WickReps Creek Mosaic Merge Palette Typeface Harmonics
open AnalyticBridge VerifiedReset Next.Scheduling Extra.Iteration Song Aria Seedlings BoxOf
variable {G : Gauge} {f c F C L: Side}{P:Teller G} {q e j N:ℕ}
variable {ι:Type} [Fintype ι] {α:Type*}{A:ℝ}
variable (R:Rep G f)(R':Rep G F)
set_option quotPrecheck false
local notation "R_"=> Placement.file R e ι
local notation "p"=> R.p
variable (v:α) (D:ι→ Tile G α q e A) (o o':ι→Site f)(d:ι→Site F)
variable (hp:0 < R.beta) (hg:0<R'.beta)
local notation "W" j:max=> Placement.plants R v D hp j
local notation "M₀" => Placement.plants R v D hp o
variable (i:ι) (x:Site c)
variable {X:StepData c f}{T:Tube G X} {Q:ConnectedActivityE6.Target G P}{w β t Γ C' T':ℝ}{O: Target.Order G w}
-- order test signatures; no sum cancellation at spending.G.C
variable (V: Cash w β t L Q O Γ T (Placement.file R e ι))
local notation "Φ"=> X.ratio.parent ∘ o
local notation "ξ"=> Pressure.radiusB β
variable (r k u:ℕ)
local notation "η"=> Sleet.cortex Q.halo (radiusB β) k u e
local notation "ζ"=> Deck.Mint.width Q.halo (radiusB β) e


-- Actual budgets traced.T empowers eventual Toolkit. L mechanism ν. Epoch purchases.SLOTS before coalescing addresses.
variable (l':ℕ→ℕ)
local notation "Ξ"=> Pressure.Stores.till β -- PH
-- pages all nonempty ≤ k root displacement η. This permits separated points too: charged high if not on same page.Prevents all-period tailoring.
omit [Fintype ι] in
def Pocket (v widthK :ℕ)(o:ι→Site c) := {b:Finset ι// b.Nonempty∧ b.card ≤ v ∧ ∀ i∈b,∀ j∈b, separation (o i) (o j) ≤ widthK}
-- Need Fintype.M.Mark counts etc. For W.SupportCost `c:S₀` ≤. positions all.
local notation "Ω"=> Placement.Pocket k η Φ
variable (hV: Sleet.cortex Q.halo (radiusB β) k u e ≤ r)
variable (x':Placement.Pocket k (Sleet.cortex Q.halo (radiusB β) k u e) ((X).ratio.parent ∘ o))
omit [Fintype ι] in
def centerMark (f:ι→ Site c)(i : Pocket k u f):ι:= Classical.choose i.2.1
include hV
omit [Fintype ι] in
def crews : Breeze.Careers ι Ω c Φ r k:= {
    pocket := ⟨fun i=> i.val,Subtype.val_injective⟩
    o' := fun i=> Φ (Placement.centerMark _ _ _ i)
    localR := fun i _ ht=> (i.2.2.2 _ (Classical.choose_spec i.2.1) _ ht).trans hV
    admits := fun i=>i.2.2.1}
local notation "K₁"=> Placement.crews o r k u (hV:=hV) -- maybe args order
local notation "A₁"=> (K₁).o'
local notation "Xx" => (K₁).pocket
local notation "Z₁"=> (fun (_:ι)=> (0:ℕ))
omit [Fintype ι] in
lemma popped : Placement.centerMark _ _ _ x'∈ (K₁).pocket x':= Classical.choose_spec x'.prop.1
lemma radar : BoxOf.Radar (S:=X) (x:=β) M₀ Set.univ Φ η r k (K₁) (n:=e) (s':=Nursery.deepest M₀ Z₁ β) :=by
   refine ⟨fun i=>mem_image_of_mem _ (Classical.choose_spec i.2.1),fun i _ _ _ _=> Placement.locates R v D o hp i,fun B he ht _ hz=>⟨⟨B,he,ht,hz⟩,rfl⟩⟩
omit [Fintype ι] in
lemma distances : ∀ i∈ (Xx x'), separation (A₁ x') (Φ i) ≤ η:=fun _ hi=> x'.prop.2.2 _ (Classical.choose_spec x'.prop.1) _ hi
 omit [Fintype ι] in
lemma revenue_center : (Xx x').Nonempty ∧ (Xx x').card≤ k ∧ Funk.Cargo.sun Φ (K₁) (fun _=>1) x'=1:=by -- Cargo namespace
   refine ⟨x'.prop.1,x'.prop.2.1,Finset.prod_const_one⟩
omit hV
local notation "C_"=> Tile.peso G q e A R.p
local notation "Wg"=> Real.exp R.p.supportExponent * (C_)
variable (hR : Sleet.cortex Q.halo (radiusB β) k u e + Deck.Mint.width Q.halo (radiusB β) e ≤ r)
include hV hR V in
lemma tickets : ∀ j:Ω, 0 < Verse.load (Set.univ:Set ι) ((K₁).pocket j).val ∧ ∀ i∈ (K₁).pocket j, Flues.candle M₀ v X i ⊆ neighbors r (A₁ j) :=by
    refine fun j=>⟨?_,fun i h₁ u hu=> ?_⟩
    · refine Multiset.card_pos.mpr ?_; intro h
      have he (Z:Set ι)(ht:Z= Set.univ)(hf:@Multiset.filter ι (fun i=>i∈ Z) (fun _=> Classical.propDecidable _) ((K₁).pocket j).val= 0): False:=by
          let t:= Placement.centerMark k _ _ j
          have hh : t∈ @Multiset.filter ι (fun i=>i∈Z) (fun _=>Classical.propDecidable _) ((K₁).pocket j).val:=Multiset.mem_filter.mpr ⟨Placement.popped _ _ _ _ hV j, ht.symm ▸ Set.mem_univ _⟩
          rw [hf] at hh; simp at hh
      exact he _ rfl h
    rw [neighbors_mem]; exact (separation_triangle _ (Φ i) _).trans ((add_le_add (Placement.distances o _ _ _ hV _ _ h₁) ((neighbors_mem ..).mp (Placement.watching R v D o hp i V (Placement.revenue R v D o hp i V hu)))).trans hR)
-- μ actual tariffs from stencil Rank, unnormalized orientation.HY. choose each anchor uniformly. Here pays via card ι.G.Length μ.Sc probes group. μ assumed nonnegative.A from any test. Include V label gauge legs.
variable (he : e ≤ R.p.B) (hx:1≤ radiusB β)
variable (hQ : 0 ≤ A)(hZ : Fintype.card ι ≤ j)
include he hx hQ hZ
lemma charter (Y d:ℝ) (hY: Real.exp R.p.supportExponent*(Tile.peso G q e A R.p) ≤ Y):
          Nursery.Charters (x:=β) (S:=X) M₀ v (fun _=>1) Z₁ (e*ξ) j d R.p.supportExponent Y:=by -- V.Sign pays even if pConstraint.H. ζ Any if Pre.Es~
   have h:0 ≤ C_:=by unfold Tile.peso; have ht:= Collection.turnFee_pos R.p; have hg:= Wages.slot_ge G R.p.power R.p.order 0; have hp:=R.p.threshold_pos; unfold Wages.startup; positivity
   refine ⟨fun _=> zero_le_one,(mul_nonneg (Real.exp_pos _).le h).trans hY,fun _ _ _=>rfl,fun i j hι he'=>?_,ι,inferInstance,o, (fun i=>{i}),fun i _=>⟨i, Finset.mem_singleton_self _,?_⟩,fun i=>?_,fun i=> ?_⟩
   · rw [wings_sig] at hι
     obtain rfl := Wing.logKey.inj hι
     exact False.elim (by obtain ⟨v,h₁,h₂⟩:=he'; rw [(Placement.facts R _ _).1] at h₁ h₂; exact h₂ (((neighbors_mem ..).1 h₁).trans (Nat.le_mul_of_pos_right _ hx)))
   · rw [show (Typeface.brand M₀ v i).crest=(M₀ i).wing.support R_ from rfl, Placement.footprint_real]; exact (neighbors_mem ..).mpr (by simp)
   · exact (le_trans (Nat.le_trans (Finset.card_filter_le ..) (by simp : #(univ:Finset ι) ≤ Fintype.card ι)) hZ)
   -- only one ray in this test.Stencil absolute tariff.S.Dimension independence.
   unfold SumBudget; let Sgg(z:ι):= (Typeface.brand M₀ v z).crest; let C' z:= Palette.wages (brand M₀ v) (fun _=>1) z
   have hH : C' i=C_:=by unfold C' Palette.wages; rw [one_mul]; exact (Placement.planted R v D hp o i).earnings
   refine ⟨fun t=>?_,(hasSum_fintype _).summable,?_⟩
   · dsimp only; split; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (show 0 ≤ Palette.wages (brand M₀ v) (fun _=>1) t from mul_nonneg zero_le_one ((brand M₀ v t).profit)) (Real.exp_pos _).le); exact le_rfl
   -- simplify support paid via e ≤B.
   have hy : coverNumber R.p.B ((Typeface.brand M₀ v i).crest) ≤ 1:=by
       change coverNumber _ ((M₀ i).wing.support (Placement.file R e ι)) ≤1
       rw [Placement.footprint_real]; exact Sleet.cap_one _ (o i) _ (fun u hu=> (neighbors_mem ..).mpr (((neighbors_mem ..).1 hu).trans he))
   simp only [tsum_fintype, Finset.mem_singleton, Nat.cast_zero, mul_zero, Real.exp_zero, mul_one, Finset.sum_ite_eq, mem_univ, if_true]; rw [show Palette.wages (brand M₀ v) (fun _=>1) i=C_ from hH]
   refine le_trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) h) hY
   exact mul_le_of_le_one_right R.p.exponent_pos.le (by exact_mod_cast hy) -- inspect
end YM.RemainderComparison.Placement
