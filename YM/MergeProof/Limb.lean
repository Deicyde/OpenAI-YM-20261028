import YM.MergeProof.Dreams
import YM.MergeProof.Lakes

set_option autoImplicit false
noncomputable section
namespace YM.Merge.Palette
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι] {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(Y:Cash W x μ L Q o C T R) (χ:Chi)
local notation "sx"=> radiusB x
open Blaze.March Multiple Ursell Trees Mixed Daisy OmitClusters Gas
variable (rA:ι→ℝ)
local notation "X'"=> swing Q L μ R.beta x C

variable (hR:Plot M Y rA) {e d B:ℝ} {j k : ℕ} (hB: Bikes Q L μ x a e B j k)
set_option quotPrecheck false
--
local notation "p₀"=> fun i:Y.ThinP=> tune M Y rA 0 k i.val
local notation "p₁"=> fun i:Y.ThickP=> tune M Y rA 1 0 i.val
local notation "P₀"=> pledgeA L Q μ x B j k
local notation "P₁"=> Charity.daisD Q L μ x k
local notation "VQ" => pledgeQ L Q μ x B j k
local notation "E0" => Q.mark L μ x
local notation "ρ"=> sailUp Q L x

-- Genuine memory of all inserted anchors; needed for reweighting and stage.
omit [Fintype ι] in
lemma mark_hit (V:Config G c)(U:Site c)(i:Molecule S) (Z:Tickets (sign M S))(hz:act M Y χ V i Z≠0)(j:ι)(hp:j∈ Z.val) (he:U∈(M j).crest.image S.ratio.parent): U∈Y.unionP i:=by
  letI:Nonempty (Forest S.ratio):=Tree.select S.ratio S.patch.odd_side
  have ht := (present M Y χ V Z i (F:=Classical.ofNonempty) hz).1 (Z.reaches_of hp)
  have hs : areas R T Q.halo (radiusB x) (sign M S j)⊆Y.unionP i:= subset_biUnion_of_mem _ ht
  apply hs; unfold sign; rw [(M j).turn.badge_area]; refine halo_subset _ _ ?_; exact Finset.image_subset_image (s₂:= RG.inspected (M j).crest) Finset.subset_union_left he -- edit
lemma forgotten (V:Config G c)(j:ι)(U:Site c)(he:U∈ (M j).crest.image S.ratio.parent)(i:Molecule S)(hz:U∉Y.unionP i)
    (t:ℝ)(Z:Finset ι): vote M Y χ rA i V t Z=vote M Y χ rA i V t (Z.erase j):=by
  unfold vote color; apply sum_congr rfl; intro v _
  by_cases hv:j∈v.val
  · rw [show act M Y χ V i v=0 from Classical.byContradiction (fun h=> hz (mark_hit M Y χ V U i v h j hv he)),mul_zero,mul_zero]
  exact congr_arg (·*_) (prod_congr rfl fun i hi=> by unfold ways; simp_rw [show i∈Z.erase j↔ i∈Z from (mem_erase.trans (and_iff_right (fun h=>hv (h ▸ hi))))]) -- DecPred
lemma limps (V:Config G c)(j:ι)(U:Site c)(he:U∈(M j).crest.image S.ratio.parent)(i:Y.fragrances)(hz:U∉Y.bookFoot (.inr i)) (t:ℝ)(Z:Finset ι): song M Y χ rA i V t Z=song M Y χ rA i V t (Z.erase j):= by
  refine congr_arg (fun v:ℝ=> (coefficient Y.seam i.2*v/↑(i.1+1).factorial)) (prod_congr rfl (fun p _=> ?_)); exact forgotten M Y χ rA V j U he (i.2 p).val (fun h=> hz (Finset.subset_biUnion_of_mem (Y.smallAt ∘ i.2) (mem_univ p) h)) t Z
lemma limbs (V:Config G c)(j:ι)(U:Site c)(he:U∈(M j).crest.image S.ratio.parent)(i:Y.Chainbook)(hz:U∉Y.library i)(t:ℝ)(Z:Finset ι): fete M Y χ rA i V t Z=fete M Y χ rA i V t (Z.erase j):=by
  unfold fete Cash.smilesMill; split
  next hx=>
    refine Finset.prod_congr rfl fun y _=> congr_arg (fun t:ℝ=> t^(i.2 y+1)/↑(i.2 y+1).factorial) ?_
    rcases y with ⟨i'|i',hv⟩
    · exact forgotten M Y χ rA V j U he i'.val (fun h=> hz (Finset.subset_biUnion_of_mem Y.bookFoot hv h)) t Z
    exact congr_arg (- ·) (limps M Y χ rA V j U he i' (fun h=>hz (Finset.subset_biUnion_of_mem Y.bookFoot hv h)) t Z)
  rfl
lemma permits (i:Y.fragrances)(p:Finset ι)(t:ℝ) : let f V := song M Y χ rA i V t p
    let X:= Y.bookFoot (.inr i); UsesFinal (Pressure.temp x) X f ∧ Measurable f ∧ GaugeInvariant f ∧ ∀ V, f V≠0 → Healthy (Pressure.temp x) X V:=by
    intro g Z
    let u V j:= Y.entriesMill (color M Y χ V (ways rA t p)) (i.2 j); let a:ℝ:=Ursell.coefficient Y.seam i.2
    have h(z): Y.smallAt (i.2 z)⊆ Y.bookFoot (.inr i):= subset_biUnion_of_mem (Y.smallAt ∘ i.2) (mem_univ _)
    refine ⟨fun V U hV hb=>?_,( (measurable_const (a:=a) |>.mul (Finset.measurable_fun_prod _ fun j _=> show Measurable (fun V=>u V j) from (color_spin M Y χ (ways rA t p) _).1)).div_const ((i.fst+1).factorial:ℝ)),fun k U=> ?_,fun V hx=>?_⟩
    · exact congr_arg (fun v:ℝ=> a*v/↑(i.1+1).factorial) (prod_congr rfl fun j _=> inheritance ((color_spin M Y χ _ _).2.1) (h j) V U hV hb)
    · exact congr_arg (fun v:ℝ=> a*v/↑(i.1+1).factorial) (prod_congr rfl fun j _=> (show u (gauge k U) j=u U j from (color_spin M Y χ _ _).2.2 k U))
    refine Finset.disjoint_left.mpr ?_; intro z hz hp; obtain ⟨j,hj,hq⟩:= mem_biUnion.mp hz
    have ht : u V j ≠0 := fun h => hx (by unfold g song Cash.trainedMill Gas.term; rw [prod_eq_zero (mem_univ j) h,mul_zero,zero_div]); have he:= (springs M Y χ V (i.2 j).val _ ht).2.1; rw [(i.2 j).2.2] at he; exact Finset.notMem_empty _ (he.symm ▸ (show z∈RG.flags _ _∩ _ from mem_inter.mpr ⟨hp,hq⟩))
include hR
open Switch

end YM.Merge.Palette
