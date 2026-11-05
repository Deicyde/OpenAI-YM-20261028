import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Borel
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Glints
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Pallet
import YM.Further.GAUSSIAN_SCALAR_LEDGER.Reads
import YM.MultiNext.VACUUM_STABILITY.Localized.Checkout
import YM.PhysicalNext.ORDERED_AFFINE_2B.SymScope
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cadre.Match
import YM.Push.GRID_APPROXIMATION.Canonical



/-! # F-averaged restoration, symmetries, reads

same-keys canonical permutation and signed Π selected from the *given*
activities permutation along a curve. Exact transport of uses-final at
threshold α. `guards` of K include flags of full support. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Match
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open AnalyticBridge.GaussianFieldAlignment Locations Channels
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Itinerary Raw Matter Pond
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented
open Gas Ursell Trees Multiple Letter OmitClusters Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C δ e : ℝ} {R R' : RG.Rep G f} {Z Z' : Support c} {L : Side}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W}
variable {H : Cash W α μ L Q o C T R} {J : Cash W α μ L Q o C T R'} (χ : Chi)

-- label equivalence, not equating constants
lemma same_area (h : R.path=R'.path) (hr : R.activities.reg=R'.activities.reg) (hk : R.activities.forced=R'.activities.forced) : H.supportP=J.supportP := by
  change areas R T _ _=areas R' T _ _
  unfold areas footprints roadway Raw.space; simp_rw [h]
  have hf (l B): forcedFoot S.ratio l B R=forcedFoot S.ratio l B R' := funext fun i=> by unfold forcedFoot; rw [hk]
  have hg (l B): regularFoot S.ratio l B R=regularFoot S.ratio l B R' := funext fun i=> by unfold regularFoot; rw [hr]
  rw [hf,hg]

def staple (h : R.path=R'.path) (hr : R.activities.reg=R'.activities.reg) (hk : R.activities.forced=R'.activities.forced) : Alliance H J 1 0 where
  units := Equiv.refl _
  terrain i := by change i.biUnion J.supportP= _; rw [← same_area (J:=J) (H:=H) h hr hk]; unfold Cash.unionP; rw [show affine 1 (0:Site c)=id from funext fun u=>by simp [Lattice.affine],image_id]
  rosterC i := by rw [show affine 1 (0:Site c)=id from funext fun u=>by simp [Lattice.affine],image_id]; rfl

section turns
variable {s : Signed} {t : Site c} (H) (π : R.activities.Moves s (S.ratio.embed t))
def swing : Alliance H H s t := ⟨Turn.caravan R π, Turn.colors T R π Q.halo (radiusB α),fun i=> (Turn.display (StepData.sendSites s t) _ _).2 (fun j=> by
    conv_lhs => rw [Turn.mark R π i]
    exact Turn.atF ..)⟩
variable (U : Config G c)
lemma younger (p : H.ThinP) : H.entriesPool χ (pull s t U) p=H.entriesPool χ U ((swing H π).bearing p) := retaining _ _ _ _ _ H π ..
lemma older (p : H.ThickP) : H.depositsPool χ (pull s t U) p=H.depositsPool χ U ((swing H π).honoring p) := retaining _ _ _ _ _ H π ..
lemma incensed (p : H.fragrances) : H.trainedPool χ (pull s t U) p=H.trainedPool χ U ((swing H π).furrow p) := sale _ (H.entriesPool χ (pull s t U)) (H.entriesPool χ U) (swing H π).sec (younger H χ π U) p
lemma rose (p : H.Chapter) : H.colognePool χ (pull s t U) p=H.colognePool χ U ((swing H π).editor p) := by
  rcases p with p|p
  · exact older ..
  exact congr_arg Neg.neg (incensed ..)
lemma blossom (p : H.Chainbook) : H.smilesPool χ (pull s t U) p=H.smilesPool χ U ((swing H π).tongs p) := by
  let K:= swing H π
  exact if_congr (and_congr (K.sap _) (and_congr (K.splint _) (K.festoon U _))) (cashes _ _ _ (rose H χ π U) _) rfl
end turns
section reads
variable (H)
lemma sites (p : Molecule S) : UsesFinal (Pressure.temp α) (H.unionP p) (fun V=> H.spawn χ V p) := by
  let f r V:= H.emerging (vary (prism T α χ o.K 1 (Greenbelt.allot (S:=S) r)) V) p
  change UsesFinal _ _ (fun V=> likely (fun r => f r V)); intro U V ha hp
  apply congr_arg likely; funext r; exact H.emerge_uses (prism T α χ o.K 1 (Greenbelt.allot (S:=S) r)) rfl rfl p U V ha hp
lemma foster (p : H.fragrances) : UsesFinal (Pressure.temp α) (H.bookFoot (.inr p)) (fun V=> H.trainedPool χ V p) := by
  intro U V ha hf; unfold Cash.trainedPool Gas.term; refine congr_arg₂ (·/·) (congr_arg (coefficient H.seam p.snd * ·) ?_) rfl
  exact prod_congr rfl fun i hp=> inheritance (sites H χ (p.snd i).val) (show H.smallAt (p.snd i)⊆_ from subset_biUnion_of_mem (H.smallAt ∘ p.2) hp) U V ha hf
lemma branching (p : H.Chapter) : UsesFinal (Pressure.temp α) (H.bookFoot p) (fun V=> H.colognePool χ V p) := by
  rcases p with p|p
  · exact sites H χ p.val
  exact fun U V ha hf=> congr_arg Neg.neg (foster H χ p U V ha hf)
lemma boughs (p : H.Chainbook) : UsesFinal (Pressure.temp α) (H.library p) (fun V=> H.smilesPool χ V p) := by
  intro U V ha hf; unfold Cash.smilesPool; apply if_congr (and_congr_right fun _=> and_congr_right fun _=> show H.statesPool U p↔ H.statesPool V p from by unfold Cash.statesPool; rw [inter_comm,hf,inter_comm]) _ rfl
  unfold manyW; apply prod_congr rfl; intro i _; rw [show H.colognePool χ U i.val=_ from inheritance (branching H χ i.val) (show H.bookFoot i.val⊆_ from subset_biUnion_of_mem _ i.2) U V ha hf]

lemma fees (p : Molecule S) : Measurable (fun V=> H.spawn χ V p) ∧ GaugeInvariant (fun V=> H.spawn χ V p) := by
  let f (i:Reserve S) := prism T α χ o.K 1 (Greenbelt.allot i)
  let k (i:Reserve S) V:= H.emerging (vary (f i) V) p
  refine ⟨measurable_const.mul (Finset.measurable_fun_sum _ (f:=k) fun i _=> H.throws (f i) rfl rfl _),fun z V=>?_⟩
  exact congr_arg likely (funext fun i : Reserve S=> (show k i (Lattice.gauge z V)=k i V from H.gauge_weight (f i) rfl rfl p z V))
lemma buds (p : H.fragrances) : Measurable (fun V=> H.trainedPool χ V p) ∧ GaugeInvariant (fun V=> H.trainedPool χ V p) := by
  refine ⟨Measurable.div_const (measurable_const.mul (Finset.measurable_fun_prod univ (f:=fun i U=> H.entriesPool χ U (p.2 i)) fun i _=> (fees H χ (p.2 i).val).1)) _, fun z V=>?_⟩
  have h i : H.entriesPool χ (Lattice.gauge z V) (p.2 i)=H.entriesPool χ V (p.2 i) := (fees H χ (p.2 i).val).2 z V
  unfold Cash.trainedPool Gas.term; simp_rw [h]
lemma bursts (p : H.Chapter) : Measurable (fun V=> H.colognePool χ V p) ∧ GaugeInvariant (fun V=> H.colognePool χ V p) := by
  rcases p with p|p
  · exact fees H χ p.val
  exact ⟨(buds H χ p).1.neg, fun z V=> congr_arg Neg.neg ((buds H χ p).2 z V)⟩
lemma bloom (p : H.Chainbook) : Measurable (fun V=> H.smilesPool χ V p) ∧ GaugeInvariant (fun V=> H.smilesPool χ V p) := by
  by_cases he : H.Fresh p ∧ Ac.Spark H.bookFoot p.1
  · have h (V) : H.smilesPool χ V p=if H.statesPool V p then manyW (H.colognePool χ V) p else 0 := by simp only [Cash.smilesPool,he.1,he.2,true_and]
    simp_rw [h]
    have hm : MeasurableSet {V | H.statesPool V p} := by
      have ht : {V|H.statesPool V p}=⋃ i : {i : Support c // H.inventory p.1.toLeft=i∩H.library p}, {V:Config G c|RG.flags (Pressure.temp α) V=i.val} := by
        ext V; simp only [Set.mem_setOf_eq,Set.mem_iUnion]; exact ⟨fun he=>⟨⟨_,he⟩,rfl⟩,fun ⟨i,hk⟩=> by unfold Cash.statesPool; rw [hk]; exact i.property⟩
      rw [ht]; exact MeasurableSet.iUnion fun _=> flags_measurable_eq _ _
    refine ⟨Measurable.ite hm (Finset.measurable_fun_prod _ fun i _=> ((bursts H χ i.val).1.pow_const _).div_const _) measurable_const, ?_⟩
    intro z V; dsimp only; apply if_congr (show H.statesPool _ _ ↔ H.statesPool _ _ from by unfold Cash.statesPool; rw [RG.gauge_flags]) _ rfl
    unfold manyW; apply prod_congr rfl; intro i _; rw [show H.colognePool χ (Lattice.gauge z V) i.val=_ from (bursts H χ i.val).2 z V]
  have h : (fun V => H.smilesPool χ V p)=(fun _ : Config G c=>0) := funext fun V=> if_neg fun hs=> he ⟨hs.1,hs.2.1⟩
  rw [h]; exact ⟨measurable_const,fun z V=>rfl⟩
end reads
end YM.PhysicalNext.Repeat.Match
