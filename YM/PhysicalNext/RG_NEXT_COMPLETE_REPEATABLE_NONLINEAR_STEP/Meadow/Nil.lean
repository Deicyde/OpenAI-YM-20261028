import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Mantel
/-!
 # finite truncation of catalogue via tags. fixed curves tilth.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' m: ℕ} {K : Teller G} {p a W U :ℝ}
section sow
variable {S:StepData c f} {T : Tube G S} {R:RG.Rep G f} {X: ConnectedActivityE6.Target G K} {o:Target.Order G W}
    {H : Cash W p a L₀ X o U T R}
def held (m: Music c f) := Sum.elim (fun i:Raw.Trans f=>i.2.2) (Sum.elim (fun i=>i.2.2) (Sum.elim (fun i=>i.2.2) (fun _ => 0))) m
def tuck (k:ℕ): Finset (Music c f) :=
    let Y:Finset (Raw.Trans f):=univ ×ˢ (univ ×ˢ Finset.range (k+1))
    Y.disjSum (Y.disjSum (Y.disjSum (univ:Finset (Miniature c f))))
lemma pocket (k:ℕ) (i:Music c f): i∈ Meadow.tuck k ↔ held i≤k:= by
  unfold held tuck; rcases i with i|i|i|i<;>simp
abbrev Poet (H:Cash W p a L₀ X o U (c:=c) (f:=f) T R) := {z:Vines _ _ // Stir H z} -- dep
-- lemma equivalence preimage support Labeling
lemma baked {k:ℕ} : { i: Vines c f| i.fst ≤1∧∀ j, (i.2 j)⊆Meadow.tuck k}.Finite:= by
  let T: Finset (Music c f):= Meadow.tuck k; let a i:=Fintype.piFinset (fun _j : Option (Fin i)=> T.powerset) -- Fintype
  let Y:Finset (Vines c f):= (Finset.range 2).sigma a
  apply Y.finite_toSet.subset; rintro ⟨i,j⟩ ⟨hv,hj⟩; change (Sigma.mk i j)∈Y
  change i≤1 at hv; apply mem_sigma.mpr; refine ⟨mem_range.mpr (by change i<2; omega),?_⟩; simp_rw [a,Fintype.mem_piFinset]; exact fun i=>mem_powerset.mpr (hj i)
lemma tiled (H : Cash W p a L₀ X o U T R) (k:ℕ): { i : Poet H | ∀ j,i.val.snd j⊆Meadow.tuck k}.Finite := Set.Finite.subset (baked.preimage (show Set.InjOn (fun p:Poet H=>p.val) _ from Subtype.val_injective.injOn)) (fun i hi=> show i.val.1≤1∧∀ j,i.val.snd j⊆ Meadow.tuck k from ⟨i.property.small,hi⟩)
def calendar (H:Cash W p a L₀ X o U T R) (k:ℕ) := (tiled H k).toFinset
lemma tunes (i:Poet H) (k:ℕ): i∈ Meadow.calendar H k↔∀ j,i.val.2 j ⊆ Meadow.tuck k:= Set.Finite.mem_toFinset ..
lemma retires (i:Poet H) : ∀ᶠ k in atTop,i ∈ Meadow.calendar H k:= by
  have hf j : ∀ᶠ k in atTop, i.val.2 j⊆ Meadow.tuck k:= (eventually_all_finset _).mpr fun u _=> (eventually_ge_atTop (held u)).mono (fun _ he=> (pocket ..).mpr he)
  exact (eventually_all.mpr hf).mono fun k h=> (tunes i k).2 h
end sow
end YM.PhysicalNext.Repeat.Meadow
