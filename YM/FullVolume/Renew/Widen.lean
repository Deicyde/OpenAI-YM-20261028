import YM.FullVolume.Renew.Afloat
/-! E6 Layout steps full volume.Epoch. Keep Records by exact tags.Canvas.Read.F. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
open Matrix Window Progress.StationaryScenes Green Census Control Flux FullVolume.Shadow
open Gate Frond Vine Mask
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{J: Ultrafilter ℕ}{Q:ConnectedActivityE6.Target G P}{W x μ C₀ a b e ℓ v :ℝ}{o:Target.Order G W}
    {Λ: Era G S}{U:ℕ→ E→ Config G c}{Z: Draft F G} {K H:ℕ→ Epoch Λ}{j:ℕ}{p:E}
open FullVolume.Neptune Flux Shield Eider Packets Polar
namespace Ledgers
open Geo WilsonStartup
open Ovens Ovens.Pipes Rack
lemma hopper {ι κ:Type}{f:ℕ→ι→ℝ}(h:Sparse f)(e:ι↪κ):Sparse fun n=> stuff e (f n):=by
    let F n:= stuff e (f n); have hv n i:0≤ F n i:=by
        unfold F; by_cases hp:i∈Set.range e
        · obtain ⟨j,rfl⟩:= hp; rw [stuffed]; exact h.value ..
        rw [Progress.DirectedRecipe.blank _ _ hp]
    have hs n (T:Finset κ):∑ x∈T,F n x=∑ x∈ T.preimage e e.injective.injOn, f n x:=by
       let X:= T.preimage e e.injective.injOn; rw [← sum_subset (Finset.Subset.trans (show X.map e⊆T from ?_) (Finset.Subset.refl _)) ?_,Finset.sum_map];
       · exact sum_congr rfl fun i _=> stuffed ..
       · intro i hi; obtain ⟨j,hj,rfl⟩:=mem_map.mp hi; exact Finset.mem_preimage ..|>.mp hj
       intro i hi hI; refine Progress.DirectedRecipe.blank _ _ fun hz=> ?_; obtain ⟨j,rfl⟩:= hz; exact hI (mem_map_of_mem e (Finset.mem_preimage ..|>.mpr hi))
    refine ⟨⟨_,fun i=> budget_of_sum (hv i) fun T=> (hs i T).trans_le (budget_sum (h.bound.choose_spec i) _)⟩,fun b hb=>?_⟩; obtain ⟨A,hA⟩:=h.stalls b hb
    exact ⟨A.map e,fun n T ht=>(hs n T).trans_le (hA n _ (disjoint_left.mpr fun i hi hm=> disjoint_left.mp ht (mem_map_of_mem _ hi) (Finset.mem_preimage ..|>.mp hm)))⟩
variable {B:BudgetPoint} {X:Pipes G c} {U V:ℕ→Tap G c}
private lemma corner {F H:ℕ→ℕ→ Config G c→ℝ}(h:Angel F H)(a:ℕ↪ℕ): Angel (fun i=>stuff a (F i)) (fun i=>stuff a (H i)):=by
    have hg {F:ℕ→ℕ→ Config G c→ℝ}(h:Vented F): Vented fun k=> stuff a (F k):=by
       obtain ⟨v,hv,V⟩:= h.sup; refine ⟨_,hopper hv a,fun i U j=>?_⟩; by_cases h:j∈Set.range a
       · obtain ⟨v,rfl⟩:=h; rw [stuffed,stuffed]; exact V ..
       rw [Progress.DirectedRecipe.blank _ _ h, Progress.DirectedRecipe.blank _ _ h, Pi.zero_apply,norm_zero]
    refine ⟨hg h.a,hg h.b,fun i b hp=>?_⟩; by_cases hi:i∈Set.range a
    · obtain ⟨k,rfl⟩:=hi; simp_rw [stuffed]; exact h.sails _ _ hp
    simp_rw [Progress.DirectedRecipe.blank _ _ hi,sub_self,norm_zero]; simp [hp.le]
lemma consume (D:Pipes G c)(h:Canopy B D.reg (fun n=>(U n).regular) (fun n=>(V n).regular)): Canopy B (drawer G c).reg (fun n=> (widen D (U n)).regular) (fun n=>(widen D (V n)).regular):=by
    let e:=upE D; have hk {F:ℕ→Tap G c}(h:PulseWise B D.reg fun i=>(F i).regular):PulseWise B (drawer G c).reg fun i=> (widen D (F i)).regular:=by
       obtain ⟨v,hv,H⟩:=h.sup; refine ⟨fun n i=>?_,_,hopper hv e,fun i b=>?_⟩
       · unfold widen; by_cases hp:i∈Set.range e
         · obtain ⟨i,rfl⟩:=hp; change B.Regular ((drawer G c).reg (upE D i)).support (stuff (upE D) (F n).regular (upE D i)); rw [stuffed,reg_up]; exact h.chart ..
         simp only; rw [Progress.DirectedRecipe.blank _ _ hp]; exact CouplingShape.reg_const _
       change B.supBounds _ _ (stuff e _ b) (stuff e _ b); by_cases h:b∈Set.range e
       · obtain ⟨j,rfl⟩:= h; rw [stuffed,stuffed]; unfold e; rw [reg_up]; exact H ..
       rw [Progress.DirectedRecipe.blank _ _ h,Progress.DirectedRecipe.blank _ _ h]; exact VerifiedReset.sup_le (CouplingShape.sup_const 0) (by simp)
    refine ⟨hk h.a, hk h.b,fun i b hb=>?_⟩; by_cases hv:i∈Set.range e
    · obtain ⟨v,rfl⟩:=hv; unfold e; simp_rw [widen,stuffed,reg_up]; exact h.sails _ _ hb
    simp only [widen,Progress.DirectedRecipe.blank (upE D) _ hv,sub_zero]; exact Eventually.of_forall fun n=> VerifiedReset.sup_le (CouplingShape.sup_const _) (Eq.le abs_zero |>.trans hb.le) -- editing
lemma entire (D:Pipes G c)(h:Angel (fun i=>(U i).logarithm ) (fun i=> (V i).logarithm))(hp:Angel (fun i=>(U i).forced ) (fun i=>(V i).forced)) : Angel (fun n=> solid (folio G c) B (widen D (U n))) (fun n=> solid (folio G c) B (widen D (V n))):=Angel.herb B _ (corner hp (upK D)) (corner h (upS D)) _
end Ledgers
end YM.ConnectedActivityE6.Lim
