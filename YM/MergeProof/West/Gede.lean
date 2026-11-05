import YM.Further.ITERATION_RECIPE_PRODUCER.Crown
import YM.MergeProof.West.Kilo
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Royal
import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Paying

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Function Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Display Display.Docking Filter RG.Supply Next.Rank.Station Finset Bid West
open scoped Topology BigOperators Classical
variable {G : Gauge}{ι:Type} [Fintype ι]
-- universal.D panel. Also Tactics preserve on ThroughLaunch raises.VarT.
structure Fortified (X: Sheet G)(B:MapPrices)(u:ℕ→ℕ)(P:∀ d,ι→Tapes.Panel d)(k:ℕ→Finset ℕ)(N:ℕ→ℕ):Prop where
   same d i j : ((P d i).θ=(P d j).θ) ∧ ∀ n:ℕ, ((P d i).bag n).era.coast.Q=((P d j).bag n).era.coast.Q
   buys (i:ι): PreStand X B (fun d=> P d i) k N
   shops (i:ι): Shops B X k (fun d=>P d i) N
   lifts (i:ι)(d j:ℕ)(h:d∈k j)(L:Side)(hu:N j ≤ L.val):
      let p:=P d i
      let v:=p.bag j
      Coul v (u d) ∧ HLane v (u d) L ∧ reserveX (u:=u d) (prepared X.kernel) j p.θ p.arc L.val
lemma y_poster (X:Sheet G)(B:MapPrices)(b:ℕ → ι→ℝ)(h:∀ d i,d+6≤ b d i) (u:ℕ→ℕ)(hu:∀ d,2 ≤ u d) (ht:Tendsto (fun i=>(X.profile i).order) atTop atTop): ∃ k N, ∃ P:∀ d,ι→ Tapes.Panel d,(∀ d,∀ᶠ i in atTop,d∈k i)∧(∀ d i,(P d i).arc=b d i)∧Fortified X B u P k N:=by
   choose P hP hE using fun d:ℕ=> y_purchases X B (b d) (u d) d (hu d) (h d)
   let K(j:ℕ):=(range (j+1)).filter fun i=> i+3≤ j ∧ ∀ x:ι, (P i x).θ+1 ≤ (X.profile j).order
   have hip {j i} (h:i∈ K j):= (mem_filter.mp h).2
   choose! μ hμ using fun j i χ (h:i ∈ K j)=> (hE i).estate j χ ((hip h).2 χ)
   choose M hM using fun χ:ι => Soft.shapers B X K (fun i=>P i χ)
   let L : ℕ→ℕ:= fun j=> (K j).sup (fun i=> univ.sup (fun χ=> μ j i χ))+univ.sup (fun χ=> M χ j)
   have fee i j χ (hp:i∈ K j)(Y:Side)(hy:L j ≤ Y.val): μ j i χ ≤ Y.val:= ((le_sup (f:=fun χ => μ j i χ) (mem_univ χ)).trans (le_sup (f:=fun i=> univ.sup (fun χ=> μ j i χ)) hp)).trans ((Nat.le_add_right _ (univ.sup (fun χ=> M χ j))).trans hy)
   refine ⟨K,L,P, fun d=> ?_, hP,fun i=> (hE i).pin, fun χ=> ⟨fun i j hi=>⟨(hip hi).1, fun v hv=>?_⟩,fun i j hi v hv=> ?_⟩,fun i=> ⟨fun j Y hy=> ?_⟩,fun i d j h L' hu=>?_⟩
   · filter_upwards [eventually_ge_atTop (d+3),eventually_all.mpr (fun i=>ht.eventually_ge_atTop ((P d i).θ+1))] with k hk hv; exact mem_filter.mpr ⟨mem_range.mpr (by omega),hk,hv⟩
   · have hh:=hμ j i χ hi v (fee _ _ _ hi v hv); exact ⟨hh.1, hh.2.2.1⟩
   · exact hμ j i χ hi v (fee _ _ _ hi v hv)|>.2.2.2.2
   · exact (hM i).poles j Y ((le_sup (f:=fun χ=> M χ j) (mem_univ i)).trans ((Nat.le_add_left ..).trans hy))
   have hp:= hμ j d i h L' (fee _ _ _ h L' hu); exact ⟨(hE d).Coulomb _ _,hp.2.1,hp.2.2.2.1⟩
end YM.PhysicalNext.InteractingRank.Soft
