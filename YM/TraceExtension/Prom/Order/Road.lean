import YM.TraceExtension.Prom.Order.Graph
import YM.MergeProof.East.Gran
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Function Filter MeasureTheory Finset Lattice Wilson RG Precision Supply
open Pressure Push.SectorMeasure Next.Rank RankCovariance Thirst Ac Baler Glyph Tapes Marker
open Display Display.Docking Display.Sew Value Flux SectorNext.Vacuum Station Perch Tapes.West Atlas
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {ι:Type}[Fintype ι]{G:Gauge}{X:Sheet G}{D:Rolls X}{R:Protection D}{E:Delays R} {Z: Bar E}
structure AskSky (X: Sheet G)(B:MapPrices) (u m:ℕ→ℕ)(c:∀ d,ι→ Tapes.Panel d)(K:ℕ→Finset ℕ):Prop where
   later : ∀ i, ∀ᶠ j:ℕ in atTop, i∈K j
   costs : ∀ i j,i∈ K j→ ∀ (x:ι),Coul ((c i x).bag j) (u i) ∧ ∀ k∈ farSky j,∀ L:Side,m k ≤ L.val → Roh X B j ((c i x).bag j) (u i) L
   pin : ∀ d i j,((c d i).θ=(c d j).θ) ∧ ∀ n:ℕ, ((c d i).bag n).era.coast.Q=((c d j).bag n).era.coast.Q
lemma asks_sky (X: Sheet G)(B:MapPrices)(u:ℕ →ℕ)(b:ℕ → ι→ℝ)(h:∀ d i,d+7≤ b d i)(hu:∀ d,2 ≤ u d) (ht:Tendsto (fun i=>(X.profile i).order) atTop atTop): ∃ m,∃ c:∀ d,ι→ Tapes.Panel d,∃ K,(∀ d i,(c d i).arc=b d i)∧AskSky X B u m c K:=by
    choose P hP hE using fun d=> y_purchasesSky X B (b d) (u d) d (hu d) (fun i=>by linarith only [h d i]);
    let K(j:ℕ):=(range (j+1)).filter fun i=> ∀ x:ι,(P i x).θ+1 ≤ (X.profile (j-1)).order
    have hip {j i}(h:i∈ K j):= (mem_filter.mp h).2
    choose! μ hμ using fun j i χ (h:i∈K j)=> (hE i).estate j χ ((hip h) χ)
    let Q (j:ℕ):= (K j).sup fun i=>univ.sup (fun χ=> μ j i χ)
    let m (j:ℕ):= max (Q j) (Q (j+1))
    have hv (j i)(x)(h:i∈ K j):μ j i x ≤ Q j:= (le_sup (f:=fun x=>μ j i x) (mem_univ _)).trans (le_sup (f:=fun i=> univ.sup (μ j i)) h)
    have hz : Tendsto (fun j:ℕ=>j-1) atTop atTop:= by apply tendsto_atTop.2; intro a; filter_upwards [eventually_ge_atTop (a+1)] with j he; omega
    refine ⟨m,P,K,hP,fun i=>?_,fun i j hi x=> ⟨(hE i).Coulomb _ _,fun k hk L he=>?_⟩,fun d=> (hE d).pin⟩
    · filter_upwards [eventually_ge_atTop i,eventually_all.mpr (fun x=> (ht.comp hz).eventually_ge_atTop ((P i x).θ+1))] with k hk hv; exact mem_filter.mpr ⟨mem_range.mpr (by omega),hv⟩
    apply hμ j i x hi L; refine (hv j i x hi).trans ((le_trans ?_ he))
    rcases show k=j ∨ k=j-1 by simpa only [farSky, mem_insert,mem_singleton] using hk with h|h
    · rw [h]; exact le_max_left ..
    cases j <;> subst k <;> unfold m
    · exact le_max_left ..
    apply le_max_right

variable {u m:ℕ→ℕ}{c:∀ d,ι→ Tapes.Panel d}{K:ℕ → Finset ℕ}(B:MapPrices)(U:Wait Z)
variable {z:ℕ→ℝ}
lemma forwardSky (Q:AskSky X B u m c K)(O:HaarBudget G)(J:ChartRatio G)(h:LocalRatio J) (hm:∀ i,m i ≤ (D.L i).val) (hc:∀ i,2≤u i) (hp:∀ i,0≤ z i) (hG:G.Simple): ∃ (W:Wait Z)(P:∀ d,ι→Tapes.Panel d),
    U.minLength ≤ W.minLength ∧ U.readyHere ≤ W.readyHere ∧ U.window ≤ W.window ∧ (∀ d k,(c d k).arc=(P d k).arc ∧ (c d k).θ=(P d k).θ) ∧
    (∀ d i j,((P d i).θ=(P d j).θ) ∧ ∀ n:ℕ, ((P d i).bag n).era.coast.Q=((P d j).bag n).era.coast.Q)∧
    ∀ (C: Family G), Paid W C.path.levels → ∀ B': Binding C, B'.prices=B→ ∀ d x, ∀ᶠ k in atTop,
       let a:= (P d x).bag (C.path.levels.clock.J k); ∀ y:ℝ,0≤y→y ≤ a.band→ MergeProof.East.topL C.path.levels k ≤ C.path.levels.clock.monitor k ∧ ∃ l r, LegacyCostSky B' J (-3) (z d) (vent a y) k (u d) d O l r:=by
   let H i x j:= (c i x).bag j; have hz i x j:0≤(H i x j).band:= by unfold H;rw [(c i x).factor]; linarith only [(c i x).huge,Nat.cast_nonneg (α:=ℝ) i]
   choose! w r δ hδ hD Hs using fun i j x (hK:i∈ K j)=> office B (hJ:=(Q.costs i j hK x).1) (fun t ht=> (Q.costs i j hK x).2 t ht (D.L t) (hm t)) (hc i) J h (hz i x j) O _ i (hp i)
   let f i j x:= if h:i∈ K j then δ i j x else (H i x j).era.coast.a
   have he(i j x): 0 < f i j x:= by
      unfold f; split
      · apply hδ _ _ _ (by assumption)
      exact (H i x j).era.coast.posA
   let P i x:= InteractingRank.curtain (c i x) (fun j=> f i j x) (fun j=> he i j x)
   have hχ (j) (i) x (hi:i∈ K j): ∀ᶠ s in atTop, CapacitySky B D ((P i x).bag j) (w i j x) (r i j x) s O (z i) J (u i) j i:=by
      change ∀ᶠ s in atTop, CapacitySky _ _ (InteractingRank.trim (H i x j) (f i j x) _) _ _ _ _ _ _ _ _ _
      simp only [f,dif_pos hi]; exact Hs i j x hi
   let v (j:ℕ)(s:ℝ):= ∑ i∈K (j+1), ∑ x : ι, Ship.benchCost Z (P i x).arc j (3*s)
   have hε : Tendsto (Ship.preHat Z) atTop atTop:= Filter.tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop (Gauge.slopeConstant_pos hG))
   have hH(i x): 0 ≤ (P i x).arc:=by linarith only [(P i x).huge,Nat.cast_nonneg (α:=ℝ) i]
   have hB (j : ℕ): ∀ᶠ s:ℝ in atTop, ∀ i∈ K (j+1),∀ x:ι, CapacitySky B D ((P i x).bag (j+1)) (w i (j+1) x) (r i (j+1) x) (Ship.preHat Z s) O (z i) J (u i) (j+1) i ∧ runTicket Z (P i x).arc (j+1) s:=
     (eventually_all_finset _).2 (fun i h=> eventually_all.mpr (fun x=> (hε.eventually (hχ _ i x h)).and (ascentSky Z (P i x).arc (j+1) hG (hH i x))))
   choose t ht' using fun j=> eventually_atTop.mp ((hB j).and (((Perch.bill_lo zero_lt_one).comp hε).eventually_ge_atTop (max ((D.L (j+1)).val:ℝ) ((D.L j).val:ℝ))))
   let W:Wait Z:={ U with readyHere:=fun j=> max (U.readyHere j) (t j)
                          window:=fun j s=> U.window j s + v j s
                          sublin:= by
                            intro j; have hv : Tendsto (fun s : ℝ=> (v j s:ℝ)/s) atTop (𝓝 0):= by
                               have hm:=tendsto_finsetSum (K (j+1)) (fun i _=> tendsto_finsetSum univ (fun x _=> lastsSky Z j (P i x).arc hG (hH i x)))
                               simpa only [v,Nat.cast_sum,Finset.sum_div,Finset.sum_const_zero] using! hm
                            simpa [add_div] using! (U.sublin j).add hv }
   refine ⟨W,P,le_rfl,(fun j=> le_max_left ..),fun j s=> Nat.le_add_right ..,fun _ _=>⟨rfl,rfl⟩,fun d i j => Q.pin d i j, fun C hp B' H i x=> ?_⟩
   let A:= C.path.levels; let b:= (P i x).arc
   filter_upwards [A.fits.deep.eventually (Q.later i),A.fits.deep.eventually_gt_atTop X.first, vault_sizeSky A hG] with k hk hV hR
   obtain ⟨a,ha⟩:= Nat.exists_eq_succ_of_ne_zero (show A.clock.J k≠0 from by omega); intro T y hY hy
   have hQ:(C.path.levels).clock.J k=a+1:= ha
   rw [ha] at hk hV
   have hw(s)(h: W.readyHere a ≤ s):= ht' a s ((le_max_right ..).trans h)
   have he(s)(h:W.readyHere a ≤ s) : runTicket Z b (a+1) s ∧ Ship.benchCost Z b a (3*s) ≤ W.window a s:= by
      refine ⟨((hw s h).1 i hk x).2,?_⟩
      exact ((single_le_sum (f:=fun x=> Ship.benchCost Z ((P i x).arc) a (3*s)) (fun _ _=>Nat.zero_le _) (mem_univ x)).trans (single_le_sum (f:=fun i=> ∑ x,Ship.benchCost Z (P i x).arc a (3*s)) (fun _ _=>Nat.zero_le _) hk)).trans (Nat.le_add_left ..)
   obtain ⟨hH,hχ⟩:= atlasSky W hp hQ (by omega) he (hy.trans_eq ((P i x).factor _)) (hH i x) hG
   have hz := hw _ hH
   constructor
   · change _ ≤ A.clock.monitor k; unfold MergeProof.East.topL wheel;rw [hQ, hp.lengths,Nat.add_sub_cancel]; change _ ≤ A.clock.monitor k; rw [fire_bill,← listSky W hp k]; exact hz.2
   have hT : T=(P i x).bag (a+1):= by unfold T; rw [ha]
   rw [hT] at hy; rw [hT]
   exact ⟨_,_,(hz.1 i hk x).1 C B' H k hp.kernel hp.lengths hp.stage ha (listSky W hp k).symm hR y hY hy hχ⟩
end YM.PhysicalNext.InteractingRank.Soft
