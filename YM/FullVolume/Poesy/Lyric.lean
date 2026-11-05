import YM.FullVolume.Poesy.Verse
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
variable {ι κ:Type}{A:ι→ RegularAddress c}{F H:ℕ→ ι→ Config G c→ℝ}{D:BudgetPoint}{σ r:ℝ}
lemma neptune (p:ι→ℕ)(hp:∀ i,∃ T:Finset ι,∀ k,p k≤ i→k∈ T){f:ℕ→ι→ℝ}(h:∀ n i, 0≤f n i)(hs:0<σ)(hx:∀ i,SumBudget (fun n=>f i n * Real.exp (σ*p n)) r): Sparse f:=by
    refine ⟨⟨_,fun i=> budget_mono (hx i) (h i) (fun x=> le_mul_of_one_le_right (h i x) (Real.one_le_exp (by positivity)))⟩,fun v hv=>?_⟩
    obtain ⟨i,hi⟩:=(((Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hs)).eventually_ge_atTop (r/v))).exists; obtain ⟨T,hT⟩:=hp i
    refine ⟨T,fun n Z hk=>?_⟩; have hp b (hb:b∈Z):i≤p b := le_of_not_gt fun ht=> disjoint_left.mp hk (hT b ht.le) hb
    apply le_of_mul_le_mul_right _ (Real.exp_pos (σ*i)); rw [sum_mul]; exact (sum_le_sum (f:=fun x=>f n x*Real.exp (σ*i)) fun x h'=> mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hp _ h')) hs.le)) (h n x)).trans ((budget_sum (hx n) Z).trans (((div_le_iff₀ hv).mp hi).trans_eq (mul_comm ..)))
lemma sparking {ι:Type}{f:ℕ→ι→ℝ}(h:Sparse f){κ:Type}[Fintype κ]:Sparse fun n(p:κ×ι)=> f n p.2:=by
    have he: Sparse (fun _:ℕ=>fun _:κ=> (1:ℝ)):= Sparse.constant (hasSum_fintype _).summable (fun _=> zero_le_one)
    simpa only [one_mul] using he.pairs h
namespace Cad
open Geo WilsonStartup Seat
set_option quotPrecheck false
variable {K H:ℕ→ Cad G}{B:BudgetPoint}{p:Clip}(hd:Decent p B)
include hd
lemma voyage (h:∀ n,(K n).path.Bounds p σ r a): PulseWise B (fun i:Tally c=> Song.strings (K 0).path B (Sum.inl i)) (fun n=> tuneLow (K n).path p 1):=by
     let R n:=(K n).path; let v n i:= |Low.mark (R n) p i| * lowCost G B (Low.length (R 0) i)
     have hv:Sparse v:=by
          refine neptune (Low.length (R 0)) ?_ (fun n i=>mul_nonneg (abs_nonneg _) (low_nonneg ..)) (half_pos (h 0|>.width)) (fun n=> low_budget G B (R n) (h n))
          intro k; obtain ⟨A,hA⟩:=tagSet k; refine ⟨Finset.univ ×ˢ ((Finset.univ:Finset Unit).disjSum (A×ˢ A)),fun i hi=>?_⟩
          rcases i with ⟨i,u|⟨u,v⟩⟩
          · simp
          change (Beacon.flag u).length+(Beacon.flag v).length≤k at hi
          exact mem_product.mpr ⟨mem_univ _,Finset.inr_mem_disjSum.mpr (mem_product.mpr ⟨hA u (by omega),hA v (by omega)⟩)⟩
     have hf (n:ℕ)(i:Tally c):= Song.tally_charge (R n) p B i 1 hd; let g:= |VerifiedReset.factor*(1:ℝ)| *turnFee B*B.threshold^2; have hg:0≤g:=by unfold g; have hB:=turnFee_pos B; positivity
     refine ⟨fun i k=> (hf i k).1, _,(sparking (κ:=Seat c) hv).climb hg, fun n i=>CouplingShape.sup_larger (hf n i|>.2) (le_of_eq ?_)⟩
     change _= g*v n i.2; change _=g*(|i.2.mark (R n) p| * lowCost G B (i.2.length (R n))); unfold g; ring
lemma lyric (h:∀ n,(K n).path.Bounds p σ r a)(he:∀ n,(H n).path.Bounds p σ r a)(hv:Soul atTop K H): Canopy B (fun i:Tally c=> Song.strings (K 0).path B (Sum.inl i)) (fun n=> tuneLow (K n).path p 1) (fun n=>tuneLow (H n).path p 1):=by
     refine ⟨voyage hd h,voyage hd he,fun ⟨s,i⟩ t ht=>?_⟩
     let A:=(K 0).path; let V(U:Config G c):= Low.plain A i (0:Site c) U
     let g(V:Cad G):=VerifiedReset.factor*(1:ℝ)* (i.mark V.path p); have hg: Glints atTop (g ∘ K) (g ∘ H):=by -- i Lambda depends.R
        unfold g; rcases i with ⟨i,i|⟨j,k⟩⟩
        · exact ⟨VerifiedReset.factor*1*p.direct,tendsto_const_nhds,tendsto_const_nhds⟩
        exact ((hv.1 i j).prods (hv.1 i k) (Q:=fun a b:ℝ=>a*b) continuous_mul).bin (Q:=fun x=>VerifiedReset.factor*1*x) (fun _ _=>continuousAt_const.mul continuousAt_id)
     have he' (P:Cad G): tuneLow P.path p 1 (s,i) = g P • (V ∘ s.view):=by
         funext x; change VerifiedReset.factor*1*((i.mark P.path p)*V (s.view x))=VerifiedReset.factor*1*(i.mark P.path p) * V (s.view x); ring
     let o : Support c:= i.home A B 0; have hL:= Low.plain_bill A p i (n:=c) 0 hd; have hR:= reg_bill hL (Low.plain_cont ..).measurable (Low.plain_local A i B hd.radius (0:Site c)) (Low.plain_gauge A i 0); let L(s:Seat c):=Seat.sup s hR (Bill.sup hL (X:=o) (fun _ h=> h)); let ℓ:= turnFee B*((faceCost G B+rowCost G B (Low.length A i))* B.threshold^2) -- V.g scale
     have hR:B.supBounds s.2 (s.spread o) (V ∘ s.view) ℓ:= Seat.sup s hR (Bill.sup hL (X:=o) (fun _ hh=>hh));
     let f n:= g (K n)-g (H n); have hm:Tendsto (fun n=> |f n| *ℓ) atTop (𝓝 0):=by simpa only [abs_zero,zero_mul,f,Function.comp_apply] using (hg.shrank.abs.mul_const ℓ)
     filter_upwards [hm.eventually (ge_mem_nhds ht)] with n hn; change B.supBounds s.2 (s.spread o) (tuneLow _ p 1 (s,i)-tuneLow _ p 1 (s,i)) _
     rw [he',he',← sub_smul]; exact CouplingShape.sup_larger (CouplingShape.sup_scale (f n) hR) hn
end Cad
end YM.ConnectedActivityE6.Lim
