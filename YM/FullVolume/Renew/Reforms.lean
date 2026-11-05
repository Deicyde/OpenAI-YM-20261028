import YM.FullVolume.Poesy.Ambit
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
variable {ι:Type}{X:ι→Support c}(B:BudgetPoint)
lemma ample (B:BudgetPoint) (c:Side) : ∃ p:ℝ,0<p∧∀ (S:Support c) t,0≤t→B.mass S t ≤ p*t:= by
     obtain ⟨v,hv⟩:= (Set.finite_range (B.mass (n:=c) · 1)).bddAbove; refine ⟨max v 1,lt_of_lt_of_le zero_lt_one (le_max_right ..),fun x t ht=>?_⟩
     have hp:= hv (Set.mem_range_self (f:=fun S:Support c=> B.mass S 1) x); unfold BudgetPoint.mass at *; rw [mul_one] at hp; exact mul_le_mul_of_nonneg_right (hp.trans (le_max_left ..)) ht
lemma curl {f:ℕ→ι→ℝ}(h:Sparse f)(C:ℕ→ι→ℝ→Prop) (hd:∀ i j,C i j (f i j))(hp:∀ i b,b>(0:ℝ)→∀ᶠ n in atTop,C n i b) (ε:ℝ)(he:0<ε):∀ᶠ n in atTop,∃ v:ι→ℝ,(∀ i,C n i (v i))∧ (∀ i,0≤v i)∧ SumBudget (fun i=>B.mass (X i) (v i)) ε:= by
     obtain ⟨p,h,hP⟩:= ample B c -- shadow h
     let t:=ε/p; have ht:0<t:= div_pos he h; obtain ⟨S,hS⟩:= (show Sparse f from ‹Sparse f›).stalls _ (half_pos ht); let s:=t/2/(S.card+1); have hs :0<s:=by unfold s; positivity
     filter_upwards [(eventually_all_finset _).2 (fun k (_:k∈S)=>hp k s hs)] with i hi; let v(k):=if k∈S then s else f i k; have hn k:0≤v k:=by unfold v; split; exact hs.le; exact Sparse.value ‹Sparse f› ..
     refine ⟨v,fun k=>?_,hn,budget_of_sum (fun k=>mul_nonneg (Real.exp_pos _).le (hn _)) ?_⟩;
     · unfold v; split; next h=> exact hi k h
       exact hd ..
     intro U; apply le_trans (sum_le_sum fun i hi=> hP (X i) _ (hn i)); rw [←mul_sum]
     let Z:=U.filter fun i=>i∉S; let G:= U.filter fun i=>i∈S; have hk:G ⊆ S:=fun i hi=> (mem_filter.mp hi).2
     refine (mul_le_mul_of_nonneg_left (?_ : ∑ j ∈ U,v j≤ t) h.le).trans_eq (by unfold t; field_simp)
     rw [← sum_filter_add_sum_filter_not U (fun i=>i∈S)]; apply le_trans _ (Eq.le (add_halves t)); apply add_le_add
     · change ∑ i∈G,v i ≤_; rw [sum_congr rfl (g:=fun _=> s) (fun x hx=> if_pos (hk hx)),sum_const,nsmul_eq_mul]; have h:=(Finset.card_le_card hk); exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (h.trans (Nat.le_succ _))) hs.le).trans_eq (by unfold s; push_cast; field_simp)
     change ∑ j∈ Z,v j ≤t/2; rw [sum_congr rfl (show ∀ j∈Z,v j=f i j from fun j hj=> if_neg (mem_filter.mp hj).2)]; exact hS i Z (disjoint_left.mpr fun i hi hh=> (mem_filter.mp hh).2 hi)
-- generic
variable {B}
lemma Canopy.loan {A:ι→RegularAddress c}{F H:ℕ→ι→ Config G c→ℝ} (h: Canopy B A F H)(ε:ℝ)(he:0<ε): ∀ᶠ n in atTop, ∃ q:ι→ℝ, (∀ i,B.supBounds (A i).site (A i).support (F n i-H n i) (q i)) ∧ SumBudget (fun i=>B.mass (A i).support (q i)) ε:=by
    obtain ⟨v,hv,V⟩:=h.a.sup; obtain ⟨w,hw,W⟩:=h.b.sup; let b:= fun n i q=> B.supBounds (A i).site (A i).support (F n i-H n i) q; have he:= curl (X:=fun i=> (A i).support) B (hv.tug hw) b (fun i j=>CouplingShape.sup_sub (h.a.chart ..) (h.b.chart ..) (V ..) (W ..)) h.sails ε he; filter_upwards [he] with i hi; obtain ⟨q,hq,-,H⟩:= hi; exact ⟨q,hq,H⟩
lemma Angel.hazel {A:ι→Support c}{F H:ℕ→ι→ Config G c→ℝ} (h:Angel F H)(ε:ℝ)(he:0<ε):∀ᶠ n in atTop, ∃ q:ι→ℝ,(∀ i,0 ≤ q i∧∀ V,‖F n i V-H n i V‖ ≤ q i)∧ SumBudget (fun i=> B.mass (A i) (q i)) ε:=by
    obtain ⟨v,hv,V⟩:=h.a.sup; obtain ⟨w,hw,W⟩:=h.b.sup; let b:=fun n i q=> 0≤q∧∀ V,‖F n i V-H n i V‖≤q; have hx:= curl (X:=A) B (hv.tug hw) b (fun i k=>⟨add_nonneg (hv.value i k) (hw.value i k),fun P=> (norm_sub_le ..).trans (add_le_add (V ..) (W ..))⟩) (fun i q he=> (h.sails i q he).mono fun n hn=>⟨he.le,hn⟩) ε he
    filter_upwards [hx] with i hi; obtain ⟨q,hq,-,H⟩:= hi; exact ⟨q,hq,H⟩
namespace Ledgers
variable {P: Listing G c}{F H:ℕ→ Collection.Source G c}
lemma vested (h: PulseWise B P.reg fun i=> (F i).logRead): ∃ C,∀ i,Averaging.Projects (P.read (F i)) B C:=by
     obtain ⟨u,hu,H⟩:= h.sup; obtain ⟨p,hp,hP⟩:= ample B c; obtain ⟨C,hC⟩:=hu.bound
     refine ⟨_,fun i=>⟨h.chart i,u i,H i,fun k=> budget_mono (budget_scale hp.le (hC i)) (fun j=> ?_) (fun j=>?_)⟩⟩
     · split; exact mul_nonneg (Real.exp_pos _).le (hu.value ..); rfl
     split; exact hP _ _ (hu.value ..); exact mul_nonneg hp.le (hu.value ..)
lemma motion (h:Canopy B P.reg (fun i=> (F i).logRead) (fun i=>(H i).logRead))(hp:Angel (fun i=>(F i).hardRead) (fun i=>(H i).hardRead))(v:ℝ)(hv:0<v): ∀ᶠ n in atTop,deviation B (P.read (F n)) (P.read (H n)) v:=by
    filter_upwards [h.loan v hv,hp.hazel (B:=B) (A:=fun i=> (P.hard i).support) v hv] with n hP hV; obtain ⟨u,hu,hU⟩:=hP; obtain ⟨w,hw,hW⟩:= hV; exact ⟨u,w,fun i=> (VerifiedReset.sup_varies (d:=P.reg i) (h.a.chart n i) (h.b.chart n i)).2 (hu i),hw,hU,hW⟩
structure Twin (a b:ℕ→ℝ): Prop where
    bound:∃ C,(∀ i,|a i|≤C)∧∀ i,|b i|≤C
    goes:Tendsto (fun i=> a i-b i) atTop (𝓝 0)
lemma incomes (hG:G.Simple)(h:Canopy B P.reg (fun i=>(F i|>.logRead)) (fun i=>(H i|>.logRead)))(hp:Angel (fun i=>(F i).hardRead) (fun i=>(H i).hardRead)): Twin (fun i=> Averaging.delta (P.read (F i))) (fun i=>Averaging.delta (P.read (H i))):=by
     obtain ⟨C,hC⟩:=vested h.a; obtain ⟨D,hD⟩:=vested h.b; have h0:= sq_pos_of_pos B.threshold_pos
     refine ⟨⟨max C D/B.threshold^2,fun i=> (le_div_iff₀ h0).mpr (by rw [mul_comm]; exact (Averaging.delta_bound hG (hC i)).trans (le_max_left ..)), fun i=> (le_div_iff₀ h0).mpr (by rw [mul_comm]; exact (Averaging.delta_bound hG (hD i)).trans (le_max_right ..))⟩,Metric.tendsto_nhds.mpr ?_⟩
     intro ε h'; filter_upwards [motion h hp (B.threshold^2*(ε/2)) (mul_pos h0 (half_pos h'))] with i hi; rw [dist_zero_right]; exact lt_of_le_of_lt (le_of_mul_le_mul_left (projection_drift hG (hC i) (hD i) hi) h0) (half_lt_self h')
end Ledgers
end YM.ConnectedActivityE6.Lim
