import YM.FullVolume.E6.Coterie
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
variable {ι κ:Type}{A:ι→ RegularAddress c}{F H:ℕ→ ι→ Config G c→ℝ}{D:BudgetPoint}
namespace PulseWise
lemma forms (h:PulseWise D A F)(hn:κ↪ι):PulseWise D (fun i=> A (hn i)) (fun n i=>F n (hn i)) :=by obtain ⟨v,hv,V⟩:= h.sup; exact ⟨fun n i=> h.chart ..,⟨_,hv.pull hn,fun i x=> V ..⟩⟩
lemma both {A:ι⊕κ→RegularAddress c}{F:ℕ→(ι ⊕ κ)→ Config G c →ℝ}(h:PulseWise D (fun i=>A (.inl i)) fun n i=>F n (.inl i))(he:PulseWise D (fun i=> A (.inr i)) fun n i=> F n (.inr i)):PulseWise D A F:=by
    obtain ⟨v,hv,V⟩:=h.sup; obtain ⟨w,hw,W⟩:=he.sup; refine ⟨fun n i=>?_,⟨fun n=> Sum.elim (v n) (w n),Sparse.either hv hw,fun n i=>?_⟩⟩; all_goals cases i <;> first|exact V ..|exact W ..|exact h.chart ..|exact he.chart ..
lemma scaled (h:PulseWise D A F) {f:ℕ→ℝ}{C:ℝ}(he: ∀ i, |f i|≤C): PulseWise D A (fun n i=> f n • F n i):=by
    obtain ⟨v,hv,V⟩:= h.sup; exact ⟨fun n i=>CouplingShape.reg_scale _ (h.chart ..), _,hv.climb ((abs_nonneg _).trans (he 0)),fun i x=>CouplingShape.sup_larger (CouplingShape.sup_scale _ (V i x)) (mul_le_mul_of_nonneg_right (he i) (hv.value ..))⟩
end PulseWise
namespace Canopy
lemma transI (h:Canopy D A F H)(hn:κ↪ι):Canopy D (fun i=> A (hn i)) (fun n i=>F n (hn i)) (fun n i=>H n (hn i)):=⟨h.a.forms hn,h.b.forms hn,fun i=> h.sails _⟩
lemma splices {A:ι ⊕ κ→RegularAddress c}{F H:ℕ→(ι⊕κ)→ Config G c →ℝ}(h:Canopy D (fun i=>A (.inl i)) (fun n i=>F n (.inl i)) (fun n i=>H n (.inl i)))(he:Canopy D (fun i=>A (.inr i)) (fun n i=> F n (.inr i)) (fun n i=>H n (.inr i))):Canopy D A F H:=⟨PulseWise.both h.a he.a, PulseWise.both h.b he.b,fun i b hv=>by cases i <;> first|exact h.sails _ _ hv|exact he.sails _ _ hv⟩
lemma repel (h:Canopy D A F H) {f g:ℕ→ℝ}{C:ℝ}(he:∀ i,|f i|≤C) (hp:∀ i,|g i| ≤ C) (ht:Tendsto (fun i=> f i-g i) atTop (𝓝 0)): Canopy D A (fun n i=> f n • F n i) (fun n i=> g n • H n i):=by
    obtain ⟨v,hv,V⟩:=h.b.sup; obtain ⟨w,hw⟩:=hv.bound; have hh:0 < C+1:= add_pos_of_nonneg_of_pos ((abs_nonneg _).trans (he 0)) zero_lt_one
    refine ⟨h.a.scaled he,h.b.scaled hp,fun i b hb=>?_⟩; let x:= b/2; have hx:0<x:=half_pos hb
    have h': Tendsto (fun i=> |f i-g i| *w) atTop (𝓝 0):= by convert! ht.abs.mul_const w using 1; simp
    filter_upwards [h.sails i (x/(C+1)) (div_pos hx hh),h'.eventually (ge_mem_nhds hx)] with n hn hB
    let y:=f n; let t:= y-g n; let u:= F n i - H n i; have ht:y • F n i-g n • H n i = y • u-(-t) • H n i:=by unfold u t; module
    rw [ht]
    apply CouplingShape.sup_larger (CouplingShape.sup_sub (CouplingShape.reg_scale _ (CouplingShape.reg_sub (h.a.chart n i) (h.b.chart n i))) (CouplingShape.reg_scale _ (h.b.chart n i)) (CouplingShape.sup_scale _ hn) (CouplingShape.sup_scale _ (V n i)))
    rw [abs_neg]; exact (add_le_add ((mul_le_mul_of_nonneg_right ((he n).trans (le_add_of_nonneg_right zero_le_one)) hn.1).trans_eq (by field_simp : (C+1)*(x/(C+1))=x)) ((mul_le_mul_of_nonneg_left (budget_single (hw n) i) (abs_nonneg t)).trans hB)).trans_eq (add_halves b)
lemma multiply (h: Canopy D A F H)(c:ℝ) : Canopy D A (fun i j=> c • F i j) (fun i j=> c • H i j):= h.repel (fun i=> le_rfl) (fun i=> le_rfl) (by simp)
end Canopy
namespace Angel
lemma forms (h:Angel F H)(hn:κ ↪ ι):Angel (fun i j=> F i (hn j)) (fun i j=> H i (hn j)):=by
    obtain ⟨v,hv,V⟩:=h.a.sup; obtain ⟨w,hw,W⟩:=h.b.sup; exact ⟨⟨_,hv.pull hn,fun n i j=> V ..⟩,⟨_,hw.pull hn,fun n i j=> W ..⟩,fun i=> h.sails _⟩
lemma empty : Angel (fun _:ℕ=> fun _:ι=> fun _:Config G c=> (0:ℝ)) (fun _ _ _=> 0):=by
    have hx:Sparse (fun _:ℕ=>fun _:ι=>(0:ℝ)):=Sparse.constant (by simp) fun _=> le_rfl
    exact ⟨⟨_,hx,fun n v i=>by simp⟩,⟨_,hx,fun n v i=>by simp⟩, fun i b h=> Eventually.of_forall fun n _=>by simpa using h.le⟩
lemma both {F H:ℕ→(ι⊕κ)→ Config G c→ℝ}(h:Angel (fun i j=> F i (.inl j)) (fun i j=> H i (.inl j)))(he:Angel (fun i j=> F i (.inr j)) (fun i j=> H i (.inr j))):Angel F H:=by
    have H {g:ℕ→(ι⊕κ)→ Config G c→ℝ}(h:Vented fun i j=> g i (.inl j))(he:Vented fun i j=>g i (.inr j)):Vented g:=by
       obtain ⟨v,hv,V⟩:= h.sup; obtain ⟨w,hw,W⟩:=he.sup; refine ⟨fun i=> Sum.elim (v i) (w i),Sparse.either hv hw,fun i x j=>?_⟩; cases j <;> first|exact V ..|exact W ..
    exact ⟨H h.a he.a,H h.b he.b,fun i b hb=>by cases i <;> first|exact h.sails _ _ hb|exact he.sails _ _ hb⟩
end Angel
end YM.ConnectedActivityE6.Lim
