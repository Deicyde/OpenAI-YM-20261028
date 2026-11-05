import YM.FullVolume.Poesy.Rosette
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
open Yard Slide Trio
structure Solo (F H:ℕ→ Config G c→ℝ):Prop where
    tribute:∃ v, ∀ n U, ‖F n U‖ ≤ v ∧ ‖H n U‖ ≤ v
    pulse:∀ U:ℕ→ Config G c,Tendsto (fun n=> F n (U n)-H n (U n)) atTop (𝓝 0)
namespace Solo
variable {F H P Q:ℕ→ Config G c→ℝ}{A:Support c}{B:BudgetPoint}{o:Site c}
lemma feeds {F H:ℕ→ Site c→ Config G c→ℝ} (h:∀ i:Site c,Solo (fun n=>F n i) (fun n=>H n i)): Angel F H:=by
    choose C hC using fun i=>(h i).tribute; have hx:=Sparse.constant (hasSum_fintype C).summable (fun i=>(norm_nonneg _).trans (hC i 0 1).1); exact ⟨⟨_,hx,fun n V i=>(hC i n V).1⟩,⟨_,hx,fun n V i=>(hC i n V).2⟩,fun i x hx=> recover (h i|>.pulse) x hx⟩
lemma born (h:Loom B o A F H) : Solo (fun i=> masked B.threshold A (F i)) (fun i=>masked B.threshold A (H i)):=by
    obtain ⟨v,hv⟩:= h.a.sharp; obtain ⟨w,hw⟩:=h.b.sharp; refine ⟨⟨max v w,fun n U=>⟨(CouplingShape.mask_cost (hv n) U).trans (le_max_left ..),(CouplingShape.mask_cost (hw n) U).trans (le_max_right ..)⟩⟩,fun V=>?_⟩
    refine Metric.tendsto_nhds.mpr fun ε he=>?_ ; filter_upwards [h.gaze _ (half_pos he)] with i hi
    by_cases h: Healthy B.threshold A (V i)
    · have h' := hi.2 (V i) h [] (Nat.zero_le _) (by simp); rw [dist_zero_right, RG.masked_eq _ _ _ _ h, RG.masked_eq _ _ _ _ h]; exact lt_of_le_of_lt h' (half_lt_self he)
    rw [masked_ne _ _ _ _ h, masked_ne _ _ _ _ h]; simpa only [sub_zero,dist_self] using he
lemma minus (h: Solo F H)(hp:Solo P Q): Solo (F-P) (H-Q):=by
   obtain ⟨v,hv⟩:=h.tribute; obtain ⟨w,hw⟩:=hp.tribute; refine ⟨⟨v+w,fun n U=>⟨(norm_sub_le ..).trans (add_le_add (hv n U).1 (hw n U).1),(norm_sub_le ..).trans (add_le_add (hv n U).2 (hw n U).2)⟩⟩,fun U=>?_⟩
   refine (sub_zero (0:ℝ) ▸ (h.pulse U).sub (hp.pulse U)).congr' ?_; filter_upwards with p; simp only [Pi.sub_apply]; ring
lemma coins (h: Solo F H)(c:ℝ):Solo (c • F) (c • H):=by
   obtain ⟨v,hv⟩:=h.tribute; refine ⟨⟨‖c‖*v,fun n U=>?_⟩,fun U=>?_⟩
   · simp only [Pi.smul_apply,norm_smul]; exact ⟨mul_le_mul_of_nonneg_left (hv n U).1 (norm_nonneg _),mul_le_mul_of_nonneg_left (hv n U).2 (norm_nonneg _)⟩
   simp_rw [Pi.smul_apply,← smul_sub, smul_eq_mul]; exact mul_zero c ▸ Tendsto.const_mul c (h.pulse U)
lemma still (h: Solo F H)(p:Config G c): Solo (fun i (_:Config G c)=> F i p) (fun i _=> H i p):=by obtain ⟨v,hv⟩:=h.tribute; exact ⟨⟨v,fun i U=>hv _ _⟩,fun U=>h.pulse fun i=>p⟩ -- parentheses
lemma stitch (h:Solo F H)(hp:Solo P Q):Solo (F+P) (H+Q):=by have hh:= h.minus (hp.coins (-1)); simpa only [neg_one_smul,sub_neg_eq_add] using hh
lemma always : Solo (0:ℕ→ Config G c→ℝ) 0:=⟨⟨0,fun _ _=> by simp⟩,fun i=>by simp⟩
lemma total {ι:Type}{F H:ℕ→ι→ Config G c→ℝ}(s:Finset ι)(h:∀ i∈ s, Solo (fun n=>F n i) (fun n=>H n i)): Solo (fun n V=>∑ i∈s,F n i V) (fun n V=>∑ i∈s,H n i V):=by induction s using Finset.induction_on with
    | empty=> simp only [sum_empty]; exact (show Solo (0:ℕ→ Config G c→ℝ) 0 from always)
    | insert i u hi ih=> simp_rw [sum_insert hi]; exact (h i (mem_insert_self ..)).stitch (ih (fun j hj=>h j (mem_insert_of_mem hj)))
lemma stitching (h:Solo F H)(f g:ℕ→Prop)[DecidablePred f][DecidablePred g](he:∀ᶠ i in atTop,f i ↔ g i) : Solo (fun i U=> if f i then F i U else 0) (fun i U=> if g i then H i U else 0):=by
    obtain ⟨v,hv⟩:=h.tribute; have hx:0≤v:=(norm_nonneg _).trans (hv 0 1).1; refine ⟨⟨v,fun n U=>?_⟩,fun U=>?_⟩
    · constructor
      · split; exact (hv ..).1; simpa
      split; exact (hv ..).2; simpa
    refine Metric.tendsto_nhds.mpr fun t ht=>?_ ; filter_upwards [Metric.tendsto_nhds.mp (h.pulse U) _ ht,he] with n hn he
    simp_rw [he]; split; · exact hn
    simpa only [sub_self,dist_self] using ht
end Solo
end YM.ConnectedActivityE6.Lim
