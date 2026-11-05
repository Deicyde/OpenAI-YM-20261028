import YM.FullVolume.E6.Bandle
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
variable {M: Bank}(I:Depot Q o x μ L C₀ K)(T:Depot Q o x μ L C₀ H){χ: Chi}(R:∀ n,Station M χ (I n) j)(P':∀ n,Station M χ (T n) j)
namespace Draft
include I R
lemma cologne (h:Sweep K) :∃ w:ℕ→ (I 0).Chapter→ℝ,Sparse w∧∀ n i V, ‖(I n).colognePool χ V i‖ ≤ w n i:=by
    obtain ⟨q,hq⟩:= carded I R (coined _ I R h).choose_spec; obtain ⟨v,hv,hV⟩:=divan I R h
    let f n: (I 0).Chapter→ ℝ:= Sum.elim (fun i=>q n i.val) (v n); refine ⟨f,Sparse.either (hq.value.pull (Embedding.subtype _)) hv, ?_⟩
    rintro n (i|i) V
    · exact Draft.flies I i.val (fun _=>V) hq n
    have hf := (R n).N; let g(V):= stream (I n) χ V i
    let T:=perf (I 0) i; change ‖-(I n).trainedPool χ V i‖ ≤ _; rw [norm_neg,show _=RG.masked (Pressure.temp x) T g V from congr_arg (fun (f:Config G c→ℝ)=> f V) (hf.permitAverage i).2.2.2.1]
    -- implicit.
    by_cases hh:Healthy (Pressure.temp x) T V
    · rw [RG.masked_eq _ _ _ _ hh]; exact (hV i n V hh ℝ (fun _=>V) 0 rfl ⟨hf.position.le,fun p=> a_oneB _ _ hf.position.le⟩).bound
    rw [RG.masked_ne _ _ _ _ hh,norm_zero]; exact hv.value ..
lemma tassels (h:Sweep K):∃ f:ℕ→ (I 0).Chainbook→ ℝ, Sparse f∧∀ n V p, ‖(I n).smilesPool χ V p‖ ≤ f n p:=by
   obtain ⟨w,hw,he⟩:= cologne I R h; refine ⟨_,hw.courtyard,fun n V p=>?_⟩; unfold Cash.smilesPool; split
   · unfold Multiple.manyW; rw [norm_prod]; apply prod_le_prod (fun i _=> norm_nonneg _) (fun i _=>?_); rw [norm_div,norm_pow,Real.norm_of_nonneg (by positivity : 0≤((_ :ℕ).factorial:ℝ))]; apply div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) _ _) (by positivity); exact he n i.val V
   rw [norm_zero]; exact hw.courtyard.value ..
variable (h:Sweep K)(he:Sweep H)(hM:Mirror K H)(hJ:(J:Filter ℕ)≤ atTop)
include T P' h he hM hJ
lemma candle [FiniteDimensional ℝ E] (i:(I 0).fragrances) (hf:∀ n,Healthy (Pressure.temp x) (perf (I 0) i) (U n p))(hz:∀ n, Mode (U n) p j M.v): Frill J j p (fun n y=> stream (I n) χ (U n y) i) (fun n y=> stream (T n) χ (U n y) i):=by
    have hh (k:Option (Fin i.fst)):=(levers I T R P' h he hM hJ (i.snd k) (fun n=> disjoint_of_subset_left (Finset.subset_biUnion_of_mem ((I 0).smallAt ∘ i.snd) (mem_univ k)) (hf n)) hz)
    exact ((Frill.still (coefficient (I 0).seam i.snd)).times (Frill.pears Finset.univ fun k _=> hh k)).via (contDiff_id.div_const ((i.fst+1).factorial:ℝ))
lemma spirits (V:ℕ→ Config G c)(r:(I 0).Chainbook) : Glints J (fun n=> (I n).smilesPool χ (V n) r) (fun n=> (T n).smilesPool χ (V n) r):=by
    have hG i:=(Draft.entryA I T R P' i V h he hM hJ); let A n i:= (I n).colognePool χ (V n) (show (I 0).Chapter from i); let f n i:= (T n).colognePool χ (V n) (show (I 0).Chapter from i)
    have hf i : Frill J 0 (0:ℝ) (fun n _=>A n i) (fun n _=> f n i):=by
       rcases i with i|i
       · exact Frill.bare (hG i.val)
       exact ((((Frill.still (coefficient (I 0).seam i.2)).times (Frill.pears Finset.univ fun k _=> Frill.bare (hG (i.snd k).1))).via (contDiff_id.div_const ((i.fst+1).factorial:ℝ))).neg)
    have ht:Frill J 0 (0:ℝ) (fun n _=>manyW (A n) r) (fun n _=>manyW (f n) r):= Frill.pears Finset.univ fun i _=> (hf i.val).via ((contDiff_id.pow _).div_const _)
    have hh := switch ht.crest ⟨(0:ℝ),tendsto_const_nhds,tendsto_const_nhds⟩ (fun n=> (I n).Fresh r ∧ Ac.Spark (I n).bookFoot r.1∧ (I n).statesPool (V n) r)
    have hl {p q:Prop}[a: Decidable p][b: Decidable q] (x y:ℝ) (he:p↔q) : (if p then x else y)=(if q then x else y):=by by_cases hh:q <;> simp [he,hh]
    refine hh.carve (Eventually.of_forall fun n=>?_) (Eventually.of_forall fun n=>?_); all_goals exact @hl _ _ (Classical.propDecidable _) _ _ _ Iff.rfl
end Draft
end YM.ConnectedActivityE6.Lim
