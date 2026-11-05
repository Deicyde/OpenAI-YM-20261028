import YM.FullVolume.E6.Triumph
import YM.FullVolume.E6.Dials
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
open Stained
variable {M:Bank}(I:Depot Q o x μ L C₀ K)(T:Depot Q o x μ L C₀ H){χ:Chi}(R:∀ n,Station M χ (I n) j)(P':∀ n,Station M χ (T n) j)
include I R
namespace Draft
local notation "b"=> radiusB x
-- shader.Word. global hit tail
lemma air : ∃ F:ℕ→ℝ,Tendsto F atTop (𝓝 0) ∧ ∀ s n, SumBudget (fun p:(I 0).fragrances=> if s≤p.fst then (R n).N.design p else 0) (F s):=by
    let v i := March.collars G M.V x j 0*(March.salary Q L μ M.B x j M.k*(1/2:ℝ)^i*(1-1/2)⁻¹);
    have hv:Tendsto v atTop (𝓝 0):=by
          have hh:= tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤ (1/2:ℝ)) (by norm_num : (1/2:ℝ)<1); unfold v; simpa only [mul_zero,zero_mul] using (((hh.const_mul (March.salary Q L μ M.B x j M.k)).mul_const ((1-1/2:ℝ)⁻¹)).const_mul (collars G M.V x j 0))
    refine ⟨fun i=>∑ _j:Site c,v i,?_,fun s n=>?_⟩; · simpa only [sum_const_zero] using (tendsto_finsetSum (f:=fun (_:Site c) =>v) Finset.univ fun _ _=>hv)
    let F(p:(I 0).fragrances):= if s ≤ p.fst then (R n).N.design p else 0
    let g x (p:(I 0).fragrances):= if x∈ perf (I 0) p then F p else 0
    have hg(x':Site c): SumBudget (g x') (v s):=by
          have hh:=(R n).army.applies (R n|>.N) 0 s x'; simp only [Captain.markΦ, zero_mul,pow_zero,one_mul,Real.exp_zero,mul_one] at hh
          exact hh
    refine budget_mono (budget_over Finset.univ (fun x'=>g x') (fun _=> v s) (fun i _=>hg i)) (fun i=>?_) (fun z=>?_)
    · split
      · exact (R n).N.pvc i --fix
      rfl
    obtain ⟨i,hi⟩:= Song.crest (I 0) z; apply le_trans (Eq.ge (show g i z=F z from if_pos hi)); exact single_le_sum (f:=fun i=> g i z) (fun x _=> (hg x).1 z) (mem_univ i)
-- product bound redoing cap on Ore
lemma divan (h:Sweep K):∃ f:ℕ→ (I 0).fragrances→ℝ,Sparse f ∧ ∀ p n V,Healthy (Pressure.temp x) (perf (I 0) p) V→ Ore V (fun U=> stream (I n) χ U p) M.v (f n p) j:=by
    obtain ⟨q,hq⟩:= carded I R (coined _ _ R h).choose_spec; let f n (i:(I 0).ThinP):= q n i.val
    let w (p:(I 0).fragrances) n:= ∏ i:Option (Fin p.fst), f n ((show (I 0).fragrances from p).snd i)
    let p(z:(I 0).fragrances):= coefficient (I 0|>.seam) z.snd/(z.fst+1).factorial; let g n (z:(I 0).fragrances):= |p z| *(w z n*(1+((z.fst+1:ℕ):ℝ))^j)
    have he n z:0≤g n z:=by unfold g; refine mul_nonneg (abs_nonneg _) (mul_nonneg (Finset.prod_nonneg (f:=fun i=>f n (z.2 i)) (fun i _=>hq.value.value ..)) ?_); positivity
    have hs n (z:(I 0).fragrances) V (hf: Healthy (Pressure.temp x) (perf (I 0) z) V):Ore V (fun U=>stream (I n) χ U z) M.v (g n z) j:=by
        intro E _ _ _ U x ht hv
        let f' i y:= March.leaflet (I n) χ (U y) (z.2 i); have hh i:Brush j (f n (z.2 i)) 1 (f' i) x:= opine I R hq n (z.2 i) (Finset.disjoint_of_subset_left (Finset.subset_biUnion_of_mem ((I 0).smallAt ∘ z.snd) (mem_univ i)) hf) E U x ht hv
        have h':= (Brush.all_prod Finset.univ f' (fun i=> f n (z.2 i)) (fun _=>1) (fun i _=> hh i)).trim.smul (p z); simp only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_option,Fintype.card_fin,mul_one] at h'
        apply h'.shimmy; filter_upwards with t; unfold stream Gas.term; change coefficient (I 0|>.seam) z.2*_/_=p z*(∏ i,f' i t); unfold p f'; ring
    let V n (p:(I 0).fragrances) := min (g n p) (R n|>.N.design p); have hV n p:0≤ V n p := le_min (he ..) ((R n).N.pvc p)
    have hS (k:ℕ): Sparse (fun n (p:Option (Fin k)→(I 0).ThinP)=> V n ⟨k,p⟩):=by
        have hr : Sparse f:= hq.value.pull (Embedding.subtype _); let v:=Sparse.square (α:=Option (Fin k)) hr
        let ν(F:Graph.Network (Option (Fin k))):= |Graph.mass F/(k+1).factorial|
        obtain ⟨x',hx⟩:= (Set.finite_range ν).bddAbove
        refine (v.climb (show 0≤ |x'| *(1+((k+1:ℕ):ℝ))^j by positivity)).smaller (fun n p=>hV ..) fun i p=>?_; apply le_trans (min_le_left ..); unfold g
        let y: (I 0).fragrances:= ⟨k,p⟩
        apply le_trans (mul_le_mul_of_nonneg_right ((hx (Set.mem_range_self (f:=ν) (Push.AbsoluteSums.Ursell.pot (I 0).seam p))).trans (le_abs_self _)) ?_)
        · dsimp only [ν]; apply le_of_eq; unfold w; ring
        exact mul_nonneg (prod_nonneg fun k _=> hr.value ..) (by positivity)
    obtain ⟨F,hF,H⟩:=air I R; refine ⟨V,Sparse.layer (d:=fun p : Sigma _=> p.fst) ?_ ?_ hF, fun p n u hx=>?_⟩
    · intro i; simpa only [Finset.mem_range] using (Sparse.braid hS (Finset.range i)) -- implicit f
    · intro z n; refine budget_mono (H z n) (fun i=> by split; exact hV ..; rfl) fun i=> ?_; split; · exact min_le_right ..
      rfl
    obtain hh|hh:= le_total (g n p) ((R n).N.design p)
    · rw [show V n p= g n p from min_eq_left hh]; exact hs n p u hx
    rw [show V n p=(R n).N.design p from min_eq_right hh]; exact ((R n).N.permitAverage p).2.2.2.2 u hx
end Draft
end YM.ConnectedActivityE6.Lim
