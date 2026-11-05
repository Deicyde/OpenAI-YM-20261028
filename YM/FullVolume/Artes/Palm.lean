import YM.FullVolume.Artes.Cruise
/-! Diag lemma.Any invocation then all finer.Stores. -/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary.Artes
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Supply
open Shade Beacon Flagship ConeRay Tralis WilsonStartup WilsonStartup.Change WilsonStartup.Change.Reading Next.Free Next.Free.Retort
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical InnerProductSpace
variable {G: Gauge}{a:Levels G} {s: Sheet G}{L: Rolls s}{Q:PostCost L}{O:ChartRatio G}{i:ℕ}
variable {F H: Tale a i}{J : Horizon a}{V:ℕ→ Reel G}{X:MapPrices}{N:ℕ→ℕ}
lemma driven {ι:Type}{b:ℝ}{F:ℕ→ Lights ι}{v:Lights ι} (h:Tendsto N atTop atTop)(he:Gleam F v b): Gleam (F ∘ N) v b:=⟨h.eventually he.budget,fun i=>(he.hinge i).comp h⟩
lemma drivenF {f:ℕ→Flagship G}{F:Flagship G}{a b}(h:Tendsto N atTop atTop)(he:Flagship.Beacon f F a b):Flagship.Beacon (f∘ N) F a b:=⟨driven h he.a,driven h he.b,driven h he.c⟩
private lemma huge {ι:Type}{f:ℕ→ι→ℝ} (h:∀ i,∃ A:ℝ,∀ᶠ j in atTop, |f j i|≤ A): ∃ T:Set (ι→ℝ), IsCompact T ∧ ∀ n,f n∈T:=by
    choose H he using h; have hp i: ∃ C:ℝ, ∀ n, |f n i| ≤C:=by
         obtain ⟨k,hk⟩:=eventually_atTop.mp (he i); refine ⟨max (H i) (∑ j∈ Finset.range k, |f j i|),fun n=>?_⟩; by_cases hi : n<k
         · exact le_trans (Finset.single_le_sum (f:=fun j=>|f j i|) (fun i _=> abs_nonneg _) (Finset.mem_range.mpr hi)) (le_max_right ..)
         exact (hk n (by omega)).trans (le_max_left ..)
    choose h hp using hp; exact ⟨_, isCompact_univ_pi (fun i=>show IsCompact (Set.Icc (-h i) (h i)) from isCompact_Icc),fun n i _=> abs_le.mp (hp i n)⟩
lemma prices {ι κ: Type}[Countable ι][Countable κ] (f:ℕ→ι→ Lights κ)(p:ι→ℝ)(h:∀ i,∀ᶠ n in atTop, ‖f n i‖ ≤ p i): ∃ (w:ι→Lights κ)(g:ℕ→ℕ),StrictMono g ∧ ∀ i,Gleam (fun n=> f (g n) i) (w i) (p i):=by
    let U(n:ℕ)(x:ι×κ):ℝ:= f n x.1 x.2
    have he x: ∀ᶠ n in atTop,|U n x|≤ p x.1 := (h x.1).mono fun n ht=> (lp.norm_apply_le_norm (by norm_num) _ _).trans ht
    obtain ⟨S,hS,hV⟩:=huge (f:=U) fun i=>⟨_,he i⟩; obtain ⟨T,hT,g,hg,H⟩:= hS.tendsto_subseq hV
    choose w hw hp H' using fun i=> promos (f:=fun n=> f (g n) i) (hg.tendsto_atTop.eventually (h i)) fun j=> tendsto_pi_nhds.mp H (i,j)
    exact ⟨w,g,hg,H'⟩
lemma shoots {ι:Type}[Countable ι]{f:ℕ→ι→Flagship G}{a b:ι→ℝ}(h:∀ i,∀ᶠ n in atTop, let x:=f n i; ‖x.a‖ ≤ a i∧ ‖x.b‖≤ b i∧ ‖x.c‖≤ b i): ∃ (x:ι→Flagship G)(w:ℕ→ℕ), StrictMono w∧ ∀ i,Flagship.Beacon (fun n=> f (w n) i) (x i) (b i) (a i):=by
   obtain ⟨A,g,hg,hA⟩:= prices (fun n i=> f n i|>.a) a (fun i=>(h i).mono fun n hi=> hi.1)
   obtain ⟨B,u,hu,hB⟩:= prices (fun n i=> f (g n) i|>.b) b (fun i=> hg.tendsto_atTop.eventually ((h i).mono fun n hi=> hi.2.1))
   obtain ⟨C,v,hv,hC⟩:= prices (fun n i=> f (g (u n)) i |>.c) b fun i=>(hg.comp hu).tendsto_atTop.eventually ((h i).mono fun n hi=> hi.2.2)
   refine ⟨fun i=> ⟨A i,B i,C i⟩, (g ∘ u) ∘ v,(hg.comp hu).comp hv, fun i=> ⟨driven (hu.comp hv).tendsto_atTop (hA i),driven hv.tendsto_atTop (hB i), hC i⟩⟩
lemma rockets {ι:Type}[Countable ι]{f:ℕ→ι→ℝ}(h:∀ i, ∃ B:ℝ,∀ᶠ n in atTop,|f n i|≤ B): ∃ (T:ι→ℝ)(w:ℕ→ℕ), StrictMono w ∧ ∀ i,Tendsto (fun n:ℕ=> f (w n) i) atTop (𝓝 (T i)) :=by obtain ⟨T,hT,H⟩:=huge h; obtain ⟨T,hT,w,hw,H⟩:= hT.tendsto_subseq H; exact ⟨T,w,hw,tendsto_pi_nhds.mp H⟩
namespace Alive
lemma radiant {f:ℕ→ Tale a i}(h:∀ᶠ k in atTop,Alive Q O J V (f k) (N k)):
     ∃ (C:ℝ), ∀ᶠ k in atTop,|(f k).α|≤ C:=by
    refine ⟨ (a.params (i+1)).drift + |G.slopeConstant*Real.log (a.S.block i).val|, h.mono fun i hi=>driving_abs _ _ _ hi.paid.earns⟩
lemma cards {f:ℕ→Tale a i} (h:∀ᶠ k in atTop,Alive Q O J V (f k) (N k)):
    ∀ᶠ k in atTop,‖(f k).sold.a‖≤ a.clock.loopCap i∧ ‖(f k).sold.b‖≤ (a.params i).paths∧ ‖(f k).sold.c‖≤ (a.params i).paths:=h.mono fun i hi=> let Q:= hi.stories.shape; ⟨Q.2.1,Q.2.2.2.1,Q.2.2.2.2.2⟩
lemma talison {f:ℕ→Tale a i} (h:∀ᶠ k in atTop,Alive Q O J V (f k) (N k)):∃ (X:Flagship G) (g:ℕ→ℕ) (b:ℝ),StrictMono g∧ Tendsto (fun k=> (f (g k)).α) atTop (𝓝 b) ∧ Flagship.Beacon (fun k=> (f (g k)).sold) X (a.params i).paths (a.clock.loopCap i):=by
     obtain ⟨X,u,hu,hX⟩:= rockets (f:= fun i (_:Unit)=> (f i).α) (fun _=>radiant h); obtain ⟨A,g,hg,hA⟩:=shoots (f:=fun i (_:Unit)=> (f (u i)).sold) (fun _=> hu.tendsto_atTop.eventually (cards h)); exact ⟨_, u∘ g,X (),hu.comp hg,(hX ()).comp hg.tendsto_atTop,hA ()⟩
end Alive
end YM.Stationary.Artes
