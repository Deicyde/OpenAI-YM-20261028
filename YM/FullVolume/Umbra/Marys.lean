import YM.FullVolume.E6.Bandle
/-! Soft polynomial estimates on any fixed volume with margin <1 for repeats. -/
-- one real mark among any two epoch carpets at the same stamp
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
namespace Umbra
variable {ι:Type}{α γ σ r q:ℝ}{Z:ι→Support c} {R:ι→ι→Prop}{B n:ℕ}
lemma raises (A:ℕ→ι→ℝ)(h:∀ i,Ready Z B (A i) α γ σ (1/2))(V:ℕ→ι→ℝ)(hp: Sparse V): ∃ δ u:ℝ,0<δ ∧ ∀ n, Ready Z B (fun i=> A n i+δ*V n i) α u σ (3/4):=by
    have hg := (h 0).1; obtain ⟨p,H⟩:= hp.bound; have ht:0 ≤ p:=budget_nonneg (H 0); obtain ⟨f,hf⟩:= (Set.finite_range (Trees.currency B (n:=c) (α+σ))).bddAbove
    let a:= |f|; have ha:0 ≤ a:=abs_nonneg _; let δ:= γ/(2*(1+a*p)); have hδ:0<δ:=by unfold δ; positivity
    refine ⟨δ,3/2*γ,hδ,fun i=>?_⟩; have hx(x):= hp.value i x; have he:= (h i).2.2.2.2.1
    refine ⟨by positivity,(h i).2.1,(le_of_eq (show degreePrice B (3/2*γ) σ=3/2* degreePrice B γ σ from by unfold degreePrice Trees.stretch;ring)).trans ((mul_le_mul_of_nonneg_left ((h i).2.2.1) (by norm_num : (0:ℝ)≤3/2)).trans_eq (by ring)),by norm_num,fun p=>add_nonneg (he p) (mul_nonneg hδ.le (hx _)),fun x=>?_⟩
    let u(s:ι):= if x∈Z s then A i s * currency B (α+σ) (Z s) else 0
    let v(s:ι):= if x∈Z s then δ * V i s * currency B (α+σ) (Z s) else 0
    rw [show (fun s=> if x∈Z s then (A i s+δ*V i s)*Real.exp ((α+σ)* coverNumber B (Z s)) else 0) = u+v from funext fun i=> by unfold u v Trees.currency; simp only [Pi.add_apply]; split <;> ring]; have hz : SumBudget u γ:= (h i).2.2.2.2.2 x
    have hV : SumBudget v (γ/2):=by
       have hh : δ*a*p≤ γ/2:=by rw [mul_assoc,show γ/2=δ*(1+a*p) by unfold δ; field_simp]; exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hδ.le
       apply budget_loosen (budget_mono (budget_scale (mul_nonneg hδ.le ha) (H i)) (fun i=>?_ ) (fun z=>?_ )) hh
       · unfold v; split; exact mul_nonneg (mul_nonneg hδ.le (hx _)) (Real.exp_pos _).le; rfl
       unfold v; split; · exact (mul_le_mul_of_nonneg_left ((hf (Set.mem_range_self (Z z))).trans (le_abs_self f)) (mul_nonneg hδ.le (hx z))).trans_eq (by ring)
       exact mul_nonneg (mul_nonneg hδ.le ha) (hx z)
    exact budget_loosen (Push.Local.sumBudget_add hz hV) (by linarith)
lemma profuse (A:ℕ→ι→ℝ)(h:∀ i,Ready Z B (A i) α γ σ q)(ht: Tests R Z)(he: Sparse A)(ha:0≤α)(hZ:∀ p:Clusters ι,(unionOf Z p.snd).Nonempty) : Sparse (fun n (p:Clusters ι)=> clusters R (A n) p.snd):=by -- bind notation edit n
    let v(i:ℕ):=γ*q^i*(1-q)⁻¹; have hf:Tendsto v atTop (𝓝 0):=by have hb:=h 0; simpa only [v,mul_zero,zero_mul] using (((tendsto_pow_atTop_nhds_zero_of_lt_one (ready_pos Z B hb).le hb.2.2.2.1).const_mul γ).mul_const (1-q)⁻¹)
    let F n (z:Clusters ι):= clusters R (A n) z.2
    let t z i:= if i≤(z:Clusters ι).fst then z.fst else 0
    have ht₀ k n:SumBudget (fun z:Clusters ι=> if k≤ z.fst then F n z else 0) (∑ i:Site c,v k):=by
       let f(x:Site c)(z:Clusters ι):= if k ≤ z.fst ∧ x∈unionOf Z z.snd then F n z*currency B α (unionOf Z z.snd) else 0
       have hz (x:Site c): SumBudget (f x) (v k):= log_hit_tail R _ _ ht (h n) ha k _; have he p:0≤F n p:=clusters_nonneg _ (he.value n) _
       refine budget_mono (budget_over Finset.univ f _ (fun i _=>hz i)) (fun i=>?_ ) fun z=>?_ ; · split; exact he _; rfl
       split; next hb=>
         obtain ⟨i,hi⟩:= hZ z; have hc: 1≤currency B α (unionOf Z z.snd):= Real.one_le_exp (mul_nonneg ha (Nat.cast_nonneg _)); apply (le_mul_of_one_le_right (he z) hc).trans; rw [← show f i z= _ from if_pos ⟨hb,hi⟩]; exact single_le_sum (fun x _=> show 0≤f x z from (hz x).1 z) (mem_univ i)
       next hb=> exact sum_nonneg fun i _=> (hz i).1 z
    have hh k: Sparse fun n (p:Option (Fin k)→ι)=> F n ⟨k,p⟩ :=by
       let ν(a:Graph.Network (Option (Fin k))):= |Graph.mass a|/(k+1).factorial; obtain ⟨b,hb⟩:=(Set.finite_range ν).bddAbove
       have X(p:Option (Fin k)→ι): |Graph.mass (Ursell.pot R p)| / (k+1).factorial ≤ |b|:= le_trans (hb (Set.mem_range_self (f:=ν) (Ursell.pot R p))) (le_abs_self _)
       refine ((he.square (α:=Option (Fin k))).climb (abs_nonneg b)).smaller (fun i p=>clusters_nonneg _ (he.value i) p) fun i p=>?_ ; exact le_trans (le_of_eq (show F i ⟨k,p⟩ = (|Graph.mass (Ursell.pot R p)| / (k+1).factorial)*(∏ j,A i (p j)) from (by unfold F clusters Ursell.coefficient;ring))) (mul_le_mul_of_nonneg_right (X p) (prod_nonneg fun j _=> he.value ..))
    apply Sparse.layer (d:=Sigma.fst) (f:=F) (v:=fun k=>∑ i:Site c,v k) _ ht₀
    · simpa only [sum_const_zero] using tendsto_finsetSum (f:=fun x:Site c=> v) univ fun i _=> hf
    intro k; simpa only [Finset.mem_range] using (Sparse.braid hh (Finset.range k)) -- order
lemma one_mark [DecidableEq ι] (X:Finset ι) (u v:ι→ℝ)(h:∀ i,0 ≤ u i)(hs:∀ i,0≤v i): (∑ i∈X,(∏ j∈X.erase i,u j)*v i)+(∏ i∈X,u i)≤ ∏ i∈X,(u i+v i):=by
   let ψ (x:Finset ι):=∑ i∈ x,(∏ j∈x.erase i,u j)*v i
   induction X using Finset.induction_on with
   | empty=>simp
   | insert i X hx ih=>
     rw [sum_insert hx,prod_insert hx,prod_insert hx];simp only [erase_insert hx]
     have hp k (hk:k∈X): (insert i X).erase k= insert i (X.erase k):= erase_insert_of_ne (fun e : i=k=> hx (e ▸ hk)) -- signature
     rw [show ∑ k∈X,(∏ j∈(insert i X).erase k,u j)*v k = u i*ψ X from ?_]; swap; · unfold ψ; rw [Finset.mul_sum]; apply sum_congr rfl; intro k hk; rw [hp k hk,prod_insert (fun h=> hx (mem_of_mem_erase h)),mul_assoc]
     let p:= ∏ i∈X,u i; let r:= ∏ i∈X,(u i+v i); have hr : p ≤ r:=prod_le_prod (fun i _=>h i) fun i _=> le_add_of_nonneg_right (hs i); change p*_+_+_*p ≤ _*r; change ψ X+p≤r at ih; nlinarith only [mul_le_mul_of_nonneg_left ih (h i), mul_le_mul_of_nonneg_left hr (hs i)]
end Umbra
end YM.ConnectedActivityE6.Lim
