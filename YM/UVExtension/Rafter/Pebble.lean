import YM.UVExtension.Rafter.Hales
import YM.MergeProof.Flavor
/-! # Fibre regrouping; sums not bounded by volume of lattice. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Rafter
open Function Filter Lattice Wilson MeasureTheory RG Push Push.AbsoluteSums
open Lamppost Local MergeProof Metric Topology BoundedContinuousFunction Set
open scoped BigOperators Topology Classical
variable {A B D X Z:Type} [NormedAddCommGroup Z][NormedSpace ℂ Z]
    {T:Opening D Z}{u:ℝ}
lemma washed {S:Set Z}(F:A→ Z→ℂ)(h:∀ i,Bumps S (F i))(hp:∀ z∈ S,SumBudget (fun i=> ‖F i z‖) u)(hu:0≤u): Bumps S (fun z=> ∑' i,F i z):=by
    intro s v hs hv he; let f(p:Finset A) z:= ∑ i∈p,F i (v z)
    have ht(p): DifferentiableOn ℂ (f p) s:= DifferentiableOn.fun_sum (fun i _=> h i s v hs hv he)
    have hh(z)(hz:z∈s)(p): ‖f p z‖≤ u:= (norm_sum_le ..).trans (budget_sum (hp _ (hv hz)) p)
    let g z:= ∑' i,F i (v z)
    have hG z(hz:z∈s): Tendsto (fun p=> f p z) atTop (𝓝 (g z)):= (((hp _ (hv hz)).2.1|>.of_norm).hasSum)
    letI : TopologicalSpace (Finset A):=⊥; letI : DiscreteTopology (Finset A):=discreteTopology_bot _
    let p(z): Finset A →ᵇ ℂ:= if hz:z∈s then ofNormedAddCommGroupDiscrete (fun i=> f i z) u (hh z hz) else 0
    have hF z(hz:z∈s) i:p z i=f i z:=by unfold p; rw [dif_pos hz]; rfl
    have hc: Bumps s p := canal (M:=u) (fun i=> bumps _ _ ((ht i).congr (fun z hz=> hF z hz i))) (fun z hz i=> by rw [hF z hz]; exact hh z hz i) hu
    have hP : ContinuousOn p s:= (hc s id hs (mapsTo_id _) differentiableOn_id).continuousOn -- mapsTo_id _
    suffices H:TendstoLocallyUniformlyOn f g atTop s from H.differentiableOn (Eventually.of_forall ht) hs
    refine Metric.tendstoLocallyUniformlyOn_iff.mpr (fun ε he z hz=>?_)
    have he' : 0< ε/4:= by positivity
    let U:= s∩ p ⁻¹' ball (p z) (ε/4)
    refine ⟨U, Filter.inter_mem self_mem_nhdsWithin ((hP z hz).preimage_mem_nhdsWithin (ball_mem_nhds _ he')),?_⟩
    filter_upwards [hG z hz|>.eventually (ball_mem_nhds _ he')] with i hi x hx
    have hv : x∈s:=hx.1
    have hm j: dist (f j x) (f j z) ≤ ε/4:=by
       rw [← hF x hv,← hF z hz,dist_eq_norm]; refine le_trans ((p x-p z).norm_coe_le_norm j) ?_; exact (dist_eq_norm (p x) (p z)) ▸ (mem_ball.mp (hx.2)|>.le)
    have hy' : dist (g x) (g z)≤ε/4:= le_of_tendsto ((hG x hv).dist (hG z hz)) (Eventually.of_forall hm)
    apply lt_of_le_of_lt (dist_triangle _ (g z) _) ; rw [add_comm];
    linarith only [he, mem_ball.mp hi,hm i,hy',dist_comm (g z) (f i z),dist_comm (f i z) (f i x), dist_triangle (g z) (f i z) (f i x)]

noncomputable def shelf (X:Type) (y:A→ℝ)(h:∀ i:A,0 < y i) : Meter.{0} A Unit:=⟨fun _=> X,fun _ i=> y i,fun _ i=>(h i).le,fun i=>⟨(),h _⟩⟩
lemma loop (q:A→B)(y:B→ℝ)(h:∀ b,1 ≤ y b)(F:D → A → X → ℂ)(ha:0≤u): let H:= shelf X y (fun i=>zero_lt_one.trans_le (h i)); let J:= shelf X (y ∘ q) (fun i=>zero_lt_one.trans_le (h (q i))); Stalk J T F u → Stalk H T (fun d i z=> cram q (fun a=> F d a z) i) u:=by
    rintro H J ⟨f,hf,hp,ht⟩; let g(z:Z)(i:B)(x:X):= cram q (fun i=>f z i x) i
    have hs z(hz:z∈T.span)(d:X) : SumBudget (fun i=> ‖f z i d‖) u:=by
       obtain ⟨b,hb,hT⟩:= (ht z hz).afloat; exact budget_mono (hT ()) (fun _=> norm_nonneg _) fun i=> ((hb i).2 d).trans (le_mul_of_one_le_left (hb i|>.1) (h (q i)))
    refine ⟨g,fun b x=> ?_,fun d=>by unfold g; rw [hp]; rfl,fun z hz=>?_⟩
    · apply washed (A:={a// q a=b}) _ (fun a=> hf a.val x) _ ha; intro z hz; exact Local.sumBudget_subtype (fun a=> q a=b) (hs z hz x)
    obtain ⟨b,hb,hT⟩:= (ht z hz).afloat; have hF := hT (); let c i:=J.cost () i*b i; have hv(i): 0 ≤ b i:= hb i|>.1; have hB : Summable b:= hF.2.1.of_nonneg_of_le hv (fun i=> le_mul_of_one_le_left (hv i) (h _))
    have hG i:y i*cram q b i = cram q c i:=by unfold cram; rw [← tsum_mul_left]; exact tsum_congr (fun a=>congr_arg (·*b a.val) (congr_arg y a.2.symm))
    have hr:= heavy q (f:=c) hF.2.1
    refine ⟨cram q b,fun i=>⟨tsum_nonneg (fun j=> hv j.val),fun k=>metric_cram _ hB (fun i=> (hb i).2 _) i⟩,fun _=>?_⟩
    change SumBudget (fun i=> y i * _) _; simp_rw [hG]; exact ⟨fun i=> tsum_nonneg (fun j=>hF.1 _),hr.summable,hr.tsum_eq.trans_le hF.2.2⟩
end YM.UVExtension.Rafter
