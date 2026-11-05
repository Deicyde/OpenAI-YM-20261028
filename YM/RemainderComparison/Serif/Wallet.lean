import YM.RemainderComparison.Serif.Price

/-!
# Actual Trek: all configurations reachability across volume
Pass to limit on both sides including every flagged layout. Only absolute convergence claims for entire product and full densities (constants in these claims deliberately may depend on whole data). Numerical estimates are on integrated log & connected force pieces in actual norm.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Serif
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι α : Type}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J:ℕ}(χ:Chi)
open Lyric Mosaic Muse Sleet
variable (Z:Set ι)(l:ι→ℝ) (δ:ℝ)
open Verse Marker
variable {τ:Type} [DecidableEq τ]{Jm:Census τ}

lemma league (v:Motto M l δ H a b u m) : Summable (wages M l) :=by
   obtain ⟨P',hP,X,z,hz⟩:=v.claim; let F:=(fun v i=> if v∈z i then Real.exp (a *coverNumber R.p.B (M i).crest)*Palette.wages M l i else 0)
   let M':= Finset.univ (α:=Support f)
   have hp (i:P'):SumBudget (F i) b:=hz.crown i
   have hh (i): 0≤ Palette.wages M l i:=mul_nonneg (hz.currency i) (Leaf.profit _)
   let b'':Support f→ℝ:=fun s=> Real.exp (a *coverNumber R.p.B s)
   obtain ⟨a,_,hk⟩:= Finset.exists_min_image M' b'' Finset.univ_nonempty
   have hm: 0<b'' a:= Real.exp_pos _
   let Y:= b'' a; apply Summable.of_nonneg_of_le hh (f:= fun i=>Y⁻¹*∑ j:P', F j i)
   · intro i; by_cases ht : 0< Palette.wages M l i
     · obtain ⟨p,h,hp'⟩:=hz.pin i ht
       rw [inv_mul_eq_div]; apply (le_div_iff₀ hm).2
       apply le_trans _ (single_le_sum (f:=fun j:P'=>F j i) (fun p _=>(hp p).1 i) (mem_univ p)); unfold F; rw [if_pos h, mul_comm]; exact mul_le_mul_of_nonneg_right (hk _ (mem_univ _)) ht.le
     rw [le_antisymm (not_lt.mp ht) (hh i)]; exact mul_nonneg (inv_pos.mpr hm).le (sum_nonneg fun p _=> (hp p).1 i)
   exact (summable_sum (fun i _=>(hp i).2.1)).mul_left _

include H
-- uniform per volume.L
lemma brood : ∃ e:ℝ,0≤e∧ ∀ M:Team R,∀ U, ‖M.cicada U‖≤ M.weight * e:=by
   let p:= R.p
   have he:= H.laws.intake.cap
   obtain ⟨b,hb,h⟩:= Activities.K_total he.labels.boundK
   obtain ⟨c',hc⟩:= ((R.exponentEnv he).exp).cost; have hv:0≤c':=(norm_nonneg _).trans (hc 1)
   let f(s:Finset ℕ):=∏ i∈s,b i; have hp i:0 ≤ f i:=prod_nonneg fun i _=>(h i).1
   have hh:Summable f:=summable_finsetProd_of_summable_nonneg (fun i=>(h i).1) hb
   refine ⟨c'*(∑' i,f i), mul_nonneg hv (tsum_nonneg hp),fun M V=>?_⟩
   unfold Team.cicada; rw [norm_mul];
   have hQ : SumBudget (fun k=> ‖M.bun k V‖) (M.weight*∑' i,f i):=by
     let a(k :{k : Finset ℕ| M.gasDue⊆k}):=k.val\ M.gasDue
     -- avoid partial: full filter
     refine budget_of_sum (fun _=> norm_nonneg _) (fun k=> ?_)
     let t:= k.filter fun j=> M.gasDue ⊆ j
     let F(j : Finset ℕ):= j\ M.gasDue
     have hk:(∑ j∈k, ‖M.bun j V‖) = ∑ j∈t, ‖M.bun j V‖:= (sum_subset (filter_subset ..) (fun j hj hp=> by unfold Team.bun Team.bill; split; rw [if_neg (fun he=> hp (mem_filter.mpr ⟨hj,he⟩)),norm_zero]; exact norm_zero)).symm
     rw [hk]; apply le_trans (b:=∑ j∈t,M.weight * f (F j))
     · apply sum_le_sum; intro j hj; unfold Team.bun; split; next=>
          rw [Team.bill,if_pos (mem_filter.mp hj).2,norm_mul,norm_prod]
          exact mul_le_mul (M.earn _) (prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>(h i).2 _)) (prod_nonneg fun i _=> norm_nonneg _) M.profit
       next=> rw [norm_zero]; exact mul_nonneg M.profit (hp _)
     rw [← mul_sum,show ∑ j∈t,f (F j) =∑ j∈t.image F,f j from (sum_image (fun i hi j hj h=> (sdiff_union_of_subset (mem_filter.mp hi|>.2)).symm.trans ((congr_arg (·∪M.gasDue) h).trans (sdiff_union_of_subset (mem_filter.mp hj|>.2))))).symm]
     exact mul_le_mul_of_nonneg_left (hh.sum_le_tsum _ (fun i _=>hp _)) M.profit
   exact (mul_le_mul (hc V) ((norm_tsum_le_tsum_norm hQ.2.1).trans hQ.2.2) (norm_nonneg _) hv).trans_eq (mul_left_comm ..)
variable (z:ι→Poly Jm){η:τ→ℝ}
lemma dominion (hg:Chorus Jm η Z z k)(hh: Summable (wages M l))(hp:∀ i,0≤ l i): Dominated (fun i:Drums M S=> (raw M i).paint Z l z) :=by
   obtain ⟨w,hw,hQ⟩:= brood H
   obtain ⟨f,hf,hH⟩:= Poly.equivalent_norm (R:=Jm) hg.votes
   have hz:=summable_finsetProd_of_summable_nonneg (fun i=> mul_nonneg (hp i) ((M i).profit):∀ i,0≤ Palette.wages M l i) hh
   let F:= fun i:Drums M S=> (∏ j∈i.val,wages M l j)*w*f; refine ⟨F, ((hz.comp_injective Subtype.val_injective).mul_right w|>.mul_right f),fun i V=>?_⟩
   apply (hH _).trans; apply mul_le_mul_of_nonneg_right _ hf
   apply (housing hg (raw M i) l V).trans
   unfold Verse.emit; rw [norm_mul]; let t:=∏ j∈i.val,l j; have hp:0 ≤ t:=prod_nonneg fun i _=> hp i; change ‖t‖*_≤ _; rw [Real.norm_of_nonneg hp]; refine (mul_le_mul_of_nonneg_left (hQ (team M i) V) hp).trans_eq ?_; rw [Palette.worth,← mul_assoc]; unfold Palette.wages; simp_rw [prod_mul_distrib]; rfl
end YM.RemainderComparison.Serif
