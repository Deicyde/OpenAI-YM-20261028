import YM.UVExtension.Rafter.Pebble
import YM.UVExtension.Rafter.Arches
import YM.UVExtension.Concert.Speakers
/-!
 # Complex hitching for a standard rooted regular mark. No scaling with period. W via vacuum REAL lift Γ meter.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Rafter
open Function Filter Lattice Wilson MeasureTheory RG Push Push.AbsoluteSums
open Lamppost Concert Local MergeProof Set
open scoped BigOperators Topology ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{D Z:Type} [NormedAddCommGroup Z][NormedSpace ℂ Z]{n:Side}{p:BudgetPoint}{b w t:ℝ}
    {T:Opening D Z} (A:Activities G n)(V:D→Activities G n)(he:∀ i,(V i).forced=A.forced)
local notation "Y"=> fusionBox A
local notation "l"=> id (α:=Support n)
local notation "C"=> bell A.forced p.B p.supportExponent
set_option quotPrecheck false
noncomputable def boxGoal (G:Gauge)(n:Side)(p:BudgetPoint): Meter.{0} (Box n) Unit:=shelf (Config G n) (fun i:Box n=> Real.exp (p.supportExponent*coverNumber p.B i.1)) (fun _=> Real.exp_pos _)
include he
-- exploit Packs.Meets receipt for each complex z
local notation "Ψ"=> p.threshold
private lemma shake (i) (X : Support n)(q: Box n)(U:Config G n): MergeProof.portion (V i) t X q U = ∑' s : Pack A X, if Y X s.val=q∧q.1 ∩ flags t U=q.2 then ∏ j∈ s.val, ((V i).K j U:ℂ) else 0 := by
   let f(s:Finset ℕ):= grasp (V i) t X s q U
   have hh (s:Finset ℕ):Packs A X s↔Packs (V i) X s:=by
     have hx: Local.patch (V i)= Local.patch A:=by unfold Local.patch; rw [he]
     constructor
     · intro h; refine ⟨h.1,?_,?_⟩; · unfold Separate; rw [hx]; exact h.2
       intro j hj; rw [hx]; exact h.3 _ hj
     intro h; refine ⟨h.1,?_,?_⟩; · unfold Separate; rw [← hx]; exact h.2
     intro j hj; rw [← hx]; exact h.3 _ hj
   have hv:∑' s:Pack A X,f s.val=MergeProof.portion (V i) t X q U:= tsum_subtype_eq_of_support_subset (s:={u|Packs A X u}) (fun s hs=> by by_contra h; exact hs (by unfold f grasp; rw [if_neg (fun g=> h ((hh s).mpr g.1))]))
   rw [← hv]; apply tsum_congr; intro s; unfold f grasp; have ht: Y X s.val=fusionBox (V i) X s.val:= by unfold fusionBox Local.patch flagsFor; simp_rw [he i]
   rw [← ht]; simp only [(hh s.val).1 s.property,true_and] -- subtype
local notation "sF"=> bank (G:=G) p (id (α:=Support n))
variable (g:D→ Response G n) (hv:Stalk (bank (G:=G) p (id (α:=Support n))) T g b) (hp:Stalk (bell A.forced p.B p.supportExponent) T (fun d i x=> ↑((V d).K i x)) w)
variable (ht:0≤w)(hz:0≤b)(hr: Push.Local.hitWidth p*w≤1)
include hv hp ht hz hr
lemma hooksX: Stalk (boxGoal G n p) T (fun d=> hook (V d) t (g d)) b:=by
   obtain ⟨f,hf,hg,hQ⟩:=hv.rises; obtain ⟨u,hu,hA,hF⟩:=hp.rises
   let X: Support n→ Support n:= id
   let J:=Letters A X; let e(s:J):=fusionBox A s.1 s.2.val
   let y(q:Box n) := Real.exp (p.supportExponent*coverNumber p.B q.1); have hy(i):1≤y i:=Real.one_le_exp (mul_nonneg p.exponent_pos.le (by positivity))
   let Tt:= shelf (Config G n) (y ∘ e) (fun i=>zero_lt_one.trans_le (hy (e i)))
   let R(z:Z)(s:J)(U:Config G n):= if (e s).1∩flags t U=(e s).2 then f z s.1 U * ∏ i∈s.2.val,u z i U else 0
   have hh(z)(hz:z∈T.span):Tt.MeasureP (R z) b:=by
       obtain ⟨v,hv,h⟩:= (hQ z hz).afloat; obtain ⟨k,hk,hL⟩:= (hF z hz).afloat; let f'(s:J):=v s.1*∏ i∈s.2.val,k i
       have htJ(i : Support n): 0 ≤ v i:= (hv i).1; have hs(i): 0≤ k i:= (hk i).1; have hh(s): 0≤ f' s:=mul_nonneg (htJ _) (Finset.prod_nonneg fun i _=> hs _)
       have hx i:SumBudget (fun j=> if i ∈ Local.patch A j then p.mass (Local.patch A j) (k j) else 0) w:=by simpa only [bell,BudgetPoint.mass,ite_mul,zero_mul,Local.patch] using! hL i
       let b'(i:Support n):=mergePrice p w i (v i)
       have hG(i):SumBudget (fun q : Pack A i=>Tt.cost () ⟨i,q⟩ * f' ⟨i,q⟩) (b' i):= packBudget i (A:=A) (htJ _) (fun i=> hs i) hx
       have hM : SumBudget b' b:=budget_mono (h ()) (fun i=> mergePrice_nonneg p _ ht (htJ i)) (fun i=> (price_meeting ht hr (htJ i) i).trans (mul_le_of_le_one_left (show 0≤ reservedMass p i (v i) from mul_nonneg (Real.exp_pos _).le (htJ i)) hr))
       refine ⟨f',fun i=>⟨hh _,fun j=>?_⟩,fun _=> Local.sumBudget_sigma hG hM⟩
       unfold R; split; swap; · rw [norm_zero]; exact hh _
       rw [norm_mul,norm_prod]; exact mul_le_mul ((hv i.1).2 j) (Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun _ _=> (hk _).2 _)) (Finset.prod_nonneg fun _ _=> norm_nonneg _) (htJ _)
   have hx: Stalk Tt T (R ∘ T.call) b:=by
       refine ⟨R,fun i j=> ?_,fun _=>rfl,hh⟩; unfold R; split; · intro s g hs hA he; exact DifferentiableOn.mul (hf i.1 j s g hs hA he) (DifferentiableOn.fun_finsetProd (fun k _=> hu k j s g hs hA he))
       exact bumps _ _ (differentiableOn_const _)
   have ht(d U): Summable (fun s:J=> R (T.call d) s U):=by
       obtain ⟨z,h,hF⟩:= (hh _ (T.within d)).afloat; exact (hF ()).2.1.of_norm_bounded (fun i=> ((h i).2 _).trans (le_mul_of_one_le_left (h i|>.1) (hy _)))
   have hm': (fun d q U=>cram e (fun s:J=> R (T.call d) s U) q)= fun d=>hook (V d) t (g d):= by
       funext d q U; rw [expand_eq]; let sE(s:J):=if e s=q then R (T.call d) s U else 0
       have hs':Summable sE:= by convert! (ht d U).indicator (s:={i| e i=q}) using 1; ext1 i; simp [sE,Set.indicator] -- simp
       unfold hook; change ∑' j,sE j= ∑ i:Support n, g d i U*MergeProof.portion (V d) t i q U
       rw [hs'.tsum_sigma,tsum_fintype]; refine Finset.sum_congr rfl (fun i _=>?_)
       rw [shake A V he,← tsum_mul_left]; apply tsum_congr; intro c
       unfold sE R; rw [hg,hA]; change (if _ then (if _ then (_:ℂ) else 0) else 0)= _; split
       next hv=> rw [hv]; simp only [show fusionBox A i c.val=q from hv, true_and]; split<;>simp [*]
       next hv=> rw [if_neg (fun h=>hv h.1),mul_zero]
   have hp:= loop (T:=T) e y hy (R ∘ T.call) hz hx; exact hm' ▸ (show Stalk (boxGoal G n p) T (fun (d:D) (q:Box n) (U:Config G n)=>cram e (fun s:J=>R (T.call d) s U) q) b from hp)
end YM.UVExtension.Rafter
