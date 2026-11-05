import YM.Extra.MULTISOURCE_BOUNDS.Root
import YM.MergeProof.Click
import YM.MergeProof.Tally
import YM.MergeProof.Twigs


set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I J Y : Type*}[DecidableEq V] {B:Census V} {G:Gauge}{n:Side}
open GridApprox.Nil Extra.Trajectories
variable [Fintype J][Fintype V]
variable (K:Box n → Config G n→Poly B)(u : J→Config G n→Poly B) (X:J→Support n)
variable (t:ℝ)(U:Config G n)
-- classical always here. applies all.
def closure := tally (forst X) (crow K u X t)
omit [Fintype V] in
lemma allclosed (hv:∀ i,K i U≠0 → Sure i) (hr:∀ i,u i U≠0→¬ Healthy t (X i) U):
   field (fun i=> closure K u X t i U) (flags t U)=field (fun i=>K i U) (flags t U)*∏ i,(1+u i U):=by
   let f(p : Finset (Box n)×Finset J) := grid (fun i=>K i U) (flags t U) p.1 * ∏ i∈p.2,u i U
   have hz(p): f (Finset.sumEquiv p) = paddle K u t U p:=rfl
   let a:= fun i=> crow K u X t i U; change field (cram (forst X) a) (flags t U)=_
   rw [field_eq _ _ a Summable.of_finite Summable.of_finite,allpoint K u X t U hv hr]; change ∑' p,f (Finset.sumEquiv.toEquiv p)= _; rw [Equiv.tsum_eq,tsum_fintype,Fintype.sum_prod_type]; unfold field; rw [sum_mul,Finset.prod_one_add]; apply sum_congr rfl; intro i _; rw [Finset.mul_sum]; rfl
lemma Bore_prod {s:I→Support n} {F:I→Config G n→ Poly B}{o : V→Site n}(p:Finset I)(h:∀ i∈p,Borne o (s i) (F i) t) : Borne o (p.biUnion s) (fun U=>∏ i∈p,F i U) t:=by
   induction p using Finset.induction with
   | empty => simp only [Finset.prod_empty,Finset.biUnion_empty]; exact ⟨fun _ _ _ _=>rfl,fun _ _=>rfl,fun _=>measurable_const,fun _=> scope_send _ B.quiet 1 (by simp [Census.quiet])⟩
   | insert i p hi ih=>
     simp_rw [Finset.prod_insert hi,Finset.biUnion_insert]; have hx:= h i (mem_insert_self ..); have hv:= ih (fun i hi=> h i (mem_insert_of_mem hi)); let Y V:= ∏ i∈p,F i V
     refine ⟨fun U V hp ht=> congr_arg₂ (·*·) (Work.H03.reads_larger subset_union_left hx.home U V hp ht) (Work.H03.reads_larger subset_union_right hv.home U V hp ht),fun u U=> congr_arg₂ (·*·) (hx.turns u U) (hv.turns u U),fun w=>?_, fun U=>?_ ⟩
     · simp_rw [Poly.part_mul]; refine Finset.measurable_fun_sum _ (fun i _=> Finset.measurable_fun_sum _ fun j _=> ?_); split; exact (hx.me i).mul (hv.me j); exact measurable_const
     exact scope_mul (fun r hr=> hx.scope _ _ (fun h=> hr (h.trans fun j hj=>Finset.mem_union_left _ hj))) (fun r hr=> hv.scope _ _ (fun h=> hr (h.trans fun j hj=>Finset.mem_union_right _ hj)))
-- equality measurable
lemma census_me (p q:Support n): MeasurableSet {U:Config G n| p∩flags t U=q}:=by
   have h : {U:Config G n| p∩flags t U=q} = ⋃ r : {i:Support n // p∩i=q}, {U|flags t U=r.val}:=by
      ext U; rw [Set.mem_iUnion];constructor; intro he; exact ⟨⟨flags _ _,he⟩,rfl⟩; rintro ⟨r,he⟩; exact (congr_arg (p∩·) (show flags t U=r.val from he)).trans r.property
   rw [h]; exact MeasurableSet.iUnion (fun _=>flags_measurable_eq ..)
variable (w:V→ℝ){o:V→Site n}(hv:∀ i, Flow o i (K i) t)(hu:∀ j,Borne o (X j) (u j) t)
include hv hu
lemma threshed (i:Box n): Flow o i (closure K u X t i) t:=by
   refine transitK (forst X) (r:=id) (F:=crow K u X t) (fun i=> ?_) (fun _=>Summable.of_finite) _
   let l:=forst X i; let f U:=∏ j∈i.val,pork K u j U; have h: Borne o l.1 f t:= Bore_prod t i.val (F:=pork K u) (s:=bloom X) (fun j _=> match j with | .inl j=> (hv j).toBorne | .inr j=> hu j)
   change Flow o l (fun U=> if l.1∩flags t U=l.2 then f U else 0) t
   refine ⟨⟨fun U V hV ht=>?_,fun k U=>?_,fun j=>?_,fun U=>?_⟩,fun U hz=>⟨by by_contra hh; exact hz (if_neg hh), moist X i⟩⟩
   · rw [ht,h.home U V hV ht]
   · rw [gauge_flags,h.turns k U]
   · simp_rw [show ∀ U, (if l.1∩flags t U=l.2 then f U else 0).part j= if l.1∩flags t U=l.2 then (f U).part j else 0 from (fun U=>by split_ifs<;>rfl)]; exact Measurable.ite (census_me _ _ _) (h.me j) measurable_const -- edit
   split; exact h.scope _; exact fun _ _=> rfl
omit hv hu
variable {b:ℕ}{d e v P : ℝ}
lemma branch (hp:Towed w Prod.fst K b (d+e) P)(hh:Towed w X u b (d+e) v)(hx: ∀ i,0<w i)(he:0≤ d)(ht:((b+b+1:ℕ):ℝ)^4*(P+v) ≤ e): Towed w Prod.fst (closure K u X t) b d (Real.exp (P+v)-1):=by
   apply towing (forst X) _ _ hx; let s:= bloom X
   obtain ⟨a,ha,hA,h⟩:=hp; obtain ⟨f,hf,hB,hp⟩:=hh
   let g(i : FlowKind J n):= i.elim a f; have hv i : Loci w (pork K u i) (g i):= by cases i; exact h _; exact hp _
   have hG i : 0 ≤ g i:= (hv i|>.fares hx).1
   choose C hC hh h0 using hv
   let e'(i:Period X):= ∏ j∈i.val,g j
   have ht' : Hit s b g (d+e) (P+v) := by
     intro i
     refine Extra.Multi.Budget.certify (fun j=> by split; exact mul_nonneg (hG _) (Real.exp_pos _).le;exact le_rfl) fun p=>?_
     rw [sum_sum_eq_sum_toLeft_add_sum_toRight]; exact add_le_add (Extra.Multi.Budget.cap (hA i) _) (Extra.Multi.Budget.cap (hB i) _)
   have ht(z):=forest_price (f:=g) s b he hG ht' ht ((tsum_nonneg (ht' 0).1|>.trans (ht' 0).2.2)) z
   refine ⟨e',Summable.of_finite,fun i=> ?_, fun i=> ?_⟩
   · refine Extra.Multi.Budget.pull_le (q:=Subtype.val) (p:=fun _=>True) (ht i) (fun i=> by split; exact mul_nonneg (prod_nonneg (fun j _=> hG j)) (Real.exp_pos _).le;exact le_rfl) (fun _ _=> trivial) Subtype.val_injective.injOn (fun j _=> ?_)
     unfold Ac.roots; by_cases h:i∈ (forst X j).1
     · rw [if_pos (show i∈(Prod.fst ∘ forst X) j from h),if_pos ⟨j.property.spark,h⟩]; exact le_of_eq (mul_comm ..)
     rw [if_neg (show i∉(Prod.fst ∘ forst X) j from h),if_neg (fun hh=> h hh.2)]
   obtain ⟨q,hq,he,hw⟩:= all_prices i.val C g (fun x l=>pork K u l x) w hx hC h0 (fun x i=>hh i x); refine ⟨q,hq,fun U p=>?_,he⟩
   unfold crow; dsimp only; split; exact hw U p; simpa using hq p
end YM.MergeProof.Accent
