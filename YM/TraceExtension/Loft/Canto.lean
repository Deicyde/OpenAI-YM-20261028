import YM.TraceExtension.Loft.Pond
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Loft
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det
open scoped BigOperators Topology ContDiff ComplexConjugate Classical
variable {W α β γ : Type}[Fintype α][DecidableEq α][Fintype β][DecidableEq β][Fintype γ][DecidableEq γ]{σ A:ℝ}{g:W→Side}{L:Filter W}{G:Gauge}{f:Side}{p:Clip}{k m n:ℕ}{T R:W→ℝ}
structure Note (n:ℕ)(T:W→ℝ)(F:W→ℝ→ℂ): Prop where
    front: T≥0
    keep:∃ C:ℝ, 0 ≤ C ∧ ∀ i, Allows n (F i) 0 (C*T i)
structure CashV (n:ℕ)(T:W→ℝ)(F:W→ℝ→ CompM α β) : Prop where
   front : T≥0
   tag : ∀ i j, Note n T (fun w x=> F w x i j)
variable {F H:W→ℝ→ℂ}
lemma nsum (h:Note m T F)(hp:Note m T H) : Note m T (F+H):=by obtain ⟨C,hC,f⟩:=h.keep; obtain ⟨D,hD,H⟩:=hp.keep; exact ⟨h.front,C+D,by positivity,fun i=> ((f i).add (H i)).mono (by rw[add_mul])⟩
lemma nil_a (T:W→ℝ)(n)(h:T≥0): Note n T 0:=⟨h,0,le_rfl,fun i=> allows_const _ (by change ‖(0:ℂ)‖≤_;simp)⟩
lemma ncost (h:Note m T F)(hp:Note m R H) : Note m (T*R) (fun i t=> F i t*H i t):=by
    obtain ⟨C,hC,f⟩:=h.keep; obtain ⟨D,hD,H⟩:=hp.keep
    let Z:=cabD m; refine ⟨fun i=>mul_nonneg (h.front i) (hp.front i),C*D*cabD m,mul_nonneg (mul_nonneg hC hD) cabD_n,fun i=>?_⟩
    apply (cabin (f i) (H i)).mono; simp only[Pi.mul_apply]; linarith
omit [DecidableEq α] [Fintype α] in
lemma nsumC (s:Finset α){F:α→ W→ℝ→ℂ}(h:T≥0) (he:∀ i∈s,Note n T (F i)) : Note n T (fun w x=>∑ i∈s,F i w x):=by induction s using Finset.induction with
  | empty=> simp_rw[sum_empty]; exact nil_a _ _ h
  | insert a s hp ih=> simp_rw[sum_insert hp]; exact nsum (he a (mem_insert_self ..)) (ih (fun i hi=> he i (mem_insert_of_mem hi)))
lemma ntipE (h:Note n T F)(hp:∀ i, F i=ᶠ[𝓝 0] H i) : Note n T H:=by obtain ⟨C,hC,f⟩:=h.keep; exact ⟨h.front,C,hC,fun i=>(f i).germ (hp i)⟩
lemma nbill {F:W→ℂ}(h:0 ≤ T)(hp:0 ≤ A)(he:∀ i, ‖F i‖ ≤ A*T i): Note n T (fun i _=> F i):= ⟨h,A,hp,fun i=> allows_const _ (he i)⟩
lemma noneN (v:ℂ): Note n (1:W→ℝ) (fun _ _=>v):= nbill (fun _=>zero_le_one) (norm_nonneg v) (fun i=> (mul_one _).ge)
lemma mulM {F: W→ℝ → CompM α β}{H:W→ℝ→ CompM β γ}(h:CashV n T F)(hp:CashV n R H): CashV n (T*R) (fun i t=> F i t * H i t):=by
    have hz:T*R ≥0:=fun i=>mul_nonneg (h.front i) (hp.front i); refine ⟨hz,fun i j=>?_⟩; simp only[mul_apply]; exact nsumC univ hz (fun k _=> ncost (h.tag i k) (hp.tag k j))
lemma negM {F:W→ℝ→ CompM α β}(h:CashV n T F): CashV n T (-F):=by
    refine ⟨h.front,fun i j=>?_⟩; have hv:=ncost (noneN (-1)) (h.tag i j); simpa only[one_mul,neg_one_mul,Pi.neg_apply,Matrix.neg_apply] using hv
lemma sumM {F H: W→ℝ → CompM α β}(h:CashV n T F)(hp:CashV n T H): CashV n T (F+H):=⟨h.front,fun i j=> nsum (h.tag i j) (hp.tag i j)⟩
lemma nilM (h:T≥0): CashV n T (0:W→ℝ → CompM α β):= ⟨h,fun i j=> nil_a _ _ h⟩
lemma nmultC (s:Finset α){F:α→ W→ℝ→ℂ}(he:∀ i∈s,Note n 1 (F i)) : Note n 1 (fun w x=>∏ i∈s,F i w x):=by induction s using Finset.induction with
  | empty=> simp_rw[prod_empty]; exact noneN _
  | insert a s hp ih=> have h:= ncost (he a (mem_insert_self ..)) (ih fun i hi=> he i (mem_insert_of_mem hi)); rw[one_mul] at h; simp_rw[prod_insert hp];exact h
section fund
variable {N: W→ ℝ → CompM α α}
lemma ndec (h:CashV n 1 N): Note n 1 (fun w t=> det (N w t)):=by
    simp_rw[det_apply, Units.smul_def,zsmul_eq_mul]; refine nsumC _ h.front fun i hi=>?_
    have hx:= ncost (noneN (Equiv.Perm.sign i)) (nmultC univ (fun j (_:j ∈univ)=> h.tag (i j) j)); rwa[one_mul] at hx
lemma nanc (h:CashV n 1 N): CashV n 1 (fun w t=> adjugate (N w t)):=by
    refine ⟨h.front,fun i j=>?_⟩; simp_rw[Matrix.adjugate_apply]; apply ndec; refine ⟨h.front,fun k l=>?_⟩; simp only [Matrix.updateRow_apply]; split
    · exact noneN _
    exact h.tag _ _
lemma npow (h:CashV n 1 N)(hp:∀ w,N w 0=1): CashV n 1 (fun w t=> (N w t)⁻¹):=by
    have hx:= ndec h; have hy: Note n (1:W→ℝ) (fun w t=> (N w t).det⁻¹):=by
       let K(z:ℂ):=z⁻¹; have hw:ContDiffAt ℝ ω K 1:= contDiffAt_id.inv one_ne_zero
       let D:= ∑ k∈range (n+1),‖iteratedFDeriv ℝ k K 1‖; have hD:0 ≤ D:=sum_nonneg fun i _=> norm_nonneg _
       obtain ⟨C,hC,H⟩:=hx.keep
       have he:Allows n K 1 D:=⟨hw,fun i hi=> single_le_sum (f:=fun k=>‖iteratedFDeriv ℝ k K 1‖) (fun k _=> norm_nonneg _) (mem_range.mpr (by omega))⟩
       let A:= composeCost n D C
       refine ⟨h.front,max 0 A,le_max_left ..,fun i=>?_⟩
       have ht:= H i; simp only[Pi.one_apply,mul_one] at ht; rw[Pi.one_apply,mul_one]
       exact Allows.mono ((show Allows n K ((N i 0).det) D by rwa [hp i,det_one]).comp (f:=fun x=>det (N i x)) ht) (le_max_right ..)
    refine ⟨h.front,fun i j=>?_⟩; simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply]; have he:=ncost hy ((nanc h).tag i j); rwa [one_mul] at he
lemma slit (h:CashV n T N)(ht:∀ w,0 < T w)(he:∀ w,IsUnit (N w 0).det)(hx:∀ w, vflux ((N w 0)⁻¹)≤ A*(T w)⁻¹)(ha:0 ≤ A) : CashV n T⁻¹ (fun w t=> (N w t)⁻¹):=by
   let K(w:W)(_t:ℝ): CompM α α:= (N w 0)⁻¹; let F(w)(t):=N w t*K w t
   have hv:T⁻¹ ≥0:=fun i=>inv_nonneg.mpr (h.front i); have hu:CashV n T⁻¹ K:=⟨hv,fun i j=> nbill (F:=fun w=>(K w 0) i j) hv ha (fun w=> le_trans (flux_tilt ((N w 0)⁻¹) i j) (hx w))⟩
   have hm:=mulM h hu; rw[show T*T⁻¹=1 from funext fun i=>mul_inv_cancel₀ (ht i).ne'] at hm
   have hf:=mulM hu (npow (N:=F) hm (fun i=> mul_nonsing_inv _ (he i))); rw[mul_one] at hf
   refine ⟨hv,fun i j=> ntipE (hf.tag i j) fun w=>?_⟩
   have hp:Prick (F w):= fun i j=>by obtain ⟨C,hC,H⟩:= (hm.tag i j).keep; exact (H w).analytic.analyticAt
   filter_upwards [hp.det.continuousAt.eventually_ne (show (F w 0).det ≠ 0 from by unfold F K; rw[mul_nonsing_inv _ (he w),det_one]; exact one_ne_zero)] with z hz
   have hh: K w z*(F w z)⁻¹=(N w z)⁻¹:=by rw [← Matrix.inv_eq_right_inv (A:=N w z) (B:= K w z*(F w z)⁻¹)]; rw [← Matrix.mul_assoc]; exact mul_nonsing_inv _ hz.isUnit
   exact congr_arg (fun M:CompM α α=> M i j) hh
end fund
end YM.Trace.Loft
