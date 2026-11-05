import YM.TraceExtension.Loft.Ice
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Loft
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det
open scoped BigOperators Topology ContDiff ComplexConjugate Classical
variable {ι W :Type} [Fintype ι]{σ A:ℝ}{g:W→Side}{L:Filter W}{G:Gauge}{f:Side}{p:Clip}{k m n:ℕ} {X Y : Type} [NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y]
abbrev Wsc(x:Side):ℝ:= (cents x)⁻¹
lemma fund_cast (x:Side):(↑(Wsc x):ℂ)=(Fintype.card (Site x):ℂ)⁻¹:=by simp[Wsc,cents]
variable {V: W→ TubeF G k}{F H:∀ w,WildM G (g w) k k}
section slice
lemma shunt_a {K:X×Y→ℂ}(p:X)(y:Y)(h:Allows k K (p,y) A): Allows k (fun z=>K (p,z)) y A:=by
    let L:Y→L[ℝ] (X × Y):= (0:Y→L[ℝ] X).prod (ContinuousLinearMap.id ℝ Y)
    let F':= fun z:X×Y=>K ((p,0)+z)
    have hx: (p,(0:Y))+L y=(p,y):=by simp[L]
    have he:Allows k F' (L y) A := by
        rw[← hx] at h; refine ⟨h.analytic.comp (f:=fun z=> (p,0)+z) _ (by fun_prop),fun i hi=>?_⟩; unfold F'; rw[iteratedFDeriv_comp_add_left]; exact h.norm_le i hi
    have hp:=pullAll (L:=L) he (show ‖L‖≤1 from L.opNorm_le_bound zero_le_one fun y=>by simp[L,Prod.norm_def]) le_rfl; rw [one_pow,mul_one] at hp; rw [show F' ∘ L=(fun z=> K (p,z)) from funext fun i=>by simp[L,F']] at hp; exact hp
lemma fern_h (h:Oil L F)(hp:∀ w,Skew (V w) σ A)(he:0 < σ)(a:Fslot G): Honor (fun w (x:TreeF)=> fern (V w) (F w) a x.1 x.2) n:= Honor.some (fun i (_:i∈univ)=> Honor.some (fun j (_:j∈univ)=> honor_sq h hp he i j a))
lemma pond_b (h:Oil L F)(hp:∀ w,Skew (V w) σ A)(he:0 < σ)(a:Fslot G): Honor (fun w=> Pond (F w) a (V w)) n:=by
    obtain ⟨C,hC,H⟩:= (fern_h (n:=n) h hp he a).top; refine ⟨C,hC,fun w x=> ?_⟩
    let N:= Wsc (g w); have hN:0 < N:= inv_pos.mpr cents_pos
    let K(i:Site (g w)):= fern (V w) (F w) a (sip i)
    have hp:= (allows_sum (s:=univ) (f:=K) (fun i _=> shunt_a (sip i) x (H w (sip i,x)))).smul N; rw [Finset.sum_const,card_univ,nsmul_eq_mul,abs_of_nonneg hN.le, inv_mul_cancel_left₀ (show (Fintype.card (Site (g w)):ℝ)≠0 from cents_pos.ne')] at hp
    rw[show Pond (F w) a (V w)=(fun p=>N • ∑ i,K i p) from funext fun p=>by rw[Complex.real_smul,fund_cast]];exact hp
lemma neap_sumE {s:Finset ι}{F:ι→ X→ℂ}{x:X}(p:X)(h: ∀ i∈s,ContDiffAt ℝ ω (F i) x): neap k (fun z=>∑ i∈s,F i z) x p = ∑ i∈s, neap k (F i) x p:=by
    unfold neap; rw [iteratedFDeriv_fun_sum_apply (fun _ h'=> (h _ h').of_le le_top), ContinuousMultilinearMap.sum_apply, Finset.smul_sum]
lemma pond_j (h:Oil L F)(hp:∀ w,Skew (V w) σ A)(he:0 < σ)(a:Fslot G)(w:W)(x:Land):
    neap n (Pond (F w) a (V w)) 0 x = Wsc (g w) • ∑ i:Site (g w),neap n (fern (V w) (F w) a (sip i)) 0 x:=by
    obtain ⟨C,hC,H⟩:=(fern_h (n:=n) h hp he a).top
    let K(i:Site (g w)):= fern (V w) (F w) a (sip i); let U(p:Land):=∑ i,K i p; let N:=Wsc (g w); have hx(i):ContDiffAt ℝ ω (K i) 0:= (shunt_a (sip i) 0 (H w (sip i,0))).analytic; have hh: ContDiffAt ℝ ω U 0:=ContDiffAt.sum (fun _ _=>hx _)
    have hp': Pond (F w) a (V w)= N • U:=funext fun p=>by simp only[Pi.smul_apply,Complex.real_smul];rw [show (N:ℂ)=_ from fund_cast _]
    rw[hp',show ∑ i,neap n _ 0 x= neap n U 0 x from (neap_sumE (s:=univ) (k:=n) x (fun i _=> hx i)).symm]
    unfold neap; rw[iteratedFDeriv_const_smul_apply (hh.of_le le_top), _root_.smul_apply, smul_comm]
lemma mosso (h:Oil L F)(hp:∀ w,Skew (V w) σ A)(he:0 < σ)(a:Fslot G)(w:W)(i:Site (g w))(p:Land):
    neap n (fern (V w) (F w) a (sip i)) 0 p= ∑ j,∑ s,neap n (moss (V w) (F w) (sip i) a j s) 0 p:=by
    have hx(j s:Loc G k): ContDiffAt ℝ ω (moss (V w) (F w) (sip i) a j s) 0:=by obtain ⟨C,hC,H⟩:= (honor_sq (n:=n) h hp he j s a).top;exact (shunt_a (sip i) 0 (H w (sip i,0))).analytic
    unfold fern; rw [neap_sumE]; exact Finset.sum_congr rfl fun i _=>neap_sumE _ (fun s _=> hx i s); intro i _; exact ContDiffAt.sum (fun s _=>hx i s)
end slice
lemma plankL (Q:Tendsto (fun w=>(g w).val) L atTop)(d i b:Axis)(q:G.ColorIndex)(h:Oil L F)(ht:∀ w,Ticket (V w) (H w))(hp:∀ w, Skew (V w) σ A)(hs:0 < σ):
    Rose L (fun w=> lux d i q b (fun x=>trace (H w x* F w x))) (fun w=> Deb fun x=> neap 3 (Pond (F w) (mood G i q) (V w)) 0 (lawn d b x)):=by
    have he(w):Memo (F w) 0:=by obtain ⟨A,C,hA,hC,H⟩:= h.jets.top;exact fun i j=> (H w i j).1
    unfold lux; simp_rw[cusp _ _ _ _ (ht _) (he _), lawn, flee_run]; exact disk_brief (gran Q) (fun w=> Pond (F w) _ (V w)) _ _ (pond_b h hp hs _)
end YM.Trace.Loft
