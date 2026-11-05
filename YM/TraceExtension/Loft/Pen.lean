import YM.TraceExtension.Loft.Canto
set_option autoImplicit false
/-!
# SCALED route jets. Permit derivatives at transferred meshes NOT h/r bounded.
Directions differentiated through aperture 3 on scale |k|+µ. ℝ immersion. -/
noncomputable section
namespace YM.Trace.Loft
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det
open scoped BigOperators Topology ContDiff ComplexConjugate Classical
variable {W X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]{a n k:ℕ}{σ A C D E R L M ρ:ℝ}{f:X→ℂ}
lemma fare_l {x v:X}(h:ContDiffAt ℝ ω f x) :
    ‖iteratedFDeriv ℝ k (fun t:ℝ=>f (x+t • v)) 0‖ ≤ ‖iteratedFDeriv ℝ k f x‖* ‖v‖^k:=by
    let T:= ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) v; let F(y:X):=f (x+y)
    have hf:ContDiffAt ℝ ω F (T 0):= ContDiffAt.comp (g:=f) (f:=fun y : X=>x+y) (T 0) (by rw[map_zero,add_zero];exact h) (by fun_prop)
    rw[show (fun t:ℝ=>f (x+t • v))=F ∘ T from rfl,iter_lin_at (hf.of_le le_top),show T 0=0 from map_zero _]; unfold F; rw [iteratedFDeriv_comp_add_left,add_zero]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans ?_
    simp only[Finset.prod_const,Finset.card_univ,Fintype.card_fin]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); have hp:‖T‖≤‖v‖:= T.opNorm_le_bound (norm_nonneg _) (fun x=> by change ‖x • v‖ ≤ ‖v‖*‖x‖; rw[norm_smul]; exact (mul_comm ‖x‖ ‖v‖).le)
    exact pow_le_pow_left₀ (norm_nonneg _) hp k
-- far-evaluation by integrating n+1, reserve weights independent ρ upper bound (fixed range)
lemma tens (d:ℕ)(hA:0≤A)(hC:0 ≤ C)(K:ℝ)(hk:0 ≤ K):∃ D:ℝ,0 ≤ D ∧ ∀ (f:X→ℂ)(x:X)(T:ℝ),0< T→ ‖x‖≤ T*K→ (∀ y:X,Allows (n+d) f y A) → (∀ i:ℕ,n ≤ i→ i<n+d→ ‖iteratedFDeriv ℝ i f 0‖ ≤ C*T^(n+d-i))→ ‖iteratedFDeriv ℝ n f x‖ ≤ D*T^d:=by
    induction d generalizing n with
    | zero=> refine ⟨A,hA,fun f x t ht hx h hp=> ?_⟩; rw[pow_zero,mul_one]; exact (h x).norm_le n le_rfl
    | succ d ih=>
        obtain ⟨D,hD,H⟩:=ih (n:=n+1)
        refine ⟨D*K+C,by positivity,fun f x T hp he hf hq=>?_⟩
        let V:=closedBall (0:X) (T*K); let Z:=iteratedFDeriv ℝ n f; have hr: n+1+d=n+(d+1):=by omega
        have h0:(0:X)∈V:= mem_closedBall_self (by positivity); have hx:x∈V:=by simpa[V] using he
        have ht(y)(hy:y∈V):‖iteratedFDeriv ℝ (n+1) f y‖≤ D*T^d:= H f y T hp (by simpa[V] using hy) (hr.symm ▸ hf) (fun i hx hy=> by rw[hr]; apply hq i <;> omega)
        have hh:= Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (s:=V) (f:=Z) (C:=D*T^d) (fun x _ => ((hf x).analytic).differentiableAt_iteratedFDeriv (by simp)) (fun x hh=> (fare_lefter X ℂ f n x).trans_le (ht x hh)) (convex_closedBall ..) h0 hx
        rw[sub_zero] at hh; have hu := hq n le_rfl (by omega); rw[show n+(d+1)-n=d+1 by omega] at hu
        change ‖Z x‖≤_; have hA': ‖Z x-Z 0‖ ≤ D*T^d*(T*K):=hh.trans (mul_le_mul_of_nonneg_left he (by positivity)); exact sub_add_cancel (Z x) (Z 0) ▸ (norm_add_le (Z x-Z 0) (Z 0)).trans ((add_le_add hA' hu).trans_eq (by ring))
lemma floret (hA:0≤A)(hC:0 ≤ C)(hM:0 ≤ M)(K L:ℝ)(hk:0 ≤ K)(hL:0 ≤ L)(ha:a≤n):∃ D:ℝ,0≤ D ∧ ∀ (f:X→ℂ)(x v:X)(T:ℝ),0<T → T≤M → ‖x‖ ≤ T*K→ ‖v‖ ≤ T*L→ (∀ y, Allows n f y A)→ (∀ i:ℕ,i<a → ‖iteratedFDeriv ℝ i f 0‖≤ C*T^(a-i))→ Allows n (fun t:ℝ=>f (x+t • v)) 0 (D*T^a):=by
    have H i: ∃ D:ℝ,0≤D ∧ (i≤n → ∀ f:X→ℂ,∀ x v:X,∀ T:ℝ, 0<T→T≤M→ ‖x‖ ≤ T*K→ ‖v‖ ≤ T*L→ (∀ y, Allows n f y A)→ (∀ i:ℕ,i<a → ‖iteratedFDeriv ℝ i f 0‖≤ C*T^(a-i))→ ‖iteratedFDeriv ℝ i (fun t:ℝ=>f (x+t • v)) 0‖≤D*T^a):=by
        by_cases hp:i<a
        · obtain ⟨D,hD,F⟩:=tens (X:=X) (n:=i) (a-i) hA hC K hk; refine ⟨D*L^i,by positivity,fun hi f x v T h ht hx hv hF H=> ?_⟩
          have hr:i+(a-i)=a:=by omega
          have hz:= F f x T h hx (fun p=> (hF p).order (by omega)) (fun i he hp=>by rw[hr]; exact H i (by omega))
          refine (fare_l (v:=v) (hF x|>.analytic)).trans ((mul_le_mul hz (pow_le_pow_left₀ (norm_nonneg _) hv i) (by positivity) (by positivity)).trans_eq ?_); rw[mul_pow]; calc
           _ = D*L^i * (T^(a-i)*T^i):=by ring
           _ = _ := by rw[← pow_add]; congr 2; omega
        refine ⟨A*L^i*M^(i-a),by positivity,fun hi f x v T h ht hx hv hF H=>?_⟩
        calc
         _ ≤ A*((T*L)^i):= (fare_l (v:=v) (hF x|>.analytic)).trans (mul_le_mul ((hF x).norm_le i hi) (pow_le_pow_left₀ (norm_nonneg _) hv i) (by positivity) hA)
         _ = (A*L^i)*T^(i-a)*T^a :=by rw[mul_pow,mul_assoc (A*L^_),← pow_add,show i-a+a=i by omega];ring
         _ ≤ _:= by gcongr
    choose D hD hv using H
    let d:=∑ i∈range (n+1),D i; refine ⟨d,sum_nonneg fun i _=>hD i,fun f x v T hx hr he ha hF H=>?_⟩; exact ⟨(show ContDiffAt ℝ ω f (x+(0:ℝ) • v) by simp; exact (hF x).analytic).comp (f:=fun t:ℝ=>x+t • v) _ (by fun_prop),fun i hi=> (hv i hi f x v T hx hr he ha hF H).trans (mul_le_mul_of_nonneg_right (single_le_sum (f:=D) (fun j _=>hD _) (mem_range.mpr (by omega))) (by positivity))⟩
variable {T:W→ℝ}{F:W→ X→ℂ}
lemma shellu (h:Honor F n)(hp:∀ w,Stationary.Rays a (F w))(hx:a≤n)(t v:W→ X) (hk:∀ w,0<T w)(hm:∀ w,T w≤M)(hM:0≤M)(u l:ℝ)(hu:0≤u)(hl:0≤l)(hz:∀ w, ‖t w‖≤T w*u)(hv:∀ w, ‖v w‖ ≤ T w*l): Note n (T^a) (fun w p=> F w (t w+p • v w)):=by
    obtain ⟨A,hA,H⟩:=h.top; obtain ⟨D,hD,f⟩:= floret (X:=X) hA (C:= (0:ℝ)) (by norm_num) hM u l hu hl hx; refine ⟨fun i=> pow_nonneg (hk i).le _, D,hD,fun i=> f (F i) _ _ _ (hk i) (hm i) (hz i) (hv i) (H i) (fun j hj=>?_)⟩
    rw [(rays_jet ((H i 0).analytic.analyticAt) a).1 (hp i) j hj]; simp
end YM.Trace.Loft
