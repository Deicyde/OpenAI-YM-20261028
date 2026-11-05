import YM.TraceExtension.Perfect.Mauve
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge} {f:Side}{p:Clip}{η B' σ A:ℝ}
lemma act_row (r:Row (TypeFace 2) (TypeFace 2))(M : Body 2 f →ℝ)(hr:r.safe)(k : Body 2 f):
    (r.acts f *ᵥ M) k= ∑ i:TypeFace 2,∑' z,r k.2 i z * M (k.1+wrap f z,i) :=by
   unfold mulVec dotProduct; rw [Fintype.sum_prod_type, Finset.sum_comm]; apply sum_congr rfl; intro i _
   let Q(x:Site f)(z:Cover):= if x=k.1+wrap f z then r k.2 i z else 0
   have ht(x:Site f): Summable (Q x):= ((hr k.2 i).of_norm.indicator {z| x=k.1+wrap f z}).congr (fun a=>by simp[Set.indicator,Q])
   have hv(x:Site f): r.acts f k (x,i) * M (x,i)=∑' z, Q x z * M (x,i):=by rw [tsum_mul_right]; rfl
   simp_rw [hv]; rw [← Summable.tsum_finsetSum]; swap; · intro x _; exact (ht x).mul_right _
   apply tsum_congr; intro z; simp [Q,ite_mul]
lemma active_pay (r:Row (TypeFace 2) (TypeFace 2))(M:Body 2 f→ℝ)(hr:r.safe)(u:Site f)(i j:TypeFace 2): Summable fun z => r i j z * M (u+wrap f z,j):=by
 have he (x:Site f): Summable fun z=> (if u+wrap f z=x then r i j z*M (x,j) else 0):= (((hr i j).of_norm.mul_right (M (x,j))).indicator {z| u+wrap f z=x}).congr (fun z=>by simp [Set.indicator])
 have ht:= summable_sum (f:=fun x: Site f=>fun z =>if u+wrap f z=x then r i j z*M (x,j) else 0) (s:=univ) (fun x _=>he x)
 exact ht.congr (fun x=> by simp)
lemma acts_berry (t:Tit G)(x:Site f)(v:Cover)(p:PlaqAxes)(i:G.ColorIndex):
  |strive (bGauge t x) i (x+wrap f v,plaquette p)|≤16*(3+(size v:ℝ))^2:=by
 rw [tribute]
 let F:ℝ:=4*(3+(size v:ℝ))^2; let u:= bGauge t x;let K:=x+wrap f v; let A:=leg1 p;let B:=leg2 p
 have hv : separation x K ≤ size v:=by unfold K;rw[separation_comm,separation,add_comm x,add_sub_cancel_right]; exact Next.Free.within_size ..
 have hh(j):separation x (K+step j) ≤ size v+1:=by refine (separation_triangle x K _).trans (Nat.add_le_add hv ?_); rw [separation_comm,separation,add_comm K,add_sub_cancel_right]; exact pdist_step j
 have he(y:Site f)(a:Axis)(h:separation x y ≤ size v+1): |edgeColor u (y,a) i| ≤ F:=by
    rw [show (y,a)=edgeOf (y,coord a) from Prod.ext rfl ((axisEquiv.symm_apply_apply a).symm),edge_parts u]; change |u _| ≤ _; unfold u; rw [edgeGauge]; apply (ballad_bound t x _).trans; unfold F; change 4*(1+(separation x y:ℝ))^2 ≤ _; gcongr 4 * ?_ ^ _
    change 1+(separation x y:ℝ)≤_; have hh:= Nat.cast_le (α:=ℝ)|>.mpr h; push_cast at hh; linarith
 unfold petal; simp only[PiLp.add_apply,PiLp.sub_apply]; have ht:= he K A (hv.trans (Nat.le_add_right ..)); have hB:=he K B (hv.trans (Nat.le_add_right ..)); have hr:=he _ A (hh B);have hx:=he _ B (hh A)
 apply le_trans (abs_sub ..); apply le_trans (add_le_add_left (abs_sub _ _) _); apply le_trans (add_le_add (add_le_add ((abs_add_le ..).trans (add_le_add ht hx)) hr) hB)
 unfold F; linarith

variable {W:Type} {F:Filter W}{n:W→Side}(x:∀ w,Site (n w))(ht:Tendsto (fun w=>(n w).val) F atTop)
include ht
lemma w_lit (v:Cover): ∀ᶠ w in F, lift (wrap (n w) v)=v:=by
 suffices ha: ∀ᶠ w in F,∀ i: Axis,-(((n w).val):ℤ)<2*v i∧2*v i≤ (n w).val from ha.mono (fun w hh=> lift_eq_iff.mpr ⟨rfl,hh⟩)
 refine eventually_all.mpr (fun i=>?_); filter_upwards [ht.eventually (eventually_ge_atTop ((2*v i).natAbs+1))] with w hw; omega
lemma stately (t:Tit G)(v:Cover)(a b:Axis):∀ᶠ w in F,petal (x w+wrap (n w) v) a b (bGauge t (x w))=mixB t v a b:=by
 filter_upwards [w_lit ht v,w_lit ht (v+step a),w_lit ht (v+step b)] with w hh h p
 unfold petal; simp only [edgeGauge_at]; let y:= x w
 rw [show y+wrap (n w) v-x w=wrap (n w) v by unfold y; abel,show y+wrap (n w) v+step a-x w=wrap (n w) (v+step a) by unfold y; rw[map_add,wrap_step]; abel,show y+wrap (n w) v+step b-x w=wrap (n w) (v+step b) by unfold y; rw[map_add,wrap_step]; abel, hh,h,p];rfl

lemma metric_berry (r:W→Bed)(hg:∀ w,Floor (r w) p (n w) η B')(t:Tit G)(hs:0<σ)(hp:0 ≤ A)(hh:∀ w,(r w).metric.strip σ A)
    (a b:Axis)(q:PlaqAxes)(i:G.ColorIndex) : Tendsto (fun w=> wagesM (r w) (bGauge t (x w)) (x w) q i a) F (𝓝 (- dal t a q.val.1 q.val.2 i)):=by
 let R(w):= (r w).metric; let M(w):= strive (bGauge t (x w)) i; let X(v:PlaqAxes):=-(dal t a v.val.1 v.val.2) i; let V:=plaquette q
 let E (v:PlaqAxes)(w:W)(z:Cover):= R w V (plaquette v) z * (M w (x w-step a+wrap (n w) z,plaquette v)-M w (x w+wrap (n w) z,plaquette v)-X v)
 have hx(w): (R w).safe:= Row.rights _ _ (hh w) hs.le
 have hy(w) : (∑ v:PlaqAxes,∑' z,E v w z)=wagesM (r w) (bGauge t (x w)) (x w) q i a-X q:=by
    unfold E wagesM; rw [act_row ..,act_row ..]; rotate_left
    · exact hx w
    · exact hx w
    let f (j:TypeFace 2)(x:Site (n w)) (z:Cover):= R w V j z*M w (x+wrap (n w) z,j)
    have hb(v:PlaqAxes): (∑' z,R w V (plaquette v) z * X v) = if v=q then X v else 0:=by
       have hi:= congr_fun (congr_fun (hg w).starts V) (plaquette v); rw [Row.read,of_apply,Laurent.read] at hi
       simp only[mode_constant,one_smul, ← Complex.ofReal_tsum,Matrix.one_apply] at hi
       rw [tsum_mul_right]; unfold V at *; simp only [plaq_iff] at hi
       by_cases H:v=q
       · rw [if_pos H]; rw [if_pos (Eq.symm H)] at hi
         rw [show (∑' z,R w (plaquette q) (plaquette v) z)=1 by exact_mod_cast hi]; ring
       rw [if_neg H]; rw [if_neg (Ne.symm H)] at hi
       rw [show (∑' z,R w (plaquette q) (plaquette v) z)=0 by exact_mod_cast hi]; ring
    have hs(v:PlaqAxes): (∑' z,E v w z) = (∑' z,f (plaquette v) (x w-step a) z)-(∑' z,f (plaquette v) (x w) z)-(if v=q then X v else 0):=by
       have hv(x):= active_pay (R w) (M w) (hx w) x V (plaquette v)
       unfold E; simp_rw[mul_sub]; rw [Summable.tsum_sub (hv _|>.sub (hv _)) ((hx w _ _).of_norm.mul_right _),Summable.tsum_sub (hv _) (hv _),hb]
    change (∑ v:PlaqAxes,∑' z,E v w z)=(∑ v:TypeFace 2,∑' z,f v (x w-step a) z)-(∑ v:TypeFace 2,∑' z,f v (x w) z)-X q
    simp_rw [hs,Finset.sum_sub_distrib]; rw [sum_ite_eq',if_pos (mem_univ _)]
    congr 2
    · exact plaqEquiv.sum_comp (fun i=>∑' z,f i (x w-step a) z)
    exact plaqEquiv.sum_comp (fun i=>∑' z,f i (x w) z)
 have hz(v:PlaqAxes): Tendsto (fun w=>∑' z,E v w z) F (𝓝 0):=by
    have hv(z): Tendsto (fun w=> E v w z) F (𝓝 0):=by
       refine tendsto_const_nhds.congr' ?_
       filter_upwards [stately x ht t z v.val.1 v.val.2,stately x ht t (z+ (-1:ℤ) • step a) v.val.1 v.val.2] with w hX hZ
       unfold E M X; rw [tribute,tribute]; rw [← show x w+wrap (n w) (z+(-1:ℤ) • step a)=x w-step a+wrap (n w) z by simp only[neg_one_smul,map_add,map_neg,wrap_step];abel,hX,hZ, radial, PiLp.add_apply,PiLp.smul_apply]; push_cast; ring
    obtain ⟨C,c,H⟩:= shelter_paid (t:=2) (α:=0) (η:=σ/2) le_rfl (half_pos hs)
    have ht(z:Cover): (1+(size z:ℝ))^2≤ C*Real.exp (σ/2*size z):= (by simpa only[shelter,zero_mul, Real.exp_zero,mul_one,one_mul] using H (size z) (by positivity))
    let f(z:Cover):=Real.exp (-(σ/2)*size z)* (A*((640+|X v|)*C))
    have hb:Summable f:= ((Width.compactPay (σ/2) (half_pos hs)).2.1).mul_right _
    have hp:∀ w z,‖E v w z‖≤ f z:=by
       intro w z; let u:=size z; have hr (v':Cover)(h:size v' ≤ u+1): ‖M w (x w+wrap (n w) v',plaquette v)‖ ≤ 320*(1+(size z:ℝ))^2:=by
          rw [Real.norm_eq_abs]; apply (acts_berry ..).trans
          have hp:(size v':ℝ) ≤ size z + (1:ℝ):=by exact_mod_cast h
          nlinarith [(Nat.cast_nonneg (α:=ℝ) (size v')),Nat.cast_nonneg (α:=ℝ) (size z)]
       have hp:= hp
       let D:=M w (x w-step a+wrap (n w) z,plaquette v)-M w (x w+wrap (n w) z,plaquette v)
       have hy: ‖D-X v‖ ≤ (640+|X v|)*(1+(size z:ℝ))^2:=by
          have he : u ≤ u+1:=Nat.le_succ _; have hs:=Sheaf.size_step_one a
          have hf : Laurent.size (z+ -(step a)) ≤ u+1:= (size_add ..).trans (by rw [size_neg,hs]); have hx:= hr _ hf; rw [show x w+wrap (n w) (z+ -(step a))=x w-step a+wrap (n w) z by simp only[map_add,map_neg,wrap_step];abel] at hx
          refine (norm_sub_le ..).trans ((add_le_add (show ‖D‖≤_ from norm_sub_le ..) le_rfl).trans ((add_le_add (add_le_add hx (hr z he)) le_rfl).trans ?_)); rw [Real.norm_eq_abs]; have ht:(1+(size z:ℝ))^2≥1:=one_le_pow₀ (by simp); nlinarith [mul_le_mul_of_nonneg_left ht (abs_nonneg (X v))]
       change ‖ R w V (plaquette v) z*(D-X v)‖ ≤ _; rw [norm_mul]
       have hw := hh w V (plaquette v); have hu := (Summable.le_tsum hw.2.1 z (fun x _=>hw.1 x)).trans hw.2.2
       refine (mul_le_mul ?_ (hy.trans (mul_le_mul_of_nonneg_left (ht z) (by positivity))) (norm_nonneg _) (show 0 ≤ A/Real.exp (σ*size z) from by positivity)).trans_eq ?_
       · rw [le_div_iff₀ (Real.exp_pos _),mul_comm]; exact hu
       unfold f;rw [div_mul_eq_mul_div]; field_simp; rw [mul_assoc,← Real.exp_add]; congr 2; ring
    simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence hb hv (Eventually.of_forall hp)
 have H:= (opt0 _ hz).add_const (X q); rw [zero_add] at H
 refine H.congr (fun w=>?_); rw [hy]; simp
end YM.Trace.Perfect
