import YM.TraceExtension.Perfect.Happy

set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset Push.Uniform
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical

-- Triangular reserve: arithmetics doesn't invoke YM analog
variable {C H D m:ℝ} {L:Side}
def reed (b:ℝ)(i:ℕ):ℝ:= Real.log b ^ i
def east (b:ℝ):ℝ:= (Real.log b)⁻¹
def vista (i:ℕ)(b:ℝ):ℕ→ℝ:= fun j=> ((1:ℝ)/2)^i*reed b j
def sheer (H x:ℝ):Prop := Tour.allSheaf*(2^13*H^2)/x * 3<1/2 ∧
   ∀ i:ℕ,2 < i→i≤4→ 3*(x^5*Tour.allSheaf*(2*H/x^2)^i)<1/2
lemma big_along (H:ℝ): ∃ j:ℕ,∀ L:Side,j ≤ L.val→sheer H L.val:=by
 let f x:= Tour.allSheaf*(2^13*H^2)/x*3
 let g(i:ℕ)(x:ℝ):= 3*(x^5*Tour.allSheaf*(2*H/x^2)^i)
 have hh : Tendsto f atTop (𝓝 0):=by simpa only [f,zero_mul,id_eq] using (tendsto_const_nhds (x:=Tour.allSheaf*(2^13*H^2))|>.div_atTop (tendsto_id (x:=(atTop:Filter ℝ)))|>.mul_const 3)
 have ht(i:ℕ)(h:2 < i)(hr:i≤4): Tendsto (g i) atTop (𝓝 0):=by
    let d:=3*Tour.allSheaf*(2*H)^i
    have hx (x:ℝ)(hx:0<x): g i x=d/x^(2*i-5):=by unfold g d; interval_cases i<;> norm_num at *<;> field_simp <;> ring
    refine ((tendsto_const_nhds (x:=d)).div_atTop  (show Tendsto (fun x:ℝ=>x^(2*i-5)) atTop atTop from tendsto_pow_atTop (show 2*i-5≠0 by omega))).congr' ?_; filter_upwards [eventually_gt_atTop (0:ℝ)] with x hh using (hx x hh).symm
 have he:∀ᶠ y:ℝ in atTop,sheer H y:=by filter_upwards [hh.eventually (gt_mem_nhds (show (0:ℝ)<1/2 by norm_num)),(ht 3 (by decide) (by decide)).eventually (gt_mem_nhds (show (0:ℝ)<1/2 by norm_num)), (ht 4 (by decide) (by decide)).eventually (gt_mem_nhds (show (0:ℝ)<1/2 by norm_num))] with x hx hp h; refine ⟨hx,fun i hi hi' =>?_⟩; interval_cases i; exact hp; exact h
 obtain ⟨a,H⟩:= eventually_atTop.1 (tendsto_natCast_atTop_atTop (R:=ℝ)|>.eventually he); exact ⟨a,fun i hh=> H i.val hh⟩
private lemma reed_pos {x:ℝ}(h:1<x)(i:ℕ):0<reed x i:=pow_pos (Real.log_pos h) _
lemma moor_log (d:ℝ): Tendsto (fun x:ℝ=> Real.log (x+d)/Real.log x) atTop (𝓝 1):=by
 have ht : Tendsto (fun x:ℝ=> (x+d)/x) atTop (𝓝 1):=by
    have hx:=(tendsto_const_nhds (x:=d)|>.div_atTop (tendsto_id (x:=(atTop:Filter ℝ)))|>.const_add 1)
    simp only[add_zero] at hx; refine hx.congr' ?_; filter_upwards[eventually_gt_atTop (0:ℝ)] with x hx; change 1+d/id x=(x+d)/x; change 1+d/x=_; rw[add_div,div_self hx.ne']
 have hh:= Tendsto.const_add 1 ((ht.log (by norm_num)).div_atTop Real.tendsto_log_atTop); rw [add_zero] at hh; apply hh.congr'; filter_upwards [eventually_gt_atTop (1:ℝ),eventually_gt_atTop (1-d)] with x hx hp; rw [Real.log_div (by linarith) (by linarith),sub_div,div_self (Real.log_pos hx).ne']; ring
lemma along_bill (C H D u:ℝ)(L:Side)(hC:0 ≤ C)(hH:0 ≤ H)(hD:0 ≤ D)(ht:sheer H L.val) (i n:ℕ) (he:i<n):
    Tendsto (fun x:ℝ=> reed (x+u) i/reed x n) atTop (𝓝 0):=by
 have hv: Tendsto (fun x:ℝ=> Real.log x ^ (n-i)) atTop atTop:= (tendsto_pow_atTop (show n-i ≠ 0 by omega)).comp Real.tendsto_log_atTop
 have hh : Tendsto (fun x:ℝ=> (Real.log (x+u)/Real.log x)^i) atTop (𝓝 1):=by simpa using (moor_log u).pow i
 refine (hh.div_atTop hv).congr' ?_; filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx; unfold reed; rw[div_pow,div_div,← pow_add,Nat.add_sub_of_le he.le]
local notation "l"=> (L.val:ℝ)
lemma bank_buys (hC:0 ≤ C)(hH:0 ≤ H)(hD:0 ≤ D)(ht:sheer H L.val)(u:ℝ):∀ᶠ x:ℝ in atTop,∀ i:ℕ, Bank H D L C (reed (x+u)) (reed x) (vista i (x+u)) (vista (i+1) x):=by
 let t:=Tour.allSheaf; let w:= (2:ℝ)^13 *H^2
 have ht':0<t:=Tour.sheaf_debt_pos; have hw:0 ≤ w:=by unfold w; positivity
 let X(x:ℝ):=reed (x+u); let Y(x:ℝ):=reed x; let e(a:ℝ):= ((1:ℝ)/2)^a
 have hl :0<l:= side_pos L
 have ha : Tendsto (fun x:ℝ=> X x 2/Y x 2) atTop (𝓝 1):=by
    have he:= (moor_log u).pow 2; simp only[one_pow] at he; refine he.congr fun x=>by rw [div_pow];rfl
 have hb : Tendsto (fun x=> C/Y x 2) atTop (𝓝 0):= (tendsto_const_nhds (x:=C)).div_atTop ((tendsto_pow_atTop (show 2≠0 by decide)).comp Real.tendsto_log_atTop)
 let J (x:ℝ):= t*w*((C/Y x 2)+(X x 2/Y x 2+C/Y x 2)/l)
 have hm :Tendsto J atTop (𝓝 (t*w/l)):=by
    have hv:= (hb.add ((ha.add hb).div_const l)).const_mul (t*w); simpa only[add_zero,zero_add,mul_one_div] using! hv
 have hj: t*w/l <1/6:=by unfold sheer at ht; change t*w/l*3<1/2∧_ at ht; linarith only[ht.1]
 let A (i:ℕ) := t*l^5*(2*H/l^2)^i
 let U (i:ℕ)(x:ℝ):= t*l^5*(((2*H/l^2)^i*X x i)+ ∑ z∈ univ.erase (OrderedFinpartition.atomic i), D^z.length*X x z.length)
 have hy (i:ℕ)(h:2 < i)(he:i ≤ 4):∀ᶠ x in (atTop:Filter ℝ), U i x/Y x i <1/6:=by
    have hz : Tendsto (fun x:ℝ=> X x i/Y x i) atTop (𝓝 1):=by have he:= (moor_log u).pow i; simp only[one_pow] at he; refine he.congr (fun x=> by rw[div_pow]; rfl)
    have hneg : Tendsto (fun x:ℝ=> ∑ z∈univ.erase (OrderedFinpartition.atomic i), D^z.length*(X x z.length/Y x i)) atTop (𝓝 0):=by
       have hf(z:OrderedFinpartition i)(he:z≠.atomic i): Tendsto (fun x:ℝ=> D^z.length*(X x z.length/Y x i)) atTop (𝓝 0):=by
           have hv:= along_bill C H D u L hC hH hD ht z.length i (lt_of_le_of_ne z.length_le (fun a=>he (YM.Planned.PrimaryIntegral295.Cases.finest _ a))); simpa only[mul_zero] using (hv.const_mul (D^z.length))
       have hz:= tendsto_finsetSum (s:=univ.erase (OrderedFinpartition.atomic i)) (fun z hz=>hf z (mem_erase.mp hz).1); simpa only [Finset.sum_const_zero] using hz
    have hp : Tendsto (fun x:ℝ=> U i x/Y x i) atTop (𝓝 (A i)) :=by
       have he:= (((hz.const_mul ((2*H/l^2)^i)).add hneg).const_mul (t*l^5)); rw [mul_one,add_zero] at he
       refine he.congr fun x=>?_; unfold U; simp only[mul_div_assoc,add_div,Finset.sum_div]
    have hh:= ht.2 i h he; refine hp.eventually (gt_mem_nhds ?_); unfold A; rw [mul_comm t]; change 3*((↑↑L:ℝ)^5*t*_ ) <_ at hh; linarith only[hh]
 filter_upwards [hm.eventually (gt_mem_nhds hj), hy 3 (by decide) (by decide),hy 4 (by decide) (by decide),eventually_gt_atTop (1:ℝ),eventually_gt_atTop (1-u)] with x hx hz hF hp hA i
 have hX j:0 ≤ X x j:=(reed_pos (by linarith only[hA]) j).le; have hY j:0< Y x j:= reed_pos hp j; have hk :0 ≤ ((1:ℝ)/2)^i:=by positivity
 let q:ℝ:= t*w/l*(X x 2); let hJ :ℝ:= t*w*(C+(X x 2+C)/l)
 have he:hJ < Y x 2/6:=by
    have hv:= (div_lt_iff₀ (hY 2)).mp (show hJ/Y x 2< 1/6 from (by unfold hJ; rw [mul_div_assoc,add_div,div_right_comm (b:=l),add_div]; exact hx)); linarith
 have hh : q ≤ hJ:= by unfold q hJ; rw [div_mul_eq_mul_div, mul_div_assoc]; gcongr; rw [add_div]; have hu:0 ≤ C/l:=div_nonneg hC hl.le; linarith only[hC,hu]
 have ho(j:ℕ)(h:2<j)(hc:j≤4): U j x ≤ (1/6:ℝ)*Y x j:=by
     refine (div_le_iff₀ (hY _)).mp ?_; interval_cases j; exact hz.le;exact hF.le
 refine ⟨hX,fun j=>(hY j).le,?_,?_,fun j=>mul_nonneg hk (hX _),fun j=>mul_nonneg (pow_nonneg (by norm_num) _) (hY _).le,?_,fun i h he=>?_,fun j h he=>?_⟩
 · rw [← mul_assoc Tour.allSheaf]; change 3*hJ ≤ Y x 2; linarith only[he,hY 2]
 · have hx: t*2^13*H^2/l*X x 2=q:=by unfold q w; ring
   change 3*(t*2^13*H^2/l*X x 2) ≤ Y x 2; rw [hx]; linarith only[hh,he,hY 2]
 · change t*w/l*_ ≤ _; unfold vista; rw [show t*w/l * ((1/2:ℝ)^i * reed _ 2)= ((1/2:ℝ)^i)*q by unfold q X;ring,pow_succ,mul_assoc]; apply mul_le_mul_of_nonneg_left _ hk; change _ ≤ 1/2*Y x 2; linarith only[he,hh,hY 2]
 · change 3*(l^5*t*_)≤Y x i; rw [mul_comm _ t]; change 3*U i x ≤Y x i; linarith only[ho i h he,hY i]
 change l^5*t*_≤_; let Z : Finset (OrderedFinpartition j):= univ.erase (.atomic j)
 change l^5*t*(((2*H/l^2)^j*((1/2:ℝ)^i*X x j))+ (∑ z∈Z,D^z.length*((1/2:ℝ)^i*X x z.length)))≤ (1/2:ℝ)^(i+1)*Y x j
 rw [show l^5*t*(_+∑ z∈Z,D^z.length*((1/2:ℝ)^i*X x z.length))=((1/2:ℝ)^i)*U j x from ?_,pow_succ,mul_assoc]
 · apply mul_le_mul_of_nonneg_left _ hk; linarith only[ho j h he,hY j]
 unfold U; rw [mul_left_comm,← mul_assoc ((1/2:ℝ)^i)]
 simp_rw[mul_add, Finset.mul_sum]; congr 1; (try ring)
 apply sum_congr rfl; intro i _; ring
end YM.Trace.Perfect
