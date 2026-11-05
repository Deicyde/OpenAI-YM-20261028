import YM.TraceExtension.Pi.Prate
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Kits
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det Loft MeasureTheory Source Source.Drops Work Planned.PrimaryIntegral295 Place Parts Next.Foundations WardBin StressFlux Labels
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace Classical
variable {G:Gauge}(x:Taylor G 0){s:Side}
open MeasureTheory
lemma fuel (z:E4)(i:Axis): variation x z i=x.value i z + (1/2:ℝ) • x.value i (basis i):=by
    rw [← fume_leg,fume]; simp_rw [coon0]; rw [intervalIntegral.integral_add,intervalIntegral.integral_smul_const]; rotate_left
    · exact intervalIntegrable_const
    · apply Continuous.intervalIntegrable; fun_prop
    simp
lemma ivy_coin (p:Site s)(i j: Axis): edgeColor (ivy 0 x) (p,i)=x.value i (Place.seat (lift p))+(1/2:ℝ) • x.value i (basis i):=by unfold ivy stepC; rw[ContinuousLinearEquiv.apply_symm_apply]; simp only[sub_zero,fuel]
lemma ivy_petal (i j:Axis)(hs:40 ≤ s.val): petal (0:Site s) i j (ivy 0 x)=curl0 i j x:=by
   unfold petal; simp_rw [ivy_coin x _ _ j]; simp only [zero_add]; have hp(a:Axis) : lift (step a:Site s)=step a:=lift_eq_iff.mpr ⟨by rw[wrap_step],fun i=>by simp only[step_apply];split_ifs <;> omega⟩
   have hv(a:Axis):x.value a 0=0:=by unfold Taylor.value; simpa only [zero_smul,zero_pow (by omega : 0+1≠0)] using Tensor.homogeneous (x.val a) 0 0
   simp [hp,curl0_value,Lattice.lift, hv]; abel
lemma born_pay (i j:Axis)(hs:40 ≤ s.val)(J:Jet G): let W:=ivy (0:Site s) (J 0); let A:= anis W W; (↑((1/2:ℝ)*A (coco i j (0:Site s))):ℂ)= prink J (-raw G i j):=by
    intro W A; let σ(a b c:Axis): loom G s:=⟨bornPair 0 a b c,(born_win ..).1⟩
    have hP(a b c:Axis): prink J (pair G a c b c)=(↑((1/2:ℝ)*A (σ a b c)):ℂ):=by
         change Labels.read J (pair G a c b c).val=(↑((1/2:ℝ)*anis W W (σ a b c)):ℂ); rw[pair_value,anum]; unfold σ; rw[show sheen _ _ _ =_ from (born_win (G:=G) (0:Site s) a b c).2 W W,ivy_petal (J 0) a c hs, ivy_petal (J 0) b c hs]; push_cast; ring
    have he : coco (G:=G) i j (0:Site s)= (if i=j then (1/4:ℝ) • (∑ a:Axis,∑ b:Axis, σ a a b) else 0) - ∑ k:Axis,σ i j k:=by ext1; simp only [Submodule.coe_sub,apply_ite Subtype.val,AddSubmonoidClass.coe_finsetSum,Submodule.coe_zero,Submodule.coe_smul];rfl
    unfold raw; rw[he,map_neg,stress_of]; split
    next hh=> subst j; simp only [weyl,Matrix.cons_val_zero,Matrix.cons_val_one, Matrix.head_cons]; simp_rw[map_sub,map_add,map_smul,map_sum,hP]; norm_num;push_cast; simp only[← Finset.mul_sum];ring
    next h=> rw[zero_sub,map_neg]; change _= -prink J ((1:ℝ) • _); rw [one_smul,map_sum,map_sum]; simp_rw [hP]; push_cast; simp only [← Finset.mul_sum]; ring
-- express link as stencil linear combination in G coordinates
abbrev Needle (G:Gauge) := Option Axis × (Loc G 1)
def mine (x: Needle G) : Tit G:= (x.1.elim .unit RowGrade.foot,x.2)
lemma mine_price (x:Needle G): ScoreG (mine x) ≤ 2:=by rcases x with ⟨_|_,p⟩<;>simp [ScoreG,mine,RowGrade.degree]
private lemma act_entry (z:E4)(i:Axis): x.value i z=∑ j:Axis,z j • x.value i (basis j):=by
   obtain ⟨h,hx⟩:= (ContinuousMultilinearMap.ofSubsingleton ℝ E4 G.Color (0:Fin 1)).surjective (x.val i); unfold Taylor.value; rw[← hx]; change h z= ∑ j:Axis,z j • _
   conv_lhs=> rhs; rw[← show ∑ i:Axis, z i • basis i=z from by ext1 i;simp]
   rw [map_sum];simp_rw[map_smul];rfl
def conjP (c: Needle G):ℝ:=let i:=axisEquiv.symm c.2.1; let k:=c.2.2; c.1.elim ((1/2:ℝ)*(x.value i (basis i) k)) fun b=> x.value i (basis b) k
lemma ivy_build : ivy (0:Site s) x=∑ c:Needle G, conjP x c • bGauge (mine c) (0:Site s):=by
   ext1 p; rcases p with ⟨u,j,k⟩; obtain ⟨j,rfl⟩:=axisEquiv.surjective j
   let y:Loc G 1:=(coord j,k)
   change edgeColor (ivy (0:Site s) x) (u,j) k=(∑ c:Needle G,conjP x c • bGauge (mine c) (0:Site s)) (u,y)
   rw[Finset.sum_apply, ivy_coin x u j j,PiLp.add_apply]; rw [act_entry,Fintype.sum_prod_type,Fintype.sum_option]; simp_rw [show ∀ c:Needle G, (conjP x c • bGauge (mine c) (0:Site s)) (u,y)= conjP x c*bGauge (mine c) 0 (u,y) from fun _=>rfl,edgeGauge]; simp [y,ballad,mine,strollT,conjP,RowGrade.price,mul_ite, show axisEquiv.symm (Exterior.coord j)=j from axisEquiv.symm_apply_apply j,mul_comm];ring
section care
variable {W:Type}{F:Filter W}{n:W→Side}{X:∀ w, loom G (n w)}{v:W→Label G 4}{H:Hol G}(hn:Tendsto (fun w=> (n w).val) F atTop)(hp:∀ w, JetTest H 0 (v w) (Complex.ofRealCLM ∘ (X w).val))(hs:G.Simple)
lemma web (X:loom G s)(u y: Tit G): loom₂ s G (ballad u 0) (ballad y 0) X= anis (bGauge u 0) (bGauge y 0) X:= (loom_banks X.property ..).trans (anum ..).symm
include hn
lemma testify_lim (i j:Axis)(he:Stoke (n:=n) F (fun _=>0) (fun w=>ballX (X w).val) (fun p q=>north p q 0 i j) 4) (k l:Needle G): Tendsto (fun w=> anis (bGauge (mine k) 0) (bGauge (mine l) 0) (X w-coco i j (0:Site (n w)))) F (𝓝 0):=by
    let h:= fun (p q:Tit G) (Z:∀ w, loom G (n w)) w=> loom₂ (n w) G (ballad p 0) (ballad q 0) (Z w)
    have ht : Tendsto (h (mine k) (mine l) X) F (𝓝 _):= he.taste (mine k) (mine l) (add_le_add (mine_price k) (mine_price l))
    let f: ℝ:= north (mine k) (mine l) 0 i j; let y w:=coco (G:=G) i j (0:Site (n w))
    have hh: Tendsto (h (mine k) (mine l) y) F (𝓝 f):= (verdant (G:=G) (fun w=>(0:Site (n w))) hn i j).taste _ _ (add_le_add (mine_price k) (mine_price l))
    have hu:= ht.sub hh; change Tendsto _ _ (𝓝 (f-f)) at hu; rw [sub_self] at hu
    refine hu.congr' (Eventually.of_forall (fun w=>?_ )); unfold h; rw [web,web,← map_sub]
include hp hs
lemma peg (i j:Axis)(h:Stoke (n:=n) F (fun _=>0) (fun w=>ballX (X w).val) (fun p q=>north p q 0 i j) 4)(J:Jet G): Tendsto (fun w=> Labels.read J (v w).val) F (𝓝 (prink J (-raw G i j))):=by
    let y w:=coco (G:=G) i j (0:Site (n w)); let U w:=X w-y w
    let W' w:= ivy (0:Site (n w)) (J 0); have hx: Tendsto (fun w=> anis (W' w) (W' w) (U w)) F (𝓝 0):=by
       let V(c:Needle G)(w):= bGauge (mine c) (0:Site (n w)); let X':= J 0; let K:=conjP X'
       have ht(w): anis (W' w) (W' w) (U w)= ∑ i:Needle G,∑ j:Needle G,K i*(K j*anis (V i w) (V j w) (U w)):=by
           unfold W'; rw [ivy_build,anum]; simp_rw[anum]; simp only[V,sheen, iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one,map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,Finset.mul_sum,smul_eq_mul,K,X']
           rw [Finset.sum_comm]; refine sum_congr rfl fun j _=> sum_congr rfl fun i _=>mul_left_comm _ _ _
       simp_rw[ht]; have hh: ∑ (_i:Needle G), (0:ℝ)=0:=by simp
       rw[← hh]; apply tendsto_finsetSum; intro k _; rw[← hh]; apply tendsto_finsetSum; intro l _; simpa only[mul_zero,V,U,y] using (testify_lim (X:=X) hn i j h k l|>.const_mul (K l)|>.const_mul (K k))
    have hv:= Complex.ofRealCLM.continuous.continuousAt.tendsto.comp (hx.const_mul (1/2:ℝ))
    simp only [mul_zero,map_zero] at hv
    have ht:= hv.add (show Tendsto (fun _=>prink J (-raw G i j)) F _ from tendsto_const_nhds (x:=prink J (-raw G i j)))
    rw [zero_add] at ht; apply ht.congr'; filter_upwards [hn.eventually (eventually_ge_atTop 40)] with w hw; rw [vista4 (X w|>.property.1) hs (hp w) J, loom0]; rw[zero_add,← born_pay i j hw]
    change (↑((1/2:ℝ)*anis (W' w) (W' w) (U w)):ℂ)+_= _; unfold U; rw [map_sub]; push_cast; rw [anum _ _ (X w)]; unfold W' y;ring
end care
end YM.Trace.Kits
