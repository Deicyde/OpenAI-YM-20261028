import YM.RG08.Rudder.Loop.Console

/-!
# Independence of the surviving axis-parity-even zero curvature coefficient from the lift
(use equation on a pure transverse second-moment jet).
-/
noncomputable section
namespace YM.RG08.Rudder.Loop
open scoped Topology BigOperators Classical ENNReal InnerProductSpace
open Forms Packets Finset Function Lattice Laurent Pert.Bulk Exterior AnalyticNext.QuarticMatch.BoxChain Symmetry Filter
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
local notation "o"=> (0:Fin 2)
local notation "p"=> (Fin.succ (0:Fin 1))
variable {G:Gauge}{I:Type}{σ C B:ℝ}{F:Raw I 2}{A:ProductR}{q a b:Axis}

def second (v:Cover→ℝ)(a:Axis):=∑' x:Cover,(x a:ℝ)^2*v x
def paid (v:Cover→ℝ) : Prop:=Moment v ∧ ∀ a:Axis, Summable fun x:Cover=>(x a:ℝ)^2*v x
variable {f g:Cover→ℝ}
lemma polar (h:Pricing A σ C)(i j:Tablet):paid (col A i j):=by
 refine ⟨col_pay h ..,?_⟩
 intro q
 have hh(v): |col A i j v|≤ C * Real.exp (-σ*length v):=by
    simpa only [Real.norm_eq_abs,cost,col,place_p,place_o,sub_zero] using h.each (place (0,i) (v,j)) p o
 have hc:=h.cap;have hp:=h.rate
 let u:=σ/3;have hu:0<u:=by unfold u;linarith
 let E(v:Cover):=Real.exp (-u*length v);have he(v:Cover):length v*E v ≤1/u:=by
   unfold E;rw [neg_mul,Real.exp_neg,←div_eq_mul_inv,div_le_div_iff₀ (Real.exp_pos _) hu]
   have := Real.add_one_le_exp (u*length v);linarith
 apply Summable.of_norm_bounded ((show Summable E from (Width.compactPay u hu).2.1).mul_left (((1/u)^2)*C));intro v; have hv:0≤ E v:=(Real.exp_pos _).le
 rw [Real.norm_eq_abs,abs_mul,abs_pow]
 apply (mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (fee q v) 2) (hh v) (abs_nonneg _) (by positivity :0≤length v^2)).trans
 have ht:Real.exp (-σ*length v) = E v *E v*E v:=by unfold E u;rw [←Real.exp_add,←Real.exp_add];congr 1;ring
 rw [ht,show length v^2*(C*(E v*E v*E v))=(length v*E v)^2*(C*E v) from by ring,mul_assoc ((1/u)^2)];gcongr;exact he v

private lemma shifted (h:paid f)(w:Cover)(a:Axis):HasSum (fun v:Cover=>(v a:ℝ)^2*f (v+w)) (second f a-2*(w a:ℝ)*first f a+(w a:ℝ)^2*load f):=by
 let T:=Equiv.subRight w
 rw [←T.hasSum_iff]
 have he:=(h.2 a).hasSum.sub ((h.1.2 a).hasSum.mul_left (2*(w a:ℝ))) |>.add (h.1.1.hasSum.mul_left ((w a:ℝ)^2))
 apply he.congr_fun
 intro v
 change ((v-w) a :ℝ)^2*f (v-w+w)= _
 simp only [sub_add_cancel,Pi.sub_apply, Int.cast_sub];ring

private lemma coin (h:paid f)(c:ℝ)(v:Cover)(a:Axis): HasSum (fun w:Cover=> (w a:ℝ)^2*(c*(f (w+v)-f w))) (c*(-2*(v a:ℝ)*first f a+(v a:ℝ)^2*load f)):=by
 have he:= ((shifted h v a).sub (h.2 a).hasSum).mul_left c
 apply (show c*(-2*(v a:ℝ)*first f a+(v a:ℝ)^2*load f)=c*((second f a-2*(v a:ℝ)*first f a+(v a:ℝ)^2*load f)-second f a) by ring) ▸ he.congr_fun
 intro b;ring

lemma shaken (h:Pricing A σ C)(i j:Tablet)(a:Axis): second (col (lower o A) i j) a = if a∈i then 0 else sign i a * (-2*first (col A (insert a i) j) a + load (col A (insert a i) j)):=by
 let T(l:Axis)(v:Cover):= if l∈i then 0 else sign i l*((col A (insert l i) j) (v+step l)-col A (insert l i) j v)
 let K(l:Axis):ℝ:= if l=a ∧ a∉i then sign i a * (-2*first (col A (insert a i) j) a+load (col A (insert a i) j)) else 0
 have ht(l:Axis):HasSum (fun v:Cover=>(v a:ℝ)^2*T l v) (K l):=by
    by_cases hx:l∈i
    · unfold T K;simp only [if_pos hx,if_neg (show ¬(l=a∧a∉i) from by rintro ⟨rfl,h⟩;exact h hx),mul_zero]
      exact hasSum_zero
    unfold T K; simp_rw [if_neg hx]
    convert coin (polar h (insert l i) j) (sign i l) (step l) a using 1
    rcases eq_or_ne l a with rfl|he
    · simp [hx]
    simp [he, Ne.symm he]
 have he:=hasSum_sum (s:=(Finset.univ:Finset Axis)) (fun i _=>ht i)
 unfold second
 have HH (v:Cover):col (lower o A) i j v=∑ l,T l v:=rim_primary h.same i j v
 simp_rw [HH,Finset.mul_sum];rw [he.tsum_eq,sum_eq_single_of_mem a (mem_univ a) (fun l _ hl=> show K l=0 by simp [K,hl])]
 by_cases hh:a∈i <;> simp [K,hh]

lemma charge_off (h:Pricing A σ C)(i j:Tablet):load (col (lower p A) i j) =0:=by
 unfold load;simp_rw [rim_secondary h.same];rw [Summable.tsum_finsetSum (f:=fun a v=>if a∈j then 0 else sign j a*(col A i (insert a j) (v-step a)-col A i (insert a j) v))]
 · apply sum_eq_zero; intro b _; split_ifs
   · simp
   let T:=col A i (insert b j)
   have hh : Summable T:=(col_pay h ..).1
   have hs : Summable fun x=>T (x-Lattice.step b):=(Equiv.subRight _).summable_iff.mpr hh
   rw [tsum_mul_left, hs.tsum_sub hh, show ∑' x, col A i _ (x-Lattice.step b)=∑' x,T x from (Equiv.subRight _).tsum_eq _]; simp [T]
 intro k _;split_ifs
 · exact summable_zero
 simpa [sub_eq_add_neg] using (Moment.balance h j i k (-Lattice.step k)).1

lemma picture_spark (hC:0≤C)(hs:0<σ)(hF:Cohort F)(h:Held (carpet (Tone I)) σ C F)(i j:Axis)(he:i≠j)(y:Tape 2 I):
  second (col (hum (picture I 2 F) y) {j} {j}) i = -2 * spectrum F (insert i {j}) (insert i {j}) y:=by
 rw [picture,patch_eval,show List.finRange 2=[o,p] from rfl,solve_head,solve_head,solve_empty]
 let A:= hum F y
 have hp:Pricing A σ C:=NextTo.unit hs hC hF h (by omega) _
 have hi:i∉({j}:Tablet):=by simpa
 rw [shaken (hp.smaller p),if_neg hi,charge_off hp,corner hp,if_neg hi]
 unfold spectrum
 let k:=sign {j} i
 calc
 _= -2*load (col A (insert i {j}) (insert i {j}))*k^2:=by unfold A k;ring
 _=_:=by rw [sq k,sign_sq,mul_one]
end YM.RG08.Rudder.Loop
