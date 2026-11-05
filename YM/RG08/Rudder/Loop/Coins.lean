import YM.RG08.Rudder.Loop.Lists

noncomputable section
namespace YM.RG08.Rudder.Loop
open scoped Topology BigOperators Classical
open Forms Packets Finset Function Lattice Laurent Pert.Bulk Exterior AnalyticNext.QuarticMatch.BoxChain
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
local notation "o"=> (0:Fin 2)
local notation "p"=> (Fin.succ (0:Fin 1))
variable {f g:Cover→ℝ}{q i:Axis}

lemma Moment.zero : Moment (0:Cover→ℝ):=⟨summable_zero,fun _=>by simp⟩
lemma Moment.add (h:Moment f)(H:Moment g):Moment (f+g):=⟨h.1.add H.1,fun i=>by simp_rw [Pi.add_apply,mul_add];exact (h.2 i).add (H.2 i)⟩
lemma Moment.neg (h:Moment f):Moment (-f):=⟨h.1.neg,fun i=>by simp_rw [Pi.neg_apply,mul_neg];exact (h.2 i).neg⟩
lemma Moment.sub (h:Moment f)(H:Moment g):Moment (f-g):=h.add H.neg
lemma Moment.scale (h:Moment f)(c:ℝ):Moment (fun i=>c*f i):= ⟨h.1.mul_left c,fun i=> ((h.2 i).mul_left c).congr fun j=>by dsimp only;ring⟩
lemma route_earn (v t:Cover): ((v q:ℝ)) = ((v+t:Cover) q:ℝ) - (t q:ℝ):=by simp
lemma Moment.west (h:Moment f)(t:Cover):Moment fun v=>f (v+t):=by
 let A:=Equiv.addRight t
 refine ⟨A.summable_iff.mpr h.1,fun q=> ((A.summable_iff.mpr (h.2 q)).sub (A.summable_iff.mpr (h.1.mul_left (t q:ℝ)))).congr (fun i=> ?_)⟩
 change ((i+t) q:ℝ)*_-(t q:ℝ)*_= _
 rw [←sub_mul, ←route_earn];rfl

lemma Moment.balance {A:ProductR}{σ C:ℝ}(h:Pricing A σ C)(T i:Flag)(a:Axis)(v:Cover) :
 Moment (fun x=> sign T a * (col A i (insert a T) (x+v)-col A i (insert a T) x)):= ((west (col_pay h ..) v).sub (col_pay h ..)).scale _
lemma first_sub (h:Moment f)(H:Moment g):first (f-g) q=first f q-first g q:=by unfold first;simp_rw [Pi.sub_apply,mul_sub];exact (h.2 q).tsum_sub (H.2 q)
lemma first_scale (r:ℝ):first (fun i=>r*f i) q = r*first f q:=by unfold first;rw [←tsum_mul_left];apply tsum_congr;intro b;ring
lemma first_shift (h:Moment f)(v:Cover):first (fun i=>f (i+v)) q=first f q-(v q:ℝ)*load f:=by
 unfold first load;rw [←tsum_mul_left,←(h.2 q).tsum_sub (h.1.mul_left _),← (Equiv.addRight v).tsum_eq (fun i=> (i q:ℝ)*f i -(v q:ℝ)*f i)];apply tsum_congr;intro i;change _=( ((i+v) q:ℝ)*f (i+v)-(v q:ℝ)*f (i+v));rw [←sub_mul,← route_earn]
lemma first_receipt (h:Moment f)(c:ℝ)(u:Cover):first (fun v=>c*(f (v+u)-f v)) q= (-c*(u q:ℝ))*load f:=by rw [first_scale];change c*first ((fun i=>f (i+u))-f) q=_;rw [first_sub (h.west u) h,first_shift h u];ring
lemma first_list {I:Type}(s:Finset I)(F:I→Cover→ℝ)(h:∀ i∈s,Moment (F i))(q:Axis):
 first (fun v=>∑ i∈s,F i v) q=∑ i∈s,first (F i) q:=by unfold first; simp_rw [Finset.mul_sum];exact Summable.tsum_finsetSum fun i hi=> (h i hi).2 q

/-- First moment of lowered form picks the candidate U zero mode directly, no convolution. -/
lemma corner {A:ProductR}{σ C:ℝ}(h:Pricing A σ C)(i j:Flag)(a:Axis) :
 first (col (lower p A) i j) a = if a∈j then 0 else sign j a * load (col A i (insert a j)):=by
 have he:col (lower p A) i j=fun v=>∑ a,if a∈j then 0 else sign j a*(col A i (insert a j) (v+-step a)-col A i (insert a j) v):=funext fun v=>by simpa [sub_eq_add_neg] using rim_secondary h.same i j v
 rw [he, first_list _ (fun k v=> if k∈j then 0 else sign j k * (col A i (insert k j) (v+-step k)-col A i (insert k j) v)) ?_ a,Finset.sum_eq_single_of_mem a (mem_univ a)]
 · split_ifs with ha
   · simp [first]
   rw [first_receipt (col_pay h ..)]
   simp
 · intro b _ hb; by_cases he:b∈j
   · simp [he,first]
   simp only [he,if_false]; rw [first_receipt (col_pay h ..)];simp [Ne.symm hb]
 intro i _;split_ifs
 · exact Moment.zero
 exact Moment.balance h ..

lemma obverse {A:ProductR}{σ C:ℝ}(h:Pricing A σ C)(i j:Flag)(a:Axis) :
 first (col (lower o A) i j) a = if a∈i then 0 else -(sign i a * load (col A (insert a i) j)):=by
 have he:=funext (rim_primary h.same i j)
 change col (lower o A) i j = fun v=>∑ a,if a∈i then 0 else sign i a*(col A (insert a i) j (v+step a)-col A (insert a i) j v) at he
 rw [he, first_list _ (fun k v=> if k∈i then 0 else sign i k * (col A (insert k i) j (v+step k)-col A (insert k i) j v)) ?_ a,Finset.sum_eq_single_of_mem a (mem_univ a)]
 · split_ifs with ha
   · simp [first]
   rw [first_receipt (col_pay h ..)];simp
 · intro b _ hb; by_cases he:b∈i
   · simp [he,first]
   simp only [he,if_false]; rw [first_receipt (col_pay h ..)];simp [Ne.symm hb]
 intro k _;split_ifs
 · exact Moment.zero
 let f:=col A (insert k i) j;exact ((Moment.west (f:=f) (col_pay h ..) (step k)).sub (col_pay h ..)).scale _

/- All first moments zero: in particular inversion-symmetric rank-2 link kernel with zero
integral (Ward) meets this (orientation origins must be included). -/
def Static (A:ProductR):Prop:=∀ i j a,first (col A i j) a=0
def Shade (A:ProductR):Prop:=∀ i j,load (col A i j)=0

theorem ninety {A:ProductR}{σ C:ℝ}(h:Pricing A σ C){r:ℕ}(hr:0<r)(H:Rank A p r)(ht:Static (lower p A)):Shade A:=by
 intro i j
 by_cases hu:j=∅
 · unfold load
   have hc(v):col A i j v=0:=H _ (by simp [place,hu];omega)
   simp [hc]
 obtain ⟨a,ha⟩:=Finset.nonempty_iff_ne_empty.mpr hu
 let J:=j.erase a
 have hj:a∉J:=by simp [J]
 have he:=ht i J a;rw [corner h,if_neg hj,insert_erase ha] at he -- J
 exact (mul_eq_zero.mp he).resolve_left (left_ne_zero_of_mul_eq_one (sign_sq J a))
end YM.RG08.Rudder.Loop
