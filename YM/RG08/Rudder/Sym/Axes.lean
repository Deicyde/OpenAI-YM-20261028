import YM.RG08.Rudder.FinalLegs

/-!
# Signed coordinate symmetry for vacuum lifts (rotations and initial-corner flags)
-/
noncomputable section
namespace YM.RG08.Rudder.Symmetry
open scoped Topology BigOperators Classical ENNReal
open Forms Packets Finset Function Lattice Pert.Bulk Exterior
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Tablet:=Finset Axis
def marks (s:Signed)(T:Tablet):Tablet:=T.image s.perm
lemma marked (s:Signed)(T:Tablet)(i:Axis): s.perm i∈marks s T ↔ i∈T:=by simp [marks,s.perm.injective.eq_iff]
lemma marked_card (s:Signed)(T:Tablet):(marks s T).card=T.card:=by rw [marks,Finset.card_image_of_injective _ s.perm.injective]
lemma marks_double (s t:Signed)(T:Tablet):marks s (marks t T)= marks (s*t) T:=by rw [marks,marks,Finset.image_image];rfl

def arrow (i j:Axis):ℝ:=if i<j then 1 else -1
lemma arrow_sq (i j:Axis):arrow i j ^ 2=1:=by unfold arrow;split<;>norm_num
lemma arrow_neg {i j:Axis}(h:i≠j):arrow j i = -arrow i j:=by
 rcases lt_or_gt_of_ne h with H|H
 · simp [arrow,H,not_lt_of_ge H.le]
 simp [arrow,H,not_lt_of_ge H.le]

def spin (s:Signed)(i:Axis):ℝ:=if s.flip i then -1 else 1
lemma spin_sq (s:Signed)(i:Axis):spin s i ^ 2=1:=by unfold spin;split<;>norm_num
lemma spin_double (s t:Signed)(i:Axis):spin (s*t) i=spin t i*spin s (t.perm i):=by
 unfold spin;rw [Signed.mul_flip];cases t.flip i <;>cases s.flip (t.perm i)<;>norm_num

/-- Only orient order-two flags by permutation. All unused higher flag-cardinalities do not
intertwine their own cell boundaries under this particular operator. -/
def address (s:Signed)(T:Tablet):ℝ:= if h:T.card=2 then let i:=plaqEquiv.symm ⟨T,h⟩; arrow (s.perm i.val.1) (s.perm i.val.2) else 1
lemma address_doublet (s:Signed){a b:Axis}(h:a≠b):address s {a,b}=arrow a b*arrow (s.perm a) (s.perm b):=by
 have H {a b:Axis}(hx:a<b):address s {a,b}=arrow a b*arrow (s.perm a) (s.perm b):=by
   have he:({a,b}:Finset Axis).card=2:=by simp [hx.ne]
   let k:Lattice.PlaqAxes:=⟨(a,b),hx⟩
   have hh:plaqEquiv k=⟨{a,b},he⟩:=rfl
   unfold address; rw [dif_pos he];simp only [←hh,plaqEquiv.symm_apply_apply]; simp only [k,arrow,hx,if_true,one_mul]
 rcases lt_or_gt_of_ne h with hx|hx
 · exact H hx
 rw [show ({a,b}:Finset Axis)={b,a} by ext;simp [or_comm],H hx,arrow_neg h, arrow_neg (s.perm.injective.ne h)];ring -- insert pair syntactic
lemma address_sq (s:Signed)(T:Tablet):address s T ^2 = 1:=by unfold address;split_ifs<;>simp [arrow_sq]
lemma address_dev (s t:Signed)(T:Tablet):address (s*t) T=address t T*address s (marks t T):=by
 by_cases h:T.card=2
 · obtain ⟨a,b,h1,rfl⟩:=card_eq_two.mp h
   rw [marks,Finset.image_insert,Finset.image_singleton,address_doublet (s*t) h1,address_doublet t h1,address_doublet s (t.perm.injective.ne h1),Signed.mul_perm_apply,Signed.mul_perm_apply]
   let x:=arrow (t.perm a) (t.perm b); have hh:x^2=1:=arrow_sq ..
   calc
    _ = arrow a b * arrow (s.perm (t.perm a)) (s.perm (t.perm b))*x^2:=by rw [hh,mul_one]
    _ = _:=by unfold x;ring
 simp [address,h,marked_card]

def toll (s:Signed)(T:Tablet):ℝ:=(∏ i∈T,spin s i)*address s T
lemma toll_slot (s:Signed)(i:Axis): toll s {i}=spin s i:=by simp [toll,address]
lemma toll_sq (s:Signed)(T:Tablet):toll s T^2=1:=by unfold toll;rw [mul_pow,address_sq,mul_one,←Finset.prod_pow];simp only [spin_sq,prod_const_one]
lemma toll_double (s t:Signed)(T:Tablet):toll (s*t) T=toll t T*toll s (marks t T):=by
 unfold toll; simp_rw [address_dev,spin_double, marks, Finset.prod_mul_distrib]
 rw [Finset.prod_image t.perm.injective.injOn];ring
lemma toll_normal (s:Signed)(T:Tablet):|toll s T|=1:=by have h:=toll_sq s T;nlinarith [sq_abs (toll s T),abs_nonneg (toll s T)]

lemma signal (i j:Axis): AnalyticNext.QuarticMatch.BoxChain.sign {i} j = if i<j then -1 else 1:=by unfold AnalyticNext.QuarticMatch.BoxChain.sign Exterior.parity Exterior.pre; by_cases h:i<j <;> simp [Finset.filter_singleton,h]

lemma toll_next (s:Signed){i j:Axis}(hi:j≠i):
   toll s {i} * AnalyticNext.QuarticMatch.BoxChain.sign {s.perm i} (s.perm j)*spin s j=AnalyticNext.QuarticMatch.BoxChain.sign {i} j * toll s (insert j {i}):=by
 have ht:toll s (insert j {i})=spin s j*spin s i*(arrow j i*arrow (s.perm j) (s.perm i)):=by simp only [toll, address_doublet s hi,prod_insert (by simpa: j∉({i}:Finset Axis)),prod_singleton]
 rw [toll_slot,ht,signal,signal]
 have he {a b:Axis}(h:a≠b): (if a<b then (-1:ℝ) else 1)= arrow b a:=by rw [arrow_neg h];unfold arrow;split<;>norm_num
 rw [he (s.perm.injective.ne (Ne.symm hi)),he (Ne.symm hi)]
 calc
 _=(spin s i * arrow (s.perm j) (s.perm i) * spin s j)*(arrow j i)^2:=by rw [arrow_sq,mul_one]
 _=_:=by ring
end YM.RG08.Rudder.Symmetry
