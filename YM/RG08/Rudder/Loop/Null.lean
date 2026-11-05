import YM.RG08.Rudder.Sym.Oaks

/-!
# Rank two: first moment zero on the link kernels, from per-leg closure and total
inversion. No silently ignored link-center phases.
-/
noncomputable section
namespace YM.RG08.Rudder.Loop
open scoped Topology BigOperators Classical ENNReal
open Forms Packets Finset Function Lattice Laurent Pert.Bulk Exterior AnalyticNext.QuarticMatch.BoxChain Symmetry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
local notation "o"=> (0:Fin 2)
local notation "p"=> (Fin.succ (0:Fin 1))
variable {I:Type} {F:Raw I 2}{σ C:ℝ}{A:ProductR}

/-- Percolor charge cancellation on each pair of displayed links. -/
lemma flux_zero (h:ClosedSlot A o)(hp:Pricing A σ C)(i:Axis)(j:Tablet) : load (col A {i} j)=0:=by
 have he:first (col (lower o A) ∅ j) i=0:=by
   unfold ClosedSlot at h
   simp [h,first,col]
 rw [obverse hp,if_neg (notMem_empty i)] at he
 exact (mul_eq_zero.mp (neg_eq_zero.mp he)).resolve_left (left_ne_zero_of_mul_eq_one (sign_sq ..))

/-- Exact Laurent coefficient under signed permutations. Positions shift by the separate
corner moves of the two rows. -/
lemma corner_lit (h:Symmetry.Cardinal F)(hp:Cohort F)(y:Tape 2 I)(s:Signed)(a b:Tablet)(v:Cover) :
 col (hum F y) a b v = toll s a * toll s b * col (hum F y) (marks s a) (marks s b) (s.act v + evil s b - evil s a) :=by
 let x:=place ((0,a):_×Tablet) (v,b)
 have hl:= (congrFun (h s) (lyre x y)).symm
 rw [col];unfold hum
 rw [hl,orbit_apply,levy, Fin.prod_univ_succ,Fin.prod_univ_one];congr 1
 have hw : markTape s (lyre x y)=lyre (place (s.act 0+evil s a,marks s a) (s.act v+evil s b,marks s b)) y:=by ext i:1;cases i using Fin.cases with
 | zero=>rfl
 | succ i=>rw [Subsingleton.elim i (0:Fin 1)];rfl
 rw [hw]
 change hum F y (place (s.act 0+evil s a,marks s a) (s.act v+evil s b,marks s b))=_ -- definitional issues tail constant on Fin1
 rw [prices (show Cohere (hum F y) from fun t w=>hp t (lyre w y)),Signed.act_zero,zero_add];rfl

lemma orbit_load (h:Symmetry.Cardinal F)(hp:Cohort F)(y:Tape 2 I)(s:Signed)(a b:Tablet):
 load (col (hum F y) a b) = toll s a * toll s b * load (col (hum F y) (marks s a) (marks s b)):=by
 let H:Equiv.Perm Cover:=(Signed.actEquiv (R:=ℤ) s).toEquiv.trans (Equiv.addRight (evil s b -evil s a))
 let f:=col (hum F y) (marks s a) (marks s b)
 have he:col (hum F y) a b=fun v=>toll s a*toll s b*f (H v):=by
   funext v;rw [corner_lit h hp y s];change _ = _*(col (hum F y) _ _ (s.act v + (evil s b-evil s a)))
   congr 2;abel
 rw [load,he,tsum_mul_left,H.tsum_eq];rfl

def inversion:Signed:=⟨Equiv.refl _,fun _=>true⟩
lemma invert_slot (i:Axis):toll inversion {i}=-1 ∧ marks inversion {i}={i} ∧ evil inversion {i}= -step i:=by simp [toll_slot,inversion,Symmetry.spin,marks,evil,stub]
lemma inverted (v:Cover): inversion.act v=-v:=by ext i;simp [inversion,Signed.act]

lemma corner_mirror (h:Symmetry.Cardinal F)(hp:Cohort F)(y:Tape 2 I)(i j:Axis)(v:Cover):
  col (hum F y) {i} {j} v=col (hum F y) {i} {j} (step i-step j-v):=by
 calc
  _ = toll inversion {i} * toll inversion {j} * col (hum F y) (marks inversion {i}) (marks inversion {j}) (inversion.act v + evil inversion {j} - evil inversion {i}):= corner_lit h hp ..
  _ = _:=by
    rw [(invert_slot i).1,(invert_slot i).2.1,(invert_slot i).2.2,(invert_slot j).1,(invert_slot j).2.1,(invert_slot j).2.2,inverted]
    rw [show -v+-step j-(-step i)=step i-step j-v from by abel];norm_num

lemma pointNull {f:Cover→ℝ}{w:Cover}(h:Moment f)(he:∀ z,f z=f (w-z))(hh:load f=0)(i:Axis):first f i=0:=by
 let T:Equiv.Perm Cover:=(Equiv.neg _).trans (Equiv.addRight w)
 have ht(v:Cover):T v=w-v:=by change -v+w=_;abel
 have H:first f i=(∑' z:Cover, ((w-z) i :ℝ)*f z):=by
   rw [first,←T.tsum_eq];apply tsum_congr; intro z;rw [ht,←he]
 simp_rw [Pi.sub_apply,Int.cast_sub,sub_mul] at H
 rw [(h.1.mul_left (w i:ℝ)).tsum_sub (h.2 i),tsum_mul_left,show ∑'z,f z=0 from hh,show (∑' z:Cover,(z i:ℝ)*f z)=first f i from rfl] at H
 linarith

theorem paidPole (hc : Symmetry.Cardinal F)(hp:Cohort F)(hg:Graded F 1)(hh:Closing F)(hV:Held (carpet (Tone I)) σ C F)(hs:0<σ)(hC:0≤C):FirstNull (n:=1) F:=by
 have h:=NextTo.unit hs hC hp hV (by omega)
 intro y a b j
 by_cases he:a.card=1∧b.card=1
 · obtain ⟨⟨i,rfl⟩,i',rfl⟩:=show (∃ i,a={i}) ∧ ∃ i,b={i} from ⟨card_eq_one.mp he.1,card_eq_one.mp he.2⟩
   exact pointNull (col_pay (h y) ..) (corner_mirror hc hp y i i') (flux_zero (hh y o) (h y) i {i'}) _
 · have hu (v:Cover):col (hum F y) a b v=0:=by
     rcases not_and_or.mp he with he|he
     · exact hg y o _ he
     exact hg y p _ he
   unfold first;simp [hu]
end YM.RG08.Rudder.Loop
