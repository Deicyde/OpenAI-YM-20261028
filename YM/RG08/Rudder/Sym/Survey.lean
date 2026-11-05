import YM.RG08.Rudder.Sym.Axes

noncomputable section
namespace YM.RG08.Rudder.Symmetry
open scoped Topology BigOperators Classical ENNReal
open Forms Packets Finset Function Lattice Pert.Bulk Exterior Laurent
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I:Type}{n:ℕ}

lemma slot (s:Signed)(i:Axis) : s.act (step i:Cover)= if s.flip i=true then -step (s.perm i) else step (s.perm i):=by
 ext j
 obtain ⟨a,rfl⟩:=s.perm.surjective j
 rw [Signed.act_at];by_cases he:a=i <;> cases hk:s.flip a <;> cases hh:s.flip i <;> simp_all

private lemma dimension (s:Signed)(x:Cover):length (s.act x)=length x:=by
 unfold length Laurent.size
 congr 1
 rw [←Equiv.sum_comp s.perm fun i=>(s.act x i).natAbs]
 apply sum_congr rfl; intro i _;rw [Signed.act_at]; cases s.flip i <;> simp

def stub (s:Signed)(i:Axis):Cover:=if s.flip i then -step (s.perm i) else 0
def evil (s:Signed)(T:Tablet):Cover:=∑ i∈T,stub s i
lemma evil_double (s t:Signed)(T:Tablet) : evil (s*t) T=s.act (evil t T)+evil s (marks t T):=by
 unfold evil marks
 rw [Finset.sum_image t.perm.injective.injOn,show s.act (R:=ℤ)=(s.actEquiv (R:=ℤ)) from rfl,map_sum,←sum_add_distrib];apply sum_congr rfl;intro i _
 change stub (s*t) i= s.act (stub t i)+stub s (t.perm i)
 unfold stub; rw [Signed.mul_flip,Signed.mul_perm_apply]
 cases hh:t.flip i<;>cases ht:s.flip (t.perm i) <;> simp [ht,Signed.act_neg,slot]

lemma evil_charge(s:Signed)(T:Tablet):length (evil s T) ≤4 :=by
 have he(i:Axis):length (stub s i) ≤1:=by
   unfold stub;split
   · rw [length_neg,length_step]
   simp [length,Laurent.size]
 have hf(R:Tablet):length (evil s R) ≤ R.card:=by
    induction R using Finset.induction_on with
    | empty=>simp [evil,length,Laurent.size]
    | @insert i R hi ih=>rw [Finset.card_insert_of_notMem hi,Nat.cast_add,Nat.cast_one,evil,sum_insert hi];apply (length_add ..).trans;rw [add_comm (R.card:ℝ)];exact add_le_add (he i) ih
 exact (hf T).trans (by exact_mod_cast (show T.card≤4 by simpa [Axis] using Finset.card_le_univ T))

def markCell (s:Signed)(x:Market (Tone I)):Market (Tone I) := (s.act x.1+evil s x.2.1, marks s x.2.1,x.2.2)
lemma markCell_double (s t: Signed)(x:Market (Tone I)):markCell s (markCell t x)=markCell (s*t) x:=by simp [markCell,evil_double,Signed.act_mul,marks_double,add_assoc]
lemma markCell_one (x:Market (Tone I)):markCell 1 x=x:=by simp [markCell,marks,evil,stub]
lemma markCell_step (s:Signed)(x:Market (Tone I))(v:Cover):markCell s (pass v x)=pass (s.act v) (markCell s x):=by simp [pass,markCell,add_right_comm]

def markEquiv(s:Signed):Equiv.Perm (Market (Tone I)):=⟨markCell s,markCell s⁻¹,fun x=>by rw [markCell_double,inv_mul_cancel,markCell_one],fun x=>by rw [markCell_double,mul_inv_cancel,markCell_one]⟩
def markTape(s:Signed):Equiv.Perm (Tape n (Market (Tone I))):=Equiv.arrowCongr (Equiv.refl _) (markEquiv s)
lemma markTape_apply(s:Signed)(x:Tape n (Market (Tone I))):markTape s x= markCell s ∘ x:=rfl

def levy(s:Signed)(x:Tape n (Market (Tone I))):=∏ i,toll s (x i).2.1
lemma levy_double (s t:Signed)(x:Tape n (Market (Tone I))): levy (s*t) x=levy t x * levy s (markTape t x):=by unfold levy;rw [←Finset.prod_mul_distrib];simp_rw [toll_double];rfl
lemma levy_normal(s:Signed)(x:Tape n (Market (Tone I))):|levy s x|=1:=by simp only [levy,Finset.abs_prod,toll_normal,prod_const_one]

def orbit (s:Signed):Raw I n→ₗ[ℝ] Raw I n where
 toFun F:=fun x=>levy s x * F (markTape s x)
 map_add' x y:=by ext i;simp [mul_add]
 map_smul' x y:=by ext i;simp [mul_left_comm]
lemma orbit_apply (s:Signed)(F:Raw I n)(x:Tape n (Market (Tone I))):orbit s F x=levy s x * F (markTape s x):=rfl
lemma orbit_double (s t:Signed)(F:Raw I n): orbit t (orbit s F)=orbit (s*t) F:=by
 ext x;rw [orbit_apply,orbit_apply,orbit_apply,levy_double,←mul_assoc];congr 2
 ext i:1;exact markCell_double s t (x i)
lemma orbit_cohort {F:Raw I n}(h:Cohort F)(s:Signed):Cohort (orbit s F):=by
 intro b x
 have he:markTape s (sway b x)=sway (s.act b) (markTape s x):=funext fun i=>markCell_step ..
 rw [orbit_apply,he,h]; rfl

lemma orbit_radius (s:Signed)(x:Tape n (Market (Tone I))): (carpet (Tone I)).radius (markTape s x) ≤ (carpet (Tone I)).radius x + 8:=by
 let d:=carpet (Tone I)
 apply Ground.radius_le;· linarith [d.radius_nn x,(carpet (Tone I)).radius_nn x]
 intro i j
 have he:(markTape s x i).1-(markTape s x j).1=s.act ((x i).1-(x j).1)+(evil s (x i).2.1+-evil s (x j).2.1):=by rw [Signed.act_sub];change s.act (x i).1+evil s (x i).2.1-(s.act (x j).1+evil s (x j).2.1)=_;abel
 change length ((markTape s x i).1-(markTape s x j).1) ≤ d.radius _+8
 rw [he]; refine (length_add ..).trans ?_
 rw [dimension];apply (add_le_add (d.le_radius x i j) (length_add ..)).trans
 rw [length_neg]; linarith [evil_charge s (x i).2.1,evil_charge s (x j).2.1]

lemma orbit_held {F:Raw I n}{σ C:ℝ}(h:Held (carpet (Tone I)) σ C F)(hs:0≤σ)(s:Signed): Held (carpet (Tone I)) σ (C*Real.exp (8*σ)) (orbit s F):=by
 let d:=carpet (Tone I); let B:= ENNReal.ofReal (Real.exp (8*σ)); rw [ensign,mul_comm,ENNReal.ofReal_mul (Real.exp_pos _).le]
 intro i z
 calc
  _ ≤ ∑' x:Tape n (Market (Tone I)),B*Forms.row (mark d σ F) i (markCell s z) (markTape s x):=ENNReal.tsum_le_tsum fun x=>?_
  _ ≤ _:=by rw [ENNReal.tsum_mul_left,(markTape s).tsum_eq];exact mul_le_mul_right ((ensign.mp h) _ _) _
 have hw:d.radius x≤d.radius (markTape s x)+8:=by
    convert orbit_radius s⁻¹ (markTape s x) using 2
    ext i:1;exact ((markEquiv s).left_inv (x i)).symm
 unfold Forms.row
 rcases eq_or_ne (x i) z with he|he
 · rw [if_pos he,if_pos (show markTape s x i=markCell s z from congr_arg (markCell s) he)]
   unfold B mark;rw [mul_comm (ENNReal.ofReal _),←bill_add,orbit_apply]; apply bill_mono _ (by nlinarith)
   rw [abs_mul,levy_normal,one_mul]
 rw [if_neg he];exact zero_le

lemma graded_at {F:Raw I n}{r:Fin n→ℕ}(h:Graded F r){x:Tape n (Market (Tone I))}{i:Fin n}(hx:(x i).2.1.card≠r i):F x=0:=h (fun j=>(x j).2.2) i (fun j=>((x j).1,(x j).2.1)) hx
lemma orbit_graded {F:Raw I n}{r:Fin n→ℕ}(h:Graded F r)(s:Signed):Graded (orbit s F) r:=by
 intro y i x hx
 rw [hum,orbit_apply,graded_at h (i:=i),mul_zero];change (marks s _).card≠_;rw [marked_card]; exact hx
end YM.RG08.Rudder.Symmetry
