import YM.RG08.Lyt.Supplies
/-! # Construct path curvature lifts deterministically on infinite cover

 Strip3 uses elementary cubical homotopy instead of lift selection. No cochains identified modulo winding. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Dart
open Function Lattice Wilson Exterior Laurent Work.F08 RG Next.Free Bloch Stationary Finset Filter
open UVExt.Paths Push.AbsoluteSums Quire Vale
open scoped Topology BigOperators ContDiff Classical
variable {E : Type}[NormedAddCommGroup E][NormedSpace ℝ E]{W:Type}{r i k:ℕ}{σ B:ℝ}
abbrev Fleck := ℝ × Face ℤ
-- signed quadrants, weights one/zero and connectors true. ℤ faces, no stage costs yet

def corner (F:Links ℤ ℝ)(p:Face ℤ):= F (p.1+step p.2.val.1,p.2.val.2) - F (p.1,p.2.val.2) - (F (p.1+step p.2.val.2,p.2.val.1)-F (p.1,p.2.val.1))
def raster (F:Links ℤ ℝ)(l:List Fleck):ℝ:= (l.map (fun i=> i.1*corner F i.2)).sum
lemma link_app (F:Links ℤ E)(x:Cover)(a b:Walk): linkSum F x (a++b)=linkSum F x a+linkSum F (stop x a) b:= by
   induction a generalizing x with
   | nil=> simp [linkSum,stop]
   | cons d t ih=> rw [List.cons_append,stop,linkSum,linkSum,ih, add_assoc]
lemma size_vec (x:Step): size (x.vec:Cover)=1:= by
   have hx (i:Axis): size (step i:Cover)=1:= by unfold size; rw [sum_eq_single_of_mem i (mem_univ _)]; simp; intro j _ h; simp [step,h]
   rcases x with ⟨i,h|h⟩; exact hx i; exact (size_neg (step i) : size (-step i:Cover)=_).trans (hx i)
lemma stop_size (x:Cover)(a:Walk):size (stop x a) ≤ size x+a.length:= by induction a generalizing x with
   | nil=> simp [stop]
   | cons i l ih=>
     unfold stop; have hv:size (x+i.vec)≤size x+1:= (size_add x (i.vec:Cover)).trans (by rw [size_vec]); simp only [List.length_cons]; exact (ih _).trans (by omega)

lemma rise_one (i:Axis)(a:ℤ)(x:Cover)(F:Links ℤ E): linkSum F x (straight i (a+1)) - linkSum F x (straight i a)= F (stop x (straight i a),i):= by
   rcases le_or_gt 0 a with h|h
   · have hh : straight i (a+1)=straight i a ++ [posDir i] := by
        unfold straight; rw [show decide (a+1<0)=false from decide_eq_false (by omega),show decide (a<0)=false from decide_eq_false (by omega),show (a+1).natAbs=a.natAbs+1 from (by omega),List.replicate_succ']; rfl -- lemma
     rw [hh, link_app]; simp only [linkSum,posDir,Step.used,Bool.false_eq_true,↓reduceIte,add_zero]; abel
   have hh : straight i a=straight i (a+1) ++ [negDir i]:= by
       unfold straight; by_cases hp:a+1=0
       · rw [hp,show a= -1 by omega]; decide +revert
       rw [show decide (a+1<0)= true from decide_eq_true (by omega),show decide (a<0)=true from decide_eq_true h,show a.natAbs=(a+1).natAbs+1 from (by omega), List.replicate_succ']; rfl
   rw [hh,link_app]; let y:=stop x (straight i (a+1)); have hx: stop x (straight i (a+1) ++ [negDir i])= y-step i:= by rw [stop_append]; change y+ -step i=y-step i; abel
   rw [hx]; simp only [linkSum,negDir,Step.used,↓reduceIte,add_zero]; change _-( _ + -F (y-step i,i))=_; abel

lemma square_strip (i:Axis)(x:Cover)(w:Walk)(he:∀ d∈w,i<Step.dir d):∃ F: List Fleck,(F.length ≤ w.length)∧ (∀ v∈F, ‖v.1‖≤1∧size v.2.1≤ size x+w.length)∧ ∀ P:Links ℤ ℝ,
     P (stop x w,i) -(P (x,i) +linkSum P (x+step i) w-linkSum P x w)=raster P F:= by
   induction w generalizing x with
   | nil=> exact ⟨[],Nat.zero_le _,fun _ h=> False.elim (List.not_mem_nil h),fun P=>by simp [raster,linkSum,stop]⟩
   | cons b u ih=>
     obtain ⟨L,hL,hl,H⟩:=ih (x+b.vec) (fun d hd=>he d (List.mem_cons_of_mem _ hd))
     have h': size (x+b.vec) ≤ size x+1:= (size_add x (b.vec:Cover)).trans (by rw [size_vec])
     have hs(v)(hp:v∈L): ‖(v:Fleck).1‖ ≤1 ∧ size v.2.1≤ size x+(b::u).length:= ⟨(hl _ hp).1,(hl _ hp).2.trans (by simp only [List.length_cons]; omega)⟩
     have hb:= he b List.mem_cons_self
     obtain ⟨a,h|h⟩:= b
     · let p:Fleck:= ⟨-1,x,⟨(i,a),hb⟩⟩; refine ⟨p ::L,by simp [hL],fun v hv=>?_ ,fun P=>?_⟩
       · rw [List.mem_cons] at hv; cases hv; subst v; simp [p]; exact hs _ ‹_›
       have he:stop x (posDir a::u)=stop (x+step a) u:=rfl
       simp only [raster,corner,p,linkSum,stop,Step.vec,Step.used,Bool.false_eq_true,↓reduceIte,List.map_cons,List.sum_cons]; have hP:= H P; change P (stop (x+step a) u, i) - (P (x+step a,i)+linkSum P (x+step a+step i) u - linkSum P (x+step a) u)=_ at hP; rw [add_right_comm x (step i)]; unfold raster corner at hP; linarith
     let p:Fleck:= ⟨1,x-step a, ⟨(i,a),hb⟩⟩; refine ⟨p::L,by simp [hL],fun v hv=>?_ ,fun P=>?_⟩
     · rw [List.mem_cons] at hv; obtain h|h:=hv; subst v; constructor; simp [p]; exact (by simpa [Step.vec,p,sub_eq_add_neg] using h':size (x-step a) ≤ size x+1).trans (by simp); exact hs _ ‹_›
     simp only [raster,corner,p,linkSum,stop,Step.vec,Step.used,↓reduceIte,List.map_cons,List.sum_cons]; have hp:= H P; simp only [Step.vec, ↓reduceIte,raster,corner] at hp; simp only [← sub_eq_add_neg] at *; rw [sub_add_cancel, add_sub_right_comm (x) (step i) (step a)]; linarith

def axesOrd:=Equiv.refl Axis
private lemma splitted (i:Axis) : ∃ a b:List Axis, allAxes axesOrd= a ++ i::b ∧ (∀ j∈a,j < i) ∧ (∀ j∈b, i<j) := by
   fin_cases i
   · exact ⟨[],[1,2,3],by decide⟩
   · exact ⟨[0],[2,3],by decide⟩
   · exact ⟨[0,1],[3],by decide⟩
   exact ⟨[0,1,2],[],by decide⟩
lemma proceed (i:Axis)(x: Cover): ∃ P Q:Walk,
   Lattice.route 0 x axesOrd=P++straight i (x i)++Q ∧ Lattice.route 0 (x+step i) axesOrd=P++straight i (x i+1)++Q ∧ (∀ d∈Q,i<Step.dir d):= by
    obtain ⟨a,b,hh,hx,ht⟩:=splitted i
    refine ⟨axisRoute 0 x a,axisRoute 0 x b,?_,?_,?_⟩
    · simp only [Lattice.route,hh,List.flatMap_append,axisRoute,List.flatMap_cons,Pi.zero_apply,sub_zero,List.append_assoc]
    · have hp (l:List Axis)(he:∀ j∈l,j≠i): axisRoute 0 x l=axisRoute 0 (x+step i) l:= by
          induction l with
          | nil=> rfl
          | cons j l ih=> rw [show axisRoute 0 x (j::l)=straight _ _ ++ axisRoute 0 x l from rfl,show axisRoute 0 (x+step i) (j::l)=straight _ _ ++ axisRoute 0 (x+step i) l from rfl,ih (fun p hp=> he p (List.mem_cons_of_mem _ hp)),Pi.add_apply]; simp [step,he j List.mem_cons_self]
      rw [Lattice.route, hh, hp a (fun j h=>(hx j h).ne), hp b (fun j h=>(ht j h).ne'),axisRoute_append]
      simp [axisRoute,step]
    intro d hd; obtain ⟨j,hj,h⟩:= List.mem_flatMap.mp hd
    exact (by have hp:= List.eq_of_mem_replicate h; rw [hp]; exact ht j hj)

def cable (z: Cover):= Lattice.route 0 z axesOrd
def budge (P:Links ℤ ℝ)(y:Cover):= linkSum P 0 (cable y)
lemma budge_spike (x:Cover)(i:Axis):∃ P:List Fleck,P.length ≤ size x ∧ (∀ v∈P, ‖v.1‖ ≤ 1∧ size v.2.1 ≤ size x) ∧ ∀ U:Links ℤ ℝ, U (x,i)-(budge U (x+step i)-budge U x)=raster U P:=by
    obtain ⟨a,b,hp,h,hL⟩:= proceed i x
    let z:=stop (0:Cover) (a++straight i (x i)); let y:= stop (0:Cover) a
    obtain ⟨F,H,hF,hX⟩:= square_strip i z b hL
    have he: (cable x).length=size x:= by unfold cable; rw [route_length,sub_zero] -- find ns
    have hh:(a++straight i (x i)).length + b.length=size x:= by rw [← he]; unfold cable; rw [hp]; simp [add_assoc]
    have hz:size z≤(a++straight i (x i)).length:= (stop_size 0 _).trans (by simp [size])
    refine ⟨F,by omega,fun v hv=> ⟨(hF _ hv).1, (hF _ hv).2.trans (by omega)⟩,fun U=>?_⟩
    have ht : stop y (straight i (x i+1))=z+step i:= by unfold z y; rw [stop_append,straight_stop,straight_stop,add_smul,one_smul]; abel
    have hv:stop z b=x:=by unfold z; rw [← stop_append,← hp,route_end]
    have hu:= rise_one i (x i) y U; have hh:= hX U; rw [hv] at hh
    unfold budge cable; rw [hp,h]; simp_rw [link_app,stop_append]; unfold y at ht hu; let K:= stop y (straight i (x i)); rw [ht]; have hk:K=z:= (stop_append ..).symm; change _-_= U (K,i) at hu; rw [hk] at hu; rw [show stop (stop (0:Cover) a) (straight i (x i))=z from hk]; linarith
end YM.RG08.Dart
