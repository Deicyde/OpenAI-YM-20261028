import YM.MergeProof.Hibiki
import YM.MergeProof.Jasper
import YM.MergeProof.Tally
import YM.Next.RANK.Evaluation
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Next.Rank Edition Baler Value Glyph Thirst Alarm Push GridApprox.Nil
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V] (o: V→Site n)
variable (w:V→ℝ){u v e:ℝ}{P:BudgetPoint} (F:Support n→ Config G n→veil V)(K:Box n → Config G n→veil V)
-- actual families
lemma stokes (hp:∀ i,Burns o i (F i) P.threshold ∧ ∀ U,rises (F i U))(he:Towed w id F P.B e u)(hw:∀ i,0<w i):∃ (ι:Type) (_: Fintype ι)(A:ι→SourceAt G o), Unpacks A P w e u ∧ (∀ j,2 ≤ (A j).fires.val.card) ∧ ∀ U, ∑ j,(A j).amount P.threshold U= ∑ i,F i U:=by
   let Y(i:Support n) (t:modes V):Prop:= 2 ≤ t.val.card ∧ t.val.image o ⊆ i
   let X:= Glide (Support n) Y
   letI: Fintype X:= inferInstanceAs (Fintype (Glide (Support n) Y))
   let f (i:X) U:= (F i.val.1 U).part i.val.2
   have hF (i:X):∃ A:SourceAt G o,A.extent=i.val.1∧A.fires=i.val.2∧∀ U,A.amount P.threshold U=Poly.send i.val.2 (f i U):=by
      let v:=F i.val.1; let T:=i.val.2; let K:= hp i.val.1|>.1
      obtain ⟨L,hL,h,H,hQ⟩:= tofu P.threshold i.val.1 (f i) (K.me _) (fun U V hu hi=> congr_arg (Poly.part · T) (K.home _ _ hu hi)) (fun k U=>congr_arg (Poly.part · T) (K.turns k U))
      refine ⟨⟨i.val.1,T,card_pos.mp (Nat.lt_of_lt_of_le (by decide:0<2) i.property.1),fun j hj=> i.property.2 (mem_image_of_mem o hj),L,hL,h,H⟩,rfl,rfl,fun U=>?_⟩
      unfold SourceAt.amount; congr 1
      by_cases hh: Healthy P.threshold i.val.1 U; rw [masked_eq _ _ _ _ hh]; exact hQ _ hh
      rw [masked_ne _ _ _ _ hh]; unfold f; rw [not_not.mp (mt (K.permits U) hh)]; rfl
   choose A hx hs hU using hF
   obtain ⟨a,ha,hP⟩:= guide (S:=Support n) (p:=Y) id F he (fun _ _ h=>h.2) hw
   refine ⟨X,inferInstance,A, ⟨a,fun i=> ⟨(ha _).1,fun U h'=> by rw [hU]; exact ha ..|>.2 U⟩,?_⟩,fun j=> (hs j).symm ▸ j.property.1, fun U=>?_⟩ -- edit
   · simp_rw [hs,hx]; exact hP
   have hc i:F i U=∑ j:X, (if j.val.1=i then (A j).amount P.threshold U else 0):=by
      simp_rw [hU]; convert (rake F (p:=Y) (fun i t ⟨U,h⟩=>⟨(hp i).2 U _ h,(hp i).1.place _ _ h⟩) U i).symm using 2; congr!
   simp_rw [hc]; rw [sum_comm]; simp
lemma knuckle (hp:∀ i,Flow o i (K i) P.threshold ∧ ∀ U,rises (K i U))(he:Towed w Prod.fst K P.B e u)(hw:∀ i,0<w i):∃ (ι:Type) (_:Fintype ι) (A:ι→Lifted G o P.threshold), Unfold A w e u (p:=P) ∧ (∀ j,2 ≤ (A j).fires.val.card)∧ ∀ i:Box n,∀ U, K i U=∑ j,(if (attached (A j)).val=i then (A j).amount U else 0) :=by
   let Y (i:Box n)(t:modes V):Prop:= Sure i∧2 ≤ t.val.card∧ t.val.image o⊆ i.1
   let X:=Glide (Box n) Y; letI:Fintype X:= inferInstanceAs (Fintype (Glide (Box n) Y))
   let F (i:X) U:= (K i.val.1 U).part i.val.2
   let A(j:X) : Lifted G o P.threshold:= ⟨j.val.1.1,j.val.1.2,j.property.1.1,j.property.1.2,j.val.2,(fun i hi=> j.property.2.2 (mem_image_of_mem o hi)),F j,(hp j.val.1).1.me _, (fun U hi=> (hp j.val.1).1.permits U (fun he=>hi (by unfold F; rw [he]; rfl))|>.1),fun U V h ht=> congr_arg (Poly.part · _) ((hp _).1.home _ _ h ht),fun k U=>congr_arg (Poly.part · _) ((hp _).1.turns k U)⟩
   obtain ⟨a,ha,hP⟩:= guide Prod.fst K (p:=Y) he (fun i t h=> h.2.2) hw
   refine ⟨X,inferInstance,A,⟨a,fun i=> ⟨(ha i).1,fun U=> (Poly.solo ..).symm.trans_le (ha i|>.2 U)⟩,hP⟩,fun i=>i.property.2.1,fun i U=>?_⟩
   convert (rake K (p:=Y) (fun j t ⟨U,h⟩=>⟨(hp j).1.permits U (fun he=> h (by rw [he];rfl))|>.2,(hp j).2 U t h,(hp j).1.place _ _ h⟩) U i).symm using 2; congr!; rfl
end YM.MergeProof.Accent
