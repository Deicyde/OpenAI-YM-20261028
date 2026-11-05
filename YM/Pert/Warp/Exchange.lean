import YM.Pert.Warp.Symmetric
/-! Symmetric Stein deletion identity on complex linear probes (centered, law any Gaussian on finite-dimensional real E). Neither conditioning nor positive nondegeneracy. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Pert.Warp
open MeasureTheory ProbabilityTheory Function
variable {K : Type*} [RCLike K] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsGaussian μ]
variable {I I' J : Type*} [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] [Fintype J]

lemma packet_equiv (p : I→E→K) (s : I'≃I) : packet μ (p∘s)=packet μ p := by
  rw [packet_mean,packet_mean,price,kick,price,kick,Fintype.card_congr s];congr 1; apply congrArg (fun F:E→K=>∫ x,F x ∂μ); funext x; exact Equiv.prod_comp s (fun i=>p i x)
lemma pay_equiv (p : I→E→K) (s : I'≃I) (i j) : nullPay μ i j (p∘s) = nullPay μ (s i) (s j) p := by
  unfold nullPay; simp only [EmbeddingLike.apply_eq_iff_eq]; split; rfl
  apply congrArg (fun A : E→E→K => ∫ x,(∫ y,A x y ∂μ) ∂μ); funext x y
  unfold fake; convert! Equiv.prod_comp s (fun k => p k (if k∈({s i, s j}: Finset I) then x else y)) using 1
  simp only [Finset.mem_insert,Finset.mem_singleton,EmbeddingLike.apply_eq_iff_eq];rfl
lemma refund_equiv (p : I→E→K) (s : I'≃I) : refund μ (p ∘ s)=refund μ p := by
  simp only [refund,pay_equiv]
  calc _ = ∑ i:I', ∑ j:I, nullPay μ (s i) j p := Finset.sum_congr rfl fun i _ => Equiv.sum_comp s (fun j=>nullPay μ (s i) j p)
       _ = _ := Equiv.sum_comp s (fun i=>∑ j, nullPay μ i j p)
variable [DecidableEq J]
lemma charge_exact (F : I→E→L[ℝ] ℝ) (h : ∀ i,∫x,F i x ∂μ=0) : packet μ (fun i=>(F i : E→ℝ)) = refund μ (fun i=>(F i : E→ℝ)) := by
  let e := (Fintype.equivFin I).symm
  let P (i : I):= (F i : E→ℝ)
  let z (i : Fin (Fintype.card I)) (j : I) : ℝ := if e i=j then 1 else 0
  have he : charge P z = P ∘ e := by
    unfold charge; funext i x; simp [z,ite_mul]
  rw [←packet_equiv μ _ e, ←refund_equiv μ _ e]
  exact he ▸ packet_cancel μ F h z
lemma scan_linear (T : Finset I) (P : I → E →ℝ) : scan (K:=ℂ) μ T (fun i x=>(P i x)) = (scan μ T P:ℝ) := by
  unfold scan fake; simp_rw [←Complex.ofReal_prod,integral_complex_ofReal]
lemma packet_complex (P : I→E→ℝ) : packet (K:=ℂ) μ (fun i x=>(P i x)) = (packet μ P:ℝ) := by rw [packet,scan_linear,packet,nsmul_eq_mul,nsmul_eq_mul]; norm_cast
lemma null_complex (P : I→E→ℝ) (i j) : nullPay (K:=ℂ) μ i j (fun f x=>(P f x)) = (nullPay μ i j P:ℝ) := by unfold nullPay; split <;> simp [scan_linear]
lemma refund_complex (P : I→E→ℝ) : refund (K:=ℂ) μ (fun i x=>(P i x)) = (refund μ P:ℝ) := by unfold refund; simp only [null_complex,Complex.ofReal_sum]

def fee (p : I→E→K) (W : (I→ E→K)→K) (f : I→I) := (W (p∘f)) -- unused
lemma expand_packet (F : J→E→ℂ) (hF : ∀ j, Orb.Tame (F j)) (z : I→J→ℂ) (atom : ∀f:I→J, packet μ (F∘f)=refund μ (F∘f)) : packet μ (charge F z) = refund μ (charge F z) := by
  let P (f : I→J) := ∏ i,z i (f i)
  have e (t : Finset I) := scan_tab μ t F z hF
  have eq (i j:I) : nullPay μ i j (charge F z) = ∑ f:I→J, nullPay μ i j (F∘f)*P f := by
    dsimp only [nullPay,P]; by_cases h:i=j; · simp [h]
    simp only [if_neg h]; exact e _
  calc _ = ∑f:I→J, packet μ (F∘f)*P f := by simp only [packet,e,tab,P,nsmul_eq_mul,Finset.mul_sum,mul_assoc]
       _ = ∑f:I→J, refund μ (F∘f)*P f := by simp only [atom]
       _ = ∑ i:I,∑ j:I,∑ f:I→J, nullPay μ i j (F ∘ f)*P f := by
          dsimp only [refund];simp_rw [Finset.sum_mul];rw [Finset.sum_comm];exact Finset.sum_congr rfl fun i _=>Finset.sum_comm
       _ = _ := by simp_rw [←eq]; rfl
lemma symmetric_cancel (P : I→E→L[ℝ] ℂ) (hP : ∀ i,∫ x,P i x ∂μ=0) : packet μ (fun i=>(P i : E→ℂ))=refund μ (fun i=>(P i:E→ℂ)) := by
  classical
  let F (j : Bool × I) := (if j.1 then Complex.imCLM else Complex.reCLM).comp (P j.2)
  let G (j : Bool×I) := fun x=> (↑(F j x) : ℂ)
  have q (i : I) := price_tame μ (Orb.Tame.clm (P i))
  have hF (j) : ∫ x,F j x ∂μ=0 := by
    cases j with | mk b i=>
      cases b
      · exact (Complex.reCLM.integral_comp_comm (q i)).trans (by rw [hP i,map_zero])
      · exact (Complex.imCLM.integral_comp_comm (q i)).trans (by rw [hP i,map_zero])
  let z (i : I) (j : Bool×I) := if i=j.2 then (if j.1 then Complex.I else 1) else 0
  have e : charge G z = fun i=>(P i : E→ℂ) := by
    funext i x; rw [charge]; simp [F,z,G, Fintype.sum_prod_type,Fintype.sum_bool,ite_mul,Complex.imCLM_apply,Complex.reCLM_apply,mul_comm Complex.I,add_comm]
  rw [←e]; refine expand_packet μ G (fun i => (Orb.Tame.clm _).ofReal) z ?_; intro f
  let xj:=F ∘ f
  have eh := charge_exact μ xj (fun i=>hF (f i))
  change packet μ (fun i x=>((xj i x:ℝ):ℂ)) = refund μ (fun i x=>((xj i x:ℝ):ℂ))
  rw [packet_complex,refund_complex]; exact congrArg _ eh
lemma exchange_s (s : Finset I) (P : I→E→L[ℝ] ℂ) (hP : ∀ i∈s,∫x,P i x ∂μ=0) :
 s.card • kick μ s (fun i=>(P i:E→ℂ)) = ∑ i∈s,∑ j∈s.erase i, (∫ x,P i x * P j x ∂μ) * kick μ (s.erase i |>.erase j) (fun k=>(P k:E→ℂ)) := by
  let A := fun i:↥s=> (P i.val : E→ℂ)
  have H := symmetric_cancel μ (I:=↥s) (fun i=>P i.val) (fun i=>hP i i.property)
  have L : packet μ A = s.card • kick μ s (fun i=>(P i:E→ℂ)) := by
    rw [packet_mean, Fintype.card_coe]; apply congrArg; apply congrArg (fun v:E→ℂ => ∫x,v x ∂μ); funext x; exact Finset.prod_coe_sort s (fun i:I=>P i x)
  rw [show packet μ _ = packet μ A from rfl,L,refund] at H
  rw [H]
  have e (i j : ↥s) (h : i.val ≠ j.val) : nullPay μ i j A = (∫ x,P i x * P j x ∂μ)*kick μ (s.erase i |>.erase j) (fun k=>(P k:E→ℂ)) := by
    rw [nullPay,if_neg (fun h'=> h (congrArg Subtype.val h')),scan_exact]; have hi : i ∉ ({j}:Finset ↥s):= Finset.notMem_singleton.mpr (by simpa using h)
    simp only [kick,A,Finset.prod_insert hi,Finset.prod_singleton]
    apply congrArg (fun (v:E→ℂ)=> (∫x,P i x * P j x ∂μ) * ∫x,v x ∂μ)
    funext x; refine Finset.prod_bij (s:=({i,j}:Finset ↥s)ᶜ) (fun k _=>k.val) (fun k hk=>?_) (fun a _ b _ he=>Subtype.ext he) (fun k hk=>?_) (fun k hk=>?_) -- arg name? 
    · have hn := Finset.mem_compl.mp hk; simp at hn; simp only [Finset.mem_erase]; simpa using And.intro hn.2 (And.intro hn.1 k.property)
    · simp only [Finset.mem_erase] at hk; refine ⟨⟨k,hk.2.2⟩, ?_,rfl⟩; simp only [Finset.mem_compl, Finset.mem_insert,Finset.mem_singleton,not_or]; exact ⟨fun h=>hk.2.1 (congrArg Subtype.val h), fun h=>hk.1 (congrArg Subtype.val h)⟩
    · rfl
  rw [← Finset.sum_coe_sort s _]
  apply Finset.sum_congr rfl; intro i _
  rw [←Finset.sum_erase_add (h:=Finset.mem_univ i)]
  rw [show nullPay μ i i (p:=A)=0 from if_pos rfl,add_zero]
  refine Finset.sum_bij (fun j _ => j.val) (fun j hj=>?_) (fun a _ b _ he=>Subtype.ext he) (fun j hj=>?_) (fun j hj=>?_) 
  · apply Finset.mem_erase.mpr ⟨Subtype.val_injective.ne (Finset.ne_of_mem_erase hj), j.property⟩
  · rw [Finset.mem_erase] at hj; refine ⟨⟨j,hj.2⟩, ?_,rfl⟩; simp only [Finset.mem_erase,Finset.mem_univ,and_true];intro h; exact hj.1 (congrArg Subtype.val h)
  · exact e i j (Subtype.val_injective.ne (Finset.ne_of_mem_erase hj).symm)
end YM.Pert.Warp
