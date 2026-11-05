import YM.TraceExtension.Cask.Limbs
import YM.TraceExtension.Cask.Fleet
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Cask
open RG Lattice Ac MergeProof Finset MergeProof.Accent Marker MeasureTheory Wilson Push Function
open scoped Classical
variable {V L W:Type}[DecidableEq V][DecidableEq L][DecidableEq W]{n:Side}[Fintype V][Fintype L][Fintype W]{G:Gauge}{R:Rep G n}(C:TourC R V L W)
local notation "A"=> agency C
local notation "r!"=>R.p.B
local notation "N!"=>lance C
lemma loftPay (f:L→ℝ) (d u:ℝ)(a:ℕ)(hd:0≤d) (hu:4*u≤1)(hv:(Real.log 2) ≤ (a:ℝ))(ha:1 ≤ a)(hc:∀ i j,i≠j→64*R.p.B*a+2*R.p.B≤ separation (C.tie i) (C.tie j)) (hf:∀ i, 0 ≤ f i ∧ ∀ U, |C.long i U|≤ f i)(ht: Hit C.path R.p.B f (d+1) u) (i:PureC C)(U:Config G n)(v:Rain V G): ‖loft C i U v‖ ≤ 4*2^(deer C (C.path i.1)).card*f i.1 := by
    let t:=C.path i.1; let s:=i.2.val; let x:=tame C i U v; let y:= f i.1; let m:=deer C t;let k:=coverNumber R.p.B t; have hy:0 ≤ y:= (hf _).1; have he : s ⊆ m:= i.2.property.1
    have h(s):|cortex C i.1 U v s| ≤ 2*y:= (abs_sub ..).trans (by rw [two_mul]; exact add_le_add ((hf _).2 _) ((hf _).2 _))
    have hp : |x|≤2^m.card*(2*y):= calc
        _ ≤ ∑ t∈s.powerset,|((-1:ℝ)^((s \ t).card)* cortex C i.1 U v t)|:= abs_sum_le_sum_abs _ _
        _ ≤ ∑ t∈s.powerset,2*y:= sum_le_sum fun t _=>by simpa [abs_mul,abs_pow] using h t
        _ ≤ _:=by simp only[sum_const, card_powerset, nsmul_eq_mul, Nat.cast_pow,Nat.cast_ofNat];gcongr;norm_num
    have hR:y*Real.exp ((d+1)*k) ≤ u:=by
       obtain ⟨b,hb⟩:= i.2.property.2; have ht:= Extra.Multi.Budget.cap (ht (C.tie b)) {i.1}; simpa [if_pos (show C.tie b∈ C.path i.1 from (mem_filter.mp (he hb)).2)] using ht
    have hε : 0 ≤ u:= (mul_nonneg hy (Real.exp_pos _).le).trans hR; have hx: y ≤ u:= (le_mul_of_one_le_right hy (Real.one_le_exp (mul_nonneg (show 0 ≤ d+1 by positivity) (by positivity)))).trans hR
    have hk : |x| ≤ 1:=by
        by_cases hz: m.card ≤ 1
        · have hh: (2:ℝ)^m.card ≤ 2:=by simpa using pow_le_pow_right₀ (show 1 ≤ (2:ℝ) by norm_num) hz
          exact hp.trans ((mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ 2*y)).trans (by linarith only [hu,hx]))
        have hm: m.card*a ≤ k:=(mul_comm ..).trans_le (billgap a ha R.p.B R.p.B_pos C.tie m (by omega) (fun j _ k _=>hc j k) t (by intro x hx; obtain ⟨p,hp,rfl⟩:=mem_image.mp hx; exact (mem_filter.mp hp).2))
        have he: (2:ℝ)^m.card ≤ Real.exp ((d+1)*k):=by
           nth_rw 1 [show (2:ℝ)=Real.exp (Real.log 2) from (Real.exp_log (by norm_num)).symm]; rw [← Real.exp_nat_mul,Real.exp_le_exp]; have ht:= mul_le_mul_of_nonneg_left hv (show (0:ℝ)≤ m.card by positivity); have hm':(m.card:ℝ)*(a:ℝ)≤ k:=by exact_mod_cast hm
           nlinarith only [ht,hm',mul_nonneg hd (show (0:ℝ)≤ k by positivity)]
        exact hp.trans ((mul_le_mul_of_nonneg_right he (by positivity : 0 ≤ 2*y)).trans (by linarith only [hR,hu,hε]))
    unfold loft; split; swap; · rw [norm_zero]; exact mul_nonneg (by positivity) hy
    rw [Complex.norm_real]; exact (Real.abs_exp_sub_one_le hk).trans (by linarith only[hp])
lemma rashPay (f : Box n→ℝ)(hf : ∀ i,0≤ f i ∧ ∀ U,‖flore R i U‖ ≤ f i)(k:Axe C)(U:Config G n)(v:Rain V G): ‖rash C k U v‖≤2^(deer C k.1.val.1).card*f k.1.val:=by
   let m:=deer C k.1.val.1; let t:=k.2.val; let b:=f k.1.val;have hh: 0 ≤ b:= (hf _).1; have he:t⊆ m:= k.2.property
   unfold rash; split; swap; · rw [norm_zero]; positivity
   calc
     _ ≤ ∑ i∈t.powerset,‖(-1:ℂ)^((t \ i).card)*skin C k.1.val U v i‖:= norm_sum_le ..
     _ ≤ ∑ i∈t.powerset,b:= sum_le_sum fun i _=>by simp only[norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]; exact (hf _).2 _
     _ ≤ _:=by simp only[sum_const, card_powerset, nsmul_eq_mul, Nat.cast_pow,Nat.cast_ofNat]; change (2:ℝ)^t.card * b ≤ 2^m.card*b; gcongr; norm_num
end YM.Trace.Cask
