import YM.TraceExtension.Filch.Herd
set_option autoImplicit false
/-! # elementary one-slot accounting. -/
noncomputable section
namespace YM.Trace.Filch
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Planned.PrimaryIntegral295 Drupes
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}
def MarksP (f:ℕ→ℝ):Prop:= (∀ i,0≤ f i) ∧ ∃ C:ℝ,∃ n:ℕ,1≤ C ∧ ∀ i, f i ≤ C*(1+i)^n
section
variable {F H:ℕ→ℝ}
lemma token (z:ℝ)(h:0 ≤ z): MarksP fun _=> z:= ⟨fun _=>h,z+1,0,by linarith,fun i=>by simp⟩
lemma poles : MarksP (fun x=>(x:ℝ)):=⟨fun _=>Nat.cast_nonneg _,1,1,le_rfl,fun i=>by simp⟩
lemma MarksP.le_one (h: MarksP F)(he:∀ i, H i ≤ F i)(hz:∀ i,0 ≤ H i): MarksP H:=by
    obtain ⟨_,A,n,hA,hh⟩:=h; exact ⟨hz,A,n,hA,fun i=> (he i).trans (hh i)⟩
lemma MarksP.pair (h:MarksP F)(he:MarksP H): MarksP fun i=> F i*H i:=by
    obtain ⟨hf,A,n,hA,ha⟩:=h; obtain ⟨hh,B,m,hB,hb⟩:=he
    refine ⟨fun i=>mul_nonneg (hf i) (hh i),A*B,n+m, one_le_mul_of_one_le_of_one_le hA hB,fun i=>?_⟩; apply (mul_le_mul (ha _) (hb _) (hh _) (by positivity)).trans_eq; rw[pow_add];ring
lemma MarksP.booth (h:MarksP F)(he:MarksP H): MarksP fun i=> F i+H i:=by
   obtain ⟨hf,A,n,hA,ha⟩:=h; obtain ⟨hh,B,m,hB,hb⟩:=he
   refine ⟨fun i=>add_nonneg (hf i) (hh i),A+B,n+m,by linarith only[hA,hB],fun i=>?_⟩
   have hz : 1 ≤ 1+(i:ℝ):=by simp
   rw[add_mul]; exact add_le_add ((ha _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz (by omega)) (by linarith only [hA]))) ((hb _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz (by omega)) (by linarith only [hB])))
lemma MarksP.tier (j:ℕ)(h:MarksP F): MarksP fun i=> F i^j:=by
   induction j with
   | zero=> simpa using token 1 (by norm_num)
   | succ n ih => simpa [pow_succ] using ih.pair h
lemma MarksP.composeM (k:ℕ)(h:MarksP F)(he:MarksP H):MarksP fun i=> composeCost k (F i) (H i):= ((token _ (Nat.cast_nonneg k.factorial)).pair h).pair (MarksP.tier _ ((token 1 zero_le_one).booth he))
lemma travel_non (G:Gauge)(k K)(C:ℝ)(h:0 ≤ C): 0 ≤ travelCost G k K C:=by unfold travelCost composeCost; positivity
lemma MarksP.travelM (G:Gauge)(k:ℕ)(v:ℕ→ℕ)(C:ℝ)(h:0≤ C)(hp: MarksP fun i=>(v i:ℝ)):
    MarksP fun i=>travelCost G k (v i) C:=by
    obtain ⟨A,hA,hv⟩:=Drupes.art C h G k
    exact (((token A (by linarith only[hA])).pair (((token 1 zero_le_one).booth hp).tier k))).le_one (fun i=> hv (v i)) (fun _=>travel_non _ _ _ _ h)
lemma mark_sum {I:Type}(s:Finset I)(f:I→ℕ→ℝ)(h:∀ i∈s,MarksP (f i)): MarksP fun z=>∑ i∈s,f i z:=by
   induction s using Finset.induction with
   | empty=> simpa using token 0 (by norm_num)
   | insert i s hi ih=>simp_rw[sum_insert hi];exact (h i (mem_insert_self ..)).booth (ih fun j hj=>h j (mem_insert_of_mem hj))
end
lemma covG(e:ℕ): MarksP (fun i=> (4*(i+e):ℕ)):=by
   push_cast; exact (token 4 (by norm_num)).pair (poles.booth (token e (by positivity)))
lemma market (G:Gauge)(C:ℝ)(h:0≤ C)(k:ℕ): MarksP (fun n=> swarm G k n C):=by
   let f:= MarksP.travelM G k _ C h (covG 1)
   let g:= token ((2:ℝ)^k) (by positivity)
   exact (g.pair ((g.pair f).pair (token C h))).pair f
end YM.Trace.Filch
