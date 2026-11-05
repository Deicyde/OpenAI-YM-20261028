import YM.RG08.Forms.Cot

noncomputable section
namespace YM.RG08.Forms
open Pert.Bulk Packets Finset Function
open scoped BigOperators Topology ENNReal Classical
set_option autoImplicit false

/-- Existential polynomial majorant (not taking powers to the number of scales; cost only
for fixed finite coupling/heat orders or occurrences). -/
def Wage (P:ℝ→ℝ) := ∃ (C:ℝ)(t:ℕ),0≤C ∧ ∀ x,1≤x → 0≤P x ∧ P x≤C*x^t

variable {P Q:ℝ→ℝ}
lemma Wage.nn (h:Wage P){x:ℝ}(hx:1≤x):0≤P x:=by have ⟨_,_,_,he⟩:=h;exact (he x hx).1
lemma Wage.constant (c:ℝ)(hc:0≤c): Wage fun _=>c:=⟨c,0,hc,fun _ _=>by simp [hc]⟩
lemma Wage.input : Wage fun x=>x:=⟨1,1,zero_le_one,fun x h=>by simpa using (by linarith:0≤x)⟩
lemma Wage.add (h:Wage P)(H:Wage Q):Wage (fun x=>P x+Q x):=by
 obtain ⟨a,n,ha,h⟩:=h;obtain ⟨b,m,hb,H⟩:=H
 refine ⟨a+b,n+m,by positivity,fun x hx=>⟨by dsimp only; linarith [(h x hx).1,(H x hx).1],?_⟩⟩
 dsimp only;rw [add_mul]; refine add_le_add ((h x hx).2.trans ?_) ((H x hx).2.trans ?_) <;> gcongr <;> omega
lemma Wage.mul (h:Wage P)(H:Wage Q):Wage (fun x=>P x*Q x):=by
 obtain ⟨a,n,ha,h⟩:=h;obtain ⟨b,m,hb,H⟩:=H
 refine ⟨a*b,n+m,by positivity,fun x hx=>?_⟩
 obtain ⟨he,hu⟩:=h x hx;obtain ⟨hf,hv⟩:=H x hx
 exact ⟨mul_nonneg he hf,(mul_le_mul hu hv hf (he.trans hu)).trans_eq (by rw [pow_add];ring)⟩
lemma Wage.sum {J:Type}(S:Finset J)(f:J→ℝ→ℝ)(h:∀ i∈S,Wage (f i)) : Wage (fun x=>∑ i∈S,f i x):=by
 induction S using Finset.induction_on with
 | empty=>simp only [sum_empty];exact constant _ le_rfl
 | @insert a s ha ih=>simp only [sum_insert ha]; exact (h a (mem_insert_self ..)).add (ih (fun _ hi=> h _ (mem_insert_of_mem hi)))

end YM.RG08.Forms
