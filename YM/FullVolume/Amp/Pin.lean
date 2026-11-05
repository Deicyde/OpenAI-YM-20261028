import YM.FullVolume.Ray.Anchor
import Mathlib.Algebra.Group.ForwardDiff
/-! Mixed to pure ∆ stencil. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Amp
open Filter Function Finset Asymptotics
open scoped Topology BigOperators NNReal ENNReal ContDiff
variable {X Y I : Type*} [DecidableEq I][SeminormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y]
variable (s:Finset I)(u:I→X)(f:X→Y)(x:X){n:ℕ}
def signed (s:Finset I)(T:Finset I):ℝ:=(-1)^(s.card-T.card)
lemma unfoldP (F : Finset I → Y) {i:I}(h:i∉s): (∑ T ∈ (insert i s|>.powerset), signed (insert i s) T • F T)=(∑ T∈s.powerset,signed s T • (F (insert i T)-F T)):=by
  have hh t (ht:t∈s.powerset): i∉t:= fun hf=> h (mem_powerset.mp ht hf)
  rw [powerset_insert, sum_union, sum_image]; rotate_left
  · intro a ha b hb hu
    -- Insertion
    simpa [erase_insert (hh _ ha),erase_insert (hh _ hb)] using congr_arg (fun t:Finset I=>t.erase i) hu
  · rw [disjoint_left]; intros t ht hV
    obtain ⟨w,_,rfl⟩:= mem_image.mp hV
    exact hh _ ht (mem_insert_self ..)
  rw [← sum_add_distrib]; apply sum_congr rfl; intro t ht
  have hp:= card_le_card (mem_powerset.mp ht); rw [smul_sub,signed, signed, signed,card_insert_of_notMem h,card_insert_of_notMem (hh t ht),show s.card+1-(t.card+1)=s.card-t.card from (by omega),show s.card+1-t.card=s.card-t.card+1 from (by omega),pow_succ]; simp; abel

def block (s:Finset I)(u:I→X)(f:X→Y)(x:X):Y:= ∑ T∈ s.powerset,signed s T • f (x+∑ i∈T,u i)
lemma start : block ∅ u f x=f x:= by simp [block,signed]
lemma cons {i:I}(hi:i∉s): block (insert i s) u f x= block s u f (x+u i)-block s u f x:=by
  unfold block; rw [unfoldP _ _ hi, ← sum_sub_distrib]; apply sum_congr rfl; intro T h; rw [smul_sub,sum_insert (show i∉T from fun ht=> hi (mem_powerset.mp h ht)),add_assoc x]
lemma same {v:I→X}(h:∀ i∈s,u i=v i) : block s u f x=block s v f x:= by apply sum_congr rfl; intro T hT; exact congr_arg (fun a=>signed s T • f (x+a)) (sum_congr rfl (fun j hj=>h j (mem_powerset.mp hT hj)))
lemma rear (y:X): block s (fun _=>y) f x= (fwdDiff y)^[s.card] f x := by
  induction s using Finset.induction_on generalizing x with
  | empty=> rw [start]; rfl
  | insert a s h ih=>rw [cons _ _ _ _ h,ih,ih,card_insert_of_notMem h,Function.iterate_succ_apply']; rfl
-- pure weights = REAL
abbrev hat (n j:ℕ):ℝ:= (-1)^(n-j)* n.choose j
lemma face (y:X)(n:ℕ): (fwdDiff y)^[n] f x= ∑ j∈range (n+1), hat n j • f (x+(j:ℝ) • y):= by
  rw [fwdDiff_iter_eq_sum_shift]; apply sum_congr rfl; intro j hj; rw [← Int.cast_smul_eq_zsmul ℝ,Nat.cast_smul_eq_nsmul]; simp [hat]
lemma snow (x:X)(x':X)(c:ℝ): block s (fun i=>c • u i) f (x+c • x')= ∑ i∈s.powerset,signed s i • f (x+c • (x'+∑ j∈i,u j)):=by simp [block,smul_add,add_assoc, smul_sum]
section cancel
-- use indexed s, m=s.card and given bij or Fin n univ. Additivity later needs (j+1)= I size changed. generalized inject stamps.
variable (r:I→ℕ)(he:∀ i∈s,r i<s.card)(hu:∀ j,j<s.card→∃ i∈s,r i=j)
def stiff (i:I):ℝ:=( (s.card:ℝ) - r i)⁻¹
def spine (T:Finset I):X:=∑ i∈T, stiff s r i • u i
def leanW (T:Finset I):X:= ∑ i∈T, -(r i:ℝ) • stiff s r i • u i -- precedence
lemma pinned {i:I}(h:i∉s)(K:Finset I) : spine K u r (insert i s)= stiff K r i • u i+spine K u r s:=sum_insert h
include hu
lemma vacant {j:ℕ}(hj:j<s.card) : (∑ T∈s.powerset,signed s T • f (x+ leanW s u r T+(j:ℝ) • spine s u r T))=0:=by
  obtain ⟨a,ha,h⟩:= hu j hj
  let H(T:Finset I):= f (x+leanW s u r T +(j:ℝ) • spine s u r T)
  have hh t (ht:t∈(s.erase a|>.powerset)): H (insert a t)=H t:=by
    have hV:a∉t:= fun h=> notMem_erase _ _ (mem_powerset.mp ht h)
    unfold H leanW spine; rw [sum_insert hV,sum_insert hV,h, smul_add]; simp only [neg_smul]; congr 1; abel
  change (∑ T∈ _, _ • H T)=0
  have hp : (∑ T∈ s.powerset,signed s T • H T)= ∑ T∈(s.erase a).powerset,signed (s.erase a) T • (H (insert a T)-H T):=by simpa only [insert_erase ha] using unfoldP (s.erase a) H (notMem_erase a s)
  exact hp.trans (sum_eq_zero fun t ht=> by rw [hh t ht,sub_self,smul_zero])
omit hu
include he
lemma diagonal (T:Finset I) (ht:T∈s.powerset): leanW s u r T+(s.card:ℝ) • spine s u r T=∑ i∈T,u i:= by
  unfold spine leanW; rw [Finset.smul_sum,← sum_add_distrib]; apply sum_congr rfl; intro i hi
  have hp := sub_ne_zero_of_ne ((Nat.cast_lt.mpr (he i (mem_powerset.mp ht hi)): (r i:ℝ)<s.card).ne')
  unfold stiff; rw [← add_smul,add_comm,← sub_eq_add_neg,smul_smul,mul_inv_cancel₀ hp,one_smul]
include hu
-- equivalent stencil using t scaling
lemma spelled (x':X) (t:ℝ): block s (fun i=>t • u i) f (x+t • x')= ∑ T∈s.powerset, signed s T • (fwdDiff (t • spine s u r T))^[s.card] f (x+t • (x'+leanW s u r T)) := by
  simp_rw [face,smul_sum,smul_comm (signed ..)]
  rw [sum_comm,sum_range_succ,sum_eq_zero, zero_add]; swap
  · intro j hj; rw [←smul_sum]; suffices hp : (∑ T∈s.powerset, _ • f (x+t • (x'+leanW s u r T)+(j:ℝ) • t • spine s u r T))=0 by rw [hp,smul_zero]
    simpa only [smul_add,add_assoc,smul_comm t] using (vacant s u (fun z=> f (x+t • z)) x' r hu (mem_range.mp hj))
  simp [hat]; rw [snow s u _ x x']; apply sum_congr rfl; intro T h; rw [← diagonal s u r he T h]; simp only [smul_add,add_assoc,smul_comm t]
end cancel
end YM.FullVolume.Amp
