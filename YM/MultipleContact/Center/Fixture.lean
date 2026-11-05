import YM.MultipleContact.Center.Base

/-! Replacing a single cluster node in the product. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace YM.MultipleContact.Centered
open Set Filter Function Table Extraction Spec Drama Script Scene ScheduleRow Bunching
open March Joins
open scoped Classical ContDiff Topology BigOperators

variable {G:Gauge}{L:Register G}{S:Table L}
variable {b:ℕ}{n:Fin b→ℕ}[hn:∀i:Fin b,Inhabited (Fin (n i))](V:∀i:Fin b,Fin (n i)→S.Tag)(p:Fin b→March S)
  (q:∀i,(p i).Data)(z:Fin b→ E4)(x:∀i:Fin b,Fin (n i)→E4)(κ ε:ℝ)(ρ:Fin b → ℝ)(N:Lattice.Side)
namespace March
def fixture(i:Fin b): Grammar (Alpha S):= (Finset.univ.erase i).prod (fun i=>(p i).payload (V i) (z i) (x i) (q i))
def minorCharge(i:Fin b):= (Finset.univ.erase i).prod fun i=>(p i).credit (V i) ε (ρ i) (q i)
lemma plug_credit (i:Fin b):plainLoad p V ε ρ q=(p i).credit (V i) ε (ρ i) (q i) * minorCharge V p q ε ρ i:= by
       unfold plainLoad minorCharge; exact Eq.symm (Finset.mul_prod_erase Finset.univ (fun i:Fin b=>(p i).credit (V i) ε (ρ i) (q i)) (Finset.mem_univ i))
lemma plug_product (i:Fin b):work p V z x q = (p i).payload (V i) (z i) (x i) (q i)*fixture V p q z x i:=(Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
omit hn in
lemma minor_pos (i:Fin b)(h:∀i,0<ρ i):0< minorCharge V p q ε ρ i:=Finset.prod_pos fun i _=> (p i).credit_pos _ _ (ρ i) _ (h i)

private lemma eq_data {α : Sort _} (f:∀ p:March S,p.Data→α){x y:March S}(v:y.Data)(h:x=y):f x (h.symm ▸ v)=f y v:=by subst y;rfl
abbrev altered (i:Fin b)(v:March S):=(update p i v)
-- dependent update with data type changing.
def newData (i:Fin b){v:March S}(w:v.Data)(j:Fin b):(altered p i v j).Data := if h:j=i then
             (show v=altered p i v j from (by rw [altered,h,update_self])) ▸ w
          else (show p j=altered p i v j from (by rw [altered,update_of_ne h])) ▸ q j
set_option pp.all false in
lemma alt_product(i:Fin b)(v:March S)(t:E4)(u:Fin (n i)→E4)(w:v.Data): work (altered p i v) V (update z i t) (update x i u) (newData p q i w)= v.payload (V i) t u w * fixture V p q z x i:=by
        unfold work; rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),update_self,update_self]; unfold fixture; congr 1
        · change (update p i v i).payload (V i) t u (newData p q i w i)=_
          unfold newData; rw [dif_pos rfl]; exact eq_data (fun m:March S=>m.payload (V i) t u) w (update_self i v p) 
        apply Finset.prod_congr rfl; intro j hj
        have hj':j≠i:=Finset.mem_erase.mp hj|>.1
        rw [update_of_ne hj',update_of_ne hj']; change (update p i v j).payload _ _ _ _= _
        unfold newData; rw [dif_neg hj']; exact eq_data (fun m:March S=>m.payload (V j) (z j) (x j)) (q j) (update_of_ne hj' v p) 
lemma alt_credit(i:Fin b)(v:March S)(w:v.Data): plainLoad (altered p i v) V ε ρ (newData p q i w)= v.credit (V i) ε (ρ i) w * minorCharge V p q ε ρ i:=by
        unfold plainLoad; rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]; unfold minorCharge; congr 1
        · change (update p i v i).credit (V i) ε _ (newData p q i w i)=_
          unfold newData; rw [dif_pos rfl]; exact eq_data (fun m:March S=>m.credit (V i) ε (ρ i)) w (update_self i v p) 
        apply Finset.prod_congr rfl; intro j hj
        have hj':j≠i:=Finset.mem_erase.mp hj|>.1
        change (update p i v j).credit _ _ _ _=_
        unfold newData; rw [dif_neg hj']; exact eq_data (fun m:March S=>m.credit (V j) ε (ρ j)) (q j) (update_of_ne hj' v p) 
lemma march_strict (r:ℝ)(i:Fin b)(hi:(p i).toMode=.signed)(hc:(p i).allow N r (x i))(hr:0<r):(∀l j:Fin (n i),l≠j→ r/4<‖x i l-x i j‖)∧∀s:Fin (n i),‖x i s‖<2*N.val*r:=by
        cases h:p i <;> simp only [h,toMode,allow] at hi hc
        exacts [(Mode.noConfusion hi),(⟨hc.1,hc.2.1⟩),(⟨hc.1,hc.2.1⟩),(Mode.noConfusion hi)] -- order
lemma allow_large (i:Fin b)(d':ℕ){r:ℝ}(hr:0<r)(h:(p i).allow N r (x i)): (p i).allow (expand N d') r (x i):=by
        by_cases hp:(p i).toMode=.fused
        · have he :∃k,p i=.field k:=by cases heq:p i <;> (try exact ⟨_,rfl⟩) <;> simp [heq,toMode] at hp
          obtain ⟨w,hw⟩:=he; rw [hw]; trivial
        have h' (u:March S)(he:u.toMode≠.fused):True:=True.intro -- fix or remove
        have bounds(s:Fin (n i)) : ‖x i s‖ < 2*(expand N d').val*r:= by
             have hf:2*(N.val:ℝ)*r ≤ 2*((expand N d').val:ℝ)*r:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by change (↑(N.val):ℝ)≤ ((N.val*(d'+1):ℕ):ℝ); exact_mod_cast (le_mul_of_one_le_right (α:=ℕ) (show 0≤ N.val from Nat.zero_le _) (by omega: (1:ℕ) ≤ d'+1))) zero_le_two) hr.le
             apply LT.lt.trans_le _ hf
             cases he:p i <;> simp only [he,toMode,March.allow] at hp h <;> first | contradiction | exact h.2.1 s
        cases he:p i <;> simp only [he,toMode,allow] at hp h ⊢ <;> try contradiction
        all_goals exact ⟨h.1,bounds,h.2.2⟩
lemma altar_allow (i:Fin b)(v:March S)(u:Fin (n i)→E4)(h:v.allow N (ρ i) u)(hx:∀i,(p i).allow N (ρ i) (x i)):
        ∀j, (altered p i v j).allow N (ρ j) (update x i u j):=by
        intro j; unfold altered; by_cases he:j=i
        · subst j; rw [update_self,update_self];exact h
        rw [update_of_ne he,update_of_ne he]; exact hx j
lemma track (i:Fin b)(hc:Joins.Close z κ)(hp:0<κ)(t:E4)(h:‖t-z i‖ < κ/4):Joins.Close (update z i t) (κ/2):=by
        let f:=update (0:Fin b→E4) i (t-z i)
        have hq(j): ‖f j‖<κ/4:=by by_cases he:j=i <;> simp [f,he,h,div_pos hp (show (0:ℝ)<4 by norm_num)]
        rw [show update z i t=z+f from (by funext j; by_cases ht:j=i <;> simp [ht,f])]
        exact close_shift hc hp hq
lemma lessen (i:Fin b)(hp:(p i).advanced)(w:March S)(h:¬ (w.advanced=true)):amount (altered p i w) < amount p:= by
        let X:= Finset.univ.filter fun j=>(p j).advanced
        have he : amount (altered p i w)=(X.erase i).card:= congr_arg _ (Finset.ext (by intro j; unfold altered; by_cases hz:j=i <;> simp [X,hz,h]))
        rw [he]; exact Finset.card_erase_lt_of_mem (show i∈X from Finset.mem_filter.mpr ⟨Finset.mem_univ i,hp⟩)
end March
end YM.MultipleContact.Centered
