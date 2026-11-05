import YM.Pert.Bulk.Discrete

set_option autoImplicit false
noncomputable section
namespace YM.Pert.Bulk
open Lattice Laurent RG Bloch Function Precision
open scoped ENNReal Topology Classical BigOperators
variable {α β γ:Type}

abbrev Packet (r:ℕ) (α:Type) := Market α → (Fin r→Market α) → ℝ
variable {r:ℕ}
def expense (x:Market α) (v:Fin r→Market α):= ∑ i,sep x.1 (v i).1
lemma expense_nonneg (x:Market α) (v:Fin r→Market α):0≤expense x v := Finset.sum_nonneg (fun _ _=>sep_nonneg ..)
def Folded (σ : ℝ) (K:Packet r α) (p : ℝ) := ∀ x, ∑'v,bill (K x v) (σ*expense x v) ≤ ENNReal.ofReal p

private def packets (α:Type) (r:ℕ) : α × (Fin r→α) ≃ (Fin (r+1)→α) where
  toFun p := Fin.cons p.1 p.2
  invFun v := (v 0, fun i=>v i.succ)
  left_inv _ := by simp
  right_inv := Fin.cons_self_tail
lemma purchase (v t u w : ℝ) : bill (v*t) (u+w) = bill v u * bill t w := by simp only [bill_eq,abs_mul, Real.exp_add,ENNReal.ofReal_mul (abs_nonneg v),ENNReal.ofReal_mul (Real.exp_pos u).le]; ring -- ring?
lemma bill_products (v t : Fin r → ℝ): bill (∏ i,v i) (∑ i,t i) = ∏ i,bill (v i) (t i) := by
  induction r with
  | zero => simp [bill]
  | succ r ih => rw [Fin.prod_univ_succ,Fin.sum_univ_succ,Fin.prod_univ_succ, purchase,ih]
lemma all_Δ (a : Fin r → α → ℝ≥0∞) : ∑' v:Fin r→α, ∏ i,a i (v i) = ∏ i,(∑'v,a i v) := by
  induction r with
  | zero => rw [tsum_fintype];simp
  | succ r ih =>
     have he := (packets α r).tsum_eq (fun v=>∏ i,a i (v i))
     rw [← he, ENNReal.tsum_prod (f:=fun x w=> (∏ i,a i (packets α r (x,w) i))), Fin.prod_univ_succ (f:=fun i=>∑' v,a i v)]
     simp_rw [Fin.prod_univ_succ (f:=fun i=>a i _), (show ∀ v x,packets α r (v,x) 0=v from fun _ _=>rfl), (show ∀ v x i,packets α r (v,x) i.succ=x i from fun a b i=> by simp only [packets, Equiv.coe_fn_mk,Fin.cons_succ]),ENNReal.tsum_mul_left, ih (fun i v=>a i.succ v),ENNReal.tsum_mul_right]

variable {L : Side}
def fullTransmit (K : Packet r α) (T: Kernel α β) (U : Market α→Kernel α β) : Packet r β := fun y z=>
   ∑'x, T x y * ∑' w, K x w * ∏ i, U x (w i) (z i)

def pull (K : Packet r α) (T: Kernel α β) := fullTransmit K T (fun _=>T)
def absolute (w : Fin r → Market α) (z : Fin r → Market β) (x : Market α) (y : Market β) (K : Packet r α) (T : Kernel α β) (U:Market α→Kernel α β):ℝ := (T x y * K x w) * ∏ i,U x (w i) (z i)

lemma expense_sep (x:Market α) (y:Market β) (z:Fin r → Market β) (σ:ℝ) (hs:0≤σ) : σ*expense y z ≤ (r:ℝ)*σ*delta L x.1 y.1 + ∑ i,σ*delta L x.1 (z i).1 := by
   have hm (i:Fin r) : sep y.1 (z i).1 ≤ delta L x.1 y.1 + delta L x.1 (z i).1 := by simpa only [sep_self,zero_div,add_zero] using inv_scaled (L:=L) x.1 y.1 x.1 (z i).1
   rw [expense,Finset.mul_sum]; apply (Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ))=>mul_le_mul_of_nonneg_left (hm i) hs).trans_eq
   simp only [mul_add, Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

lemma absolute_point (K:Packet r α) (σ:ℝ) (hs:0≤σ) (T: Kernel α β)(U : Market α→Kernel α β) (x y w z) : bill (absolute w z x y K T U) (σ*expense y z) ≤
   bill (T x y) (r*σ*delta L x.1 y.1) * bill (K x w) 0 * ∏ i,bill (U x (w i) (z i)) (σ*delta L x.1 (z i).1) := by
  change bill ((T x y * K _ _) * _) _ ≤ _
  have hh := bill_mono (x:=absolute w z x y K T U) le_rfl (expense_sep (L:=L) x y z σ hs)
  apply hh.trans_eq
  unfold absolute; rw [← add_zero (r*σ*delta L ..),purchase,purchase,bill_products]; simp only [add_zero]
lemma absolute_outputs (K:Packet r α) (σ:ℝ) (hs:0≤σ) (T:Kernel α β)(U : Market α→Kernel α β) (q : ℝ≥0∞)
     (hU:∀ x v, ∑'z,bill (U x v z) (σ*delta L x.1 z.1) ≤ q * bill 1 (σ*sep x.1 v.1)) (x y w): ∑' z,bill (absolute w z x y K T U) (σ*expense y z) ≤
       q^r * bill (T x y) (r*σ*delta L x.1 y.1) * bill (K x w) (σ*expense x w) := by
    let b := bill (T x y) (r*σ*delta L x.1 y.1)
    calc _ ≤ ∑'z,b*bill (K x w) 0 * ∏ i,bill (U x (w i) (z i)) (σ*delta L x.1 (z i).1) := ENNReal.tsum_le_tsum fun z=>absolute_point (L:=L) K σ hs T U x y w z
         _ ≤ (b*bill (K x w) 0) * ∏ i:Fin r,(q*bill 1 (σ*sep x.1 (w i).1)) := by
             rw [ENNReal.tsum_mul_left, all_Δ (a:=fun i (z:Market β)=>bill (U x (w i) z) (σ*delta L x.1 z.1))]
             apply mul_le_mul_right
             exact Finset.prod_le_prod' fun i _=>hU ..
         _ = _ := by
             rw [Finset.prod_mul_distrib,← bill_products,← Finset.mul_sum]; simp only [Finset.prod_const,Finset.card_univ,Finset.prod_const_one,Fintype.card_fin]
             rw [mul_mul_mul_comm, ← purchase, mul_comm b,one_pow,mul_one,zero_add]; rfl -- simplifications

lemma absolute_row (K : Packet r α) (T:Kernel α β)(U : Market α→Kernel α β) {σ : ℝ}(hs:0≤σ) (y : Market β) (p q : ℝ≥0∞)
 (hK:∀ x,∑'w,bill (K x w) (σ*expense x w) ≤ p)
 (hU:∀ x v, ∑'z,bill (U x v z) (σ*delta L x.1 z.1) ≤ q * bill 1 (σ*sep x.1 v.1)) : ∑' z,∑' x,∑' w,bill (absolute w z x y K T U) (σ*expense y z) ≤
 q^r*(∑' x,bill (T x y) (r*σ*delta L x.1 y.1))*p := by
   rw [ENNReal.tsum_comm (f:=fun z x=>∑' w,_),← ENNReal.tsum_mul_left,← ENNReal.tsum_mul_right]; refine ENNReal.tsum_le_tsum (fun x=>?_)
   rw [ENNReal.tsum_comm (f:=fun z w=>bill (absolute ..) _)]
   apply (ENNReal.tsum_le_tsum fun w => absolute_outputs K σ hs T U q hU x y w).trans
   rw [ENNReal.tsum_mul_left]; exact mul_le_mul_right (hK ..) _

lemma transmitted_est (K : Packet r α) (T:Kernel α β)(U : Market α→Kernel α β) {σ : ℝ}(hs:0≤σ) (p q c: ℝ) (hk:Folded σ K p)(hc:0≤c)(hq:0≤q)
     (hT:∀ y, ∑'x,bill (T x y) (r*σ*delta L x.1 y.1) ≤ ENNReal.ofReal c)
 (hU:∀ x v, ∑'z,bill (U x v z) (σ*delta L x.1 z.1) ≤ ENNReal.ofReal q * bill 1 (σ*sep x.1 v.1)) : Folded σ (fullTransmit K T U) (q^r*c*p) := by
 intro y
 refine (ENNReal.tsum_le_tsum fun z => (bill_tsum ..).trans (ENNReal.tsum_le_tsum (g:=fun x=>∑' w, bill (absolute w z x y K T U) (σ*expense y z)) ?_)).trans ((absolute_row K T U hs y _ _ hk (fun x v=>hU x v)).trans ?_)
 · intro x; rw [show _ * ∑' w,_ = ∑' w,absolute w z x y K T U by rw [← tsum_mul_left]; simp_rw [absolute,mul_assoc]]
   exact bill_tsum ..
 simp only [ENNReal.ofReal_mul (mul_nonneg (by positivity : 0≤q^r) hc),ENNReal.ofReal_mul (by positivity : 0≤q^r),ENNReal.ofReal_pow hq]
 gcongr; exact hT y
end YM.Pert.Bulk
