import YM.Pert.Bulk.Binding

set_option autoImplicit false
noncomputable section
namespace YM.Pert.Bulk
open Lattice Laurent RG Bloch Function
open scoped ENNReal Topology BigOperators Classical
variable {L:Side} {α β γ:Type}

def plain (T:Row α β) : Kernel α β:= fun v u => T v.2 u.2 (u.1-v.1)
@[simp] lemma delta_one (x y : Cover) : delta (1:Side) x y=sep x y := by unfold delta; norm_num
lemma plain_reads (x : Cover) (i:α)(y:Cover) (j:β)(T:Row α β) (a:Cover) : plain T (x+a,i) (y+a,j)=plain T (x,i) (y,j) := by unfold plain;simp
lemma plain0 {T:Row α β} {σ p θ:ℝ} (h:T.strip θ p) (hσ:σ≤θ) :
   RowCost σ 1 (plain T) p ∧ ColCost σ 1 (plain T) p := by
  have hh (i:α)(j:β) : ∑' z,bill (T i j z) (σ*length z) ≤ ENNReal.ofReal p := by
    apply (ENNReal.tsum_le_tsum fun z => bill_mono le_rfl (mul_le_mul_of_nonneg_right hσ (show 0≤length z by positivity))).trans
    apply bill_width_sum
    convert h i j using 2
    dsimp [Width]; simp_rw [mul_comm (Real.exp _) _]
  constructor
  · intro v j
    convert (Equiv.tsum_eq (e:=(Equiv.addRight v.1).symm) (f:=fun z=>bill (T v.2 j z) (σ*length z))).trans_le (hh v.2 j) using 1
    congr 1; ext1 y
    rw [delta_one,sep_comm]; rfl
  intro i v
  let e := (Equiv.neg _).trans (Equiv.addRight v.1)
  convert (e.tsum_eq (f:=fun z=>bill (T i v.2 z) (σ*length z))).trans_le (hh i v.2) using 1
  congr 1; ext1 y; rw [delta_one,sep_comm]
  change bill (T i v.2 _) _ = bill (T i v.2 _) _
  simp only [sep,show e y=v.1-y from by change -y+_=_; abel]

lemma tame_product_row {K:Kernel α β}{U:Kernel β γ}{θ σ p q:ℝ}{c:Side}
  (hK:RowCost σ L K p)(hσ:0≤σ)(hu:RowCost θ c U q) (hp:0≤θ) (v:Market α)(u:Market γ)(i:β)(a:Cover) :
  Summable fun z=>K v (z,i)*U (z+a,i) u := by
  have hW z : ‖U (z+a,i) u‖ ≤ max q 0 := by
    rw [show ‖U ..‖ = (bill (U (z+a,i) u) 0).toReal from by rw [bill,Real.exp_zero,mul_one,ENNReal.toReal_ofReal (abs_nonneg _)]; rfl]
    apply (ENNReal.toReal_le_of_le_ofReal (le_max_right q 0))
    · exact (bill_mono le_rfl (show 0≤ θ*delta c (z+a) u.1 from mul_nonneg hp (delta_nonneg ..))).trans ((ENNReal.le_tsum (f:=fun y=>bill (U (z+a,i) (y,u.2)) (θ*delta c (z+a) y)) u.1).trans ((hu (z+a,i) u.2).trans (ENNReal.ofReal_le_ofReal (le_max_left q 0))))
  have hV : Summable (fun z=>K v (z,i)) := summable_from_receipt (fun _=> mul_nonneg hσ (delta_nonneg ..)) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hK v i))
  apply Summable.of_norm_bounded (hV.norm.mul_right (max q 0)); intro z; rw [norm_mul]; gcongr; exact hW _
lemma foot_bind [Fintype β] {K:Kernel α β}{U:Kernel β γ}{σ p θ q:ℝ}{c:Side} (hK:RowCost σ L K p) (hp:0≤σ) (hU:RowCost θ c U q) (hq:0≤θ)(d:Axis) : foot d (bind K U)=bind (foot d K) U := by
  funext ⟨x,i⟩ ⟨v,j⟩; let u:Cover:=x+step d
  simp only [foot,bind_apply,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro k _
  simp_rw [tagged,foot,sub_mul]
  have e y := (tame_product_row hK hp hU hq (y,i) (v,j) k (0:Cover)).congr (g:=fun z=>K (y,i) (z,k) * U (z,k) (v,j)) (by simp)
  rw [Summable.tsum_sub (e u) (e x)]
lemma plain_bind [Fintype β] {K : Row α β}{U:Kernel β γ}{σ θ p q:ℝ}
  (hK:K.strip σ p)(hp:0≤σ)(hu:RowCost θ L U q)(ht:0≤θ)(d:Axis) : foot d (bind (plain K) U)=bind (plain K) (foot d U) := by
  funext ⟨x,i⟩ ⟨v,j⟩; let a:Cover:=step d; let u:Cover:=x+a
  simp only [foot,bind_apply,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro k _; dsimp only [tagged]
  have hR := (plain0 hK le_rfl).1
  have hx (y b) : Summable (fun z=>plain K (y,i) (z,k)*U (z+b,k) (v,j)) := tame_product_row hR hp hu ht (y,i) (v,j) k b
  replace hw (y) := (hx y 0).congr (g:=fun z=>plain K (y,i) (z,k) * U (z,k) (v,j)) (by simp)
  rw [← (Equiv.addRight a).tsum_eq (fun z=>plain K (u,i) (z,k) * U (z,k) (v,j))]
  simp_rw [foot, mul_sub, (show ∀ z,plain K (u,i) ((Equiv.addRight a) z,k)=plain K (x,i) (z,k) from fun z=>plain_reads ..)]
  dsimp; rw [← Summable.tsum_sub (hx x a) (hw x)]

lemma pre_plain_row {σ θ:ℝ} (h:σ≤θ) (hs:0≤σ) (x y z:Cover) : σ*delta L x z≤θ*delta 1 x y +σ*delta L y z := by
    have hm := delta_fine L x y z
    have hn : 0≤sep x y := sep_nonneg ..
    rw [delta_one]; have h' := div_le_self hn (by exact_mod_cast L.property : (1:ℝ)≤L.val)
    nlinarith
lemma pre_plain_col {σ θ:ℝ} (h:σ≤θ) (hp:0≤θ) (hσ:0≤σ) (x y z:Cover) : σ*delta L x z≤σ*delta L x y +θ*delta 1 y z := by
  have hm := delta_coarse L x y z
  rw [delta_one]
  nlinarith [sep_nonneg y z]
lemma row_left [Fintype β] {θ σ p q:ℝ} {K:Row α β} {T:Kernel β γ} (hK:K.strip θ p)(h:σ≤θ)(he:RowCost σ L T q)(hs:0≤σ)(hp:0≤p)(hq:0≤q):
  RowCost σ L (bind (plain K) T) (Fintype.card β * (p*q)) := row_block hp hq (plain0 hK le_rfl).1 he (pre_plain_row h hs)
lemma row_right [Fintype β] {θ σ p q:ℝ} {T:Kernel α β} {K:Row β γ} (he:RowCost σ L T q)(hK:K.strip θ p)(h:σ≤θ)(hs:0≤σ)(hp:0≤p)(hq:0≤q):
  RowCost σ L (bind T (plain K)) (Fintype.card β * (q * p)) := row_block hq hp he (plain0 hK le_rfl).1 (pre_plain_col h (hs.trans h) hs)
lemma col_left [Fintype β] {θ σ p q:ℝ} {K:Row α β} {T:Kernel β γ} (hK:K.strip θ p)(h:σ≤θ)(he:ColCost σ L T q)(hs:0≤σ)(hp:0≤p)(hq:0≤q):
  ColCost σ L (bind (plain K) T) (Fintype.card β * (p*q)) := col_block hp hq (plain0 hK le_rfl).2 he (pre_plain_row h hs)
lemma col_right [Fintype β] {θ σ p q:ℝ} {T:Kernel α β} {K:Row β γ} (he:ColCost σ L T q)(hK:K.strip θ p)(h:σ≤θ)(hs:0≤σ)(hp:0≤p)(hq:0≤q):
  ColCost σ L (bind T (plain K)) (Fintype.card β * (q * p)) := col_block hq hp he (plain0 hK le_rfl).2 (pre_plain_col h (hs.trans h) hs)
end YM.Pert.Bulk
