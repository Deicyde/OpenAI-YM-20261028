import YM.Pert.Bulk.UseRows

set_option autoImplicit false
noncomputable section
namespace YM.Pert.Bulk
open Lattice Laurent RG Bloch Function Precision Filter
open scoped ENNReal Topology Classical BigOperators
variable {α β:Type} {L:Side}
def neutral (K:Packet 1 α):Prop:= ∀ x i, ∑' u, K x (fun _=> (u,i))=0

def identify (X:Type) : (Fin 1 → X) ≃ X where
 toFun w := w 0
 invFun x := fun _=>x
 left_inv _ := funext fun i=>by simp only [Fin.fin_one_eq_zero i]
 right_inv _:= rfl
lemma bill_folded {K:Packet 1 α} {σ p:ℝ}(x:Market α) (hσ:0≤σ)(hk:Folded σ K p) : Summable (fun w : Market α=>K x (fun _=>w)) := by
   apply summable_from_receipt
   · exact fun (w : Market α) => mul_nonneg hσ (expense_nonneg x (fun _:Fin 1=>w))
   have h := (identify (Market α)).symm.tsum_eq (fun w => bill (K x w) (σ*expense x w))
   exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.le.trans (hk x))
lemma atlas_entry {σ q:ℝ}{m:ℕ}{T:Kernel α β}(h:Atlas σ L m T q)(x:Market α)(y:Market β) : ‖T x y‖≤ q := by
   have hq := h.nonneg
   have hs : q/(L.val:ℝ)^m≤q := div_le_self hq (one_le_pow₀ (by exact_mod_cast L.property : (1:ℝ)≤ L.val))
   apply ENNReal.ofReal_le_ofReal_iff hq |>.1
   calc _ = bill (T x y) 0 := by rw [bill,Real.exp_zero,mul_one,Real.norm_eq_abs]
        _ ≤ ∑' k,bill (T x (k,y.2)) (σ*delta L x.1 k) := (bill_mono le_rfl (mul_nonneg h.width (delta_nonneg L x.1 y.1))).trans ((ENNReal.le_tsum y.1)) -- maybe no
        _ ≤ ENNReal.ofReal q := (h.row ..).trans (by gcongr)
lemma transmit_one (K:Packet 1 α) (V : Market α→Kernel α β) (x) (z:Fin 1→Market β) : (∑'w:Fin 1→Market α,K x w * ∏ i,V x (w i) (z i)) = ∑'w,K x (fun _=>w) * V x w (z 0) := by
   rw [← (identify (Market α)).symm.tsum_eq (fun w=> K x w * ∏ i,V x (w i) (z i))]
   simp [Fin.prod_univ_succ,identify]
lemma subtract_null [Fintype α] {T:Kernel α β} {K:Packet 1 α} {σ q:ℝ}{m:ℕ}(h:Atlas σ L m T q) (h₀:neutral K) {θ p:ℝ} (he:0≤θ)(hk:Folded θ K p):
 fullTransmit K T (centered T) = pull K T := by
  have hA x := bill_folded x he hk
  have hW x (y) (v : Market α → Market α) : Summable fun w=>K x (fun _=>w) * T (v w) y := by
     apply Summable.of_norm_bounded ((hA x).norm.mul_right q); intro z; rw [_root_.norm_mul]; exact mul_le_mul_of_nonneg_left (atlas_entry h ..) (norm_nonneg _)
  funext y z; change (∑'x, T x y* _)=∑'x,T x y*_
  apply tsum_congr; intro x; congr 1
  simp_rw [transmit_one, centered,mul_sub,transmit_one K (fun _=>T) x z]; rw [Summable.tsum_sub (hW x (z 0) (fun w=>w)) (hW x (z 0) (fun w=>(x.1,w.2)))]
  let f (u:Cover)(i:α) := K x (fun _=>(u,i)) * T (x.1,i) (z 0)
  have ht := (Equiv.prodComm α Cover).tsum_eq (f:=fun z=> f z.fst z.snd)
  have hy' : ∑'t:α×Cover, f t.2 t.1= ∑'i:α,∑'u:Cover,f u i := (hW x (z 0) (fun w=>(x.1,w.2))).prod_symm.tsum_prod
  have hv' (i:α): ∑'u:Cover,f u i=0 := by unfold f; rw [tsum_mul_right,h₀ x i,zero_mul]
  change _-(∑'t : Market α,f t.1 t.2)=_
  rw [← ht, show (∑'t:α×Cover,f (Equiv.prodComm _ _ t).1 (Equiv.prodComm _ _ t).2) = ∑'i:α,∑'u:Cover,f u i from hy',show _ = (0:ℝ) from (tsum_congr hv').trans tsum_zero,sub_zero]
lemma null_all [Fintype α][Fintype β] {K:Packet 1 α}{T:Kernel α β}{σ θ p q:ℝ}(hσ:0<σ)(ht:Atlas θ L 2 T q)(hxy:σ≤θ)(hk:Folded σ K p)(hb:2≤(L.val:ℝ))(h₀:neutral K) : Folded σ (pull K T) ((Fintype.card β *(2/σ)*q * (Fintype.card α*q) * p)/(L.val:ℝ)) := by
 rw [← subtract_null ht h₀ hσ.le hk]
 convert center_all hσ ht hxy hk hb using 1
 rw [div_mul_eq_mul_div]
end YM.Pert.Bulk
