import YM.Pert.Bulk.Stacks

set_option autoImplicit false
noncomputable section
namespace YM.Pert.Bulk
open Lattice Laurent RG Bloch
open scoped ENNReal Topology Classical BigOperators
variable {α β:Type} {L:Side} {r d:ℕ}
lemma convert_market [Fintype α] (a : Market α→ℝ≥0∞) (p:ℝ≥0∞) (h:∀ i,∑' x, a (x,i)≤p): ∑'w,a w ≤ Fintype.card α * p := by
 calc _ = ∑' i:α,∑'x,a (x,i) := ENNReal.tsum_prod.trans ENNReal.tsum_comm
      _ ≤ ∑' i:α,p := ENNReal.tsum_le_tsum h
      _ = _ := by simp [nsmul_eq_mul]
lemma use_head [Fintype α] {r:ℕ} {σ θ p:ℝ} {T:Kernel α β} (hθ:r*σ≤θ) (h:Atlas θ L d T p) (y) : ∑' v, bill (T v y) (r*σ*delta L v.1 y.1) ≤ ENNReal.ofReal (Fintype.card α * (p*(L.val:ℝ)^4/(L.val:ℝ)^d)) := by
   rw [ENNReal.ofReal_mul (by positivity : 0≤ (Fintype.card α:ℝ)),ENNReal.ofReal_natCast]
   apply convert_market
   exact fun x => h.col.mono hθ x y
lemma use_tail [Fintype β] {σ θ p:ℝ} {T:Kernel α β} (hθ:σ≤θ) (hσ:0≤σ) (h:Atlas θ L d T p) (x v:Market α): ∑'z,bill (T v z) (σ*delta L x.1 z.1) ≤ ENNReal.ofReal (Fintype.card β * (p/(L.val:ℝ)^d)) * bill 1 (σ*sep x.1 v.1) := by
   rw [ENNReal.ofReal_mul (by positivity : 0≤ (Fintype.card β:ℝ)),ENNReal.ofReal_natCast,mul_assoc]
   apply convert_market
   intro i
   have hunit : (1:ℝ) ≤ L.val := by exact_mod_cast L.property
   let s := σ*sep x.1 v.1
   have hs y : σ*delta L x.1 y ≤ θ*delta L v.1 y + s := by
       have ht := delta_fine L x.1 v.1 y
       have e1 := sep_nonneg x.1 v.1
       have es' := delta_nonneg L v.1 y
       calc _ ≤ σ*(sep x.1 v.1 / L.val + delta L v.1 y) := mul_le_mul_of_nonneg_left ht hσ
            _ ≤ (s + θ*delta L v.1 y) := by
                rw [mul_add]; apply add_le_add ?_ (by gcongr)
                · exact mul_le_mul_of_nonneg_left (div_le_self e1 hunit) hσ
            _ = _ := by rw [add_comm]
   apply (ENNReal.tsum_le_tsum (g:=fun y=>bill (T v (y,i)) (θ*delta L v.1 y + s)) (fun y=> bill_mono le_rfl (hs y))).trans
   simp_rw [bill_add,ENNReal.tsum_mul_right, show bill 1 (σ*sep x.1 v.1) = ENNReal.ofReal (Real.exp s) by simp [s,bill]]
   exact mul_le_mul_left (h.row v i) _
lemma transfer_all [Fintype α][Fintype β] {K:Packet r α}{T:Kernel α β}{σ θ p q:ℝ}(hσ:0≤σ)(ht:Atlas θ L d T q)(hxy:σ≤θ)(hx:r*σ≤θ)(hk:Folded σ K p) : Folded σ (pull K T)
       ((Fintype.card β * (q/(L.val:ℝ)^d))^r * (Fintype.card α * (q*(L.val:ℝ)^4/(L.val:ℝ)^d))*p):=
   transmitted_est K T (fun _=>T) hσ _ _ _ hk (by have hq:=ht.nonneg;positivity) (by have hq:=ht.nonneg;positivity) (use_head hx ht) (use_tail hxy hσ ht)

lemma paying_width (a σ : ℝ)(ha:0≤a)(hs:0<σ)(hL:2≤(L.val:ℝ)) : a*Real.exp (σ*(a / L.val)) ≤ (2/σ)*Real.exp (σ*a) := by
   have hu : σ*(a/(L.val:ℝ)) ≤ σ*(a/2) := by gcongr
   have he := Real.add_one_le_exp (σ*(a/2))
   calc _ ≤ ((2/σ)*Real.exp (σ*(a/2)))*Real.exp (σ*(a/2)) := by
          gcongr
          rw [div_mul_eq_mul_div,le_div_iff₀ hs]; linarith
        _ = _ := by rw [mul_assoc,← Real.exp_add,show σ*(a/2)+σ*(a/2)=σ*a by ring]
def centered (T: Kernel α β) := fun x : Market α => fun v : Market α => fun u : Market β => T v u - T (x.1, v.2) u
lemma use_null [Fintype β] {σ θ p:ℝ} {T:Kernel α β} (hθ:σ≤θ) (hσ:0<σ) (h:Atlas θ L d T p)(hL :2≤ (L.val:ℝ)) (x v): ∑'z,bill (centered T x v z) (σ*delta L x.1 z.1) ≤ ENNReal.ofReal (Fintype.card β * ((2/σ)*p/(L.val:ℝ)^(d+1))) * bill 1 (σ*sep x.1 v.1) := by
   rw [ENNReal.ofReal_mul (by positivity : 0≤ (Fintype.card β:ℝ)),ENNReal.ofReal_natCast,mul_assoc]
   apply convert_market
   intro i
   calc _ ≤ ENNReal.ofReal (Laurent.size _ *diffScale _ d σ _ _ _) := atlas_difference (h.mono hθ hσ.le) v.2 i x.1 v.1
        _ ≤ _ := by
          rw [bill,abs_one,one_mul,← ENNReal.ofReal_mul (by have hp:=h.nonneg; positivity : 0≤ (2 / σ) * p/(L.val:ℝ)^(d+1)),← sep_comm v.1, diffScale, ← mul_assoc (Laurent.size _:ℝ), div_mul_eq_mul_div]
          apply ENNReal.ofReal_le_ofReal
          have hp' := h.nonneg
          change (sep v.1 x.1 * Real.exp (σ*(sep v.1 x.1 / L.val))) * (p / _) ≤ _
          convert mul_le_mul_of_nonneg_right (paying_width (sep v.1 x.1) σ (sep_nonneg ..) hσ hL) (by positivity : 0≤p/(L.val:ℝ)^(d+1)) using 1
          · rfl
          ring
lemma use_head2 [Fintype α] {σ θ p:ℝ} {T:Kernel α β} (hθ:σ≤θ) (h:Atlas θ L 2 T p) (y:Market β) : ∑' v, bill (T v y) (σ*delta L v.1 y.1) ≤ ENNReal.ofReal (Fintype.card α * p * (L.val:ℝ)^2) := by
  convert use_head (L:=L) (r:=1) (by simpa) h y using 1
  · simp
  congr! 1; field_simp
lemma center_all [Fintype α][Fintype β] {K:Packet 1 α}{T:Kernel α β}{σ θ p q:ℝ}(hσ:0<σ)(ht:Atlas θ L 2 T q)(hxy:σ≤θ)(hk:Folded σ K p)(hb:2≤(L.val:ℝ)) : Folded σ (fullTransmit K T (centered T))
    ((Fintype.card β *(2/σ)*q * (Fintype.card α*q) /L.val)*p) := by
   convert transmitted_est K T (centered T) hσ.le _ _ _ hk (by have hq := ht.nonneg;positivity : 0≤ (↑(Fintype.card α)*q*(L.val:ℝ)^2)) (by have hq:=ht.nonneg; positivity) (by simpa using use_head2 hxy ht) (use_null hxy hσ ht hb) using 1
   field_simp; ring
end YM.Pert.Bulk
