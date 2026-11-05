import YM.Pert.Bulk.Atlas
import YM.Next.FREE_KERNELS.Curl

set_option autoImplicit false
noncomputable section
namespace YM.Pert.Bulk
open Lattice Stationary Laurent RG Bloch Precision
open scoped Topology BigOperators Classical ENNReal
variable {α β:Type} {L:Side}

def install (S : Cross L α β) : Kernel α β := fun v w => S (wrap L v.1,v.2) w.2 (w.1 - rent L v.1)
lemma mixed_sep (x y : Cover) : delta L x y ≤ sep y (rent L x)+4 := by
  apply (delta_coarse L x (rent L x) y).trans
  rw [show delta L x (rent L x) = length (lift (wrap L x))/(L.val:ℝ) from (by change length _/_=_; congr 2; rw [sub_eq_iff_eq_add,← rent_balance L x]),sep_comm (rent L x) y]
  linarith [length_lift L (wrap L x)]
lemma strip_cost {σ C:ℝ} {S : Cross L α β} (h:S.strip σ C) (x:Site L) (i:α) (j:β) (z:Cover) : ∑' y, bill (S (x,i) j (y-z)) (σ*sep y z) ≤ ENNReal.ofReal C := by
  let e : Cover ≃ Cover := (Equiv.addRight z).symm
  rw [show ∑' y, bill (S (x,i) j (y-z)) (σ*sep y z) = ∑' y,bill (S (x,i) j (e y)) (σ*length (e y)) from by simp_rw [sub_eq_add_neg]; rfl,Equiv.tsum_eq (f:= fun y => bill (S (x,i) j y) (σ*length y))]
  apply bill_width_sum
  convert h (x,i) j using 2
  dsimp [Width]
  simp_rw [mul_comm |S _ _ _| _]
lemma strip_centre {θ σ C:ℝ} {S : Cross L α β} (h:S.strip σ C) (x:Site L) (i:α) (j:β) (f:Cover→ℝ) (hf:∀ y,f y≤length y+4) (hσ:0≤θ) (hmono:θ≤σ) : ∑' y, bill (S (x,i) j y) (θ*f y) ≤ ENNReal.ofReal (Real.exp (4*θ) * C) := by
  calc ∑' y,bill _ _ ≤ ∑' y,bill (S (x,i) j y) (θ*length y+4*θ) :=
                       ENNReal.tsum_le_tsum fun y => bill_mono le_rfl (by nlinarith only [mul_le_mul_of_nonneg_left (hf y) hσ])
       _ ≤ (∑' y,bill (S (x,i) j y) (σ*length y)) * ENNReal.ofReal (Real.exp (4*θ)) := by
                       rw [← ENNReal.tsum_mul_right]
                       refine ENNReal.tsum_le_tsum fun y => ?_
                       rw [bill_add]
                       exact mul_le_mul_right' (bill_mono le_rfl (mul_le_mul_of_nonneg_right hmono (by positivity))) _
       _ ≤ _ := by rw [mul_comm,ENNReal.ofReal_mul (by positivity : 0≤Real.exp (4*θ))]; refine mul_le_mul_left' ?_ _; convert strip_cost h x i j 0 using 1; congr 2; ext1 y; simp [sep]
def colony (L : Side) : Site L × Cover ≃ Cover where
  toFun p := lift p.1+L.val • p.2
  invFun z := (wrap L z,rent L z)
  left_inv := fun p => by obtain ⟨a,b⟩ := @rent_raw L p.2 _ p.1 rfl; simp_rw [a,b]
  right_inv := fun x => (rent_balance L x).symm

lemma cross_row {S : Cross L α β} {σ θ C : ℝ} (hs:S.strip σ C) (hp:0≤θ) (ha:θ≤σ) : RowCost θ L (install S) (Real.exp (4*θ)*C) := by
    intro u j
    rw [← (Equiv.tsum_eq (Equiv.addRight (rent L u.1)) (fun y => bill (install S u (y,j)) (θ*delta L u.1 y)))]
    convert strip_centre hs (wrap L u.1) u.2 j (fun y=>delta L u.1 (y+rent L u.1)) ?_ hp ha using 1
    · congr 2; ext1 y; change bill (S (wrap L u.1,u.2) j (_ - _)) _ = _; simp
    intro y; apply (mixed_sep _ _).trans_eq; simp [sep]
lemma cross_col {S : Cross L α β} {σ θ C : ℝ} (hs:S.strip σ C) (hC:0≤C) (hp:0≤θ) (ha:θ≤σ) : ColCost θ L (install S) ((L.val:ℝ)^4*(Real.exp (4*θ)*C)) := by
    intro i u
    rw [← (colony L).tsum_eq _,ENNReal.tsum_prod (f:=fun z v=>bill (install S (colony L (z,v),i) u) (θ*delta L (colony L (z,v)) u.1))]
    apply (ENNReal.tsum_le_tsum (g:=fun _ => ENNReal.ofReal (Real.exp (4*θ)*C)) ?_).trans_eq
    · simp [site_card, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity : 0≤(L.val:ℝ)^4)]
    intro z
    let e : Cover ≃ Cover := Equiv.trans (Equiv.neg _) (Equiv.addRight u.1)
    rw [← e.tsum_eq _]
    have he v : e v = u.1-v := by change -v+_= _; abel
    have ht (v:Cover) := @rent_raw L (e v) _ z (show colony L (z,e v)=_ from rfl)
    change ∑' v, bill ((install S) (_,_) _) _ ≤ _
    convert strip_centre hs z i u.2 (fun v=>delta L (colony L (z,e v)) u.1) ?_ hp ha using 1
    · congr 2; ext1 v
      rw [install, (ht v).1,(ht v).2,he,sub_sub_cancel]
    intro v; apply (mixed_sep _ _).trans_eq; rw [(ht _).2,he,sep,sub_sub_cancel]
lemma install_step (h:Odd L.val) (s:Axis) (T : Cross L α β) : foot s (install T)=install (forwardC L T s) := by
  funext ⟨u,i⟩ ⟨v,j⟩
  have hh := Next.Free.cover_step h s ((wrap L) u)
  have he : u+step s=lift (wrap L u+step s)+L.val • (rent L u+Next.Free.carryStep s (wrap L u)) := by rw [smul_add,add_comm (L.val • rent L u),← add_assoc,hh,add_right_comm,← rent_balance]
  have ⟨hw,hk⟩ := Stationary.rent_raw _ _ _ he
  dsimp only [foot,install,hw,hk,forwardC]
  rw [hw,hk]
  congr 2
  change v-(rent _ _+_) = v-rent _ _- Next.Free.carryStep _ _
  abel

lemma cross_atlas {m:ℕ} {T : Cross L α β} {σ p:ℝ} (h: Odd L.val) (he:T.strip σ (p/(L.val:ℝ)^m)) (hk: ∀ s,(forwardC L T s).strip σ (p/(L.val:ℝ)^(m+1)))
 {θ:ℝ} (hθ:θ≤σ) (hp : 0≤θ) (hg :0≤p) : Atlas θ L m (install T) (Real.exp (4*θ)*p) :=
 by
  refine ⟨hp,by positivity,?_,?_,fun i=>?_⟩
  · rw [mul_div_assoc]; exact cross_row he hp hθ
  · convert cross_col he (by positivity) hp hθ using 1
    ring
  rw [mul_div_assoc,install_step h i T]; exact cross_row (hk i) hp hθ
end YM.Pert.Bulk
