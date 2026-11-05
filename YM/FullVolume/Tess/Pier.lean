import YM.FullVolume.Tess.Suds
/- Resize existence independent of x (scale). Linear→ polynomial root bounds. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Amp.Beam
open Filter Function Finset RG Push.AbsoluteSums Ray Asymptotics
open PhysicalNext.Repeat.Muse
open scoped Topology BigOperators Classical ContDiff
local notation "η"=>aurora
lemma divide (X:Beam ℂ) (a c:ℝ)(hv:∀ v:sun, ‖read ℂ v X‖≤a)(ht:‖X‖≤c)(v:sun)(k:ℕ):‖fit v X‖≤ aurora^k*(a + 2*(|v.val|^(k+1)*c)):=by
   let Z:= fit v X; let S:=stem Z k; let Y:=Z-S; let p:= |v.val|^(k+1)* c
   have hh : ‖Y‖ ≤ p:= (stemSize v X k).trans (mul_le_mul_of_nonneg_left ht (pow_nonneg (abs_nonneg _) _))
   have hP:‖S‖≤aurora^k*(a+p):=welded S (Crop.cropped _ k) _ fun s=>by
      have hy:‖read ℂ s Y‖≤ p:= le_trans (price Y s) hh
      have ht :read ℂ s S=read ℂ (slash v v.2 s) X-read ℂ s Y:=by rw [← fitL]; unfold Y; rw [map_sub]; unfold Z; abel
      rw [ht]; exact (norm_sub_le ..).trans (add_le_add (hv _) hy)
   have hp :p ≤aurora^k*p:=le_mul_of_one_le_left ((norm_nonneg _).trans hh) (one_le_pow₀ aurora_above.le)
   have hz:S+Y=Z:=by unfold Y; abel
   rw [show fit v X=S+Y from hz.symm]
   exact (norm_add_le ..).trans ((add_le_add hP (hh.trans hp)).trans_eq (by unfold p; ring))
lemma seek (Y:ℝ)(hY:1≤Y):∃ k:ℕ,aurora^k ≤ Y∧Y ≤ aurora^(k+1):=by
    have hh : ∃ k:ℕ,Y < aurora^k:= ((tendsto_pow_atTop_atTop_of_one_lt aurora_above).eventually_gt_atTop Y).exists
    obtain ⟨k,hk⟩:=(show ∃ k,Nat.find hh=k+1 from ⟨Nat.find hh-1,by have h:Nat.find hh≠0:=fun ht=>not_le.mpr (Nat.find_spec hh) (by rw [ht,pow_zero]; exact hY); omega⟩)
    exact ⟨k,le_of_not_gt (Nat.find_min hh (by omega)), hk ▸ (Nat.find_spec hh).le⟩
lemma ear (A M:ℝ) (hA:0≤A)(hM:0≤ M)(m:ℕ) : ∃ (C:ℝ)(v:sun),0≤ C ∧ 0 < v.val ∧ ∀ (Y:ℝ)(X:Beam ℂ),1≤ Y→‖X‖≤A*Y^m → (∀ s:sun, ‖read ℂ s X‖≤ M/Y) →‖fit v X‖≤ C/Real.sqrt Y:=by
    let n:=2*(m+1)
    have hα:=aurora_above
    have h_:0<η:=zero_lt_one.trans hα
    let u:ℝ:=η⁻¹^n; have hx:0<u:=pow_pos (inv_pos.mpr h_) n
    let v:sun:= ⟨u,⟨by linarith only [hx],pow_le_one₀ (inv_pos.mpr h_).le ((inv_le_one₀ h_).2 hα.le)⟩⟩
    refine ⟨M+2*A,v,by linarith,hx,fun Y X hp hv ht=>?_⟩
    let t:= Real.sqrt Y; have hP: t^2=Y:= Real.sq_sqrt (zero_le_one.trans hp); have hh:1≤t:= by simpa [t] using Real.sqrt_le_sqrt hp
    have hz:0<t:=zero_lt_one.trans_le hh
    obtain ⟨k,hk,hK⟩:=seek t hh
    have he:u^(k+1)*Y^(m+1)≤ 1:=by
       unfold u; rw [show (η⁻¹^n)^(k+1)= ((η^(k+1))^n)⁻¹ from (by rw [← pow_mul,inv_pow, Nat.mul_comm n, ← pow_mul]),← div_eq_inv_mul]; apply (div_le_one (pow_pos (pow_pos h_ _) _)).mpr
       rw [← hP,← pow_mul]; exact pow_le_pow_left₀ hz.le hK n -- use hK
    have hi:= divide X (M/Y) _ ht hv v k
    change _≤aurora^k*(M/Y+2*(|v.val|^(k+1)*(A*Y^m))) at hi; rw [show (v.val)=u from rfl, abs_of_pos hx] at hi
    have hr:u^(k+1)*(A*Y^m)≤ A/Y:=by rw [le_div_iff₀ (zero_lt_one.trans_le hp)]; rw [pow_succ Y] at he; nlinarith only [mul_le_mul_of_nonneg_right he hA]
    apply hi.trans; refine (mul_le_mul hk (add_le_add_right (mul_le_mul_of_nonneg_left hr zero_le_two) (M/Y)) (by positivity) hz.le).trans_eq ?_
    rw [← hP]; change t*(_+_)= (M+2*A)/Real.sqrt (t^2); rw [Real.sqrt_sq hz.le]; field_simp <;> ring
end YM.FullVolume.Amp.Beam
#print axioms YM.FullVolume.Amp.Beam.ear
