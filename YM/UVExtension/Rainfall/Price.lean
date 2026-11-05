import YM.UVExtension.Lacing.Rooms
/-! Real tolls pay already. Extra relayed solo clock inequality incurred outside. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Mast
open Function Filter Set Lattice RG RG.Supply Wilson Labels Bid Extra.Histories Motion
open Lacing Lacing.RoutesF
open scoped Topology BigOperators Classical
private lemma slender {c p r:ℝ}(hc:1≤c)(hp:0 < p)(ht:10000*c ≤ p)(hr:r ≤ p⁻¹ ^ (3:ℕ)): 4*2*c*r ≤ 1/8:=by
   have hv : p⁻¹ ^ (3:ℕ) ≤ p⁻¹:= by
      exact pow_le_of_le_one (inv_nonneg.mpr hp.le) (inv_le_one_of_one_le₀ (by linarith only [ht,hc])) (by decide)
   have h: 64*c ≤ p := by linarith only [ht,hc]
   apply le_trans (mul_le_mul_of_nonneg_left (hr.trans hv) (by linarith only [hc]))
   rw [← div_eq_mul_inv]; exact (div_le_iff₀ hp).2 (by linarith only [h])
variable {G:Gauge}
open Planned.GuardedAtom
private lemma saline {d:ℕ} (F:Frame G d)(u v c w s p r:ℝ)(hu:0≤ u)(hv:1≤ v)(hc:v ≤ c)(hew:1 ≤ w)(hs:1≤ s)(hp:0 < p)(hw:4*c^2 ≤ w)(hP:10000*c ≤ p)(hq:r ≤ p⁻¹ ^ (3:ℕ))(hV:(v+u*s)*orbitCost F ≤ c)(ht:u*(1+s)*orbitCost F ≤ r): Tollgate F u v v w s:=by
   let V:=orbitCost F; have h0 : 1≤V:= orbitCost_one_le ..; have hv': 1≤ c:=hv.trans hc; have hp':= slender hv' hp hP hq
   have he : (u*s)*V ≤ r:= (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hu) (zero_le_one.trans h0)).trans ht
   have hf :2*u*s*V*(2*v) ≤ 1/16:=by
      calc _ =2*((u*s)*V)*(2*v):=by ring
           _ ≤ 2*r*(2*c):=mul_le_mul (mul_le_mul_of_nonneg_left he zero_le_two) (mul_le_mul_of_nonneg_left hc zero_le_two) (by linarith [hv]) (mul_nonneg zero_le_two (le_trans (by positivity) he))
           _ ≤ _:=by linarith only [hp']
   have hh :2*u*s*(2*v) ≤ 1/16:=by refine le_trans ?_ hf; exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) h0) (by positivity)
   refine ⟨hv, hew, hs,?_,?_,?_,?_,hh.trans (by norm_num)⟩
   · change _*((u+2*u*s)*V) ≤ _
     calc _ ≤ 2*c*(2*(u*(1+s)*V)):=by
              apply mul_le_mul (mul_le_mul_of_nonneg_left hc zero_le_two) _ (by positivity) (by positivity);
              rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans h0); linarith only [hu]
          _ ≤ 2*c*(2*r):= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht zero_le_two) (by linarith)
          _ ≤ 1:= by linarith only [hp']
   · change (v+2*u*s)*V*_ ≤ _
     calc _ ≤ 2*((v+u*s)*V)*(2*v):=by
               rw [← mul_assoc 2]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only [hv]) (zero_le_one.trans h0)) (by positivity)
          _ ≤ 2*c*(2*c):= mul_le_mul (mul_le_mul_of_nonneg_left hV zero_le_two) (by linarith) (by positivity) (by positivity)
          _ = 4*c^2:=by ring
          _ ≤ _:=hw
   · change (1+w)*_*V*_ ≤ _
     calc _ = (1+w)*(2*u*s*V*(2*v)):=by ring
          _ ≤ (1+w)*(1/16):=mul_le_mul_of_nonneg_left hf (by positivity)
          _ ≤ (1/8)*w:=by linarith only [hew]
   calc _ = (1+w)*(2*u*s*(2*v)):=by ring
        _ ≤ (1+w)*(1/16):=mul_le_mul_of_nonneg_left hh (by positivity)
        _ ≤ (1/8)*w:=by linarith only [hew]
lemma paintBudget {H:History G}{d:ℕ}{V:Labels.Frame G d}{a b:ℝ}{m:ℕ}{W:Worth}(h:Buys H V W m a b)(hr:roomCost H.levels W)(hb:Bank W H.levels): let w:= (H.levels.params m).columns; let s:= (H.levels.params (m+1)).columns
    Tollgate V b a a w s ∧ 2*a≤ s:=by
    intro w s; let i:=H.levels.clock.J m; let j:=H.levels.clock.J (m+1); let p:=puffs (H.S.block m); let x:=W.K j; let P:=W.K (j+1); let X:=orbitCost V
    have ht: x≤P:=W.growth (Nat.le_succ _); have he₀ :1 ≤ x:= W.prices _; have hP :1≤P:= he₀.trans ht
    have hx : x ≤ W.K (i+1):= W.growth (H.levels.fits.stepSlow m)
    have hv : 64*x^2 ≤ w:= (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hx 2) (by norm_num)).trans (hr m)
    have hF :64*x^2 ≤ s:= (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ht 2) (by norm_num)).trans (hr (m+1))
    have hp :1 ≤ s:= H.levels.params (m+1)|>.columns_ge
    have hI :1 ≤ w:= H.levels.params m|>.columns_ge
    have hQ:10000*x≤ p:=by
       have hI' : x ≤ P^(6:ℕ):= ht.trans (by exact le_self_pow₀ hP (by decide))
       apply le_trans _ (hb m); change 10000*x≤ 100000*P^6*(1+s)^2; calc
         _ ≤ 100000*P^6:=by linarith only [hI',he₀]
         _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith only [hp]))
    have ha:=h.cost; have he:=h.epsilon; have hc : a≤ x:= (le_mul_of_one_le_right (by linarith) (orbitCost_one_le V)).trans ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (show 0≤ b*s by positivity)) (zero_le_one.trans (orbitCost_one_le V))).trans h.funds)
    exact ⟨saline V b a x w s p _ he ha hc hI hp (by linarith only [hQ,he₀]) (by nlinarith only [hv,he₀]) hQ (le_refl (barunit (H.S.block m))) h.funds h.tiny,by nlinarith only [he₀, hc, hF]⟩
end YM.UVExtension.Mast
