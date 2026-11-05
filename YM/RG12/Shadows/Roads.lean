import YM.RG12.Shadows.Orbit
/-! Retain order per temperature on bona fide projections on Hot platform -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Sanction
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet Quill Baffle Prism Brim Lotus Peak
open WardBin.Lies Push.PriceCompiler Foramen Gate Planned.AtomRegular.Foliage
open YM.RG12.Shadows
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{V:Loom G}
variable {S:Shows V}
namespace Bazaar
variable (H:Bazaar V S)
local notation "η*"=>H.winter
local notation "B!" i:max =>S i
lemma clear' {ι:Type}{z:ι→ℝ}{w:ℝ} (h:z∉outage w):(-z)∉ outage w:=by
   rintro ⟨i,hx⟩; exact h ⟨i, hx.trans_eq (abs_neg _)⟩
variable (M : ∀ i,Leaf (S i).A) (u:Chi){C:ℕ→ℝ}(hM:RG12.Shadows.Charges H.winter 0 (fun i=>(M i).weight))(hC:RG12.Shadows.Charges H.winter 0 C)
include hM hC
lemma handbook' (F:∀ i,(S i).Horn (M i) (C i)) : Charges η* 2 (fun i=> normJ 2 ((S i).gale (M i) u (F i).g) 0):=by
   obtain ⟨A⟩:= anthems V.n
   obtain ⟨d,e,t,r,N,W,K,hF,hN,hK,h0,hB,hH⟩:= H.leases A u
   -- Uniform price t not scaling.E sigma available from Calls.Other.
   let fee i:= 2*((M i).weight*(2*K i))*spentP (hands (fun i=> (B! i).Q₀) i) t (B! i).swell
   have hL:Charges η* 2 fee:=by
      have hv:= H.hands0; obtain ⟨hy,hg⟩:= H.banks0
      have hp: Charges η* 2 (fun i=>spentP (hands (fun i=> (B! i).Q₀) i) t (B! i).swell):=by
          unfold spentP; simp_rw [Real.exp_add]; exact RG12.Shadows.Charges.holdMul (((hg 2).right (Real.exp (t/2))).left 2) hv
      exact RG12.Shadows.Charges.holdMul hp ((RG12.Shadows.Charges.holdMul (hK.left 2) hM).left 2)
   let v:=(η*).H  -- notation with * lexical
   -- at each p price.Enforce bad set.Material by contradictions exact p eventual.No need integral uniform bound if not. 
   unfold RG12.Shadows.Charges OPE.RateLE
   intro p hp
   obtain ⟨q,hq,hP⟩:= exists_between hp
   have he (R:ℕ→ℝ)(h:Charges (H.winter) 2 R):∀ᶠ i in atTop, |R i| ≤ Real.exp (q*v i):= h _ hq
   let f i:= Real.exp (q*v i)
   have hs:∀ᶠ i in atTop,∀ z:Prices G (S i).I,z∉ outage (S i).swell → ‖z‖ ≤ (S i).tongs → (S i).art (M i) u d z ≤ f i := by
     -- select z every i even without NeBot atHot
     classical
     let P i (z:Prices G (S i).I) := z∉outage (S i).swell ∧ ‖z‖ ≤ (S i).tongs
     let Q i:=∃ z,P i z ∧ f i < (S i).art (M i) u d z
     let z:Water S := fun i=> if h:Q i then Classical.choose h else 0
     have hPQ i (hi:Q i):= Classical.choose_spec (show ∃ z, P i z ∧ f i<(S i).art (M i) u d z from hi)
     have hJ i (hi:Q i) : P i (z i)∧ f i < (S i).art (M i) u d (z i):= by unfold z; rw [dif_pos hi]; exact hPQ i hi
     have hp0: ∀ᶠ i:ℕ in atTop,P i (z i):=by
        -- swell>0 true all.
        have hh x : 0<sliceD G V.patch.L V.D x := by unfold sliceD; have hv:= V.D.guards; have hp := Delay.monitor_pos G V.patch.L x; positivity
        filter_upwards [hH] with i he; by_cases hx:Q i; exact (hJ _ hx).1
        unfold z; rw [dif_neg hx]; constructor; swap; · rw [norm_zero]; exact he.scales.1
        rintro ⟨v,hv⟩; rw [Pi.zero_apply,abs_zero] at hv; apply lt_irrefl 0 ((lt_of_lt_of_le ?_ hv)); unfold Barque.swell; rw [(S i).well]; exact hh _
     have hz:Charges η* 0 (H.Flood z):= H.banks0.1.move (hp0.mono fun i hi=> by unfold Flood; rw [abs_of_nonneg (norm_nonneg _)]; exact hi.2)
     have hm : ∀ᶠ i:ℕ in atTop, ((B! i).OpenKey (z i)∧(B! i).OpenKey (-z i)) ∧ ∀ᶠ x in 𝓝 (0:Panels 2),(S i).honor d u x (z i)∧(S i).honor d u x (-z i):=by
        filter_upwards [hH,hp0] with i ha hb; obtain ⟨hA,hB⟩:= (S i).salute ha (z i) hb.2 hb.1; obtain ⟨hC,hD⟩:= (S i).salute ha (-z i) (by rw [norm_neg]; exact hb.2) (clear' hb.1); exact ⟨⟨hA,hC⟩,hB.and hD⟩
     have Ht :Charges η* 2 (fun i=>(S i).art (M i) u d (z i)):= H.mirror_price M u hF hz hC (Eventually.of_forall fun i=> Nonempty.intro (F i)) (hm.mono fun _ hi=>hi.1) (hm.mono fun _ hi=>hi.2) hM
     filter_upwards [he _ Ht] with i hi w hx hS; by_contra! hb; have h:=hJ i (show Q i from ⟨w,⟨hx,hS⟩,hb⟩); exact lt_irrefl _ (lt_of_lt_of_le h.2 ((le_abs_self _).trans hi))
   filter_upwards [hs,hH,he _ hL,H.winter.warmth.eventually_ge_atTop 0] with i hZ ha hb hi
   have hh:= (S i).scoop_bill _ ha (F i) (Real.exp_pos _).le hZ
   have he0 : 0≤ spentP (↑(Fintype.card (S i).Q₀)) t (S i).swell:=by unfold spentP; positivity
   rw [Real.norm_of_nonneg (norm_nonneg _)]
   apply le_trans _ (Real.exp_monotone (mul_le_mul_of_nonneg_right hP.le (show 0≤v i from hi)))
   refine le_of_mul_le_mul_left ?_ (zero_lt_two (α:=ℝ)); apply hh.trans
   change _ ≤ 2 * f i; rw [two_mul (f i)]; apply add_le_add_right; apply le_trans (b:=fee i) _ ((le_abs_self _).trans hb)
   unfold fee; change 2*((M i).weight*_)*_ ≤ 2*((M i).weight*_)*spentP (↑(Fintype.card (S i).Q₀)) t (S i).swell; gcongr; exacts [(M i).profit,hB _]
end Bazaar
end YM.PhysicalNext.Repeat.Sanction
