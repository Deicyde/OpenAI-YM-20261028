import YM.MergeProof.Wallet
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p i : ℕ) (Y : Hol G)
local notation "Rout" => H.rep N p i
local notation "Old" => H.rep N p (i+1)
local notation "c'" => H.S.side i p
local notation "StartSite" => H.S.side (i+1) p
local notation "g₀" => Config G StartSite → ℂ
local notation "Lℓ" => H.S.block i
open Extra.Histories
set_option quotPrecheck false
lemma zeroSlot (X:Wing→Prop)(q:GaugeDoor Old Rout)(h:H.Selected) {t u:ℝ}(ht:0≤t)(hu:0≤u) : Coupon B H N p i Y 0 0 0 q X 0 0 t t u:=by
   let P:Coefficient F c':= Extra.Histories.primary 0 0; have hp: P.Format 0 Y Rout:= primary_format _
   have he: P.density 0 B Rout=0:=by
      funext V; rw [show P.density 0 B Rout V= _ from primary_density B (Rout) 0 V];change _*part B 0 Rout V 0=0;rw [map_zero,mul_zero]
   have hκ: P.remBound 0 Rout (kappa H i) 0:= primary_rem _ (Real.sqrt_pos.mpr (forcedPos _ _))
   obtain ⟨a,b,hb,h₁⟩:= rem_tabs.mp hκ
   have h2:a=0∧ b=0:= by have hz:=hb.first; have hr:=hb.second; constructor<;>linarith
   obtain ⟨rfl,rfl⟩:=h2
   refine ⟨P,⟨hp,?_,by simpa only [P, Extra.Histories.primary,sub_zero,Frame.coeffSize,Pi.zero_apply,norm_zero,sum_const_zero,mul_zero] using ht, 0,0,hb,by rw [mul_zero,add_zero]; exact ht⟩,?_⟩
   · have hx:= (H.levels.transition_mass i p (Old).beta)
     rw [he,Extra.Histories.blast]; funext x; simp [StepData.push]
   rw [show profile (Rout).activities P.forced = 0 by funext i j; simp [profile,P,cram,Extra.Histories.primary]]; exact taped hu ht

-- Unit
lemma currency (A:Wing→Prop)(q:GaugeDoor Old Rout)(h:H.Selected)(hm:i<N) (c w t:ℝ)(hp:0≤t)(T:Heading F):let P:= Extra.Histories.primary 0 F.e0
    Coupon B H N p i Y (P.exponentialEntry 0 B Old) 0 1 q A (P.density 0 B Old) (T.leads Lℓ F.e0)
      (w*F.coeffSize (F.core F.e0)) (c*F.coeffSize (vowel F Lℓ (F.core F.e0))) t:=by
   intro P; let Q:= H.S.block i; let x:ℂ:=(Q.val:ℂ)^d
   have hx : T.leads Q F.e0=x • F.e0 := by
    change T.map (vowel F Q F.e0) = _
    rw [show vowel F Q F.e0 = x • F.e0 by
      funext i
      by_cases hi : i=0
      · rw [hi]; simp [x,vowel,F.zero_degree]
      simp [vowel,Frame.e0,Pi.single_eq_of_ne hi],map_smul,T.unit]
   rw [Size.unit_core, show vowel F Q 0=0 from funext fun i=>by simp [vowel], show F.coeffSize 0=0 from by simp [Frame.coeffSize],mul_zero,mul_zero]
   let R:= Extra.Histories.primary (0:Site c') (x • F.e0)
   have hu:P.exponentialEntry 0 B Old= fun _=>1:=by
      funext U
      have he j:P.maskedTerm Old j U=0:= congr_fun (map_zero (Push.Local.maskLinear _ _)) U
      change F.e0 0+maskLinear _ _ (presented B 0 _ (F.core F.e0)) U+∑' j,P.maskedTerm Old j U=1; rw [Size.unit_core]; simp only [map_zero,Pi.zero_apply,add_zero,Frame.e0,Pi.single_eq_same,he,tsum_zero]
   have hκ:R.remBound 0 Rout (kappa H i) 0:= primary_rem _ (Real.sqrt_pos.mpr (forcedPos _ _)); obtain ⟨a,b,hb,hA⟩:= rem_tabs.mp hκ
   have ha:a=0∧b=0:=by have h:=hb.first; have h':=hb.second; constructor<;> linarith
   obtain ⟨rfl,rfl⟩:= ha
   refine ⟨R, ⟨primary_format _,?_ ,?_, 0,0,hb,by simp⟩,?_⟩
   · have hz : blast H N p i d (P.density 0 B (H.rep N p (i+1)))=x • liftVac H N p i:=by unfold P;rw [unit_density]; exact blast_vac H N p i d h hm
     unfold R; rw [hz,show Extra.Histories.primary (0:Site c') (x • F.e0) = Extra.Histories.stretch x (Extra.Histories.primary 0 F.e0) by simp [Extra.Histories.stretch,Extra.Histories.primary]]
     funext V; rw [stretch_density,_root_.YM.Extra.Histories.unit_density];rfl
   · rw [show T.leads (Lℓ) F.e0=x • F.e0 from hx]; simp [R,Extra.Histories.primary,Frame.coeffSize]
   rw [hu, show profile (Rout).activities R.forced=0 by funext i j; simp [R,Extra.Histories.primary,profile,cram]]; exact taped hp le_rfl
end YM.MergeProof
