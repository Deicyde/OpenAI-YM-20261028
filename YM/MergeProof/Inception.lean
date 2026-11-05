import YM.MergeProof.Alpaca
import YM.MergeProof.Ballad
import YM.MergeProof.Jubilee

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p : ℕ) {A:Hol G}
variable {n:Side} (R:Rep G n)
lemma drive (m:Motion)(P:F.Coeff)(h:B.Sound A): upwards m 0 (booster B R 0 P)=booster B R 0 (Motion.patch F m P):=by
   let p:=B.footprint (0:Site n); let Q:=Motion.patch F m P
   have he: affine m.1 (0:Site n) 0=0:=by simp [affine]
   have hP:sky m (0:Site n) p=p:=by rw [shading]; exact (footprint_turn h m.1 (0:Site n) 0|>.symm).trans (congr_arg _ he)
   have hp0 U: Motion.scalar m (part B 0 R (pull m.1 0 U) P)= part B 0 R U Q :=by
      let Z:= Extra.Histories.primary (0:Site n) P; -- derive directly
      have hX: part B 0 R U (F.act m.1.ortho P)=part B 0 R (pull m.1 0 U) P:=by
         have ht: (B.footprint (0:Site n)).image (turnSites m.1 (0:Site n))=B.footprint (0:Site n):= (shading ..).symm.trans hP
         unfold part; simp only [LinearMap.coe_mk,AddHom.coe_mk]
         rw [act_at_zero, Local.masked_pull,ht, ← core_act, F.scaling];congr 2; funext j; dsimp only [Function.comp_apply]; rw [B.placed_signed h]; rw [he]
      have hb (v:F.Coeff): part B 0 R U (star v)= star (part B 0 R U v):=by
         unfold part; simp only [LinearMap.coe_mk,AddHom.coe_mk,Pi.star_apply]; rw [core_star,scaled_star,show B.places (star (F.scaled R.p.threshold⁻¹ (F.core v))) (0:Site n) = star (B.places (F.scaled R.p.threshold⁻¹ (F.core v)) 0) from funext fun U => h.ordinary_real ..]; rw [star_add,masked_bar]
      unfold Motion.scalar Q Motion.patch;split;exact congr_arg star hX.symm |>.trans (hb _).symm;exact hX.symm
   funext i U; obtain ⟨i,rfl⟩:= (sky m (0:Site n)).surjective i; unfold upwards; rw [Equiv.symm_apply_apply]; unfold stepUp; unfold booster
   by_cases hi:i=p
   · rw [hi,hP,show p=B.footprint 0 from rfl,Pi.single_eq_same,Pi.single_eq_same]; change Motion.scalar m (supplement B R 0 P _)=supplement B R 0 Q _; rw [supplement,supplement,scalar_sub, hp0,B.placed_signed h,he]; unfold Q Motion.patch Motion.scalar; split; next=>rw [scaled_star,F.scaling]; exact congr_arg₂ (·-·) (h.ordinary_real ..).symm rfl
     next=>rw [F.scaling]
   have heq : sky m (0:Site n) i≠ p:= hP ▸ (sky m 0).injective.ne hi
   rw [Pi.single_eq_of_ne hi,Pi.single_eq_of_ne heq]; exact scalar_z _
variable (K:Keeper ((H.rep N p N).p) (H.rep N p N).activities)(h: ∀ s,(H.rep N p N).activities.K (K.code s)=0)(q:ℕ)
local notation "RT"=> H.rep N p N
local notation "V"=> Guard.summit F B H N p K h q
lemma voice (ht:H.Selected)(hT:B.Sound A)(hv:OnTop B H N p A V): Chorus H N p N V:=by
   refine ⟨fun j z=>?_⟩
   obtain ⟨π⟩:= (ht.represents N p N le_rfl).good.labels.moves z.1 0
   simp_rw [fun i=> onRise B H N p K h q i (rem_dominated (hv.heard.earns i|>.2))]; rw [← hooked z 0 π,drive B _ z _ hT]
end YM.MergeProof
