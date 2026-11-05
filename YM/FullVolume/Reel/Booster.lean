import YM.FullVolume.Reel.Brew
import YM.MergeProof.Alpaca
/-! payment for TOP turn. full scalar projection. keep talent receipt. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Nectar
open RG Set Finset Filter Ray Function PhysicalNext.Repeat PhysicalNext.Repeat.Luna.Aank Paint.Tower Amp Beam
open scoped Topology BigOperators Classical ENNReal ContDiff
open MergeProof Marker Push Local Extra.Histories Lattice Wilson Source
variable {G:Gauge}{n:Side}{t v:ℝ}{d:ℕ}{F:Labels.Frame G d}(T: SectionData F)(R:Rep G n) {Y:Hol G}(hY:T.Sound Y) (o:Site n) {e:ℝ}
-- ALL support.Param.Stage ℓ. Publication Ω only Eλ so ex exponent.Com.
local notation "Q"=> R.p
local notation "W"=> T.footprint o
local notation "c_"=>fullCost F R.p e
local notation "h_"=> (fullCost F R.p e*χ F)
local notation "k!"=>Real.exp (R.p.supportExponent+2)*h_
variable (he:1 ≤ e)(hp:∀ (i:F.Index)(U:Config G n),‖T.places (Size.axis F i) o U‖≤e)(ht:coverNumber R.p.B (T.footprint o) ≤ 1)
open Matric Local
include hY hp he ht
local notation "e!"=> fun i:Support n=> Real.exp ((R.p.supportExponent+2)*coverNumber R.p.B i)
lemma fuseP (x:F.Coeff): Attainment R.p o (booster T R o x) (k!*‖x‖):=by
   have ha :0≤ (fullCost F R.p e):=by have h:=R.p.threshold_pos; unfold fullCost; positivity
   have hx :0 ≤ h_:= mul_nonneg ha (Nat.cast_nonneg _); let y:= h_ *‖x‖
   have hpv:0≤y:=mul_nonneg hx (norm_nonneg _)
   let c(i:Support n):= if i= W then y else (0:ℝ); refine ⟨fun i=> ?_,fun i hi=> ?_,c,⟨fun i=> ?_,Summable.of_finite,?_⟩,fun i=>?_⟩
   · unfold booster; by_cases hi:i=W
     · rw [hi,Pi.single_eq_same]; exact ⟨supplement_read T R o x,supplement_gauge T R o hY x,supplement_meas T R o x,healthy_supplement _ _ _ hY _⟩
     rw [Pi.single_eq_of_ne hi]; exact Local.Attaches.zero ..
   · have hp:i= W:= not_not.mp (fun h=>hi (Pi.single_eq_of_ne h _)); rw [hp]; exact Finset.mem_image.mpr ⟨0,hY.anchored,by simp⟩
   · unfold c reservedMass; simp only; split_ifs; exact mul_nonneg (Real.exp_pos _).le hpv; rw [mul_zero]
   · rw [tsum_fintype, Finset.sum_eq_single (W)]; unfold reservedMass c; simp only [if_true]; refine (mul_le_mul_of_nonneg_right (Real.exp_monotone (?_ : _ ≤ R.p.supportExponent+2)) hpv).trans_eq ?_
     · exact mul_le_of_le_one_right (add_nonneg R.p.exponent_pos.le zero_le_two) (by exact_mod_cast ht)
     · exact (mul_assoc ..).symm
     · intro j _ hi; unfold c reservedMass; rw [if_neg hi,mul_zero]
     simp

   unfold c booster
   split
   next hi=> rw [hi,Pi.single_eq_same]; refine ⟨hpv,fun p=>?_⟩ ; exact (supplement_bound T R o hY he hp x p).trans ((mul_le_mul_of_nonneg_left (coreW F x) ha).trans_eq (mul_assoc ..).symm)
   next hi=> rw [Pi.single_eq_of_ne hi]; simp
lemma dawnBoost (X:sun→F.Coeff)(hx:PaidBeam X v): Treasure e! (fun i=>booster T R o (X i)) (k! *v):=by
   let w:Support n→ℝ:=e!; have hw(i):0<w i:=Real.exp_pos _; let q(i:F.Coeff):=booster T R o i
   let p(u):=haul w (q u); let c:= k!
   have hi(x):Glacier.Bagged (lattice w (q x)) ∧ ‖p x‖≤c*‖x‖:=by
      obtain ⟨v,h,hX⟩:= (fuseP T R hY o he hp ht x).toll; have hS: Treasure w (fun _=>q x) (c*‖x‖):= Treasure.subdued (fun i=> (hX i).1) ((tsum_fintype (fun i=> w i*v i)).symm.trans_le h.2.2) (fun i=> (hX i).2); exact hS.taxes hw Jams.tip
   have he0:0 ≤ c:=by
       have hz:0≤c_ :=by have h:=R.p.threshold_pos.le; unfold fullCost; positivity
       exact mul_nonneg (Real.exp_pos _).le (mul_nonneg hz (Nat.cast_nonneg _))
   have hu(x y:F.Coeff):p (x-y)=p x-p y:=by
       have hv: q (x-y)= q x-q y:=by
           unfold q booster;let z:=supplement_linear T R o; rw [show supplement T R o (x-y)=supplement T R o x-supplement T R o y from map_sub (IsLinearMap.mk' _ z) x y]; funext i; by_cases ht:i=T.footprint o; rw [ht]; simp
           simp [Pi.single_eq_of_ne ht]
       unfold p; rw [hv]; exact Treasure.hoisted (hi x).1 (hi y).1 (hv ▸ (hi (x-y)).1)
   exact Treasure.pay hw (PaidBeam.transit p hu he0 (fun i=>(hi i).2) X hx) (fun i=> (hi _).1)
end YM.FullVolume.Nectar
