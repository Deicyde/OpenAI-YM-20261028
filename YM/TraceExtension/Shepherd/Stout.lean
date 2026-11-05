import YM.Push.FREE_RESOLVENT.SharedCells
import YM.TraceExtension.Shepherd.Abyss
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Shepherd
open RG Wilson Lattice Source AnalyticBridge VerifiedReset Finset Ac MergeProof Cask Function Pressure Next.Fluctuations PathData Extra.Iteration Push.AbsoluteSums Extra.Multi StressFlux MeasureTheory Cells Accent Menu
open Push.GridApprox Overlay
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff
variable {G:Gauge}{n:Side}{C:Family G}(H:C.Makes) {b:ℝ}
def mama (b:ℝ) (x: Site n) (U:Config G n):ℂ:= if x∈flags b U then 1 else 0
lemma mommy (b:ℝ) : Interior (Push.GridApprox.window 0 8) (mama (n:=n) (G:=G) b 0):=by
    refine ⟨fun g t=>by simp [mama], .ite ((flags_open ..).measurableSet) measurable_const measurable_const,fun U V hu=> ?_,1,fun V=>by unfold mama; split <;> simp⟩
    let P:= ({0}:Support n); have hp : (inspected P:Set (Site n))⊆ Push.GridApprox.window 0 8:=by
        intro x hx; have hv:= Next.Rank.Thirst.inspect P hx; have hx : pdist x≤ 8:=by simpa [P,halo_spec,separation] using! hv
        exact ⟨lift x,FreeResolvent.Lifted.lift_box x 8 hx,by simp⟩
    have hv := flags_agree b U V P (agrees_mono hu hp)
    by_cases hx:0∈flags b U; rw [mama,if_pos hx,mama,if_pos (show 0∈flags b V from (mem_inter.mp (show 0∈P∩flags b V from hv ▸ mem_inter.mpr ⟨mem_singleton_self _,hx⟩)).2)]
    rw [mama,if_neg hx,mama,if_neg]; exact fun hd=>hx (mem_inter.mp (show 0∈P∩flags b U from hv.symm ▸ mem_inter.mpr ⟨mem_singleton_self _,hd⟩)).2
section
set_option quotPrecheck false
variable {J p k N:ℕ}
local notation "n!"=> (C.side k p)
local notation "S"=> C.S
local notation "R"=> (C.path.rep N p k)
local notation "Q"=> C.path
local notation "M!"=> (C.path.levels)
local notation "F"=> mama (G:=G) b (0:Site (C.side k p))
include H
def brinkP (C:Family G)(J p k N:ℕ) (b:ℝ):= let A:= C.path.rep N p k; (C.S.a J/C.S.a k)^4 * Vac.treasury C.path.levels k - A.beta*(A.clip.linear/5*b^2)
lemma ritual (hk:k ≤ N) (hJ:J ≤ k)(hb:0<b)(hT:2*b≤ (C.path.rep N p k).p.threshold) (hr:Push.GridApprox.room C.path.levels J k 8):
    (tilesAt C.S p (hJ.trans hk)).rootTest (C.beta N p) (backTo C.path N p hk F) ≤ Real.exp (brinkP C J p k N b):=by
    let W:= tilesAt S p (hJ.trans hk); let X:=tilesAt S p hJ; let V:= Site (C.side J p); let g U:= ∏ i : V,X.copy i F U; have hG:=Joint.incoming_env C.path p hJ (cylinder_env (show Interior (Push.GridApprox.window 0 8) F from mommy b)) univ
    let y:= backTo Q N p hk F
    have hp: backTo Q N p hk g=fun U=>∏ i:V, W.copy i y U:= backTo_copies Q N p hJ hk univ F 8 (mommy b) hr
    let M:=moment (C.beta N p) (backTo Q N p hk g); let Z:= Wilson.partition G (C.side N p) (C.beta N p)
    have hz : 0< Z:= partition_pos _
    have hw:=H.wilson.represents N p k hk; obtain hh:=hw.good
    let f:=R; let A:=(C.path.levels.params k).paths; let t':=C.path.levels.clock;let Y:=t'.loopCap k;let δ:=t'.allowance k; let w:=t'.forcedAllowance k; have hW:0 ≤ w:= (Real.exp_pos _).le; have hκ:w ≤1:=Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_pos _).le _)); let u:= t'.hatCoupling k; have hu : 0<u:= inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans (C.path.levels.fits.delayed _))); let β:= f.beta; have hB:0 ≤ β:= (Overlay.beta_positive H.wilson hk).le; have hvk : u ≤ f.p.threshold:=by rw[show f.p= _ from hw.vac]; exact le_mul_of_one_le_right hu.le (Real.one_le_exp (sq_nonneg _))
    let K':= Fintype.card V; let C':= Fintype.card (Site n!); let s:= f.exCost A Y δ;let η:=β*(f.clip.linear/5*b^2);let a:= f.scalar+C'*s-K'*η;have hA: Fintype.card V=Fintype.card W.Cell:=rfl
    have He : Z*‖M‖ ≤ Real.exp a:=by
       have hx(U): ‖(f.eval U:ℂ)*g U‖≤Real.exp a:=by
           by_cases ht:g U=0; rw[ht,mul_zero,norm_zero]; exact (Real.exp_pos _).le
           let z(i:V):Seat n! := (X.omega i,X.translateBy i)
           have h' (i:V): F (Seat.view (z i) U)≠0:=by
               have hν:(X.copy i F U)≠0:= fun h=> ht (prod_eq_zero (mem_univ i) h); intro h; apply hν; unfold Tiling.copy; split; swap;exact h; rw[show F (pull _ _ U)=0 from h]; simp
           have hχ(i:V):0∈flags b ((z i).view U):= not_not.mp (fun hw=> h' i (if_neg hw))
           have hp(i:V): anchor S p hJ i∈ flags b U:=by
               let e:= z i; rw[← Work.H03.flags_send e.1 e.2 b U]; exact mem_image.mpr ⟨0,hχ i, (show affine e.1 e.2 0=anchor S p hJ i by simp only[affine,Signed.act_zero,zero_add]; exact tile_translate ..)⟩
           have hz : K' ≤ (flags b U).card:=  (card_univ (α:=V)).symm.trans_le ( Finset.card_le_card_of_injOn (s:=(@univ V _)) (t:=flags b U) (anchor S p hJ) (fun i _=>hp i) ((show Function.Injective (anchor S p hJ) from fun i j he=> by let s:=C.S.toDepth hJ p; exact (s.embed_parent i|>.symm.trans ((congr_arg s.parent he).trans (s.embed_parent j)))).injOn))
           have he: g U=1:= prod_eq_one fun i _=> by
              have hx: F ((z i).view U)=1:= if_pos (hχ i); unfold Tiling.copy; split; rw[show F (pull _ _ U)=_ from hx];simp; exact hx
           rw [he,mul_one,Complex.norm_real]; exact (flourishX f U b hh hκ hB K' hz hb hT).trans_eq (by unfold a η β s; congr 2; ring)
       have hv:= norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hx : ∀ᵐ U:Config G n! ∂prior G _, _); rw [show (∫ U:Config G n!, _ ∂prior G _) =(Z:ℂ)*M from forfeit Q hk H.wilson g hG] at hv; simpa [norm_mul, Real.norm_of_nonneg hz.le] using hv
    have hν:= f.denominator hh hB u hu hvk (History.nonnegative Q H.wilson N p k hk); have hD:=History.partition_eq Q H.wilson N p k hk; let B:= brinkP C J p k N b
    have hpZ: ‖M‖ ≤ Real.exp (K'* B):=by
       refine le_of_mul_le_mul_left ?_ hz; apply le_trans He; apply le_trans _ (mul_le_mul_of_nonneg_right (hν.trans hD.le) (Real.exp_pos ((K':ℝ)*B)).le)
       rw [← Real.exp_add, Real.exp_le_exp]
       have hz := Vac.suffices_bill H.wilson (p:=p) hk 0 0 0 0 0
       unfold Bands.finalBill at hz; simp only [Nat.cast_zero,zero_mul,add_zero] at hz
       have hT : (C':ℝ)* ( (2*s)+w+β*baseBudget f.clip A u +4*Module.finrank ℝ G.Mat*Real.log (16/u)) ≤ C'* Vac.treasury C.path.levels k:= hz
       rw [show Fintype.card (Edge (Site (C.path.levels.S.side k p)))= Fintype.card (Site n!)*4 from by simp [Edge, Axis]]; let M':=(C.S.a J/C.S.a k);have hx : (↑C':ℝ)= K'*M'^4:=Stock.tallies S ..; unfold a; change f.scalar+C'*s- _≤ f.scalar-C'* (s+ _)- _+ (K':ℝ)*(M'^4* _-η); push_cast; nlinarith only [hT,mul_nonneg (Nat.cast_nonneg C') hW,show (K':ℝ)*M'^4*Vac.treasury C.path.levels k=C'*Vac.treasury C.path.levels k from hx ▸ rfl]
    have hv:=Stock.spacer ‖M‖ B 1 K' (norm_nonneg _) zero_lt_one (show 0< K' from Fintype.card_pos) (by simpa using hpZ)
    unfold M at hv; rw [div_one,hp] at hv; exact hv
end
end YM.Trace.Shepherd
