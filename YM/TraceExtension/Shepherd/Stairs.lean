import YM.TraceExtension.Shepherd.Breath
import YM.Vac.Caps
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Shepherd
open RG Wilson Gauge Lattice Source AnalyticBridge VerifiedReset Finset Ac MergeProof Cask Function Pressure Next.Fluctuations PathData
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff
variable {G:Gauge}{n:Side}(R:Rep G n)
local notation "W!"=> R.path
local notation "r!"=> R.clip.relaxation
local notation "C!"=> R.clip
local notation "b!"=> R.p.threshold
variable {U V:Config G n}
structure Brink (d:ℝ)(U V:Config G n):Prop where
    pos:0≤ d
    close (s:Seat n) e : knot (s.view U e) (s.view V e) ≤ d
    kept (s:Seat n) : PathData.kept R.clip R.p.threshold 0 (s.view U) ↔ PathData.kept R.clip R.p.threshold 0 (s.view V)
    wet (s:Seat n) (p:PlaqAxes) : let F(a):= G.chord (faceValue a ((0:Site n),p)); F (s.view U) ≠F (s.view V) →F (s.view U) ≤ R.p.threshold ∧ F (s.view V)≤ R.p.threshold
variable {d:ℝ} (H:Brink R d U V) (s:Seat n)
def phial (p:Low):= |p.mark R.path R.clip| *(p.length R.path + (1:ℝ))*Real.exp (p.length R.path/R.clip.relaxation)
def thyme (p:Low)(d:ℝ):= phial R p * ((2*kindle G) * d * R.p.threshold)
def prime (p:Low) :=|p.mark R.path R.clip| * (2 * R.p.threshold * Real.exp ((p.length R.path)/R.clip.relaxation))
local notation "U'!" => s.view U
local notation "V'!" => s.view V
lemma phial_nonneg (p) : 0 ≤ phial R p:=by unfold phial; positivity
lemma primed (p : Low): |Low.live R.path R.clip p R.p 0 (s.view U)| ≤ prime R p:= Low.shapeBound ..
include H
lemma kube (p:Low) : |Low.live W! C! p R.p 0 U'! -Low.live W! C! p R.p 0 V'!| ≤ thyme R p d:=by
    let F:=p.1; let X:=U'!; let Y:=V'!;let a:=p.mark R.path R.clip
    have hv:= H.pos; have hp:= R.p.threshold_pos; have ht:= G.colorScale_pos; have hxk: 4 ≤ kindle G:=by unfold kindle; linarith only[ht]
    have hx': 0 ≤ thyme R p d:=mul_nonneg (phial_nonneg ..) (by positivity)
    have hm:=H.kept s; cases he:p.2 with
    | inl u=>
        unfold Low.live; rw[he]
        let x:=G.chord (faceValue X ((0:Site n),F)); let y:=G.chord (faceValue Y ((0:Site n),F)); change |clipped _ _ x-clipped _ _ y|≤_
        by_cases hs:x=y; rw [hs,sub_self,abs_zero]; exact hx'
        obtain ⟨h,h'⟩:= H.wet s F (show x≠y from hs); let c:=R.clip.direct; have h0:0≤ c:= (C!|>.quadratic_pos).le
        unfold thyme phial Low.mark Low.length; rw [he]; unfold clipped; rw [if_pos h,if_pos h']
        change |c*x^2/2-c*y^2/2|≤ |c| *(↑(0:ℕ)+1)*Real.exp ((↑(0:ℕ):ℝ) / r!)*_
        have hh:= castC (faceValue X ((0:Site n),F)) (faceValue Y ((0:Site n),F)); have hu:= hike X Y (H.close s) (0:Site n) (square F.val.1 F.val.2); have ht:|x-y| ≤ 4*d:= hh.trans (by simpa [square] using! hu); have he' : |x+y| ≤ 2*b!:=by rw [abs_of_nonneg (add_nonneg (G.chord_nonneg _) (G.chord_nonneg _))]; linarith only [h,h']
        rw [show c*x^2/2-c*y^2/2=c/2*((x+y)*(x-y)) by ring,abs_mul,abs_of_nonneg (show 0≤c/2 by positivity), abs_mul]; have hL:|x+y| *|x-y|≤(2*b!)*(4*d) := mul_le_mul he' ht (abs_nonneg _) (by positivity)
        simp only [Nat.cast_zero,zero_add,zero_div,Real.exp_zero,mul_one,abs_of_nonneg h0]; apply (mul_le_mul_of_nonneg_left hL (by positivity : 0≤c/2)).trans; nlinarith only[mul_le_mul_of_nonneg_right hxk (show 0 ≤ c*d*b! by positivity),show 0 ≤ c*d*b! by positivity]
    | inr j=>
        unfold Low.live; rw [he]; dsimp only [Sum.elim_inr]; by_cases h:kept C! b! 0 X; swap;· rw [if_neg h,if_neg (mt hm.mpr h),sub_self,abs_zero]; exact hx'
        rw [if_pos h,if_pos (hm.mp h),← mul_sub,abs_mul]; unfold thyme phial; rw[mul_assoc,mul_assoc]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        let l:=p.left R.path j; let u:= p.right R.path j; let L (V:Config G n):= l.atSite V 0; let Z (V:Config G n):=u.atSite V 0
        let k:ℝ:=p.length R.path; let t:=Real.exp (k/r!); let b:= R.p.threshold*t
        have hb₀ := kept_slot l h; have ht₀:= kept_slot u (hm.1 h); have hr : 0 ≤ r!:= R.clip.radius_pos.le; have htL : p.length R.path=l.length + u.length:= by rw[Low.length,he];rfl
        have hl : (l.length:ℝ) ≤ k:= Nat.cast_le.mpr (htL.symm ▸ Nat.le_add_right ..); have hu : (u.length:ℝ) ≤ k:= Nat.cast_le.mpr (htL.symm ▸ Nat.le_add_left ..); have hi: 0 ≤ k:= by positivity
        have hhL: ‖L X‖≤ b:= hb₀.trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (div_le_div_of_nonneg_right hl hr)) hp.le); have hhU:‖Z Y‖≤ b:= ht₀.trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (div_le_div_of_nonneg_right hu hr)) hp.le)
        let z:= kindle G*k*d; have hy (c:Slot) (hv':(c.length:ℝ) ≤ k): ‖c.atSite X (0:Site n)-c.atSite Y 0‖ ≤ z:= (costsH X Y (H.close s) hv _ _).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv' (by positivity)) hv)
        unfold Low.plain; rw[he]; change |⟪L X,Z X⟫_ℝ/2 - ⟪L Y,Z Y⟫_ℝ/2| ≤ (k+1) * (t* _)
        rw [show ⟪L X,Z X⟫_ℝ/2-⟪L Y,Z Y⟫_ℝ/2=(⟪L X,Z X-Z Y⟫_ℝ+⟪L X-L Y,Z Y⟫_ℝ)/2 from by rw[inner_sub_right,inner_sub_left]; ring, abs_div,abs_of_pos (by norm_num : 0<(2:ℝ)), div_le_iff₀ (by norm_num : 0<(2:ℝ))]; apply (abs_add_le ..).trans
        have h1:= (abs_real_inner_le_norm (L X) (Z X-Z Y)).trans (mul_le_mul hhL (hy u hu) (norm_nonneg _) (by positivity)); have h2:= (abs_real_inner_le_norm (L X-L Y) (Z Y)).trans (mul_le_mul (hy l hl) hhU (norm_nonneg _) (by positivity))
        apply (add_le_add h1 h2).trans; unfold z b; nlinarith only [mul_nonneg (show 0 ≤ t*(kindle G*d*b!) by positivity) hi, show 0 ≤ t*(kindle G*d*b!) by positivity]
def lilt (p:Fleece):= (tooth R p).magnitude * b!^(rowD p)
def bingo (p:Barley):= |wake R p| *p.elim (prime R) (lilt R)
def balm (p:Barley)(d:ℝ):= |wake R p| *p.elim (fun i=>thyme R i d) (fun i=>2*lilt R i)
omit H
lemma canto (p:Barley)(V:Config G n): |chore R p V|≤ bingo R p:= by unfold chore bingo; rw [abs_mul]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); cases p; exact Low.shapeBound ..; exact healthy_atom ..
include H
lemma casto (p: Barley): |chore R p U'!-chore R p V'!| ≤ balm R p d:=by unfold chore balm; rw[← mul_sub,abs_mul]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); cases p with | inl i=> exact kube R H s i | inr i=> exact (abs_sub ..).trans ((add_le_add (healthy_atom ..) (healthy_atom ..)).trans_eq (show lilt R i+lilt R i=2*lilt R i from (two_mul _).symm))
end YM.Trace.Shepherd
