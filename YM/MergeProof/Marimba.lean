import YM.MergeProof.Badlands
import YM.Next.RANK.HomeSync
import YM.Next.RANK.Stepped
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Function Filter Set Lattice Wilson RG Push Source Extra.Histories Motion
open Planned.GuardedAtom Next.Foundations Labels Extra.Multi
open RelayDifference
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{p N d:ℕ}
section
variable (F:Labels.Frame G d) (X:F.Index→F.Coeff)
def decor : F.Coeff →ₗ[ℂ] F.Coeff where
    toFun:= repaint F X
    map_add' a b:= by simp [repaint,add_smul,Finset.sum_add_distrib]
    map_smul' a b:= by simp [repaint,mul_smul,Finset.smul_sum]
def sliver (F:Labels.Frame G d):= (2*(orbitCost F)^2)⁻¹
lemma sliver_pos (F:Labels.Frame G d):0<sliver F:=inv_pos.mpr (mul_pos zero_lt_two (pow_pos (zero_lt_one.trans_le (orbitCost_one_le _)) _))
set_option maxRecDepth 4000 in
lemma chipcost (a:F.Coeff): (∑ i:Motion.Tally F, ‖chips F a i‖) ≤ orbitCost F*F.coeffSize a:=by
    have hA(m:Motion): (∑ i:F.Index, ‖chips F a (m,i)‖)≤ share*(orbitCost F * F.coeffSize a):=by
       simp_rw [norm_chips, ← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (patch_cost F (backward m) a) share_pos.le
    rw [Fintype.sum_prod_type]; refine le_trans (Finset.sum_le_sum fun i _=> hA i) (le_of_eq ?_)
    have ht:= Motion.card_pos
    simp only [Finset.sum_const,Finset.card_univ, nsmul_eq_mul]
    rw [←mul_assoc,show (Fintype.card Motion : ℝ)*share=1 from mul_inv_cancel₀ (Nat.cast_ne_zero.mpr ht.ne'), one_mul]
private lemma ePack (F:Labels.Frame G d)(T:F.Coeff →ₗ[ℂ] F.Coeff)(he:∀ i,F.coeffSize i≤ 2*F.coeffSize (T i)): ∃ V:F.Coeff≃ₗ[ℂ] F.Coeff,(∀ i,V i=T i)∧∀ i,F.coeffSize (V.symm i)≤2*F.coeffSize i:=by
    have hi : Injective T:= LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun i hp=>by
       apply Work.G08.size_separates; simpa [hp, Labels.Frame.coeffSize] using he i)
    let V:= LinearEquiv.ofBijective T ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩; refine ⟨V,?_, fun i=>?_⟩
    · intro i; rfl
    have hv:= he (V.symm i); have hx : T (V.symm i)=i:= V.apply_symm_apply i; rw [hx] at hv; exact hv
set_option maxRecDepth 4000 in
lemma cheaper (h:∀ i,F.coeffSize (Size.axis F i-X i) ≤ sliver F): ∃ V:F.Coeff≃ₗ[ℂ] F.Coeff, (∀ i,V i=decor F X i)∧ ∀ i, F.coeffSize (V.symm i) ≤ 2*F.coeffSize i:=by
    let T:= decor F X; let z:= Size.axis F; let c:=orbitCost F; have hc:0<c:= zero_lt_one.trans_le (orbitCost_one_le _)
    have he (i): F.coeffSize i ≤ 2*F.coeffSize (T i):=by
       have hs: i - T i=(∑ j:Motion.Tally F, chips F i j • Motion.patch F j.1 (z j.2-X j.2)):=by
           conv_lhs=> lhs; rw [← show repaint F z i=i from repaint_same F LinearMap.id (fun v m=> rfl) i]; unfold repaint
           simp_rw [patch_sub,smul_sub,Finset.sum_sub_distrib]; rfl
       have hp : F.coeffSize (i-T i) ≤ F.coeffSize i/2:=by
           rw [hs]; apply (Size.finite F _ _).trans; let p:=sliver F
           have hA(j:Motion.Tally F): F.coeffSize (chips F i j • Motion.patch F j.1 (z j.2-X j.2)) ≤ ‖chips F i j‖ * (orbitCost F*p):=by
              rw [Size.smul]; exact mul_le_mul_of_nonneg_left ((patch_cost ..).trans (mul_le_mul_of_nonneg_left (h j.2) hc.le)) (norm_nonneg _)
           apply le_trans (Finset.sum_le_sum (fun j _=> hA j)); rw [←Finset.sum_mul]; apply (mul_le_mul_of_nonneg_right (chipcost F i) (mul_nonneg hc.le (sliver_pos F).le)).trans_eq; unfold c sliver; unfold c at hc; field_simp
       have hv := Work.G08.size_triangle F i (T i); linarith only [hv,hp]
    exact ePack F T he
end
-- purchases not through literal. actual oriented.Face. deph.
section
variable (C) (V:SectionData (C.labels.level d)) (H:C.Makes)(hV:V.Sound C.params)
local notation "L"=> C.labels.level d
local notation "T"=> C.path
-- any section
lemma notationL (Y:History G)(d:ℕ) (F:Labels.Frame G d)(S:SectionData F) (N p:ℕ)(o:Site (Y.S.side N p)):
    IsLinearMap ℂ fun v=> initial S Y N p v o:=by
   constructor
   · intro x y; funext U; simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,initial,map_add,SectionData.places,S.eval_linear.map_add]; ring
   intro x y; funext U; simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,initial,map_smul,SectionData.places,S.eval_linear.map_smul]; ring
include hV in
lemma signed_intro (N p:ℕ)(m:Motion) (v:C.label d) :dance m (initial V C.path N p v 0)=initial V C.path N p (Motion.patch (C.labels.level d) m v) 0:=by
   -- translate.Alt
   let α:= C.path.levels.clock.threshold N; let x:=(C.labels.level d).scaled α⁻¹; let T':=C.localSection d; let g:=m.1; let F:= (C.labels.level d); let L':= (C.labels.level d).act g.ortho v
   have hb (b): x (star b)=star (x b):=funext fun i=> by simp [x]
   have he(U:Config G (C.side N p)) : V.places (x v) 0 (pull g 0 U)=V.places (x L') 0 U:=by
     rw [V.placed_signed hV,show affine g (0:Site (C.side N p)) 0=0 by simp [affine], Frame.scaling]
   funext U; unfold Motion.patch dance Motion.scalar; split
   · change star (((C.S.a N:ℂ)^d)⁻¹ * V.places (x v) 0 _) = _ * V.places (x _) 0 _; rw [he,hb]; unfold SectionData.places; rw [hV.ordinary_real]; simp; exact Or.inl rfl
   change _= _ * V.places (x _) 0 _; change _ * V.places (x v) 0 _ = _; rw [he]
end
end YM.MergeProof
