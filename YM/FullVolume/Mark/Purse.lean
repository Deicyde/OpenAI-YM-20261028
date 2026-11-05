import YM.FullVolume.Mark.Carts
/-! ℓ¹ gauge on source(Family) regular entries keeping every label; gas entries actual at the step's fixed vacuum addresses. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{n:Side}{R E : Rep G n}{Y:Hol G} {κ a b t:ℝ}{S:Desk G n}
def ticket (f:tent F Y S):= sInf {v| Pay F Y S f.val v}
lemma credits (f:tent F Y S){v:ℝ}(h:Pay F Y S f.val v):ticket f≤ v:= csInf_le ⟨0,fun _ h=> rem_nonneg h.2⟩ h
lemma posture (f:tent F Y S): Pay F Y S f.val (ticket f):=by
   let p:ℝ→ Prop:= Pay F Y S f.val
   have hu: ∃ q,p q:= f.property
   obtain ⟨t,hQ,hf⟩:= f.property
   let X:=book (0:F.Coeff) f.val; let P:= S.orient.p
   have hm: ∀ j:ℕ,∃ y,P.supBounds 0 (X.support j) (X.regular j) y∧∀ v:ℝ,P.supBounds 0 (X.support j) (X.regular j) v→ y≤v :=by
      obtain ⟨c,d,h,p⟩:= rem_tabs.mp hf; obtain ⟨p,u,hx⟩:=h.regular; intro j
      let Z:Set ℝ:= {y|P.supBounds 0 (X.support j) (X.regular j) y}; have hc:(0:ℝ)∈ lowerBounds Z:= fun _ h=> h.1
      have hy: Z.Nonempty:= ⟨_,hx j⟩; exact ⟨sInf Z,⟨le_csInf hy hc,fun i hi k hk hu=> le_csInf hy fun i' hx=> hx.2 _ hi _ hk hu⟩,fun v h=> csInf_le ⟨0,hc⟩ h⟩
   have hk (j:ℕ): ∃ x:ℝ, (0 ≤ x∧ ∀ y, ‖X.forced j y‖ ≤ x) ∧ (∀ v:ℝ,(0 ≤ v ∧ ∀ y, ‖X.forced j y‖ ≤ v) → x≤ v):=by
      obtain ⟨c,b,hv,h⟩:= rem_tabs.mp hf; obtain ⟨p,u,h⟩:= hv.forced
      let Z:Set ℝ:= {x| 0 ≤ x∧ ∀ y, ‖X.forced j y‖ ≤ x}; have hc:(0:ℝ)∈ lowerBounds Z:= fun _ h=> h.1
      have hy: Z.Nonempty:= ⟨_,h j⟩; exact ⟨sInf Z,⟨le_csInf hy hc,fun i=> le_csInf hy fun i' hx=> hx.2 i⟩,fun v h=> csInf_le ⟨0,hc⟩ h⟩
   choose y he hy using hm; choose x hx hk using hk; let u j:=P.mass (X.support j) (y j); let v j:=P.mass (S.orient.activities.forced j).support (x j)
   have hw (a b:ℝ)(h: Tab X 0 S.orient S.k a b) : SumBudget u a∧ SumBudget v (S.k*b):=by
      obtain ⟨f,hf,h'⟩:= h.regular; obtain ⟨g,hg,H⟩:=h.forced
      exact ⟨sumBudget_mono hf (fun j=>mul_nonneg (Real.exp_pos _).le (he j).1) (fun j=>mul_le_mul_of_nonneg_left (hy j _ (h' j)) (Real.exp_pos _).le) le_rfl,sumBudget_mono hg (fun j=>mul_nonneg (Real.exp_pos _).le (hx j).1) (fun j=> mul_le_mul_of_nonneg_left (hk j _ (H j)) (Real.exp_pos _).le) le_rfl⟩
   obtain ⟨a,b,h',he'⟩:= rem_tabs.mp hf; obtain ⟨hU,hV⟩:=hw a b h'
   refine ⟨hQ, ∑' i,u i, (∑' i,v i)/S.k,tsum_nonneg hU.1,div_nonneg (tsum_nonneg hV.1) S.sane.le,le_csInf hu (fun i hi=>?_ ),S.sane,⟨y,⟨hU.1,hU.2.1,le_rfl⟩,he⟩, x,⟨hV.1,hV.2.1,?_⟩,hx⟩
   · obtain ⟨a,b,H,hq'⟩:= rem_tabs.mp (show Pay F Y S f.val i from hi).2; obtain ⟨hf,hg⟩:= hw a b H
     exact (add_le_add hf.2.2 ((div_le_iff₀ S.sane).mpr (hg.2.2.trans_eq (mul_comm ..)))).trans hq'
   apply le_of_eq; rw [mul_comm,div_mul_cancel₀ _ S.sane.ne']
lemma entrust (f g:tent F Y S): ticket (f+g) ≤ ticket f+ticket g:=by
   obtain ⟨h,hp⟩:= posture f; obtain ⟨hv,hu⟩:= posture g; exact credits _ ⟨format_add _ _ _ h hv,remAdd _ _ h hv hp hu⟩
lemma entrust_smul (c:ℂ)(f:tent F Y S):ticket (c • f)≤ ‖c‖*ticket f:=by
  obtain ⟨h,hp⟩:= posture f; have h:= stretch_format c h; have hx:=stretch_rem c hp; rw [disguise,smul_zero] at h hx; exact credits _ ⟨h,hx⟩
variable (F Y)
def fortune (S:Desk G n): Seminorm ℂ (tent F Y S) :=
  Seminorm.of ticket entrust fun c f=>by
     refine le_antisymm (entrust_smul c f) ?_; by_cases he:c=0
     · rw [he,norm_zero,zero_mul]; exact rem_nonneg (posture _).2
     have h:= entrust_smul c⁻¹ (c • f); rw [inv_smul_smul₀ he] at h; exact (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans_eq (by rw [norm_inv,← mul_assoc,mul_inv_cancel₀ ((norm_pos_iff.mpr he).ne'),one_mul])
def Coin (S:Desk G n): Type:= tent F Y S
namespace Coin
-- Upgrade to avoid inheriting irrelevant topology
instance: AddCommGroup (Coin F Y S):= inferInstanceAs (AddCommGroup (tent F Y S))
instance: Module ℂ (Coin F Y S):= inferInstanceAs (Module ℂ (tent F Y S))
noncomputable instance: SeminormedAddCommGroup (Coin F Y S):=
  { (inferInstance : AddCommGroup (Coin F Y S)), (Seminorm.toAddGroupSeminorm (fortune F Y S)).toSeminormedAddCommGroup with }
noncomputable instance: NormedSpace ℂ (Coin F Y S) where
   __:= (inferInstance : Module ℂ (Coin F Y S))
   norm_smul_le c f:= entrust_smul c (show tent F Y S from f)
variable {F Y}
def wallet : Coin F Y S≃ₗ[ℂ] tent F Y S:= LinearEquiv.refl _ _
def uses : Coin F Y S →ₗ[ℂ] File G n:= (tent F Y S).subtype.comp wallet.toLinearMap
lemma wealth (f:Coin F Y S):Pay F Y S (uses f) ‖f‖:= posture (wallet f)
lemma wealths (f:Coin F Y S){v:ℝ} : ‖f‖≤ v ↔ Pay F Y S (uses f) v:= ⟨fun h=>⟨(wealth f).1,rem_mono (wealth f).2 h⟩, credits (wallet f)⟩ -- v implicit
lemma noted : Function.Injective (uses (F:=F) (Y:=Y) (S:=S)):= (tent F Y S).injective_subtype.comp wallet.injective
variable (F Y S)
def saver (P:File G n){v:ℝ}(h: Pay F Y S P v): Coin F Y S:= wallet.symm ⟨P,v,h⟩
@[simp] lemma use_save (P:File G n){v:ℝ}(h:Pay F Y S P v): uses (saver F Y S P h)=P:=rfl
end Coin
end YM.MergeProof.Matric
