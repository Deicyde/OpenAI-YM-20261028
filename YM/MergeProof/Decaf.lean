import YM.MergeProof.Castle
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Festal

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Menu
open Function Filter Lattice Wilson RG MeasureTheory Finset Push Local Extra.Histories PhysicalNext.Repeat Lotus Merge Merge.Palette Accent Marker
open Extra.Multi GridApprox.Nil
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {V ι β : Type}[DecidableEq V] {B:Census V} {G:Gauge}{f c:Side}{R:Rep G f}{E:Rep G c}
open Extra.Trajectories
variable {D:GaugeDoor R E}{q:ι→Leaf R}
    {x:Set Wing}{o:Site f}{b:Site c}{t:ι→ℂ}{ψ:Response G c}
    {α:Config G f→ℂ}{δ:ℂ}{F:Box f→ Config G f→ℂ}{Z:Box c→ Config G c→ℂ}
    {A p e:ℝ}
variable {w:V→ℝ}
private lemma burning (B:Census V)(v:B.Mode) [Fintype ι](u:ι→ℂ): ∑ j,Poly.send v (u j)=Poly.send v (∑ j,u j):=by
   ext i; rw [Poly.part_sum,Poly.part_send]; simp_rw [Poly.part_send]; split
   next h=>rfl
   next h=>simp only [sum_const_zero]
-- singular bores compress wing. quantitative on actual toll.
lemma narrow1 (B:Census V)[Countable ι](v:V)(h: Odyssey x o b 1 α F Z δ A p D q t ψ)(hs:x.Finite){S:StepData c f}(hc:SoundDoor S D)(ht:Tunes D)(hv:∀ i,0<w i):
   ∃ I : Type,∃ _ : Fintype I,∃ N:I→ Hat B R,(∀ i,(N i).s=B.fire v ∧ o∈ (N i).M.crest) ∧
   (∑ j:I, R.p.mass (N j).M.crest (fare (N j) w)) ≤ 2*w v*A ∧ (∀ U,∑ j,odour (N j) U= Poly.send (B.fire v) (α U-δ)) ∧
   (∀ i U,∑ j,fragrance (N j) U i=Poly.send (B.fire v) (F i U)) ∧ ∀ i U,(∑ j,owl (N j) D v i U)=Z i U-hook E.activities E.p.threshold ψ i U:=by
   let a i:= (q i).turn; have ht': (Set.range a).Finite:= hs.subset (by rintro j ⟨v,rfl⟩; exact (h.member v).2)
   let P:= Set.range a; letI:Fintype P:= ht'.fintype; let k:ι→↥P:=fun i=> ⟨a i,i,rfl⟩; let locus(i:↥P):={i':ι // k i'=i}; have ho (i:↥P):∃ j, k j=i:= by obtain ⟨j,h⟩:= i.property; exact ⟨j,Subtype.ext h⟩
   letI (i:↥P): Nonempty (locus i):= ⟨⟨_, (ho i).choose_spec⟩⟩
   let tag1 (i:↥P)(v:locus i):= q v.val; let X (i:↥P)(v:locus i):= t v.val
   have he (i:↥P)(x:locus i): (tag1 i x).turn=i.val:= congr_arg Subtype.val x.property
   let Y i:= ‖t i‖* load (q i); have hY:SumBudget Y A:= h.purchase
   choose N hM hP hO hK hF using fun i:↥P=> solo D (tag1 i) i.val (he i) hc ht (X i) (hY.2.1.comp_injective Subtype.val_injective) v B w hv
   let I:= ↥P × Bool
   have hp₀ (i:↥P): ∑' j:locus i,Y j.val = Real.exp (R.p.supportExponent *coverNumber R.p.B (i.val.support R))*(∑' j:locus i, ‖X i j‖*(tag1 i j).weight):= by -- type i
      rw [← tsum_mul_left]; refine tsum_congr fun x=>?_ ; unfold Y load BudgetPoint.mass; rw [show (q x.val).crest=i.val.support R from congr_arg (fun z=> z.support R) (he i x)]; unfold X tag1; ring
   have hd: (∑ i: ↥P,∑' j:locus i,Y j.val) ≤ A:=by
      have h := (heavy k hY.2.1).tsum_eq; rw [tsum_fintype] at h; exact h.trans_le hY.2.2
   have hz (i:↥P): o∈ i.val.support R:= let j:locus i:=Classical.ofNonempty; (he i j) ▸ (show _ from (h.member j.val).1)
   let N' (i:I): Hat B R:= N i.1 i.2
   have ha (i:↥P) j: (N i j).M.crest=i.val.support R:= congr_arg (fun j=> j.support R) ((hM ..).2)
   have hG(p:ι→ℂ){t:ℂ}(h:HasSum p t) : ∑ i: ↥P,∑' j:locus i,p j.val=t:=by
      have ht := (bulky k h.summable).tsum_eq; rw [tsum_fintype] at ht; exact ht.trans h.tsum_eq
   refine ⟨I,inferInstance,N',fun i=> ⟨(hM ..).1,(ha i.1 i.2).symm ▸ hz _⟩, ?_,fun U=>?_,fun i U=>?_,fun i U=>?_⟩
   · refine le_trans ?_ (mul_le_mul_of_nonneg_left hd (mul_nonneg zero_le_two (hv v).le)); unfold N' I; rw [Fintype.sum_prod_type,mul_sum]; refine sum_le_sum fun i _=>?_ ; dsimp only; simp_rw [ha,BudgetPoint.mass]; rw [← Finset.mul_sum,hp₀]; exact (mul_le_mul_of_nonneg_left (hP i) (Real.exp_pos _).le).trans_eq (by ring)
   · unfold N' I; rw [Fintype.sum_prod_type,← hG _ (h.lyric U),← burning B]; exact sum_congr rfl fun i _=> hO ..
   · unfold N' I; rw [Fintype.sum_prod_type,← hG _ (h.old i U),← burning B]; exact sum_congr rfl fun i _=> hK ..
   unfold N' I; have hv := h.grants i U; simp_rw [one_mul] at hv; rw [Fintype.sum_prod_type,← hG _ hv]; exact sum_congr rfl fun i _=> hF ..
end YM.MergeProof.Menu
