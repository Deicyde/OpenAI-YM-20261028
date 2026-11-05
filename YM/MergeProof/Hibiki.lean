import YM.MergeProof.Accent
import YM.Next.RANK.HomeSync
import YM.Next.RANK.SealMix
import YM.Work.F05.Reindex


/-! compaction by actual support & inventory, no volatile terminal loss -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Next.Rank Edition Baler Value Glyph Thirst Push GridApprox.Nil
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V]{B:Census V}{o: V→Site n}
variable {u v t e:ℝ}{w:V→ℝ}{P: BudgetPoint}
section index
variable (S: Type) [Fintype S] [DecidableEq S] {p:S→modes V→Prop}(Φ:S→Support n)(F:S → Config G n→ veil V)
abbrev Glide (p:S→modes V→Prop):= {i:S × modes V // p i.1 i.2}
variable {S}
lemma rake (h:∀ i T, (∃ U, (F i U).part T ≠ 0) → p i T)(U:Config G n)(i:S):
    ∑ j:Glide S p,(if j.val.1=i then Poly.send j.val.2 ((F j.val.1 U).part j.val.2) else 0) = F i U:=by
    ext t; rw [Poly.part_sum]; by_cases hx:p i t
    · let j:Glide S p:= ⟨(i,t),hx⟩
      rw [Finset.sum_eq_single j]; rotate_left
      · rintro ⟨⟨k,u⟩,hK⟩ _ hU; change Poly.part (if k=i then _ else 0) t=0; split_ifs with he; apply (Poly.part_send ..).trans (if_neg (fun hh=> hU (Subtype.ext (Prod.ext he hh.symm)))); rfl
      · simp
      rw [if_pos (show j.val.1=i from rfl)]; exact (Poly.part_send ..).trans (if_pos rfl)
    rw [Finset.sum_eq_zero]
    · exact (Classical.byContradiction fun hh=> hx (h i t ⟨U, Ne.symm hh⟩))
    rintro ⟨⟨k,u⟩,hK⟩ _; change Poly.part (if k=i then _ else 0) t=0; split_ifs with he
    · apply (Poly.part_send ..).trans (if_neg (fun (h:t=u)=> hx (h.symm ▸ he ▸ hK)))
    rfl
lemma guide (h:Towed w Φ F P.B e t)(hg:∀ i v,p i v→ v.val.image o ⊆ Φ i)(hw:∀ i,0<w i): ∃ a:Glide S p→ℝ, (∀ i,0 ≤ a i ∧ ∀ U, Poly.price w (Poly.send i.val.2 ((F i.val.1 U).part i.val.2)) ≤ a i) ∧ stars P (fun i:Glide S p=>i.val.2) (fun i=>Φ i.val.1) e a t:=by
    obtain ⟨f,-,hx,hF⟩:= h
    choose α hA hQ hv using hF
    let v (j:S×modes V):= Poly.toll w j.2*α j.1 j.2; have hp j:0 ≤ v j:= mul_nonneg (Poly.worth hw _).le (hA _ _)
    let a(i:Glide S p):=v i.val
    refine ⟨a,fun i=> ⟨hp i.val,fun U=> (Poly.solo ..).trans_le (mul_le_mul_of_nonneg_left (hQ ..) (Poly.worth hw _).le)⟩,fun i=>?_⟩
    let Q (j:S×modes V):= if o i∈Φ j.1 then v j*Thirst.debt P.B e (Φ j.1) else 0; have hc j:0≤ Q j:= by unfold Q; split; exact mul_nonneg (hp _) (Real.exp_pos _).le;rfl
    let K:= Thirst.pay (fun j:Glide S p=> a j*Thirst.debt P.B e (Φ j.val.1)) (fun j=> i∈j.val.2.val)
    suffices hh:SumBudget K t from hh; refine ⟨fun i=>?_,Summable.of_finite,?_⟩
    · unfold K Thirst.pay; dsimp only; split; exact mul_nonneg (hp _) (Real.exp_pos _).le;rfl
    rw [tsum_fintype]; refine (Finset.sum_le_sum (g:=fun i:Glide S p=> Q i.val) ?_).trans ?_
    · intro j _; unfold K Thirst.pay; dsimp only; split; next ht=> rw [show Q j.val=_ from if_pos (hg _ _ j.property (mem_image_of_mem _ ht))]
      exact hc _
    · let Y: Finset (S×modes V):=(univ:Finset (Glide S p)).image Subtype.val
      have hh :=sum_le_sum_of_subset_of_nonneg (subset_univ Y) (fun i _ _=>hc i); unfold Y at hh; rw [sum_image (fun _ _ _ _ he=>Subtype.val_injective he)] at hh; apply hh.trans
      apply le_trans _ (hx (o i)|>.2.2); rw [Fintype.sum_prod_type,tsum_fintype]; refine Finset.sum_le_sum fun j _=> ?_; by_cases h : o i∈Φ j
      · unfold Q; dsimp only; simp_rw [if_pos h]; rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hv j) (Real.exp_pos _).le
      unfold Q;dsimp only; simp only [if_neg h,Finset.sum_const_zero,le_refl]
end index
end YM.MergeProof.Accent
