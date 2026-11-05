import YM.MergeProof.Buys
import YM.MergeProof.North.Fermi
import YM.MergeProof.Routes


set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory Matrix
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Switch
open scoped Topology BigOperators Classical
variable {V ι : Type}[Fintype V][DecidableEq V][Fintype ι]{G:Gauge}{f c:Side}{R:Rep G f}
local notation "X"=> Aged V
lemma jetTurn {F G F' G':Ways ι}(h:Models F F')(hg:Models G G')(b:Equiv.Perm ι){s}(hh:∀ x∈Set.Icc (0:ℝ) 1,∀ p⊆s, G x (p.image b)= F x p): jet G (s.image b)=jet F s:=by
   have he x (hx:0<x)(he:x≤1)(p:Finset ι)(hp:p⊆s) : F' x p=G' x (p.image b):=by
       induction p using Finset.strongInduction with
       | H p IH=>
         have hz : value x (G' x) (p.image b)= value x (F' x) p:= (congr_fun (hg.current x ⟨hx.le,he⟩) _).trans ((hh x ⟨hx.le,he⟩ _ hp).trans (congr_fun (h.current x ⟨hx.le,he⟩) p).symm)
         rw [Switch.value_subset,Switch.value_subset,← Equiv.sum_comp b.finsetCongr] at hz
         have hb(j:Finset ι): b.finsetCongr j=j.image b:=by rw [Equiv.finsetCongr_apply,map_eq_image];rfl
         simp_rw [hb,image_subset_image_iff b.injective, card_image_of_injective _ b.injective] at hz
         let a j:=if j⊆p then x^Finset.card j*G' x (j.image b) else 0
         let g j:=if j⊆p then x^Finset.card j*F' x j else 0; change ∑ j,a j=∑ j,g j at hz
         rw [← sum_erase_add univ a (mem_univ p), ← sum_erase_add univ g (mem_univ p)] at hz
         have ht : ∑ j∈univ.erase p,a j=∑ j∈univ.erase p,g j:= by
             refine sum_congr rfl fun j hj=>?_ ; unfold a g; split
             next hh=> rw [IH j (Finset.ssubset_iff_subset_ne.mpr ⟨hh,ne_of_mem_erase hj⟩) (hh.trans hp)]
             rfl
         rw [ht] at hz; apply mul_left_cancel₀ (pow_pos hx p.card|>.ne')
         exact (if_pos (show p⊆p from Finset.Subset.rfl)).symm.trans ((add_left_cancel hz).symm.trans (if_pos Finset.Subset.rfl))
   rw [hg.exact,h.exact]; exact tendsto_nhds_unique ((hg.converge _).congr' (approached.mono fun x hx=> (he x hx.1 hx.2 _ Finset.Subset.rfl).symm)) (h.converge _)
-- Hat lev
variable (M:ι→Hat (Aged V) R)(c₀ v:V) (b:Equiv.Perm V)(m: Motion)(x: Site f)
structure Kin (P:R.activities.Moves m.1 x)(E:Equiv.Perm ι):Prop where
   here: b c₀=v
   cares i: Focused c₀ (M i).s↔ Focused v (M (E i)).s
   plot i: Focused c₀ (M i).s→ (M (E i)).s=drum b (M i).s ∧ (M (E i)).M=(M i).M.route P ∧ (M (E i)).charge= scalar m (M i).charge
end YM.MergeProof.Ribbons
