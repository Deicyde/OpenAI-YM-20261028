import YM.UVExtension.Harvest.Oats
import YM.UVExtension.Hearth.Tureen

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Harvest
open Finset Filter Set MeasureTheory Function Lattice Wilson Metric
open Extraction
open scoped Topology BigOperators ContDiff Classical
variable {X Y :Type*}[MetricSpace Y]
-- stable patched continuous diagonal readability. variation uniform across arbitrary offsets for each-period disk. no first-countable assumption on space of choices needed when gate one fixed scalar
lemma stitched {f:ℕ→ X→Y}(h:X→ ℝ) (x:X) (hx:h x=0) (hp:∀ z:ℕ→X,Tendsto (fun i=> h (z i)) atTop (𝓝 0)→ Arrives (fun i=>f i (z i)))(y:Y)(hy:Tendsto (fun i=>f i x) atTop (𝓝 y))(ε:ℝ)(he:0 < ε): ∃ δ:ℝ,0 < δ∧ ∀ᶠ n in atTop,∀ z:X,|h z| ≤ δ → dist (f n z) y<ε:=by
    by_contra hc
    have hf δ (hd:0<δ):∀ i:ℕ,∃ j:ℕ,i≤j∧ ∃ z:X,|h z|≤δ ∧ ε ≤ dist (f j z) y:=by
       have he : ¬ ∀ᶠ n in atTop,∀ z:X,|h z|≤δ → dist (f n z) y<ε := fun e=> hc ⟨δ,hd,e⟩
       simpa using he
    let r(i:ℕ):ℝ:= (↑i+1)⁻¹; have hr(i):0<r i:=by unfold r; positivity
    have hR:Tendsto r atTop (𝓝 0):= tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    choose k hk z hZ ht using fun i=>hf (r i) (hr i)
    let g (n:ℕ):ℕ:= Nat.rec 0 (fun i v=>k i (v+2)) n
    let G':= fun i:ℕ=>g (i+1)
    have hG i:g (i+1)= k i (g i+2):=rfl; have hm i:g i+2 ≤ g (i+1):= hG i ▸ hk i _
    have hg: StrictMono g:= strictMono_nat_of_lt_succ fun i=> by simpa only [] using Nat.lt_of_lt_of_le (by omega) (hm i)
    have hG':StrictMono G':=strictMono_nat_of_lt_succ fun i=>hg (Nat.lt_succ_self (i+1))
    let V i:= z i (g i+2); let W(j): X:= if h:∃ i,G' i=j then V (Classical.choose h) else x
    have hv(i): W (G' i)=V i:=by unfold W; rw [dif_pos (show ∃ j:ℕ,G' j=G' i from ⟨_,rfl⟩)]; exact congr_arg V (hG'.injective (Classical.choose_spec (show ∃ j:ℕ,G' j=G' i from ⟨_,rfl⟩)))
    have hs(i):W (G' i+1)=x:=dif_neg (by rintro ⟨t,ht⟩; rcases le_or_gt t i with h|h; have hh:=hG'.monotone h; omega; have hh:= hG'.monotone (show i+1 ≤ t from h); have hy:G' i+2≤G' (i+1):=hm (i+1); omega)
    obtain ⟨Z,hY⟩:=hp W (by
       rw [Metric.tendsto_nhds]; intro ε he; obtain ⟨l,hl⟩:= eventually_atTop.mp (hR.eventually (gt_mem_nhds he)); filter_upwards [eventually_ge_atTop (G' l)] with n hn; by_cases h:∃ i,G' i=n; · obtain ⟨i,rfl⟩:=h; simp only [hv,Real.dist_eq,sub_zero]; exact lt_of_le_of_lt (hZ i _) (hl i (hG'.le_iff_le.mp hn))
       unfold W; rw [dif_neg h,hx,dist_self]; exact he)
    have hT: Tendsto (fun i=>G' i+1) atTop atTop:= (strictMono_nat_of_lt_succ fun i=>Nat.add_lt_add_right (hG' (Nat.lt_succ_self i)) 1).tendsto_atTop
    have hX : Z=y:= tendsto_nhds_unique_of_eventuallyEq (hY.comp hT) (hy.comp hT) (Eventually.of_forall (fun i=> by dsimp only [Function.comp_apply]; rw [hs i]))
    obtain ⟨i,hi⟩:=(Metric.tendsto_nhds.mp (hY.comp hG'.tendsto_atTop) ε he).exists
    change dist (f (G' i) (W (G' i))) Z< ε at hi; rw [hv i,hX] at hi; exact hi.not_ge (ht i (g i+2))
end YM.UVExtension.Harvest
