import YM.FullVolume.Relay.Sectors
import YM.FullVolume.Nectar.Farey
/-
 `WindowP`: per-site weighted ℓ¹ across range. Used with K families.
 `Polaris` of lively and quiet budgets, and back into Pact hot.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Nectar
open RG Set Finset Filter Ray Function Amp Beam
open scoped Topology BigOperators Classical ENNReal
open MergeProof MergeProof.Accent Marker Push Push.AbsoluteSums Lattice Wilson Ac GridApprox.Nil
variable {V I:Type}[DecidableEq V] [Fintype V] [Fintype I]{B:Marker.Census V}{G:Gauge}{n:Side}
variable {F:sun→I→ Config G n→Poly B}{S:I→Support n}{p q v t c:ℝ}{a:ℕ}{w:V→ℝ}
    {k:Finset B.Mode}{x: V→ Site n}(hw:∀ i,0<w i)
def WindowP (F:sun→ I→ Config G n→ ℂ) (S:I→Support n)(b:ℕ)(e A:ℝ):Prop:= ∃ p, Summable p ∧ Ac.Hit S b p e A ∧ ∀ i:I,Feel (fun t:sun=> F t i) (p i)
abbrev receive (F:sun→ I→ Config G n→ Poly B)(j:B.Mode)(s:sun)(i:I)(U:Config G n):= (F s i U).part j
private lemma siteBudgetFin (f:I→ℝ) (h:∀ i,0≤f i)(hv:∑ i,Real.exp (p*coverNumber a (S i))*f i ≤ v):Hit S a f p v:=by
    intro i; refine ⟨fun j=> ?_, Summable.of_finite,?_⟩
    · dsimp only; split; exact mul_nonneg (h _) (Real.exp_pos _).le; rfl
    rw [tsum_fintype]; refine (sum_le_sum (fun j _=>?_)).trans hv
    split; exact le_of_eq (mul_comm ..); exact mul_nonneg (Real.exp_pos _).le (h _)
private lemma siteBudgetBoth (f g:I→ℝ)(h:Hit S a f p q)(hv:Hit S a g p v):Hit S a (f+g) p (q+v):=by
    intro i
    let A(f:I→ℝ)(j:I):= if i∈ S j then f j*Real.exp (p*coverNumber a (S j)) else 0
    have he : A (f+g)=A f+A g:=by ext j; unfold A; by_cases ht:i∈ S j <;> simp [ht,add_mul]
    change SumBudget (A (f+g)) (q+v); rw [he]; obtain ⟨hp,hx,hQ⟩:= h i; obtain ⟨ha,hV,hW⟩:= hv i
    refine ⟨fun i=> add_nonneg (hp i) (ha i),Summable.of_finite,?_⟩; change (∑' j:I,(A f j + A g j)) ≤ _
    change Summable (A f) at hx; change Summable (A g) at hV
    rw [hx.tsum_add hV]; exact add_le_add hQ hW
include hw
lemma Polaris.from_modes (h:Pact w S F (lively B) a p v) (hx:WindowP (receive F B.quiet) S a p q):Polaris w S F a p (q+v):=by
    let k:= lively B
    obtain ⟨f,hf,hx,hB⟩:=hx; obtain ⟨b,hb,hV⟩:=h.coins
    let g(i:I)(j:B.Mode):= if ht:j∈ (lively B) then b (i,⟨j,ht⟩) else f i
    let z (i:I):=∑ j:↑k, Poly.toll w j.val*b (i,j)
    have hQ(i):0≤ z i:= sum_nonneg fun j _=>mul_nonneg (Poly.worth hw _).le (hV _|>.positives)
    have he(i j): Feel (fun t U=>(F t i U).part j) (g i j):=by
       unfold g; split
       next ha=> exact hV (i,⟨j,ha⟩)
       next ha=> have ht : j=B.quiet:=of_not_not (fun hh=>ha ((lively_ne _).2 hh)); rw [ht]; exact hB i
    have ht (i) : wordsPrice w (g i)=f i+z i:=by
       unfold wordsPrice; rw [← Finset.sum_erase_add _ _ (a:=B.quiet) (by simp),add_comm]
       refine congr_arg₂ HAdd.hAdd ?_ ?_
       · unfold g; simp [lively]
       change ∑ i₁∈ lively B, Poly.toll w i₁ * g i i₁ = _; unfold z k; rw [← sum_coe_sort]; refine sum_congr rfl (fun i _=>?_)
       unfold g; rw [dif_pos i.property]
    refine ⟨f+z,Summable.of_finite, siteBudgetBoth f z hx (siteBudgetFin z hQ ?_),fun i=>⟨g i,fun j=> (he i j).positives,(ht i).le, he i⟩⟩
    rw [Fintype.sum_prod_type] at hb; unfold z; simp_rw [mul_sum, ← mul_assoc]; exact hb
-- from site per-Polaris to global Pact. Trim dead weights when support misses all roots. No factor volume.
lemma Polaris.roll_up (h:Polaris w S F a p v) (hB:∀ u i, Borne x (S i) (F u i) t) (hl:k ⊆ lively B) : Pact w S F k a p ((Fintype.card V:ℝ)*v):=by
    let Q i:= ∃ j:V,x j∈ S i
    obtain ⟨z,hz,hp,hx⟩:=h; have hu i:0≤z i:=LeafPaid.pricesN hw (hx i)
    choose b hb hB' hV using hx
    let f (i:I× ↑k):= if Q i.1 then b i.1 i.2.val else 0
    have hX (i : I× ↑k): Feel (fun s u=>(F s i.1 u).part i.2.val) (f i):=by
       unfold f; split
       next h=> exact hV ..
       next hn=>
          have he i:(i: ↑k).val ≠ B.quiet:= (lively_ne _).1 (hl i.2)
          have h(i : ↥k): i.val.val.Nonempty:= nonempty_iff_ne_empty.mpr (fun hh=> he i (Subtype.ext hh))
          obtain ⟨j,hj⟩:= h i.2
          have hs(u y) : (F u i.1 y).part i.2.val=0:= of_not_not (fun hh=> hn ⟨j,(hB u i.1).place _ _ hh (mem_image_of_mem _ hj)⟩)
          simp_rw [hs]; exact Feel.staticC (fun _=> 0) le_rfl (fun _=> norm_zero.le)
    let V₁ (i:I)(j:V):= if x j∈ S i then z i*Real.exp (p*coverNumber a (S i)) else 0
    have ht (i j) : 0 ≤ V₁ i j:=by unfold V₁; split; exact mul_nonneg (hu _) (Real.exp_pos _).le; rfl
    refine ⟨f,?_,hX⟩
    rw [Fintype.sum_prod_type]; refine le_trans (b:=∑ i:I,∑ j:V,V₁ i j) ?_ ?_
    · apply sum_le_sum; intro i _; by_cases hh:Q i
      · obtain ⟨j,hj⟩:=hh
        apply le_trans _ (Finset.single_le_sum (fun k _=>ht i k) (mem_univ j)); unfold V₁ f; dsimp only; simp_rw [if_pos (show Q i from ⟨j,hj⟩)]; rw [if_pos hj,mul_comm (z i)]; simp_rw [mul_assoc];rw [← Finset.mul_sum]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; rw [show (∑ j:↥k,Poly.toll w j.val * b i j.val)=∑ j∈k, Poly.toll w j*b i j from sum_coe_sort k (fun j:B.Mode=> Poly.toll w j*b i j)]; exact (Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun j _ _=> mul_nonneg (Poly.worth hw _).le (hb i j)).trans (hB' i)
      unfold f; dsimp only; simp only [if_neg hh,mul_zero,sum_const_zero]; exact sum_nonneg fun j _=> ht _ _
    rw [sum_comm]; calc
     _≤ ∑ _j:V,v:=sum_le_sum fun j _=> Extra.Multi.Budget.cap (hp (x j)) _
     _=_:=by simp
-- from global Pact.View."ψ" to Polaris of connection.
lemma conviction_paid (ψ:sun→ V→ Response G n) (v:V→ℝ) (hv:∀ i,Treasure (fun s:Support n=>Real.exp (p*coverNumber a s)) (fun t=> ψ t i) (v i)) : Polaris w Prod.snd (fun t=> Accent.conviction (ψ t) B) a p (∑ i,w i*v i):=by
   choose f hF h using fun i=> (hv i).coins
   let g(i: V × Support n):= w i.1*f i.1 i.2
   refine ⟨g,Summable.of_finite,siteBudgetFin _ (fun i=>mul_nonneg (hw _|>.le) (h i.1 i.2|>.positives)) ?_,fun i=>?_⟩
   · rw [Fintype.sum_prod_type]; apply sum_le_sum; intro i _; apply le_trans _ (mul_le_mul_of_nonneg_left (hF i) (hw i).le); unfold g; rw [mul_sum]; simp_rw [mul_left_comm (Real.exp _)]; exact le_rfl
   let b:B.Mode:=B.fire i.1; let C (j:B.Mode):= if j=b then f i.1 i.2 else 0
   refine ⟨C,fun j=>?_,?_,fun j=>?_⟩
   · unfold C; split; exact (h _ _|>.positives); rfl
   · simp [wordsPrice,C,g,b,mul_ite]
   unfold Accent.conviction; simp_rw [Poly.part_send]; by_cases hz:j=b
   · rw [show C j=f i.1 i.2 from if_pos hz]; simp_rw [if_pos (show j=B.fire i.1 from hz)]; exact h i.1 i.2
   rw [show C j=0 from if_neg hz]; simp_rw [if_neg (show j≠B.fire i.1 from hz)]; exact Feel.staticC (fun _=> 0) le_rfl (fun _=> norm_zero.le)
end YM.FullVolume.Nectar
#print axioms YM.FullVolume.Nectar.Polaris.roll_up
#print axioms YM.FullVolume.Nectar.Polaris.from_modes
#print axioms YM.FullVolume.Nectar.conviction_paid
