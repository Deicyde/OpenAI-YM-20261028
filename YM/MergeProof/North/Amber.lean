import YM.MergeProof.North.Clause
import YM.MergeProof.Wicket

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Float
open Function Filter Set Lattice Wilson RG Source Accent Push Local Extra.Histories PhysicalNext.Repeat Lotus Finset Marker Ribbon
open scoped Topology BigOperators Classical
variable {ι:Type}{G:Gauge}{n:Side}{R:Rep G n}{κ e t z a:ℝ} {o:Site n}
lemma prof_add (A:Activities G n){p q:ℕ→ Config G n→ℂ}(hp:Dominated p)(hq:Dominated q): profile A (p+q)= profile A p+profile A q:=by
   funext i U; exact (Summable.tsum_add ((hp.summable U).comp_injective Subtype.val_injective) ((hq.summable U).comp_injective Subtype.val_injective))
lemma pawn0 : Dominated (0:ℕ→ Config G n→ℂ):=⟨0,summable_zero,by simp⟩
variable (M:Leaf R)
-- gas postage
local notation "u"=> Config G n→ℂ
def line : ℕ→ u := match M.turn with
   | .gasKey j=> Pi.single j (Complex.ofReal ∘ M.ingredient)
   | .logKey _=> 0
lemma linemark : Dominated (line M):=by
   unfold line; split
   next i hv=>
     refine ⟨Pi.single i M.weight,?_ ,fun j U=>?_⟩
     · exact summable_of_ne_finset_zero (s:={i}) fun j hj=> Pi.single_eq_of_ne (by simpa using hj) _
     by_cases hj:j=i; subst j; simpa only [Pi.single_eq_same, Function.comp_apply,Complex.norm_real] using M.earn U
     rw [Pi.single_eq_of_ne hj,Pi.single_eq_of_ne hj]; simp
   next=> exact pawn0
lemma banner : profile R.activities (line M)= entry M:=by
   funext j H; unfold entry line; cases M.turn
   · simp [profile,cram]
   next i=> unfold profile; dsimp only; rw [expand_eq,tsum_eq_single i (fun l hl=> ?_),Pi.single_eq_same] -- need simp at evaluation
            · rfl
            rw [Pi.single_eq_of_ne hl]; simp
lemma coin_leaf : coin R (prose M) (line M)= Complex.ofReal ∘ M.cicada:=by
   funext U
   unfold line; cases hT:M.turn with
   | logKey i =>
     have hz k: M.bun k U=M.ingredient U* R.activities.gasOccurrence R.p k U:= by
       unfold Leaf.bun
       split
       next h=> unfold Leaf.bill; rw [hT,Activities.gasOccurrence,if_pos h]; simp [Wing.Occupied,Wing.remaining]
       next h=> unfold Activities.gasOccurrence; rw [if_neg h, mul_zero]
     simp_rw [coin₀,prose,hT, Function.comp_apply,Leaf.cicada,hz, tsum_mul_left]; unfold Rep.eval Activities.gas; push_cast; ring
   | gasKey i=>
     unfold prose Accent.coin; rw [hT]; simp only [mul_zero,zero_add,Function.comp_apply,Leaf.cicada,Complex.ofReal_tsum,Complex.ofReal_mul]; congr 1; apply tsum_congr; intro b; unfold nickel Leaf.bun; split
     next h =>
        unfold Leaf.bill; rw [hT]; simp only [Wing.Occupied,Wing.remaining]
        by_cases hi:i∈b
        · rw [if_pos hi,Finset.sum_eq_single_of_mem i hi (fun j _ hj=> ?_),Pi.single_eq_same]; push_cast;rfl
          simp only [Pi.single_eq_of_ne hj, Pi.zero_apply, zero_mul]
        rw [if_neg hi]; push_cast; apply Finset.sum_eq_zero; intro j hj; rw [Pi.single_eq_of_ne (ne_of_mem_of_not_mem hj hi)]; simp
     next=>simp
section lots

lemma combies (p:ι→ℕ→ Config G n→ℂ)(hp:∀ i,Dominated (p i))(s:Finset ι) : Dominated (∑ i∈s,p i):=by induction s using Finset.induction_on with
   | empty=> simpa using (pawn0 (G:=G) (n:=n))
   | @insert i s hi IH=> rw [Finset.sum_insert hi]; exact combn (hp i) IH
lemma prof_sum (p:ι→ℕ→ Config G n→ℂ)(hp:∀ i,Dominated (p i))(A:Activities G n)(s:Finset ι): profile A (∑ i∈s,p i)= ∑ i∈s,profile A (p i):=by induction s using Finset.induction_on with
   | empty=> ext; simp [profile,cram]
   | @insert i s hi IH=> rw [Finset.sum_insert hi,Finset.sum_insert hi,prof_add _ (hp i) (combies p hp _),IH]
lemma coin_sum (p:ι→ℕ→ Config G n→ℂ)(f:ι→ u)(hp:∀ i,Dominated (p i))(A:Rep G n)(hA:A.activities.KBound A.p t)(s:Finset ι): coin A (∑ i∈s,f i) (∑ i∈s,p i)= ∑ i∈s,coin A (f i) (p i):=by induction s using Finset.induction_on with
   | empty=> funext i; simp [coin₀]
   | @insert i s hi IH=> rw [Finset.sum_insert hi,Finset.sum_insert hi,Finset.sum_insert hi,coin_plus _ _ _ (hp i) (combies p hp _) hA,IH]
end lots
end YM.MergeProof.Float
