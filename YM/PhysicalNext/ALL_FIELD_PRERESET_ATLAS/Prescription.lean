import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Orders
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.TwoMasks
import YM.SectorNext.RECONNECTED_LOCALITY.Leads

/-!
# Giving back the prescribed masked atoms

The first gas only has the distinguished base outside. Between it and `earlyValue`
the path, clip and BudgetPoint are held. `β` is the same ONE before correction and
`α` is separate. We put **negative** of those additional terms in the local bill
(list that can be gathered with parts of the anchored unforced log). Require all
support/regularity/summability at actual width; cumulative smallness for the cost
after merging is a distinct (hard, conditional) estimate. Equivalent at ONE V where
all these hard indicators are read.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PreAtlas.Prescription
open RG Lattice Wilson PathData Function
open AnalyticBridge.CouplingShape Push.BetaTransport AnalyticBridge.VerifiedReset
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} (n : Side) (R : PathData G) (c : Clip) (p : BudgetPoint)

abbrev Bins (n : Side) := Post n ⊕ (Post n ⊕ (Post n ⊕ Card n))

def stock : Plate n := ⟨Bins n,Sum.elim (Post.park R.cubic)
    (Sum.elim (Post.park R.quartic) (Sum.elim (Post.park R.loop) (TwoMasks.wide R p)))⟩

def desire (β α : ℝ) : (stock n R p).Ink G := Sum.elim (fun i => -β • Post.fee R.cubic i)
    (Sum.elim (fun i => -β • Post.fee R.quartic i)
      (Sum.elim (fun i => - Post.fee R.loop i) (fun i => -α • young R c i)))

variable {k : ℕ} {n}
def postal (F : ℕ → Atom G k) (i : Post n) : ℝ := AnalyticBridge.CouplingShape.weight * ((F i.token).magnitude * 2^k)

lemma around_norm {ι : Type} {f : ι → ℝ} (h : Summable f) :
    Summable (fun i : Around n ι => f i.token) := by
  let u (j : Signed × ι) := ‖f j.2‖
  have hu := (summable_prod_of_nonneg (f:=u) (fun i=>norm_nonneg _)).mpr
    ⟨fun i => h.norm,Summable.of_finite⟩
  exact Summable.of_norm ((summable_prod_of_nonneg (f:=fun i : Site n × Signed × ι => u i.2)
    (fun i => norm_nonneg _)).mpr ⟨fun i => hu,Summable.of_finite⟩)

lemma postal_sum (F : ℕ → Atom G k) {σ C : ℝ} (hσ : 0<σ) (hF : SumBudget (fun i => (F i).budget σ) C) :
    Summable (postal (n:=n) F) := by
  have he : Summable fun i => (F i).magnitude := hF.2.1.of_nonneg_of_le
    (fun i => by unfold RG.Atom.magnitude; positivity) (fun i => (F i).lower_budget _ hσ)
  exact around_norm ((he.mul_right _).mul_left _)

lemma postage (F : ℕ → Atom G k) (i : Post n) (U : Config G n) :
    ‖Post.fee F i U‖ ≤ postal F i := by
  change ‖AnalyticBridge.CouplingShape.weight * (F i.token).unmasked _ _‖ ≤ _
  rw [norm_mul,Real.norm_of_nonneg weight_pos.le]
  exact mul_le_mul_of_nonneg_left (RG.Atom.unmasked_bound ..) weight_pos.le

lemma mount (F : ℕ → Atom G k) {σ C : ℝ} (hσ : 0<σ) (hF : SumBudget (fun i => (F i).budget σ) C)
    (V : Config G n) :
    Summable (fun i => Post.restore F p i V) ∧
      ∑' i,Post.restore F p i V = AnalyticBridge.CouplingShape.weight * ∑ s : Signed, ∑ x,atomSeries F p (pull s 0 V) x := by
  have hs : Summable fun i => Post.fee F i V :=
    (postal_sum F hσ hF).of_norm_bounded (fun i=>postage F i V)
  have he : Summable fun i => Post.restore F p i V := Low.masked_summable _ _ _ _ hs
  refine ⟨he,?_⟩
  rw [tally he,Finset.sum_comm,Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Equiv.sum_comp (s.actEquiv (R:=Per n)).toEquiv (fun x => ∑' i:ℕ,Post.restore F p (x,s,i) V),
    Finset.mul_sum]
  apply Finset.sum_congr rfl; intro x _
  change ∑' i:ℕ,Post.restore F p (s.act x,s,i) V = _
  simp_rw [Post.active_site,tsum_mul_left]; rfl

variable {R c p} {σ C Λ : ℝ}
lemma permits (hR : R.Bounds c σ C Λ) (β α : ℝ) (i : (stock n R p).letter) :
    p.Regular ((stock n R p).range i) (desire n R c p β α i) := by
  rcases i with i|(i|(i|i))
  · exact reg_scale _ (Post.active _ p (fun i=>(hR.invariant i).2.1) i).1
  · exact reg_scale _ (Post.active _ p (fun i=>(hR.invariant i).2.2) i).1
  · have he := reg_scale (-(1:ℝ)) (Post.active _ p (fun i=>(hR.invariant i).1) i).1
    rw [neg_smul,one_smul] at he; exact he
  exact reg_scale _ (SectorNext.Reconnect.Snip.swell (young_local R c p i).1 (TwoMasks.inclusion R p i))

def stamps (n : Side) (R : PathData G) (c : Clip) (maxBeta maxAlpha : ℝ) : Bins n → ℝ :=
    Sum.elim (fun i => maxBeta*postal R.cubic i)
      (Sum.elim (fun i => maxBeta*postal R.quartic i)
        (Sum.elim (postal R.loop) (fun i => maxAlpha*TwoMasks.due R c i)))

lemma stamp_income (hR : R.Bounds c σ C Λ) (b a : ℝ) : Summable (stamps n R c b a) := by
  exact Summable.sum _ ((postal_sum _ hR.width hR.three).mul_left _) <| Summable.sum _
    ((postal_sum _ hR.width hR.four).mul_left _)
    (Summable.sum _ (postal_sum _ hR.width hR.two) (by exact ((TwoMasks.prices (n:=n) R c hR).mul_left a)))

private lemma permit_w {b : SheetFunction G n} {x : Config G n} {s A t : ℝ} (h : ‖b x‖ ≤ t) (ht : ‖s‖ ≤ A) :
    ‖(-s • b) x‖ ≤ A*t := by
  rw [Pi.smul_apply,norm_smul,norm_neg]
  exact mul_le_mul ht h (norm_nonneg _) ((norm_nonneg _).trans ht)

lemma desires {β α b a : ℝ} (hb : ‖β‖ ≤ b) (ha : ‖α‖ ≤ a) (i : (stock n R p).letter) (U : Config G n) :
    ‖desire n R c p β α i U‖ ≤ stamps n R c b a i := by
  rcases i with i|(i|(i|i))
  · exact permit_w (postage _ _ _) hb
  · exact permit_w (postage _ _ _) hb
  · exact (norm_neg _).trans_le (postage _ _ _)
  exact permit_w (TwoMasks.profile R c _ U) ha

private lemma count_four {X Y Z W : Type} (f : X ⊕ (Y ⊕ (Z ⊕ W)) → ℝ) (hf : Summable f) :
    ∑' i,f i =
      (∑' i,f (.inl i)) + ((∑' i,f (.inr (.inl i))) +
        ((∑' i,f (.inr (.inr (.inl i)))) + (∑' i,f (.inr (.inr (.inr i)))))) := by
  let g i := f (.inr i); let h i := g (.inr i)
  have he : Summable g := hf.comp_injective Sum.inr_injective
  have hh : Summable h := he.comp_injective Sum.inr_injective
  calc
    _ = _ := criss f hf
    _ = (∑' i,f (.inl i)) + ((∑' i,g (.inl i)) + (∑' i,g (.inr i))) := congr_arg _ (criss g he)
    _ = _ := by rw [show (∑' i, g (.inr i)) = _ from criss h hh]

/-- Combination of the two types of counterterms and their exact masks. -/
theorem quoted (hR : R.Bounds c σ C Λ) (V : Config G n) (β α : ℝ) :
    let D := (stock n R p).maskedLog p (desire n R c p β α) V
    Summable (fun i => ‖D i‖) ∧ ∑' i, D i = β * hub R c p V - R.inChannels c p β V -
      α * Collection.receipt R c p V := by
  intro D
  obtain ⟨hc,he⟩ := mount p R.cubic hR.width hR.three V
  obtain ⟨hq,hg⟩ := mount p R.quartic hR.width hR.four V
  obtain ⟨hh,hu⟩ := mount p R.loop hR.width hR.two V
  have ht := (TwoMasks.original R c p hR V).2
  let f : Bins n → ℝ := Sum.elim (fun i => -β * Post.restore R.cubic p i V)
    (Sum.elim (fun i => -β * Post.restore R.quartic p i V)
      (Sum.elim (fun i => -(Post.restore R.loop p i V)) (fun i => -α * TwoMasks.wider R c p i V)))
  have hf : Summable f := Summable.sum _ (hc.mul_left _) (Summable.sum _ (hq.mul_left _)
    (Summable.sum _ hh.neg (ht.mul_left _)))
  have hD : (show Bins n → ℝ from D) = f := by
    funext i
    rcases i with i|(i|(i|i))
    · exact Collection.mask_mul ..
    · exact Collection.mask_mul ..
    · have he (w : Support n) (F : SheetFunction G n) : masked p.threshold w (-F) V = -masked p.threshold w F V := by
        by_cases hu : Healthy p.threshold w V
        · rw [masked_eq _ _ _ _ hu,masked_eq _ _ _ _ hu]; rfl
        rw [masked_ne _ _ _ _ hu,masked_ne _ _ _ _ hu,neg_zero]
      exact he ..
    exact Collection.mask_mul ..
  change Summable (fun i : Bins n => ‖D i‖) ∧ ∑' i : Bins n, D i = _
  rw [hD]; refine ⟨hf.norm,?_⟩; rw [count_four f hf]
  simp only [f, Sum.elim_inl,Sum.elim_inr, tsum_mul_left,tsum_neg]
  rw [he,hg,hu,TwoMasks.tallyWide R c p hR V]
  simp only [inChannels,principal,Finset.sum_add_distrib,← Finset.mul_sum,hub,AnalyticBridge.CouplingShape.weight,mul_add]
  ring

end YM.PhysicalNext.PreAtlas.Prescription
