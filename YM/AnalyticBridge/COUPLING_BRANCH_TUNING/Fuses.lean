import YM.AnalyticBridge.COUPLING_BRANCH_TUNING.Reading
import YM.Bid.Kitchen
import YM.Next.FREE_KERNELS.Lifts
import YM.Next.SCHEDULE.GridCost
import YM.Next.SCHEDULE.Postal
import YM.Next.SCHEDULE.Stadium
import YM.Push.CUTOFF_PROJECTORS.Equations
import YM.Push.PRICE_COMPILER.Builders

set_option warningAsError false

/-!
# Price variations of genuine final K formulae packed by attachment pellets

Prices a *derivative-sized* (difference) estimate: uses original addressing,
indicators and all-left/right ledger identities of the pellets, with the compulsory
price at least once. Not requiring any function of V continuous for this, and in
particular NOT applying a K identity on all U just from the probe reading. Acts even for
K supported on sparse flag outcomes. Supplies a proportional comparison for actual
`solid`-packed templates, hence to the h.inputs for `from_book`. Work of constructing
initial Tap/regular K, integrations/old flag and topology payments for allowable pellets,
validity of these actual cost purchases and proof of evaluator shape/certificate (even
through H03) remains separate. Don't manufacture a fused tape ex post.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.BranchTuning
open Lattice RG Wilson Ovens Ovens.Pipes Function UVNext.CouplingReset
open scoped Matrix.Norms.Frobenius BigOperators Topology Classical
variable {G : Gauge} {n : Side} {P : BudgetPoint} {A B : Tap G n}

def surcharge (κ : ℝ) (i : Label) := i.elim (fun _ => Real.exp (-κ)) (fun _ => 1)

/-- Price joint *half budget* on both compared attachment factors including all old packets
or signed paths prescribed by the caller. Include changes per unit twist before pricing in
beta or d. Prices endpoint factors themselves too; not differentiating even where one becomes
eligible by K crossing 0. -/
structure Assets (X : Pipes G n) (P : BudgetPoint) (A B : Tap G n) (δ κ γ : ℝ) : Prop where
  delta_nonneg : 0 ≤ δ
  linear : 0 ≤ κ
  mass : 0 ≤ γ
  margin : (P.B+P.B+1:ℕ)^4 * γ ≤ 1
  certificate : ∃ b : Label → ℝ, (∀ i, 0 ≤ b i) ∧
    Ac.Hit X.patch P.B b (P.supportExponent+1) γ ∧
    ∀ i U, let p := surcharge κ i * b i / 2
    ‖Pipes.reach A i U‖ ≤ p ∧ ‖Pipes.reach B i U‖ ≤ p ∧ ‖Pipes.reach A i U-Pipes.reach B i U‖ ≤ δ * p

variable {κ γ δ : ℝ} {X : Pipes G n}

/-- Include Ready assets on each pair to earn its per-hit comparison. Could
use varying δ,κ,γ on the way to a common price. No torus constant paid by this rule. -/
theorem pays_fused (F : ℕ ≃ X.Pellet) (h : Assets X P A B δ κ γ) :
    ForcedDrift P (Pipes.fused F P A) (Pipes.fused F P B) (δ * Bid.quote κ γ) := by
  let p := surcharge κ
  let w := Real.exp (-κ)
  have hw : 0 ≤ w := (Real.exp_pos _).le
  obtain ⟨b,hb,ha,H⟩ := h.certificate
  let s (i : ℕ) := (F i).val
  let c i := δ * w * ∏ j ∈ s i, b j
  have hv i : 0 ≤ p i := by cases i <;> first | exact hw | exact zero_le_one
  have he i : p i ≤ 1 := by cases i <;> first | exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr h.linear) | exact le_rfl
  have hδ : 0 ≤ δ * w := mul_nonneg h.delta_nonneg hw
  refine ⟨rfl,c,fun i => ⟨mul_nonneg hδ (Finset.prod_nonneg (fun _ _ => hb _)),fun U => ?_⟩,fun o => ?_⟩
  · unfold Pipes.fused; dsimp only; unfold Pipes.solid
    split_ifs
    next hearn =>
      have hh := Push.BetaTransport.product_diff (h.delta_nonneg) (fun i => Pipes.reach A i U) (fun i => Pipes.reach B i U)
        (fun i => surcharge κ i*b i/2) (fun i => (H i U).1) (fun i => (H i U).2.1) (fun i => (H i U).2.2) (s i)
      obtain ⟨j,hj⟩ := (F i).property.1
      have ht : (∏ j ∈ s i, p j) ≤ w := by
        have hz : Sum.inl j ∈ s i := by simpa [lefts,s] using hj
        calc
          _ ≤ ∏ j ∈ ({Sum.inl j} : Finset Label), p j :=
            Finset.prod_le_prod_of_subset_of_le_one (Finset.singleton_subset_iff.mpr hz) (fun j _ => hv _) (fun j _ _ => he _)
          _ = w := by rw [Finset.prod_singleton]; rfl
      refine hh.trans ?_
      simp_rw [show ∀ i, 2*(surcharge κ i * b i / 2)=p i *b i by intro i; unfold p; ring,
        Finset.prod_mul_distrib]; unfold c; rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht h.delta_nonneg)
        (Finset.prod_nonneg fun i _ => hb i)
    rw [sub_zero,norm_zero]; exact mul_nonneg hδ (Finset.prod_nonneg (fun _ _ => hb _))
  let R := Ac.roots X.patch P.B b P.supportExponent o
  have hR : SumBudget R (Real.exp γ - 1) := Ac.forest X.patch P.B P.exponent_pos.le hb ha h.margin h.mass o
  have hr : Injective s := Subtype.val_injective.comp F.injective
  have hx (i) : (if o ∈ ((Pipes.fused F P A).forced i).support then P.mass ((Pipes.fused F P A).forced i).support (c i) else 0) = δ*w*R (s i) := by
    have hs := (F i).property.2.1
    unfold Pipes.fused Pipes.addr R Ac.roots c s
    by_cases hb : o ∈ Pipes.skin X (F i).val
    · simp only [hb,hs,true_and,if_true,BudgetPoint.mass]; unfold Pipes.skin at hb ⊢; rw [if_pos hb]; ring
    unfold Pipes.skin at hb ⊢; simp [hs,hb]
  simp_rw [hx]
  have hs : Summable fun i => R (s i) := hR.2.1.comp_injective hr
  refine ⟨fun i => mul_nonneg hδ (hR.1 _), hs.mul_left _,?_⟩
  rw [tsum_mul_left]
  have hk : (∑' i, R (s i)) ≤ ∑' j, R j := Summable.tsum_le_tsum_of_inj s hr (fun j _ => hR.1 _) (fun i => le_rfl) hs hR.2.1
  exact (mul_le_mul_of_nonneg_left (hk.trans hR.2.2) hδ).trans_eq (by unfold Bid.quote w; ring)

open Shoot RG.Supply Input Precision 
variable {c : Sheet G} {D : Rolls c} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {M : MapPrices} {L : PostCost D} {H : Directed G I Z M L} {m p N : ℕ}
    {T : ℝ → Tap G (H.a.S.side m p)} {X : Pipes G (H.a.S.side m p)} {e : ℕ ≃ X.Pellet}
    {s : Set ℝ} {V : Config G (H.a.S.side m p)} {Q : In H.a m p}
    {η : ℕ → ℝ} {q : ResetPrices} {r : Rates} {u : ℝ → ℝ}
    {S : ℝ → Activities G (H.a.S.side m p)}


end YM.AnalyticBridge.BranchTuning
