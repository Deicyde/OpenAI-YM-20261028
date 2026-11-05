import YM.AnalyticBridge.VERIFIED_RESET_STEP.Investor
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Rewrites

/-! Exact unnormalized density as a function, in terms of the EARLY local
species required from the interacting Gaussian calculation. Includes receipt
before the last compulsory-packet fusion for shape comparison with trials.
All summed activities have the fixed signs, masks and paths. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection
open Function Filter Set Lattice Wilson RG Ovens Quotes Residual WilsonStartup Averaging Geo Progress.DirectedRecipe Extra.Iteration Push.BetaTransport
open UVNext.CouplingReset
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ H w δ γ : ℝ}
    {X : Listing G n} {v : Source G n}

def branch (X : Listing G n) (R : PathData G) (c : Clip) (p : BudgetPoint) (v : Source G n) (α : ℝ) := fill X R c p v α (delta (X.read v))
def frozen (X : Listing G n) (R : PathData G) (c : Clip) (p : BudgetPoint) (v : Source G n) (β τ : ℝ) : Rep G n :=
    ⟨R,c,X.read v,p,β,τ⟩

def receipt (R : PathData G) (c : Clip) (p : BudgetPoint) := layer (fun d : Low => d.maskedPlain (n:=n) R c 0 p)
/-- Pre-reset specification. Not the logarithm of an integral stripped of its
absolute prefactor. Incoming coupling on the output kinetic, alpha (committed
loop coefficient) on an additional genuinely masked S^0', only loop at output
price. `X` has been priced *separately*. -/
def earlyValue (X : Listing G n) (R : PathData G) (c : Clip) (p : BudgetPoint) (v : Source G n) (β τ α : ℝ) (U : Config G n) :=
    (frozen X R c p v β τ).eval U * Real.exp (-α*receipt R c p U)

def vac (v : Source G n) (τ : ℝ) := τ - (∑' i, v.logRead i 1)/sites n

def stack {ι : Type*} (f : ι → Pot G n) (U : Config G n) (i : Seat n × ι) := factor * f i.2 (i.1.view U)
lemma stack_series {ι : Type*} (f : ι → Pot G n) (U : Config G n) (h : ∀ V, Summable fun i => f i V) : Summable (stack f U) := by
  let g (x : Seat n × ι) := f x.2 (x.1.view U)
  have he : Summable g := Summable.of_norm ((summable_prod_of_nonneg fun i => norm_nonneg (g i)).mpr ⟨fun i => (h (i.view U)).norm, Summable.of_finite⟩)
  exact he.mul_left _
lemma mask_mul (Y : Support n) (t c : ℝ) (U : Config G n) (f : Pot G n) :
    masked t Y (fun x => c*f x) U = c*masked t Y f U := by
  by_cases hu : Healthy t Y U <;> simp [masked_eq,masked_ne,hu]
private def piece (X : Listing G n) (R : PathData G) (c : Clip) (p : BudgetPoint) (v : Source G n) (α Δ : ℝ) (i : EKey n) :=
    masked p.threshold (incoming X R p i).support (archive X R c v α Δ i)
lemma piece_low (α Δ : ℝ) (i : Faces n) (U) : piece X R c p v α Δ (.inr (.inl i)) U = stack (fade R c p Δ) U i := by
  change masked p.threshold (i.1.spread (i.2.home R p 0)) (i.2.fresh R c 0 _ ∘ i.1.view) U = factor * _
  have hi : Low.fresh R c i.2 (0:Site n) (factor*Δ) = fun V => factor * Low.fresh R c i.2 (0:Site n) Δ V := by funext; simp [Low.fresh]; ring
  rw [Seat.distribute, hi, comp_apply, mask_mul]; rfl
lemma piece_high (α Δ : ℝ) (i : Spikes n) (U) : piece X R c p v α Δ (.inr (.inr i)) U = stack (upperFade R p α Δ) U i := by
  change masked p.threshold (i.1.spread (i.2.home R 0)) (i.2.fresh R 0 _ _ ∘ i.1.view) U = factor * _
  have hi : High.fresh R i.2 (0:Site n) (factor*α) (factor*Δ) = fun V => factor * High.fresh R i.2 (0:Site n) α Δ V := by
    funext; simp [High.fresh]; ring
  rw [Seat.distribute, hi, comp_apply, mask_mul]; rfl
lemma loans_earn (α Δ : ℝ) (i : Faces n) (U) : loses X R c p v α Δ (.inr i) U = stack (fun d : Low => d.loan R c 0 p α Δ) U i := by
  change i.2.loan R c 0 p (factor*α) (factor*Δ) _ = factor * _; unfold Low.loan; dsimp only []; split_ifs <;> ring

namespace Local
variable (g : G.Simple) (h : Local X p v H w) (hx : R.Bounds c σ C Λ) (hc : Decent c p) (hw : Width p c σ) (α Δ : ℝ)
include g h hx
lemma additive (U : Config G n) : ((shelves X R p).pours (fill X R c p v α Δ)).additive p U =
    (∑' i, untagged X p v i U) + (layer (fade R c p Δ) U + layer (upperFade R p α Δ) U) := by
  let f i := piece X R c p v α Δ i U; let N := numbering (EKey n)
  have hl : Summable (f ∘ Sum.inr ∘ Sum.inl (β:=Spikes n)) := (stack_series _ _ (fade_sum hx p Δ)).congr (fun i => (piece_low ..).symm)
  have hh : Summable (f ∘ Sum.inr ∘ Sum.inr (α:=Faces n)) := (stack_series _ _ (high_fade_sum hx p α Δ)).congr (fun i => (piece_high ..).symm)
  change ∑' i, f (N i) = _; rw [N.tsum_eq f, Summable.tsum_sum (f:=f) (h.raw_sum g U).2.2.2 (Summable.sum _ hl hh),
    Summable.tsum_sum (f:=fun i => f (.inr i)) hl hh]
  rw [layer_total _ U (fade_sum hx p Δ),layer_total _ U (high_fade_sum hx p α Δ)]; dsimp only [f]; simp only [piece_low,piece_high]; rfl
include hw hc in
lemma throw_sum (U : Config G n) : (∑' i, (fill X R c p v α Δ).logarithm i U) = (∑' i, dust X p v i U) + layer (fun d : Low => d.loan R c 0 p α Δ) U := by
  let f i := loses X R c p v α Δ i U; let N := numbering (LKey n)
  have hh : Summable (f ∘ Sum.inr) := (stack_series _ _ (loan_sum hx hw hc α Δ)).congr (fun i => (loans_earn ..).symm)
  change ∑' i, f (N i) = _; rw [N.tsum_eq f,Summable.tsum_sum (f:=f) (h.raw_sum g U).2.1 hh,layer_total _ U (loan_sum hx hw hc α Δ)]
  dsimp only [f]; simp only [loans_earn]; rfl
include hc hw in
lemma exponent (hn : 20 < n.val) (β τ : ℝ) (U : Config G n) : let Δ := delta (X.read v)
    let t := branch X R c p v α; let Y := shelves X R p; let T := trunk R c p Y t (β+α+Δ) (vac v τ)
    T.exponent U + (∑' i, t.logarithm i U) = (frozen X R c p v β τ).exponent U - α*receipt R c p U := by
  intro Δ t Y T
  change vac v τ * sites n - R.inChannels c p (β+α+Δ) U - _ + _ = (τ*sites n - R.inChannels _ _ β U - _)-_
  rw [vac,sub_mul,div_mul_cancel₀ _ (sites_pos n).ne', channels_split U (β+α+Δ),channels_split U β]
  have hh := h.first_split g hn U
  have he := h.additive g hx α Δ U
  have ht := h.throw_sum g hx hc hw α Δ U
  have hz := path_split hx hw hc α Δ U
  dsimp only [T,trunk,t,Y,branch,receipt,frozen]
  dsimp [Δ] at *; linarith

include hw hc in
lemma raw_evaluator (hn : 20 < n.val) (β τ : ℝ) (U : Config G n) : let Δ := delta (X.read v)
    let t := branch X R c p v α; let Y := shelves X R p; let T := trunk R c p Y t (β+α+Δ) (vac v τ)
    T.eval U * Real.exp (∑' i, t.logarithm i U) = earlyValue X R c p v β τ α U := by
  intro Δ t Y T
  rw [Rep.eval, mul_right_comm _ (T.activities.gas T.p U),← Real.exp_add,h.exponent g hx hc hw α hn β τ U,earlyValue,Rep.eval,
    mul_right_comm _ ((frozen X R c p v β τ).activities.gas _ _),← Real.exp_add, neg_mul, sub_eq_add_neg]
  rfl
include hw hc in
lemma actual (hn : 20 < n.val) (hF : Fees G p c σ C α H w δ γ) (β τ : ℝ) :
    (finish R c p (shelves X R p) (branch X R c p v α) (β+α+delta (X.read v)) (vac v τ)).eval = earlyValue X R c p v β τ α := by
  ext U; rw [branch,(h.renew g hx hc hw α hn hF).unshifted]; exact h.raw_evaluator g hx hc hw α hn β τ U
end Local
end YM.AnalyticBridge.VerifiedReset.Collection
