import YM.AnalyticBridge.VERIFIED_RESET_STEP.Trays

/-! Equality of the two reorganization operations separately. No sector
or selected-trial assumption; same data, even when gas vanishes. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection
open Function Filter Set Lattice Wilson RG Ovens Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration Push.BetaTransport
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ H w : ℝ}
    {X : Listing G n} {v : Source G n}

def untagged (X : Listing G n) (p : BudgetPoint) (v : Source G n) (i : ℕ) :=
    masked p.threshold (expand (X.reg i)) (rebate (X.reg i) (v.logRead i))
def dust (X : Listing G n) (p : BudgetPoint) (v : Source G n) (i : ℕ) := fault (X.reg i) (v.logRead i) p.threshold
private def picked (X : Listing G n) (p : BudgetPoint) (v : Source G n) (i : ℕ) :=
    masked p.threshold {(X.reg i).site} (payout (X.reg i) (v.logRead i))

namespace Local
variable (g : G.Simple) (h : Local X p v H w) (hn : 20 < n.val) (U : Config G n)
include g h
lemma raw_sum : Summable (fun i => v.logRead i 1) ∧ Summable (fun i => dust X p v i U) ∧
    Summable (fun i => picked X p v i U) ∧ Summable (fun i => untagged X p v i U) := by
  obtain ⟨u,hu,h'⟩ := RG.Activities.E_total h.unweighted
  refine ⟨Summable.of_norm_bounded hu (fun i => (h' i).2 1 (flat_ok p _) [] (by simp) (by simp)),
    Summable.of_norm_bounded (hu.mul_left (resetLoss G p)) (fun i => fault_sup (X.reg i) g (h.smooth i) (h' i) U),
    Summable.of_norm_bounded (hu.mul_left (multiplier G p)) (fun i => ?_), Summable.of_norm_bounded (hu.mul_left (resetLoss G p)) (fun i => ?_)⟩
  · have hz := payout_bill (X.reg i) g (h.smooth i) (h' i)
    unfold picked; by_cases he : Healthy p.threshold {(X.reg i).site} U
    · rw [masked_eq _ _ _ _ he]; exact Bill.norm hz (l:=[]) (by simp) (by simp) he
    rw [masked_ne _ _ _ _ he,norm_zero]; exact hz.nonneg
  have hz := rebate_sup _ g (h.smooth i) (h' i)
  unfold untagged; by_cases he : Healthy p.threshold (expand (X.reg i)) U
  · rw [masked_eq _ _ _ _ he]; exact hz.2 U he [] (by simp) (by simp)
  rw [masked_ne _ _ _ _ he,norm_zero]; exact hz.1
include hn in
private lemma picked_sum : (∑' i, picked X p v i U) = delta (X.read v) * ∑ o, heads p o U := by
  have hP := h.projects
  let f (o : Site n) i := if (X.reg i).site = o then picked X p v i U else 0
  have he i : ∑ o, f o i = picked X p v i U := by simp [f]
  have hg o : Summable (f o) := Summable.of_norm_bounded (h.raw_sum g U).2.2.1.norm (fun i => by unfold f; split <;> simp)
  rw [← funext he,Summable.tsum_finsetSum (fun o _ => hg o), Finset.mul_sum]; refine Finset.sum_congr rfl fun o _ => ?_
  unfold heads; by_cases he : Healthy p.threshold {o} U
  · rw [masked_eq _ _ _ _ he,← mul_div_assoc, ← identity g hP (by omega) o h.transforms,← tsum_div_const]
    refine tsum_congr fun i => ?_
    dsimp only [f, Listing.read]; split <;> rename_i hb
    · dsimp only [picked,payout]; rw [hb, masked_eq _ _ _ _ he,counter]
    simp
  have hz (i : ℕ) : f o i = 0 := by
    unfold f; split <;> rename_i hp
    · simp [picked,hp,masked_ne _ _ _ _ he]
    rfl
  simp [masked_ne _ _ _ _ he,hz]
include hn in
lemma first_split : ((∑' i, v.logRead i 1) + delta (X.read v) * (∑ o, heads p o U) - ∑' i, dust X p v i U) +
      ∑' i, untagged X p v i U = (X.read v).additive p U := by
  obtain ⟨hf,hd,hp,hu⟩ := h.raw_sum g U
  rw [← h.picked_sum g hn U, ← hf.tsum_add hp, ← (hf.add hp).tsum_sub hd,← ((hf.add hp).sub hd).tsum_add hu]
  exact tsum_congr fun i => Residual.splits ..
end Local

def fade (R : PathData G) (c : Clip) (p : BudgetPoint) (Δ : ℝ) (d : Low) : Pot G n :=
    masked p.threshold (d.home R p 0) (d.fresh R c 0 Δ)
def upperFade (R : PathData G) (p : BudgetPoint) (α Δ : ℝ) (d : High) : Pot G n :=
    masked p.threshold (d.home R 0) (d.fresh R 0 α Δ)
lemma fade_sum (h : R.Bounds c σ C Λ) (p : BudgetPoint) (Δ : ℝ) (U : Config G n) : Summable (fun d => fade R c p Δ d U) :=
  Low.masked_summable _ _ _ _ ((((Low.analogue_sum h (petals U 0)).sub (Low.plain_sum h 0 U)).mul_left Δ).congr fun d => by unfold Low.fresh Low.proxy; ring)
lemma loan_sum (h : R.Bounds c σ C Λ) (hw : Width p c σ) (hc : Decent c p) (α Δ : ℝ) (U : Config G n) : Summable fun d : Low => d.loan R c 0 p α Δ U :=
  (((((Low.live_sum h hw 0 U).mul_left (α+Δ)).add (fade_sum h p Δ U)).sub ((Low.maskedPlain_sum h p 0 U).mul_left α)).sub
    ((Low.proxy_sum h p 0 U).mul_left Δ)).congr fun i => by dsimp [fade]; linarith only [i.loans_identity R c 0 hc α Δ U]
lemma high_fade_eq (α Δ : ℝ) (U : Config G n) (d : High) : upperFade R p α Δ d U = -(α+Δ) * summit R p d 0 U := by
  unfold upperFade summit; by_cases he : Healthy p.threshold (d.home R 0) U
  · rw [masked_eq _ _ _ _ he,masked_eq _ _ _ _ he]; rfl
  rw [masked_ne _ _ _ _ he,masked_ne _ _ _ _ he,mul_zero]
lemma high_fade_sum (h : R.Bounds c σ C Λ) (p : BudgetPoint) (α Δ : ℝ) (U : Config G n) : Summable fun i => upperFade R p α Δ i U := by
  simp_rw [high_fade_eq]; exact (summit_sum h p U 0).mul_left _
lemma path_split (h : R.Bounds c σ C Λ) (hw : Width p c σ) (hc : Decent c p) (α Δ : ℝ) (U : Config G n) :
    (α+Δ)* kinetic R c p U + (layer (fade R c p Δ) U + layer (upperFade R p α Δ) U) =
      α*layer (fun d : Low => d.maskedPlain R c 0 p) U + Δ*(∑ o, heads p o U) + layer (fun d : Low => d.loan R c 0 p α Δ) U := by
  let D (i : Low) := i.live R c p (0:Site n); let E (i : Low) := i.maskedPlain R c (0:Site n) p
  let f := fade R c (n:=n) p Δ; let L (i : Low) := i.loan R c (0:Site n) p α Δ
  have ht : layer (upperFade R p α Δ) U = -(α+Δ) * layer (fun i => summit R p i 0) U := by
    rw [show upperFade (n:=n) R p α Δ = _ from funext (fun i => funext fun V => high_fade_eq α Δ V i),layer_scale]
  rw [← true_base h hw]; rw [ht]
  have hq V (i : Low) : (α+Δ)*D i V + f i V = (α*E i V + Δ*sketch R c p 0 i V)+L i V := by
    rw [sketch,← mul_assoc]; exact i.loans_identity R c 0 hc α Δ V
  have he := congrArg (layer · U) (show (fun i V => (α+Δ)*D i V + f i V) = _ from funext fun i => funext fun V => hq V i)
  have hs (V : Config G n) : Summable (fun i => Δ*sketch R c p 0 i V) := (Low.proxy_sum h p 0 V).mul_left Δ
  rw [layer_combine (fun V => (Low.live_sum h hw 0 V).mul_left _) (fade_sum h p Δ),layer_combine
    (fun V => ((Low.maskedPlain_sum h p 0 V).mul_left α).add (hs V)) (loan_sum h hw hc α Δ),
    layer_combine (fun V => (Low.maskedPlain_sum h p 0 V).mul_left _) hs, layer_scale, layer_scale,
    layer_scale, sketch_sum h] at he
  linarith
end YM.AnalyticBridge.VerifiedReset.Collection
