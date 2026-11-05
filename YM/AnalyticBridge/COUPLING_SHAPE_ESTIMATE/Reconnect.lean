import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Quota
import YM.Work.H01
/-!
# Exact local identities carried through at the shape reset

The previous unforced prescription in the exponent is NOT a
post-reset valid evaluator. In particular the pre-reset data can have
both flat and nonzero affine log-Hessian coefficients; no postulate
about their evaluation matching a trial. The all-field identity with
this *earlier* prescription on true sector/Gaussian integrals is a
major still-open producer obligation. Here reconstruct the AFTER shape
pointwise from that entrance, so can check precisely the shape control
such a physical template would deliver at ANY tested dial.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.CouplingShape
open Function Filter Lattice RG Wilson PathData Push.BetaTransport UVNext.CouplingReset Ovens
open scoped Matrix.Norms.Frobenius ContDiff Topology BigOperators Classical
variable {G : Gauge} {n : Side} (P : PathData G) (p : Clip) (b : BudgetPoint) (R : Activities G n)

/-- Don't strip V-independent bills from the
input unless part of the raw integral identity. All local paths sum on their
full indicator. Clips etc use the B Clip, alpha multiplies the masked
quadratic (not the clipped field). The loop, cubic/quartic already included
in `inChannels` at entrance. -/
def foreword (u β α : ℝ) (U : Config G n) := u * sites n - P.inChannels p b β U - α * quadraticMask P p b U - R.additive b U

def received (u β α : ℝ) (U : Config G n) := Real.exp (foreword P p b R u β α U) * R.gas b U

def perVac (R : Activities G n) (u : ℝ) := u - (∑' i, heart R i) / sites n

def installAt (u β α ε : ℝ) : Rep G n := ⟨P,p,written P p b R α ε,b,β+α+ε,perVac R u⟩

variable {P p b R} {σ C Λ H₀ w ε α κ γ : ℝ} (U : Config G n)

private lemma scrollBy (f : Scroll n → ℝ) (h : Summable f) : ∑' i, f (wheel n i) =
    (∑' i,f (.inl i)) + ((∑' i,f (.inr (.inl i))) + ((∑' i,f (.inr (.inr (.inl i))))+(∑' i,f (.inr (.inr (.inr i)))))) := by
  rw [(wheel n).tsum_eq, criss f h]
  have hh := h.comp_injective (Sum.inr_injective)
  rw [criss (fun i=> f (.inr i)) hh]; rw [criss (fun i=> f (.inr (.inr i))) (hh.comp_injective Sum.inr_injective)]

/-- Sums without using any evaluator bounds or flags at 1. -/
private lemma receipt (h : Grace p b σ) (hd : P.Bounds p σ C Λ)
    (α ε : ℝ) {δ a : ℝ} (hr : (slate P p b R α ε).Valid b δ a) :
    let D := slate P p b R α ε
    D.additive b U = (∑' i,reap R b i U)+ (
      ε*((∑' i,broad P p b i U)-quadraticMask P p b U) -
        (α+ε) * (kinetic P p b U-hub P p b U)) := by
  intro D
  let E (i) := masked b.threshold (corners P b R i).support (arrange P p R α ε i) U
  have he : Summable E := (wheel n).summable_iff.mp (show Summable (E ∘ wheel n) from (Activities.ESeries hr).summable U)
  have hf : ∀ i, E (.inr (.inl i))= ε*(broad P p b i U-framed P p b i U) := fun i => by
    by_cases hh : Healthy b.threshold (cardSite P b i).support U
    · exact (masked_eq _ _ _ _ hh).trans (by simp only [broad,framed,masked_eq _ _ _ _ hh]; rfl)
    change masked _ (cardSite P b i).support (residue _ _ _ _ ) _ = _
    rw [masked_ne _ _ _ _ hh,broad,framed,masked_ne _ _ _ _ hh,masked_ne _ _ _ _ hh]; ring
  have hg {l : ℕ} (F : ℕ → Atom G l) (i) : masked b.threshold (Post.park F i).support (-(α+ε) • Post.fee F i) U = -(α+ε)*Post.restore F b i U := by
    unfold Post.restore
    by_cases hv : Healthy b.threshold (Post.park F i).support U
    · rw [masked_eq _ _ _ _ hv, masked_eq _ _ _ _ hv]; rfl
    rw [masked_ne _ _ _ _ hv, masked_ne _ _ _ _ hv,mul_zero]
  change ∑' i, E (wheel n i)=_
  rw [scrollBy E he]
  simp_rw [hf, tsum_mul_left, ((broad_cost hd h).summable U).tsum_sub ((frame_cost hd h).summable U),
    (show ∀ i, E (.inr (.inr (.inl i)))=_ from fun i => hg P.cubic i), (show ∀ i, E (.inr (.inr (.inr i)))=_ from fun i => hg P.quartic i),
    tsum_mul_left]
  rw [kin_assembled hd h]; unfold quadraticMask; simp_rw [show ∀ i, E (.inl i)=_ from fun i=>show _=reap R b i U from rfl]; ring

set_option maxHeartbeats 800000 in
private lemma returns (hd : P.Bounds p σ C Λ) (hh : Grace p (boost b) σ) (hv : Selector p b)
    (hs : G.Simple) (hn : 10 < n.val) (hr : Earnings b R H₀ w) (α : ℝ) (u : G.Color) (hu : ‖u‖=1) :
    let ε := delta R u
    let d:=ink P p b R α ε
    (∑' i, d.logarithm i U) =
      (∑' i, heart R i) + (∑' i,reap R b i U) - R.additive b U +
        (α+ε)*(hub P p b U-quadraticMask P p b U)+ε*∑' i,broad P p b i U := by
  intro ε d
  let B:=boost b
  have hx:=taps hd hh hv hs hn hr α ε
  let f (i : Scroll n) := hooks P p b R α ε i U
  have hf : Summable f := (wheel n).summable_iff.mp (hx.1.pays.summable U)
  have hrT := live_budget hs (by omega) hr.core
  have he₁ : Summable (heart R) := (flat_income hr.core.bound).2.1.of_norm
  have he₂ := hrT.2.1.summable U; have he₃ := hrT.1.summable U; have he₄ := hrT.2.2.2.summable U
  have hk:=sums_hub hd hh U; have hS:= whittle hd hh U
  change ∑' i,f (wheel n i) = _
  rw [scrollBy f hf]; simp only [show ∀ i, f (.inr (.inr i))=0 from fun i => Sum.recOn i (fun _=>rfl) (fun _=>rfl),tsum_zero,add_zero]
  have hA : (∑' i,f (.inl i))= (∑' i, heart R i)+(∑' i,reap R b i U)+ε*∑ x, short b U x-R.additive b U := by
    change ∑' i, (((heart R i+reap R B i U)+pinch R B i U)-R.regularOccurrence B i U)=_
    rw [((he₁.add he₂).add he₃).tsum_sub he₄,(he₁.add he₂).tsum_add he₃,he₁.tsum_add he₂,measured hs hn hr.core u hu]; rfl
  have hm : (∑' i,f (.inr (.inl i)))=(α+ε)*(hub P p b U-quadraticMask P p b U)+ ε*((∑' i,broad P p b i U) - ∑ x, short b U x) := by
    have hu := ((summable_attached hd hh).summable U).sub ((frame_cost hd hh).summable U)
    have hv := ((broad_cost hd hh).summable U).sub ((narrow_cost hd hh).summable U)
    change ∑' i, ((α+ε)*(attachedClip P p (boost b) i U-framed P p (boost b) i U)+ε*(broad P p (boost b) i U-narrow P p (boost b) i U)) = _
    rw [(hu.mul_left (α+ε)).tsum_add (hv.mul_left ε),tsum_mul_left,tsum_mul_left,
      ((summable_attached hd hh).summable U).tsum_sub ((frame_cost hd hh).summable U), hk,
      ((broad_cost hd hh).summable U).tsum_sub ((narrow_cost hd hh).summable U),hS]; rfl
  rw [hA,hm]; ring

private lemma relax_grace (hh : Grace p (boost b) σ) : Grace p b σ :=
  ⟨hh.1,le_trans (div_le_div_of_nonneg_right (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 2)) (Nat.cast_nonneg (α:=ℝ) b.B)) hh.2⟩

lemma transfer_exponent (hd : P.Bounds p σ C Λ) (hh : Grace p (boost b) σ) (hv : Selector p b)
    (hs : G.Simple) (hn : 10 < n.val) (hr : Earnings b R H₀ w) (z : G.Color) (hz : ‖z‖=1) (v β α : ℝ) :
    let ε := delta R z
    foreword P p b R v β α U=(installAt P p b R v β α ε).exponent U+∑' i, (ink P p b R α ε).logarithm i U := by
  intro ε
  have h := receipt U (relax_grace hh) hd α ε (taps hd hh hv hs hn hr α ε).1.stamp
  have hA : (installAt P p b R v β α ε).activities.additive b U=(slate P p b R α ε).additive b U := rfl
  rw [show (installAt P p b R v β α ε).exponent U=_ from (show _=perVac R v*sites n-P.inChannels p b (β+α+ε) U-(installAt P p b R v β α ε).activities.additive b U from rfl)]
  have hh':=(returns U hd hh hv hs hn hr α z hz)
  change (∑' i, (ink P p b R α ε).logarithm i U)=_ at hh'
  rw [hh',hA,h,foreword, channels_split U β,channels_split U (β+α+ε), perVac]
  field_simp [sites_pos n|>.ne']; ring

/-- Exponential and gas separately used. Don't assume log of a signed
numerator on an argument failing one of these indicators. -/
lemma transferred (hd : P.Bounds p σ C Λ) (hh : Grace p (boost b) σ) (hv : Selector p b)
    (hs : G.Simple) (hn : 10 < n.val) (hr : Earnings b R H₀ w) (z : G.Color) (hz : ‖z‖=1) (v β α : ℝ)
    (hj : Reserve p b G H₀ σ C w α (delta R z) κ γ) :
    let ε:=delta R z
    received P p b R v β α U=(installAt P p b R v β α ε).eval U := by
  intro ε
  let A:=installAt P p b R v β α ε
  unfold received; rw [transfer_exponent U hd hh hv hs hn hr z hz v β α,Real.exp_add]; unfold Rep.eval
  have hg := flowing hd hh hv hs hn hr hj
  have hx : A.activities.gas b U=(slate P p b R α ε).gas b U*Real.exp (∑' i,(ink P p b R α ε).logarithm i U) :=
    Work.H01.answer _ _ _ _ (pelletKey (ward P b R)) _ _ _ _ _ (taps hd hh hv hs hn hr α ε).1 hg U
  change Real.exp (A.exponent U)*_ *_ =Real.exp (A.exponent U)*A.activities.gas b U
  rw [hx,show (slate P p b R α ε).gas b U=R.gas b U from rfl]
  dsimp only [ε]; ring
end YM.AnalyticBridge.CouplingShape
