import YM.MergeProof.North.Partly
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Graces.Fort




/-!
 # η power with reserved Mass transfer. small price oracle only Matins.d additional. Arc works both and MARK clocks.C.Struct.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mercury
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Polar Silica Eider Metric Set Gaussian Tablet Quill Baffle Prism Brim Lotus Peak Greenbelt WardBin.Lies March
open Gas Ursell Trees Daisy Daisy.Charity
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
    {B B' : BudgetPoint} {Y : Support c} {K : Support f} {U : Config G c} {W μ x C' : ℝ} {R : Rep G f}
    {p j n m k : ℕ} {L : Side} {Q: ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable {d A t C w M N z β r η v b Y' q: ℝ}{C₀ : Libretto G n}
variable (H: Cash W x μ L Q o C T R)(M': Lotus.Leaf R) (hN: Captain H p C' d v t A b r M q m Chi.canonical)
variable {a e d':ℝ}(h: Herd H hN.conduit A M m) (hB:Bikes Q L μ x a e M p m)(hS: B.supportExponent+3≤a)(hw:foam Q L)
variable (hb:B.B=radiusB x)(hu:B.threshold=Pressure.temp x)(hk:B.order=p)
    (hq:Q.halo+5 ≤ k)(hr: Release.accepts k R.p.supportExponent (B.supportExponent+2) S.patch.L)(hl:Daisy.tailCost L Q μ x M e p m B.power ≤ Daisy.poster Q L x)
    (hp:R.p.B ≤ 2* B.B)
variable (y:Site c)(hy:y∈M'.crest.image S.ratio.parent)
include h hw hB hS hb hu hk hq hr hl hp hy
local notation "w"=> R.p.mass M'.crest M'.weight
local notation "xS"=> locus M' H y
local notation "met"=> Real.exp (Release.base (B.supportExponent+2) k)
open Blush
omit hq hr hp hl hy in
lemma shelves (T:Cloud R)(hU:y∈T.live.crest.image S.ratio.parent)(x':ℂ):
   ∃ f:H.fragrances→ℝ,
     SumBudget (fun i=>Push.Local.reservedMass B (locus T.live H y i) (f i)) (2*‖x'‖*(volt x p B.power*(Q.goal L x)⁻¹)*R.p.mass T.live.crest T.live.weight) ∧ ∀ i,prince T.live H i → B.supBounds y (locus T.live H y i) (Blush.pane H T x' i) (f i) :=by
    let F:= T.live; let F':=T.pale; let t₀:=2*‖x'‖*(volt x p B.power*(Q.goal L x)⁻¹); have hF:0 ≤ R.p.mass F.crest F.weight:= F.profit.trans (R.p.loMass _ _ F.profit)
    cases hi : T.live.turn with
    | gasKey i =>
      have ht:= hB.paid; have hf:0 ≤ volt x p B.power:= mul_nonneg (by unfold shiftG; positivity) (by unfold Reserves.polyPrice; positivity)
      have he:0 ≤ (Q.goal L x)⁻¹:= inv_nonneg.mpr (Real.rpow_nonneg ht.le _)
      refine ⟨0,?_,fun j hz=> (Graces.never H T.live i hi _ hz).elim⟩
      simp_rw [Pi.zero_apply,Push.Local.reservedMass,mul_zero]; exact Push.Local.sumBudget_zero (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (norm_nonneg _)) (mul_nonneg hf he)) hF)
    | logKey i=>
      let Y:= (plate H i).support; let v:= icon H i; let φ(M:Lotus.Leaf R) := matin M H v Chi.canonical; have hU': y∈T.pale.crest.image S.ratio.parent:= by rwa [← T.turnout]
      have hi': T.pale.turn = Wing.logKey i:= T.together.symm.trans hi
      obtain ⟨s,hs,hs'⟩:= haze H F i hi hN h hB hS hw y hU hk hu hb
      obtain ⟨s₁,hp,hp'⟩:= haze H F' i hi' hN h hB hS hw y hU' hk hu hb
      have hh : B.Regular (plate H i).support (φ F):= grinchY H F i hi y ▸ scops F H hN h B hU hu hk.le v
      have hQ : B.Regular (plate H i).support (φ F'):=grinchY H F' i hi' y ▸ scops F' H hN h B hU' hu hk.le v
      have he:=pricingG hh hs; have hg:= Next.Foundations.bound_smul Complex.I (pricingG hQ hp); rw [Complex.norm_I,one_mul] at hg
      let S' := ‖x'‖*(s+s₁)
      have h' : B.supBounds y Y (Blush.pane H T x' v) S':= Next.Foundations.bound_smul _ (Next.Foundations.bound_add (ornate hh) (Next.Foundations.regular_smul _ (ornate hQ)) he hg)
      let f(p:H.fragrances):=if p=v then S' else 0; have hf : f v=S':=if_pos rfl; let t(i):=Push.Local.reservedMass B (locus T.live H y i) (f i); have Hq(i)(hi:i≠v): t i=0:=by unfold t f; rw [if_neg hi,Push.Local.reservedMass,mul_zero];
      refine ⟨f,⟨fun i=> mul_nonneg (Real.exp_pos _).le (show 0 ≤ f i from (by unfold f;split; exact h'.1;exact le_rfl)), summable_of_ne_finset_zero (s:={v}) (fun i hi=> Hq i (by simpa using hi)),?_⟩,fun j hj=>?_⟩
      · change (∑' i,t i) ≤ _; rw [tsum_eq_single v Hq]; unfold t; rw [hf,show locus T.live H y v=Y from grinchY H T.live i hi y]
        have hx := T.turnout; have h0:= T.rates; change F.crest=F'.crest at hx; change F.weight=F'.weight at h0; rw [← hx, ← h0] at hp'; unfold S'; let b(t):=Push.Local.reservedMass B Y t
        change b _ ≤ _
        rw [show b (‖x'‖*(s+s₁))= ‖x'‖*(b s+b s₁) from (by unfold b Push.Local.reservedMass; ring)]
        apply (mul_le_mul_of_nonneg_left (add_le_add hs' hp') (norm_nonneg _)).trans_eq; unfold F; ring
      have ht : j= v:= grinch H T.live i hi|>.2 j hj; rw [ht,hf, show locus T.live H y v=Y from grinchY H T.live i hi y]; exact h'
end YM.PhysicalNext.Repeat.Mercury
