import YM.MergeProof.North.Parties
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Graces.Fort
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mercury.Optics



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
lemma corresponding : ∃ f:H.fragrances→ℝ,SumBudget (fun i=>B.mass (locus M' H y i) (f i)) (w * Real.exp (-Q.ε*coverNumber R.p.B M'.crest)* Daisy.poster Q L x+met*w) ∧ ∀ i,B.Regular (locus M' H y i) (matin M' H i Chi.canonical) ∧ ∀ U, ‖masked B.threshold (xS i) (matin M' H i Chi.canonical) U‖ ≤ f i :=by
   obtain ⟨ht,hh⟩:= clockP M' H hN h B y hy hu hk hb hB hw hl
   let F:=pine M' H hN y B.power 1
   have hF(p)(hz:¬prince M' H p)(V:Config G c): ‖masked B.threshold (xS p) (matin M' H p Chi.canonical) V‖ ≤ F p:=by
       have hx:= (ht p).2 hz; by_cases he : Healthy B.threshold (xS p) V
       · rw [masked_eq _ _ _ _ he]; exact hx.2 V he [] (Nat.zero_le _) (fun i hh=> by simp at hh)
       rw [masked_ne _ _ _ _ he,norm_zero]; exact hx.1
   have he : SumBudget (fun i=> B.mass (xS i) (F i)) (w * Real.exp (-Q.ε*coverNumber R.p.B M'.crest)* Daisy.poster Q L x):=by
       refine Push.AbsoluteSums.budget_mono hh (fun _=> mul_nonneg (Real.exp_pos _).le (quench ..)) (fun i=>?_)
       unfold BudgetPoint.mass; rw [mul_comm]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right (show B.supportExponent ≤ a by linarith) (by positivity))) (quench ..)
   cases hX:M'.turn with
   | gasKey i => refine ⟨F,Push.AbsoluteSums.budget_loosen he (le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le M'.profit))),fun j=>⟨(ht j).1,hF j (Graces.never H M' i hX j)⟩⟩
   | logKey i =>
     let v:= icon H i; let P(p:H.fragrances):= if p=v then M'.weight else 0; have hi(u:H.fragrances): 0≤P u:=by unfold P;split; exact M'.profit; rfl
     have hV : SumBudget (fun i=> B.mass (xS i) (P i)) (met*w):=by
        have hz(i')(hb:i'≠v): B.mass (xS i') (P i')=0:=by unfold P BudgetPoint.mass; rw [if_neg hb,mul_zero]
        refine ⟨fun i=>mul_nonneg (Real.exp_pos _).le (hi i), summable_of_ne_finset_zero (s:={v}) (fun i h'=> hz i (by simpa using h')),?_⟩
        rw [tsum_eq_single v hz]; unfold P; rw [if_pos rfl]
        have he:= fades H M' i hb hq hr hp 1 zero_le_one
        have hz: M'.crest=(R.activities.reg i).support:=by unfold Leaf.crest; rw [hX]; rfl
        dsimp only [v]; rw [grinchY H M' i hX]; rw [mul_one,one_mul,← hz] at he -- v let
        apply le_trans ?_ he; unfold BudgetPoint.mass; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right (by linarith only : B.supportExponent ≤ B.supportExponent+2) (by positivity))) M'.profit
     refine ⟨F+P,?_,fun j=>⟨(ht j).1,fun U=>?_⟩⟩
     · simpa only [Pi.add_apply,BudgetPoint.mass,mul_add] using! Push.AbsoluteSums.budget_plus he hV
     by_cases hh:j=v
     · subst j; dsimp only [v]; rw [grinchY H M' i hX,Pi.add_apply,show P (icon H i)=M'.weight from if_pos rfl,hu]; exact (heels H M' i hX hN h U).trans (le_add_of_nonneg_left (quench ..))
     exact (hF j (fun z=> hh ((grinch H M' i hX).2 j z)) U).trans (le_add_of_nonneg_right (hi j))
end YM.PhysicalNext.Repeat.Mercury
