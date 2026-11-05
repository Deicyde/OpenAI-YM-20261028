import YM.FullVolume.Relay.Pact
import YM.FullVolume.Spiral.Saffron
/- K.vacuum on a true Contest. Does not charge beyond vacuum halo. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Muse
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Animals
open MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Height Input Org Supply Pane Slide
open Push.PriceCompiler Progress.DirectedRecipe Jams Apse Empire Time Roof Chord Ovens
open FullVolume.Ray FullVolume.Urns FullVolume.Amp Pass Tent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}
variable {q v d t t':ℝ}{N n m k:ℕ}{L:Lyrics R t t}
open UniformSpace FullVolume Paint Paint.Tower PaidBeam
set_option maxHeartbeats 440000
set_option synthInstance.maxHeartbeats 100000
variable {c:Side} (S:Price G c) (T:Team S)
local notation "ft"=> layout G c S.p
local notation "B!"=> S.p
local notation "X!"=> World T
open Luna FullVolume.Ray Jams Amp.Beam
-- explicit summable simultaneous sup along K up.Hut no β
variable {K:Beam (World T)} {X:sun→ Home T}
open FullVolume.Nectar Marker MergeProof
lemma ex_profile (hx: ‖K‖≤1)(hX : ∀ s:sun, World.ready ((X s):Completion (Home T))=read _ s K): let F(s:sun):= observe T (X s)
     WindowP (fun s:sun=> profile (F s) (fun j=>Complex.ofReal ∘ (F s).K j)) Prod.fst S.p.B S.p.supportExponent S.k:=by
    intro F
    obtain ⟨b,hB,h⟩:= monies S T hx hX
    let C:= barcode (F tip); have hc s: barcode (F s)=C:=rfl
    have hp(i):0≤b i:= (h i).positives
    have hs : Summable b:=Activities.summable_charge (fun i=> (F tip|>.forced i).inventory_ne.mono (F tip|>.forced i).inventory_sup) hp hB
    refine ⟨cram C b, (heavy C hs).summable,fun v=> ?_,fun i=>?_⟩
    · let A(i):= if v∈ (C i).1 then (B!).mass (C i).1 (b i) else 0
      have hz:SumBudget A S.k:=hB v; have hh:= heavy C hz.2.1
      let P:=fun i:Box c=> if v∈i.1 then (cram C b i)*Real.exp (S.p.supportExponent*coverNumber S.p.B i.1) else 0; have hC:P=cram C A:=by
          ext i; unfold P; by_cases hi:v∈ i.1
          · rw [if_pos hi,cram,cram, ← tsum_mul_right]; apply tsum_congr; intro j; unfold A BudgetPoint.mass; rw [j.property,if_pos hi,mul_comm]
          rw [if_neg hi]; symm; refine (tsum_congr ?_).trans tsum_zero; intro j; unfold A; rw [j.property,if_neg hi]
      change SumBudget P S.k; rw [hC]; exact ⟨fun _=> tsum_nonneg (fun j=> hz.1 j.val), hh.summable, hh.tsum_eq.trans_le hz.2.2⟩
    have he(j): Feel (fun s:sun=>Complex.ofReal ∘ (F s).K j) (b j):=by
       have ht:= Feel.transit Complex.ofRealCLM (id (α:= Config G c)) (h j) (fun v=>by rw [one_mul]; exact (Complex.norm_real v).le) zero_le_one
       rw [one_mul] at ht; exact ht
    unfold profile; simp_rw [hc]; exact Feel.rollup (fun j:{l// C l=i}=> (fun s:sun=>Complex.ofReal ∘ (F s).K j.val)) (fun _=> he _) (hs.comp_injective Subtype.val_injective)
end YM.PhysicalNext.Repeat.Muse
#print axioms YM.PhysicalNext.Repeat.Muse.ex_profile
