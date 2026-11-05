import YM.FullVolume.Spiral.Horns
import YM.FullVolume.Spiral.Hessian
/- Holder of prices at Output.Sensor. ℓ1 each anchored.Pulls.Lev. Prescribed Beam at full length.C. -/
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
set_option maxHeartbeats 880000
set_option synthInstance.maxHeartbeats 100000
variable {c:Side} (S:Price G c) (T:Team S)
local notation "ft"=> layout G c S.p
local notation "B!"=> (S.p)
local notation "X!"=> World T
open Luna FullVolume.Ray Jams Amp.Beam
-- explicit summable simultaneous sup along K up.Hut no β
variable {K:Beam (World T)} {X:sun→ Home T}
private lemma countRows (f:ℕ→ℕ→ℝ) {v:ℝ} (h:SumBudget (fun p:ℕ×ℕ=> f p.1 p.2) v): SumBudget (fun i=>∑' j,f j i) v:=by
   refine ⟨fun i=> tsum_nonneg (fun j=>h.1 (j,i)),h.2.1.prod_symm.prod,?_⟩
   calc
    _=∑' i,∑' j,f i j:= Summable.tsum_comm h.2.1
    _=∑' i:ℕ×ℕ,f i.1 i.2:= h.2.1.tsum_prod.symm
    _≤ v:= h.2.2
lemma ores (hx: ‖K‖≤1)(hX : ∀ s:sun,World.ready ((X s):Completion (Home T))=read _ s K): ∃ a:ℕ→ℝ,(∀ v :Site c, SumBudget (fun i=>if v∈(ft|>.hard i).support then (S.p).mass (ft|>.hard i).support (a i) else 0) S.k)∧∀ i U,PaidBeam (fun s:sun=> (observe T (X s)).K i U) (a i):=by
   obtain ⟨D,hD,hq⟩:=birthUse S T
   choose p hp hb using fun i:ℕ=>hq (K i); let z(i:ℕ):=∑' j,p j i; let h i:=(layout G c S.p|>.hard i); let e:=S.p
   let f(v:Site c)(j i:ℕ):ℝ:=if v∈ (h i).support then (S.p).mass (h i).support (p j i) else 0
   have ht(v:Site c): SumBudget (fun i:ℕ×ℕ=> f v i.1 i.2) S.k:=by
      refine budget_loosen (@Extra.Histories.budget_prod _ _ (fun i:ℕ×ℕ=> f v i.1 i.2) (fun j:ℕ => ‖K j‖*S.k) (fun i=> hb i v) ((paid K).summable.mul_right S.k)) ?_
      rw [tsum_mul_right,(paid K).tsum_eq]; exact mul_le_of_le_one_left S.k0.le hx
   have hs(i:ℕ): Summable fun j=>p j i:=by
      obtain ⟨x,hx⟩:=(h i).inventory_ne.mono (h i).inventory_sup
      apply Summable.of_nonneg_of_le (fun j=>(hp j i).1) _ ((ht x).2.1.prod_symm.prod_factor i); intro j; change _≤f x j i; rw [show f x j i= _ from if_pos hx]; exact (e.loMass _ _ (hp j i|>.1)) -- syntax .. plus
   refine ⟨z,fun v=>?_,fun i U=>?_⟩
   · let t(i:ℕ):=∑' j,f v j i; have htB: (fun i:ℕ=>if v∈(h i).support then S.p.mass (h i).support (z i) else 0)=t:=by
         ext i; by_cases he:v∈ (h i).support
         · rw [if_pos he]; unfold t f z;
           simp_rw [if_pos he, BudgetPoint.mass,tsum_mul_left]
         rw [if_neg he]; unfold t f; simp only [if_neg he,tsum_zero]
     rw [show (fun i:ℕ=>if v∈(ft |>.hard i).support then S.p.mass (ft|>.hard i).support (z i) else 0)=t from htB]; exact countRows (f v) (ht v)
   let P:= D i U; have hℓ(k:ℕ):‖P (K k)‖≤ p k i:= hp k i|>.2 U
   have hy : Summable (fun i:ℕ=> ‖P (K i)‖):= .of_nonneg_of_le (fun _=>norm_nonneg _) hℓ (hs i)
   let Y: Beam ℝ:= ⟨fun i=> P (K i),memℓp_gen (by simpa using hy)⟩
   refine ⟨Y,(paid Y|>.tsum_eq.symm).trans_le (hy.tsum_le_tsum hℓ (hs i)),fun s=>?_⟩
   rw [← hD, hX]; have ht':= P.hasSum (K.spar (abs_le.mpr s.property)); simp_rw [map_smul] at ht'; exact ht'.tsum_eq.symm
section narrow
variable {Z:Type}[NormedAddCommGroup Z][NormedSpace ℝ Z][CompleteSpace Z]{p:sun→Z}
def slash (x:ℝ)(h: x∈sun)(s:sun): sun:= ⟨s.val*x,abs_le.mp (by rw [abs_mul]; exact mul_le_one₀ (abs_le.mpr s.property) (abs_nonneg x) (abs_le.mpr h))⟩
lemma slashes {x:ℝ}(h:x∈sun) {v:ℝ}(hx: PaidBeam p v): PaidBeam (p ∘ slash x h) v:=by
    obtain ⟨u,hu,hB⟩:=hx.arrives; let t(i:ℕ):=x^i • u i; have hx₀: SumBudget (fun i=> ‖t i‖) ‖u‖:= at_flight x (abs_le.mpr h) (togg u)
    let v:Beam Z:=⟨t,memℓp_gen (by simpa using hx₀.2.1)⟩
    refine ⟨v,((paid v|>.tsum_eq.symm).trans_le hx₀.2.2).trans hu,fun s=>?_⟩
    rw [Function.comp_apply,hB]; change ∑' i:ℕ,(s.val*x)^i • u i=∑' i:ℕ,s.val^i • t i
    simp_rw [mul_pow,t,smul_smul]
def verso : sun→sun:= slash (1/2:ℝ) (by norm_num [sun])
lemma arc2 (hp : PaidBeam p v): Scout 2 (phraseS (p ∘ verso)) v:=by
    obtain ⟨u,hu,h⟩:=hp.arrives; refine ⟨by norm_num,u, budget_loosen (togg u) hu, fun s hs=>?_⟩; let v:= (⟨s,hs⟩:sun)
    have hh(t:sun):p t=Beam.read _ t u:=h t
    rw [show phraseS (p∘ verso) s=p (verso v) from phrased (p∘ verso) v,hh (verso v)]; convert (u.spar (abs_le.mpr (verso v|>.property))) using 1
    simp [verso,v,slash,div_eq_mul_inv]
    rfl
end narrow
end YM.PhysicalNext.Repeat.Muse
