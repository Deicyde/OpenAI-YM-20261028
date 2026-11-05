import YM.FullVolume.Nectar.Funnel
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
open FullVolume.Nectar in
lemma monies (hx: ‖K‖≤1)(hX : ∀ s:sun,World.ready ((X s):Completion (Home T))=read _ s K): ∃ a:ℕ→ℝ,(∀ v :Site c, SumBudget (fun i=>if v∈(ft|>.hard i).support then (S.p).mass (ft|>.hard i).support (a i) else 0) S.k)∧∀ i,Nectar.Feel (fun s:sun=> (observe T (X s)).K i) (a i):=by
   obtain ⟨D,hD,hq⟩:=birthUse S T
   choose p hp hb using fun i:ℕ=>hq (K i); let z(i:ℕ):=∑' j,p j i; let h i:=(layout G c S.p|>.hard i); let e:=S.p
   let f(v:Site c)(j i:ℕ):ℝ:=if v∈ (h i).support then (S.p).mass (h i).support (p j i) else 0
   have ht(v:Site c): SumBudget (fun i:ℕ×ℕ=> f v i.1 i.2) S.k:=by
      refine budget_loosen (@Extra.Histories.budget_prod _ _ (fun i:ℕ×ℕ=> f v i.1 i.2) (fun j:ℕ => ‖K j‖*S.k) (fun i=> hb i v) ((paid K).summable.mul_right S.k)) ?_
      rw [tsum_mul_right,(paid K).tsum_eq]; exact mul_le_of_le_one_left S.k0.le hx
   have hs(i:ℕ): Summable fun j=>p j i:=by
      obtain ⟨x,hx⟩:=(h i).inventory_ne.mono (h i).inventory_sup
      apply Summable.of_nonneg_of_le (fun j=>(hp j i).1) _ ((ht x).2.1.prod_symm.prod_factor i); intro j; change _≤f x j i; rw [show f x j i= _ from if_pos hx]; exact (e.loMass _ _ (hp j i|>.1)) -- syntax .. plus
   refine ⟨z,fun v=>?_,fun i=>?_⟩
   · let t(i:ℕ):=∑' j,f v j i; have htB: (fun i:ℕ=>if v∈(h i).support then S.p.mass (h i).support (z i) else 0)=t:=by
         ext i; by_cases he:v∈ (h i).support
         · rw [if_pos he]; unfold t f z;
           simp_rw [if_pos he, BudgetPoint.mass,tsum_mul_left]
         rw [if_neg he]; unfold t f; simp only [if_neg he,tsum_zero]
     rw [show (fun i:ℕ=>if v∈(ft |>.hard i).support then S.p.mass (ft|>.hard i).support (z i) else 0)=t from htB]; exact countRows (f v) (ht v)
   let F(k:ℕ): Tint ℝ (Config G c):= Tint.wear (⟨fun v=> D i v (K k), memℓp_infty ⟨p k i,Set.forall_mem_range.mpr (hp k i|>.2)⟩⟩: lp (fun _: Config G c=>ℝ) ⊤)
   have hv k:‖F k‖≤p k i:= lp.norm_le_of_forall_le (f:=Tint.cast (F k)) (hp k i|>.1) (hp k i|>.2)
   have hy : Summable (fun i:ℕ=> ‖F i‖):= .of_nonneg_of_le (fun _=>norm_nonneg _) hv (hs i)
   let Y: Beam (Tint ℝ (Config G c)):= ⟨F,memℓp_gen (by simpa using hy)⟩
   refine ⟨fun s:sun=> FullVolume.Amp.Beam.read _ s Y,fun t U=>?_,Y,(paid Y|>.tsum_eq.symm).trans_le (hy.tsum_le_tsum hv (hs i)),fun _=>rfl⟩
   let p:= D i U;let f:= Tint.see ℝ U
   rw [← hD, hX]; have ht':= p.hasSum (K.spar (abs_le.mpr t.property)); have hp:= f.hasSum (Y.spar (abs_le.mpr t.property)); simp_rw [map_smul] at hp ht'; exact hp.unique ht'
end YM.PhysicalNext.Repeat.Muse
