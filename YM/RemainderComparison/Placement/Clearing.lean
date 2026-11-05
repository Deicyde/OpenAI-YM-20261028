import YM.RemainderComparison.Placement.Tariff
/-!
 # Calibration of star λ. Vanishing vertical and full derivatives when
 k < number of powers in the model.B.Author.Centre.C.Domain.Input.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Placement
open Function Filter Finset
open Lattice RG Pressure Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Shell Census Raw Footprint Matter
open PhysicalNext.Repeat Deck Stellar Mint Poll Pond MeasureTheory ProbabilityTheory Greenbelt Lotus Sienna Fare
open Further.PhysicalPeriodLimitF933 Macrame
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Gas Ursell Trees Blaze March Lyric WickReps Creek Mosaic Merge Palette Typeface Harmonics
open AnalyticBridge VerifiedReset Next.Scheduling Extra.Iteration Song Aria Seedlings BoxOf
variable {ι:Type}
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {m k i r q v:ℕ}
variable {x:E}
-- Smooth only through target order. May vanish to all available derivatives due to power prefactors.
structure Decimates (f:E→ℝ)(k:ℕ)(q:ℕ)(x:E):Prop where
    attain : ContDiffAt ℝ k f x
    flat : ∀ i, i≤ k→i<q→ iteratedFDeriv ℝ i f x=0
namespace Decimates
variable {f g:E→ℝ} (h:Decimates f k q x)
include h
lemma flex (n:ℕ)(p:n≤q): Decimates f k n x := ⟨h.attain,fun i hi hp=> h.flat i hi (Nat.lt_of_lt_of_le hp p)⟩
lemma times (hh: Decimates g k r x) : Decimates (f*g) k (q+r) x:=by
    have hv:= h.attain.mul hh.attain
    refine ⟨hv,fun i hi he=>?_⟩
    obtain ⟨s,hs,hx,hf⟩:=h.attain.contDiffOn' le_rfl (by simp)
    obtain ⟨t,ht,hX,hg⟩:=hh.attain.contDiffOn' le_rfl (by simp)
    simp only [Set.insert_eq_of_mem (Set.mem_univ _), Set.univ_inter] at hf hg
    let B:= ContinuousLinearMap.mul ℝ ℝ
    have hx : x∈s∩t:=⟨hx,hX⟩; have hd:UniqueDiffOn ℝ (s∩t):=(hs.inter ht).uniqueDiffOn
    apply norm_le_zero_iff.mp
    change ‖iteratedFDeriv ℝ i (fun y=> f y*g y) x‖≤0
    rw [← iteratedFDerivWithin_eq_iteratedFDeriv hd (hv.of_le (by exact_mod_cast hi)) hx]; refine (B.norm_iteratedFDerivWithin_le_of_bilinear (hf.mono Set.inter_subset_left) (hg.mono Set.inter_subset_right) hd hx (by exact_mod_cast hi)).trans ?_
    refine le_of_eq ?_; rw [show _*(∑ b∈Finset.range (i + 1), _)=‖B‖*0 from congr_arg (fun z:ℝ=> ‖B‖*z) (Finset.sum_eq_zero ?_),mul_zero]
    intro j hj; have hp:j < i + 1:= Finset.mem_range.mp hj
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hd (h.attain.of_le (by exact_mod_cast (show j ≤ k by omega))) hx,iteratedFDerivWithin_eq_iteratedFDeriv hd (hh.attain.of_le (by exact_mod_cast (show i-j≤k by omega))) hx]; by_cases hP:j<q
    · simp [h.flat j (by omega) hP]
    simp [hh.flat (i-j) (by omega) (by omega)]
omit h
lemma zeroₚ : Decimates (0:E→ℝ) k q x:=by
    refine ⟨contDiffAt_const,fun i _ _=>?_⟩; cases i with
    | zero => ext t; simp
    | succ i=>change iteratedFDeriv ℝ _ (fun (_:E)=> (0:ℝ)) _=_; rw [iteratedFDeriv_succ_const]; rfl
lemma enough (hf:ContDiffAt ℝ k f x): Decimates f k 0 x:= ⟨hf,fun _ _ hp=>False.elim (Nat.not_lt_zero _ hp)⟩
include h in
lemma union (hg:Decimates g k q x) : Decimates (f + g) k q x :=by
    refine ⟨h.attain.add hg.attain,fun i hi hh=>?_⟩; rw [iteratedFDeriv_add_apply (h.attain.of_le (by exact_mod_cast hi)) (hg.attain.of_le (by exact_mod_cast hi)), h.flat i hi hh,hg.flat i hi hh,add_zero] -- name inspect
lemma rolls (s:Finset ι) (F:ι→E→ℝ)(hp:∀ i∈s,Decimates (F i) k q x): Decimates (∑ i∈s,F i) k q x:=by
   induction s using Finset.induction_on with
   | empty=> rw [sum_empty]; exact zeroₚ
   | insert i s hi H=> rw [sum_insert hi]; exact union (hp _ (mem_insert_self ..)) (H (fun j hj=> hp j (mem_insert_of_mem hj)))
lemma summation (s:Finset ι) (F:ι→E→ℝ)(hp:∀ i∈s,Decimates (F i) k q x): Decimates (fun x=>∑ i∈s,F i x) k q x:=by
    convert rolls s F hp using 1
    ext1; simp
lemma prod_decimate (s : Finset ι) (F:ι→E→ℝ)(Q:ι→ℕ)(hp:∀ i∈s,Decimates (F i) k (Q i) x) : Decimates (∏ i∈s,F i) k (∑ i∈s,Q i) x:=by
   induction s using Finset.induction_on with
   | empty=> rw [sum_empty,prod_empty]; exact enough contDiffAt_const
   | insert i s hi h=> rw [sum_insert hi,prod_insert hi]; exact times (hp _ (mem_insert_self ..)) (h (fun i hi=> hp i (mem_insert_of_mem hi)))
lemma multiplied (s:Finset ι)(F:ι→E→ℝ)(Q:ι→ℕ)(hp:∀ i∈s,Decimates (F i) k (Q i) x):Decimates (fun x=>∏ i∈s,F i x) k (∑ i∈s,Q i) x:=by
    convert prod_decimate s F Q hp using 1; ext; simp
lemma valued (hp:ContDiffAt ℝ k f x)(he:f x=0): Decimates f k 1 x:=by
   refine ⟨hp,fun i _ hy=>?_⟩; obtain rfl:i=0:=by omega
   ext y; simp [he]
-- (b,z) chart.O: ordinary Trace coeff, p≤k moments vanish then verdict.Log polynomial any b.
lemma stamped (k q:ℕ) (x:E) : Decimates (fun a:ℝ×E=>a.1^q) k q (0,x):=by
    induction q with
    | zero=> simp only [pow_zero]; exact Decimates.enough contDiffAt_const
    | succ q ih=> simp_rw [pow_succ]; exact ih.times (q:=q) (f:=fun a:ℝ×E=>a.1^q) (g:=fun a:ℝ×E=> a.1) (valued contDiffAt_fst rfl)
lemma clears {f:ℝ×E→ℝ} (H:Decimates f k q (0,x)) (hp:i ≤ k)(he:i < q): Trace.coefficient f i x=0 := by unfold Trace.coefficient Trace.plain; rw [H.flat i hp he]; simp
end Decimates
end YM.RemainderComparison.Placement
