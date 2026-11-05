import YM.RG08.Ratio.Gift
/-!
# Read kinetic on aggregate quadratic, positivity reset (boundary branch)
All equations equality, including grade/slot restrictions, pure kernel k via
`marked_units`. No interpolation with the actual running relation. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Conductor
open Filter MeasureTheory
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent Profiles Finset Next.Free
open PertExtension.Series.Tested PertExtension.Series.Radial Matrix Reflect PowerSeries
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} (i : G.ColorIndex)

-- Ω reader total with constant grade hardcoded (exact agreement from unitRead later).
def compass (F : Air G) : ℕ→ ℝ := fun q=> if q=0 then 1 else probeK i (F (2*q) 2)
@[simp] lemma compass_zero (F : Air G) : compass i F 0=1 := if_pos rfl
lemma compass_eq (F : Air G) (Q : Pot G 2)(h : probeK i Q=1) (q : ℕ) : compass i F q=probeK i (sector Q F q 2) := by
  by_cases he : q=0
  · subst q; rw [sector_t, compass_zero,h]
  have hp:0<q:=Nat.pos_of_ne_zero he
  rw [sector_unique _ _ (show 0<2*q by positivity) (by omega) (by omega),compass,if_neg he]

variable (F : Air G)(Q : Pot G 2)
local notation "Ω" => compass i F

-- explicit per-rank finite map; leaves r=0 out of recalibrated action.
def revise (e r : ℕ) := ∑ j∈range (e+1), recitalR Ω e j • sector Q F j r
lemma reviseLead (r) : revise i F Q 0 r=sector Q F 0 r := by unfold revise; rw [sum_range_one,recital_priced Ω (compass_zero ..),one_smul]
-- grade variety reconstruction
instance playedDecide (e r : ℕ) : Decidable (Played e r) := Classical.propDecidable _
def correct : Air G := fun e r=> if Played e r ∧ r ≠ 0 then revise i F Q ((e+2-r)/2) r else 0
lemma corrigendum : Decked (correct i F Q) ∧ Halt (correct i F Q) := by
  constructor
  · intro i j hj; unfold correct at hj; split at hj; next h=> exact h.1
    contradiction
  intro i; rw [correct,if_neg]; simp
lemma correct_p {e r q : ℕ} (hr : 0<r)(hp : 0<e)(hv : e+2=r+2*q) : correct i F Q e r= revise i F Q q r := by
  unfold correct; rw [if_pos ⟨⟨hp,q,hv⟩,Nat.ne_of_gt hr⟩,show (e+2-r)/2=q by omega]
lemma sector_adjust (h : Decked F) (q r : ℕ) : sector Q (correct i F Q) q r=revise i F Q q r := by
  match r with
  | 0=> rw [sector]; unfold revise; simp only [sector,smul_zero,sum_const_zero]
  | 1=>
    by_cases hh:q=0
    · subst q; rw [sector_l _ (corrigendum ..).1,reviseLead,sector_l _ h]
    rw [sector_unique _ _ (e:=1+2*q-2) (by omega) (by omega) (by omega), correct_p i F Q (q:=q) (by omega) (by omega) (hv:= by omega)] -- q bind
  | j+2=>
    by_cases hh:j+2*q=0
    · rw [show j=0 by omega,show q=0 by omega,reviseLead (r:=0+2)]; rw [sector_t,sector_t]
    rw [sector_unique _ _ (e:=j+2*q) (by omega) (by omega) (by omega),correct_p i F Q (q:=q) (by omega) (by omega) (hv:= by omega)]

lemma fiscal_sector (h : Gets F)(hv : Glows Q)(e k) : Glows (sector Q F e k) := by
  unfold sector; split; exact Glows.zero; exact (h.2 _ _).2; next n=>
    split; next h=> rw [show n=0 by omega,prolong_self]; exact hv
    exact (h.2 _ _).2
lemma glows_fleet {s : ℕ}{I: Type} {f : I→ Pot G s} (t: Finset I)(hp : ∀ i∈t, Glows (f i)) : Glows (∑ i∈t,f i) := by
  induction t using Finset.induction_on with
  | empty=> rw [sum_empty]; exact Glows.zero
  | insert i s hi ih=> rw [sum_insert hi]; exact (hp _ (mem_insert_self ..)).plus (ih fun _ hj=> hp _ (mem_insert_of_mem hj))
lemma traffic (h : Gets F)(hv : Tunable Q)(hc : Glows Q) : Gets (correct i F Q) := by
  refine ⟨(corrigendum ..).1, fun e r=>?_⟩
  unfold correct; split
  · exact ⟨Tunable.sum _ (fun i hi=>Tunable.scale _ (Tune_sector F Q (fun i j=> (h.2 i j).1) hv _ _)), glows_fleet _ (fun i hi=>Glows.scale (fiscal_sector F Q h hc _ _) _)⟩
  exact ⟨Tunable.zero ..,Glows.zero⟩

private lemma solely {f : Pot G 2} (hp : Glows f) (a : ℝ) : probeK i (a • f)=a*probeK i f := by obtain ⟨w,C,hw,H⟩:=hp; exact probe_scale i a H hw
private lemma shownAdd {f g : Pot G 2} (hp : Glows f)(h : Glows g) : probeK i (f+g)=probeK i f+probeK i g := by
  have ht : Glows (-g) := by simpa using h.scale (-1)
  have hu : probeK i (-g)= -probeK i g := by simpa using solely i h (-1)
  obtain ⟨w,C,hw,H⟩:=hp; obtain ⟨v,D,hv,hd⟩:=ht; simpa [hu] using probe_diff i H hd hw hv
@[simp] lemma shownZero : probeK i 0=0 := by simpa using (show probeK i (_ • (0:Pot G 2))=_ from solely i Glows.zero 0)
private lemma shownSum {I: Type} {s:Finset I} {f : I→Pot G 2} (h : ∀ i∈s, Glows (f i)) : probeK i (∑ j∈s,f j)=∑ j∈s,probeK i (f j) := by
  induction s using Finset.induction_on with
  | empty=>simp
  | insert i s hi ih=>
    have ht j hj:= h j (mem_insert_of_mem (s:=s) hj); rw [sum_insert hi,sum_insert hi,shownAdd _ (h i (mem_insert_self ..)) (glows_fleet _ ht),ih ht]

/-- Literal slot coefficient reset as substitution in formal squared coupling after
 extracting b⁻¹ again, at all displacements. Includes empty rank 0 sector = 0;
 no assertion about F(..,0). -/
theorem decor (h : Decked F) (q r : ℕ) (p : Beads (Loc G 1) r) :
    let S:=PowerSeries.mk (fun i=> sector Q F i r p)
    let V:=reform Ω
    sector Q (correct i F Q) q r p=PowerSeries.coeff q ((PowerSeries.mk V)⁻¹ * S.subst (Span V)) := by
  intro S V; rw [sector_adjust i F Q h]; unfold S
  rw [show PowerSeries.coeff q ((PowerSeries.mk V)⁻¹ * PowerSeries.subst (Span V) _)=_ from rewrite_back Ω (compass_zero ..) _ q]; unfold revise; simp [Finset.sum_apply]

-- marginal exactly reset. Need pre-produce hF. Flipped-oriented all q.
def Balanced (i : G.ColorIndex) (F : Air G) := ∀ q, probeK i (F q 2)=0

theorem trueUP (h : Gets F) (hp : Glows Q) (hx : probeK i Q=1) : Balanced i (correct i F Q) := by
  intro e; by_cases he: Played e 2
  · obtain ⟨hi,k,hk⟩:=he
    rw [correct_p _ _ _ (by decide) hi hk]; unfold revise
    have hz i:= fiscal_sector F Q h hp i 2
    rw [shownSum]; swap; · intro i _; exact (hz _).scale _
    simp_rw [solely i (hz _), ← compass_eq i F Q hx]
    rw [restored Ω (compass_zero ..),if_neg (by omega)]
  rw [correct,if_neg (by tauto),shownZero]
lemma sunCorrect (i : G.ColorIndex) : Balanced i (wilsonTop i) := by
  intro q; unfold wilsonTop; rw [if_neg (by omega),shownZero]

private lemma spin_sums {m : Side} {s: Finset ℕ} {v : ℕ→Link G m→ℝ} (he : ∀ i∈s,Pointwise (v i)) : Pointwise (∑ i∈s,v i) := by
  induction s using Finset.induction_on with
  | empty=> rw [sum_empty]
            simpa using! (Pointwise.coin (F:=WilsonQ G m) Wilson_witness 0)
  | insert i s hi ih=> rw [sum_insert hi]; exact (he i (mem_insert_self ..)).add (ih fun i hj=> he i (mem_insert_of_mem hj))
private lemma taylorSum {m : Side} {s: Finset ℕ} {v : ℕ→Link G m→ℝ} (he : ∀ i∈s,Pointwise (v i)) (k) :
    Tensor.coeff (∑ i∈s,v i) k 0=∑ i∈s,Tensor.coeff (v i) k 0 := by
  induction s using Finset.induction_on with
  | empty => rw [sum_empty,sum_empty]; exact Tensor.coeff_zero k (0 : Link G m)
  | insert i s hi ih=>
    have hp j hj:=he j (mem_insert_of_mem (s:=s) hj); rw [sum_insert hi,sum_insert hi,Tensor.coeff_add (by exact ((he i (mem_insert_self ..)).analytic.contDiffAt).of_le le_top) (by exact ((spin_sums hp).analytic.contDiffAt).of_le le_top),ih hp]

theorem remake {m : Side} (hF : Gets F) (hp : Faithful Q F m) (hQ : Tunable Q) : Faithful Q (correct i F Q) m := by
  intro q j; choose f ht he using (fun e=> hp e j)
  let k := recitalR Ω q
  have hv z : Pointwise (k z • f z) := (ht z).coin _
  refine ⟨∑ e∈range (q+1),k e • f e,spin_sums (fun i _=> hv i),fun p hc=>?_⟩
  have hS (e a) : Summable (a • sector Q F e p) := (Tunable.scale a (Tune_sector F Q (fun i j=>(hF.2 i j).1) hQ e p)).1
  rw [taylorSum (fun i _=>hv i), sector_adjust i F Q hF.1, revise,recital_sum _ _ (fun i _=>hS _ _)]
  apply sum_congr rfl; intro e _; rw [Tensor.coeff_smul _ ((ht e).analytic.contDiffAt), he e p hc, recital_scale _ (Tune_sector F Q (fun i j=>(hF.2 i j).1) hQ e p).1]
end YM.RG08.Conductor
