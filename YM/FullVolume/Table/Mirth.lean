import YM.FullVolume.Table.Atlas
/-! Analytics via actual stencil volumes, only real-argument jumps. -/
/-!
# S.pilt on actual shelves. Power.Test. empty τ.Moves furnished via budgeted metadata.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Pass
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Height Input Org Supply Pane Slide
open Push.PriceCompiler Progress.DirectedRecipe Jams Apse Empire Time Roof Chord Ovens
open FullVolume.Ray FullVolume.Urns
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}
variable (g:G.Simple){v q d t t':ℝ}{N n m:ℕ}(H:Chord R N m n t t)(h:Degree R.shape R.scout A.delay)(hq:Savvy R.scout R.target A.delay q v d t)

-- Scenic dividends in real Completion. hq>2.
open UniformSpace
local notation "T'"=> stageP A.B.a (m+1) n
local notation "P'"=> stageP A.B.a m n
local notation "s"=> A.B.a.S.side m n
local notation "S"=> A.B.a.S.side (m+1) n
local notation "f₀"=> Flight A N m n
local notation "Ω"=> A.B.a.clock.hatBeta (m+1)
local notation "W"=> A.B.a.budget (m+1)
variable {T:Team (stageP A.B.a (m+1) n)} {U:Team (stageP A.B.a m n)}(hp:Passage H (T:=T) (U:=U))
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
lemma s0 (i:sun)(V:Climate Ω): |i.val|≤6* grand Ω:= (abs_le.mpr i.property).trans (by linarith [V.grade])
lemma s1 (i:sun) (x:ℝ) (hx:1≤x):|i.val| ≤6*x:= (abs_le.mpr i.property).trans (by linarith)
-- any discontinuous Choice between primitive readings, as long as activity values affine
-- o,Y. enforce output arcs independent of meta & v
variable {x x' u:ℝ} (V:Climate (A.B.a.clock.hatBeta (m+1)))
include g H h hq hp V
abbrev fn (a:Levels G) (m:ℕ)(v:ℝ):= chores G (a.params m) v (a.clock.hatBeta m) / (a.budget m).threshold^2
local notation "β"=> fn A.B.a m v
local notation "D'"=> Director N m n T
variable {A₀ B₀:Home T}
lemma tours (F : sun → Director N m n T)(ht:emcee Ω x)(hw:|u|≤1)
    (he:∀ i:sun,(F i).val.val.activities=observe T (A₀+i.val • B₀))
    (hV:∀ i:sun,(F i).val.val.beta=fromLambda Ω (x+i.val*u)): Rebar (q/2) (phraseS (cho H hp∘ F)) d ∧ Rebar q (phraseS (fun i=> Delta H (F i).val)) (fn A.B.a m v):=by
  obtain ⟨W',hW⟩:= Pass.priced _ V ht hw
  have hL:= beta_eq A.B.valid m
  have hp1 :grand Ω=fire G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m):= congr_arg grand hL
  have hp2 :joy Ω=thaw G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m):= congr_arg joy hL
  suffices hv : ∃ Y:Mist A.B.a m (grand Ω) (joy Ω),
      (∀ i:sun,(Y.peak i).val = (F i).val.val.beta) from (by
        rw [hp1,hp2] at hv; obtain ⟨Y,hY⟩:=hv
        apply stamped g H h hq hp _ (Y:=Y); constructor
        · exact fun _=>(hY _).symm
        · exact fun i j=> prier
        ·
          intro A j; simp_rw [fun t=>(F t).val.property.1.point, he]
          let P u:= (observe T u).regularOccurrence W j A
          let α:=P A₀; let b:=P B₀
          refine ⟨fun i=>α+b*i,(FullVolume.Ray.ink.straight ..).rise (by norm_num),fun i=>?_⟩
          have hp (x:Home T): (observe T x|>.reg)=(layout G (S) W).reg:= rfl
          unfold α b P Activities.regularOccurrence; dsimp only; simp_rw [hp]
          by_cases hh: Healthy ((W).threshold) ((layout G (S) W).reg j|>.support) A
          · rw [masked_eq _ _ _ _ hh,masked_eq _ _ _ _ hh,masked_eq _ _ _ _ hh]; rw [mul_comm _ i.val]; rfl
          rw [masked_ne _ _ _ _ hh, masked_ne _ _ _ _ hh, masked_ne _ _ _ _ hh,zero_mul,zero_add]
        intro W' j; simp_rw [he]; let x := (observe T A₀).K j W'; let y:=(observe T B₀).K j W'
        exact ⟨_,(FullVolume.Ray.ink.straight x y).rise (by norm_num),fun t=> by rw [mul_comm y t.val]; rfl⟩)
  exact ⟨⟨W'.knot,W'.flow,W'.poses,W'.move⟩,fun i=>(hW _ (s1 i _ V.grade)).trans (hV i).symm⟩
-- jump from t=0 argument using Stripe.On.That no Vitali edits.
omit g H h hq hp V
section diag
lemma stripe_one {p:ℝ}(hp:1≤p) (i:sun):Stripe (Finsupp.single i 1) p 1:= by intro k; rw [← mix_id, ← combo_eq,combo]; simp only [Finsupp.linearCombination_single,one_smul,Real.norm_eq_abs,abs_pow]; exact pow_le_one₀ (abs_nonneg _) (ratio_le hp i.property)
lemma solo {X:Type*}[NormedAddCommGroup X] [NormedSpace ℝ X]{f:sun→ X}{p b:ℝ}(hr:Rebar p (phraseS f) b)(y:sun): ‖f y‖ ≤ b:=by
   have hx:= hr.beam _ _ (stripe_one hr.ray y); rw [mix_made, ← combo_eq,combo] at hx; simpa using hx
lemma snap {p:ℝ}(hq:2≤p){i:sun}: Stripe (Finsupp.single i 1 - Finsupp.single tip 1) p |i.val| :=by
  intro n; rw [← mix_id, ← combo_eq,map_sub]; simp only [combo,Finsupp.linearCombination_single,one_smul]
  cases n; · simp
  next n=>
    simp only [zero_div,zero_pow (n:=n+1) (by omega),sub_zero,Real.norm_eq_abs,abs_pow]
    have hu := ratio_le (show 1≤p by linarith) i.property; apply (pow_le_pow_of_le_one (abs_nonneg _) hu (by omega:1≤n+1)).trans; rw [pow_one,abs_div]; exact (div_le_self (abs_nonneg _) (show 1≤|p| from (le_trans (by linarith) (le_abs_self _))))
lemma unison {X:Type*}[NormedAddCommGroup X] [NormedSpace ℝ X] {v:sun→ X}{b: X}{p z:ℝ}(hr:Rebar p (phraseS v) z)(hp:2≤p)(h:∀ i:sun,i.val≠0→ v i=b): v tip=b:=by
  apply sub_eq_zero.mp; apply norm_le_zero_iff.mp; by_contra! hx; let d:= min 1 (‖v tip-b‖/(2*(1+z))); have hd : 0<d:= lt_min zero_lt_one (div_pos hx (by linarith [hr.nonneg])); let i:sun:=⟨d,⟨by linarith,min_le_left ..⟩⟩
  have hv:= hr.beam _ _ (snap hp (i:=i)); rw [mix_made, ← combo_eq,map_sub] at hv; simp only [combo,Finsupp.linearCombination_single,one_smul,h i (show i.val≠0 from hd.ne'),norm_sub_rev b] at hv
  have hz : d ≤ ‖v tip-b‖/(2*(1+z)) := min_le_right ..; rw [le_div_iff₀ (by linarith [hr.nonneg])] at hz; change _≤ |d| *z at hv; rw [abs_of_nonneg hd.le] at hv; nlinarith
end diag
-- hoist scalar indifferent
include g H h hq V hp
lemma switchyard (i j: D')(hv:4≤q)(ht: emcee Ω x)(hβ : (i.val.val).beta = fromLambda Ω x)(hs: (i.val.val).beta=(j.val.val).beta)(hh : i.val.val.activities=j.val.val.activities):
    cho H hp i=cho H hp j ∧ Delta H i.val=Delta H j.val:=by
   let F(t:sun):= if t.val=0 then i else j
   let z:Home T:= (uniformR i).val
   have hx (b:sun) : (F b).val.val.activities= observe T (z+b.val • (0:Home T)):=by
      unfold F; split
      next h=> simpa using (show _=observe T z from (uniformR i).property.symm)
      next=> simp only [smul_zero,add_zero]; rw [← hh]; exact (uniformR i).property.symm
   obtain ⟨h,hY⟩:= tours g H h hq hp V F ht (u:=0) (by norm_num) hx (fun b=> by unfold F; split_ifs <;> simp [← hs,hβ])
   have ht:F tip=i:= if_pos rfl
   have hz := unison h (by linarith) (b:=cho H hp j) fun b (h:b.val≠0)=> congr_arg (cho H hp) (if_neg h : F b=j)
   have hA := unison hY (by linarith) (b:=Delta H j.val) fun b (h:b.val≠0)=> congr_arg (fun x:Director N m n T=> Delta H x.val) (if_neg h : F b=j)
   change cho H hp (F tip)=_ at hz; change Delta H (F tip).val=_ at hA
   rw [ht] at hz hA; exact ⟨hz,hA⟩
end YM.PhysicalNext.Repeat.Pass
