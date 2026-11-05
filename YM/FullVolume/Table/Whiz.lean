import YM.FullVolume.Table.Aces
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

/-!
# Souls N payroll. Any stance common, forward. m≤N. Later holds fields. -/
open Tent
variable {a:ℝ}
abbrev Top (N n)(T:Team (stageP A.B.a N n)):=∀ x: RG.Shoot.band A.B.a N, Nonempty (Row (A:=A) N N n T (launch (A:=A) N n x))
section step
variable (R) (he:Tent.Credit A.delay a) (hr:Planned.Port.AtTop A.B.kin)
include he hr R
local notation "P"=>stageP A.B.a N n
local notation "Y"=> RG.Shoot.band A.B.a N
lemma at_top : ∃ T:Team (stageP A.B.a N n),Top N n T := by
  choose f hf using fun (s:Signed) (v:Site (A.B.a.S.side N n))=>Tent.affable (N:=N) s v
  let y: Y:= ⟨_,left_mem_Icc.mpr (show A.B.a.clock.hatBeta N/2 ≤ 2*A.B.a.clock.hatBeta N from by linarith [A.B.a.fits.delayed N])⟩
  have hp i v : amid (f i v) ((0:Show P).proper) i v:=by
    obtain ⟨x,hx,h⟩:= hf i v y
    exact ⟨⟨_,_,x.reg_site, x.reg_support,x.forced_support,x.forced_inventory,x.forced_tests,fun _ _=> rfl,fun _ _=>rfl⟩,hx,h⟩
  let T:Team P:= ⟨f,hp⟩
  refine ⟨T,fun x=>?_⟩
  have h:= (speaks R he hr N n).2 x x.property
  obtain ⟨k,hk⟩:= corresponds T (launch (A:=A) N n x).activities rfl rfl h.2.1.valid.labels (fun i v=> hf i v _)
  exact ⟨k,hk⟩
end step
structure Circle (N n:ℕ) (H:∀ m,m<N→ Chord R N m n t t) where -- A repeats X; Lean guard
   plan (m:ℕ) : m≤N→ Team (stageP A.B.a m n)
   receives : Top (A:=A) N n (plan N le_rfl)
   walks m (h:m<N): Passage (H m h) (T:=(plan (m+1) h)) (U:=(plan m h.le))
-- shadow collision expect
section
variable (V: ∀ m,m<N→ Chord R N m n t t)(he:Tent.Credit A.delay a) (hr:Planned.Port.AtTop A.B.kin)
include he hr g V
lemma cycle : Nonempty (Circle N n V):=by
  obtain ⟨p,hp⟩:= at_top (N:=N) (n:=n) R he hr
  let step (m:ℕ) (h:m<N)(T:Team (stageP A.B.a (m+1) n)) := (passage g (V m h) T).choose
  let W (m:ℕ)(hv:m≤N): Team (stageP A.B.a m n):= Nat.decreasingInduction (motive:=fun m h=>Team (stageP A.B.a m n)) step p hv
  refine ⟨⟨W,?_,?_⟩⟩; · rwa [show W N le_rfl=p from Nat.decreasingInduction_self ..]
  intro m hm; rw [show W m hm.le=step m hm (W (m+1) hm) from Nat.decreasingInduction_succ_left ..]; exact (passage g (V m hm) _).choose_spec
end
-- Portrait for top costs
variable {P':Team (stageP A.B.a N n)}(ht:Top N n P')
open UniformSpace
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
abbrev lips (i:band A.B.a N):= Classical.choice (ht i)
local notation "X'"=> Completion (Home P')
local notation "Ω"=> A.B.a.clock.hatBeta N
def Yawn (x:ℝ): Completion (Home P'):= if h:fromLambda Ω x∈band A.B.a N then ↑((lips ht ⟨_,h⟩).val) else 0
lemma readingOn {x:ℝ}(h:fromLambda Ω x∈band A.B.a N): Yawn ht x=↑((lips ht ⟨_,h⟩).val):=dif_pos h
include ht
variable (R) (he:Tent.Credit A.delay t) (hr:Planned.Port.AtTop A.B.kin)(hY:Climate (A.B.a.clock.hatBeta N))
include R he hr hY
lemma instruct (hq: 1≤q)(hK:q≤ grand Ω) {u v:ℝ} (hp:emcee Ω u) (hv:|v|≤1): Rebar q (phraseS (fun i:sun=> Yawn ht (u+i.val*v))) (4*t):=by
  obtain ⟨W,hx⟩:= Pass.priced _ hY hp hv
  let V(i:sun): Home P':= (lips ht (W.poses i)).val
  have ht' i: observe P' (V i)=(Tent.launch (A:=A) N n (W.poses i)).activities:= (lips ht _).property
  rw [show (fun i:sun=>Yawn ht (u+i.val*v))=(fun i:sun=>(↑(V i):Completion (Home P'))) from ?_]; swap; · ext1 i; have he:= hx i (s1 i _ hY.grade); have hh:fromLambda Ω (u+i.val*v)∈ RG.Shoot.band _ N:=he ▸ (W.poses i|>.property); rw [readingOn ht hh, show (⟨_,hh⟩:band A.B.a N)=W.poses i from Subtype.ext he.symm]
  apply witness _ _ _ hq; intro w η hw
  obtain ⟨hh,hV⟩:= Tent.columns R he hr W (n:=n); simp_rw [← ht'] at hh hV
  let Y:= stageP A.B.a N n; have hf:0≤t:=  by have hh:= ((hV.choose_spec.2) 0 (1:Config G (A.B.a.S.side N n))).nonneg; have hv:=budget_nonneg (hV.choose_spec.1 0); change 0 ≤ t*Y.k at hv; exact nonneg_of_mul_nonneg_left hv Y.k0
  refine eats V (v:=t*(A.B.a.clock.forcedAllowance N)) hw ⟨fun i b hv=>hh.stars i b (stripe_down hv (zero_lt_one.trans_le hq) hK)⟩ ?_ (le_of_eq (by change 4*(t*Y.b)=4*t*Y.b; ring)) ?_
  · obtain ⟨f,hf,hV⟩:=hV; exact ⟨f,hf,fun i U=> (hV i U).lessen hq hK⟩
  change t*Y.k ≤4*t*Y.k; nlinarith [Y.k0]
end YM.PhysicalNext.Repeat.Pass
