import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Wall
import YM.Further.STRONG_STARTUP_CREDIT.Launch
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Rent
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Song.Embassy
import YM.PhysicalNext.UNMASKED_THROUGH_LAUNCH.Dome
import YM.Planned.RECIPE_STARTUP_PORT.Horizon


/-!
# At the purchased RG calendar

Actual preliminary output INCLUDING T/d/κ witnesses for the downstream
 shape interface. For now not exposing continuity, and not pricing the
 fine remainder after reattachment, do NOT confuse word-size E price with
 the running-coupling window. But the K price is in forecast units,
 with all quantitative bookings made in the actual order.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Opera
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration Greenbelt Match Time Supply Input Testing
open ConnectedActivityE6.Blaze Blaze.March Captain PriceCompiler
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {D : Rolls s} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D}
    {E : ℕ → ℕ → Exchange} {F : ℕ → ℕ → Postage} {w u : ℝ→ℝ} {f r b : Return.Wages}
    {q : UVNext.CouplingReset.ResetPrices} {η : ℕ → ℝ} {A : Scouts (F:=F)} {hL : ℕ→ℝ}
    {Q : Targets s K} {p : Expenses Q} {c : ℝ}
    (B : Directed G I Z K P) (R : Register D p f hL)

def Treble (W : Delays Θ) := ∀ j x,W.betaEntry j≤x → ∀ i,StepStages j i → ((s.profile i).supportExponent+3) / radiusB x ≤ (s.profile i).width/2
lemma conducts (V : Delays Θ) : ∃ W : Delays Θ, DelayLe V W ∧ ∀ X : Delays Θ, DelayLe W X → Treble X := by
  have h := @YM.Work.E01.radiusB_tendsto
  have hp (i:ℕ) : ∀ᶠ x in atTop, ((s.profile i).supportExponent+3) / radiusB x ≤ (s.profile i).width/2 :=
    (((tendsto_const_nhds (x:=(s.profile i).supportExponent+3)).div_atTop (tendsto_natCast_atTop_atTop.comp h)).eventually (gt_mem_nhds (half_pos (s.profile i).width_pos))).mono (fun _ H=>H.le)
  obtain ⟨x,-,hy,hS⟩ := collect_upper V.betaEntry _ fun j=> eventually_transitions j _ _ fun i (h:StepStages j i)=> hp i
  exact ⟨{V with betaEntry:=x}, ⟨hy,le_rfl,le_rfl,le_rfl⟩, fun _ h j y hv=> hS j y ((h.beta _).trans hv)⟩

variable {N m n : ℕ}
abbrev Guide (N m n) (X : RG.Rep G (B.a.S.side (m+1) n)) := Cash (f (B.a.clock.J (m+1)) (B.a.clock.J m)) (B.a.clock.hatBeta m) (R.μ (B.a.clock.J (m+1)) (B.a.clock.J m)) (D.L (B.a.clock.J (m+1))) (Q (B.a.clock.J (m+1)) (B.a.clock.J m)) (R.o (B.a.clock.J (m+1)) (B.a.clock.J m)) (R.c (B.a.clock.J (m+1)) (B.a.clock.J m)) (ships B N m n) X
abbrev Price (N m n X) (H : Guide B R N m n X) := let v:=p (B.a.clock.J (m+1)) (B.a.clock.J m); Cash.Renewed v.degrees v.earn v.one v.two H

def earlyFee (N m) (β : ℝ) := turnFee (B.a.budget m)*(betaF G (B.a.clock.hatBeta m) (D.L (B.a.clock.J (m+1))) ^ (p (B.a.clock.J (m+1)) (B.a.clock.J m)).wanting+
    Song.octaveNeed G (B.a.budget m) (B.a.params m).clip (B.a.params m).width (B.a.params m).paths (B.a.clock.loopCap m) β (B.kin.alpha N m))
-- all ships same. read args abstract
variable (hm : m<N)
    (h : ∀ N m n,m≤N → Bid.Sworn (B.M.H N m) n G)
    (hr : Receiving R A W c)
    (hQ : ∀ j i:ℕ, StepStages j i → (s.profile i).supportExponent+3≤(p j i).earn)
    (M : Use.Machine B E A η q f r b) (ht : Treble W)
    {X X' : RG.Rep G (B.a.S.side (m+1) n)}

include h hr hm
lemma feature (hl : Lives B.bake N (m+1) n X) (hb : X.beta∈band B.a (m+1)) : ∃ I : Guide B R N m n X, Price B R N m n X I := by
  obtain ⟨I,hI,hA⟩:= Planning.walls B R hr.grow.1 h N m n hm X hl hb; exact ⟨I,hI⟩

omit hr in
lemma protocol : SliceRows.Stamp (ships B N m n) :=
    ⟨B.M.H N (m+1),B.M.H N m,B.plan.crossings N m n hm,B.plan.stack N m n hm,h N _ _ hm,
      h N _ _ hm.le,B.support.links _ _ hm,B.support.links _ _ hm.le,_,_, B.plan.all N _ hm _,_,_,B.plan.all _ m hm.le _⟩
omit hm hr h in
def forum : Return.Bookings B m n f := Chi.profiles Chi.canonical G _ _ _ (R.consumes (B.a.clock.J (m+1)) (B.a.clock.J m) (step_paid B.a m)).1 (by
    have hx : 0 < B.a.clock.threshold (m+1) := (B.a.budget (m+1)).threshold_pos
    change 0<Pressure.temp (betaF G _ _); rw [show (B.a.clock.op m n).patch.L=_ from PriceCompiler.block_eq B.valid m, ← PriceCompiler.beta_eq B.valid]; exact hx)
omit hm h in
lemma backing (hp : X.beta∈ band B.a (m+1)) : Cash.armK (Q (B.a.clock.J (m+1)) (B.a.clock.J m)) (D.L (B.a.clock.J (m+1))) (R.μ (B.a.clock.J (m+1)) (B.a.clock.J m)) (B.a.clock.hatBeta m) 0 (p (B.a.clock.J (m+1)) (B.a.clock.J m)).degrees ≤ c*forecastK B.a m A X.beta := by
  have hh := hr.earns (B.a.clock.J (m+1)) (B.a.clock.J m) (step_paid B.a m) _ (B.valid.pays m) _ (show inBand (betaF G (B.a.clock.hatBeta m) (D.L (B.a.clock.J (m+1)))) X.beta from by rw [← PriceCompiler.beta_eq B.valid m]; exact trial_in hp)
  rw [← PriceCompiler.beta_eq B.valid m] at hh; exact hh

include hQ M ht
lemma symphony (hl : Lives B.bake N (m+1) n X') (hb : X'.beta∈band B.a (m+1)) (O : Return.Wood B m n) (d : Return.Bookings B m n f)
    (U : Guide B R N m n X) (I : Guide B R N m n X') (he : Price B R N m n X' I) (pact : Alliance U I 1 0) :
    let H:= Song.posting (B.a.budget m) U; let V:= Song.plusone U pact Chi.canonical (B.kin.alpha N m)
    Return.atlas B N O d Chi.canonical r X' H V (Song.weighty I Chi.canonical O) ∧
      Collection.Local H (B.a.budget m) V (earlyFee (p:=p) B N m X'.beta) (c*forecastK B.a m A X'.beta) := by
  intro H V
  have hf:= protocol B hm h (n:=n)
  let T:=ships B N m n
  have hy := (M.passes (Q:=fun _ : ℝ=> X') hm (l:=Set.univ) (fun _ _=> ⟨hl,hb⟩)).1
  let σ:= B.a.params m
  have hp : T.down=B.kin.path N m := rfl
  have hv : T.low=σ.clip := rfl
  have hg : T.down.Bounds T.low σ.width σ.paths (B.a.clock.loopCap m) := hp ▸ hv ▸ B.support.cap N m hm.le
  have hz:= hr.grow.2 (B.a.clock.J (m+1)) (B.a.clock.J m) (step_paid B.a m) (B.a.clock.hatBeta m) (B.valid.pays m) _ _ (B.a.clock.op m n) T I.laws.data.funds hf X' I
  obtain ⟨L,d',X,y,A',b',r',B',t,k',u,⟨C'⟩,hC,h₂,h₃,h₄⟩:= hz
  have hS : σ=s.profile (B.a.clock.J m) := params_eq B.valid m
  have hA : (B.a.budget m).order ≤ (s.profile (B.a.clock.J m)).order := le_of_eq (congr_arg Stage.order hS)
  have hM : (B.a.budget m).power ≤ (s.profile (B.a.clock.J m)).power := le_of_eq (congr_arg Stage.power hS)
  have hB : Quotes.preExponent (B.a.budget m) ≤ (p (B.a.clock.J (m+1)) (B.a.clock.J m)).earn := (show σ.supportExponent+3=_ from congrArg (fun x : Stage=>x.supportExponent+3) hS).trans_le (hQ _ _ (step_paid B.a m))
  have hΞ : preExponent (B.a.budget m) / ((B.a.budget m).B:ℝ) ≤ σ.width/2 := by change (σ.supportExponent+3)/radiusB (B.a.clock.hatBeta m) ≤ _; rw [hS]; exact ht (B.a.clock.J (m+1)) (B.a.clock.hatBeta m) (B.valid.pays m) (B.a.clock.J m) (step_paid B.a m)
  refine ⟨(Return.earnings B N O d Chi.canonical r M.ring M.bill hm X' hl hb).2.2.symm.trans ?_,?_⟩
  · exact funext fun V=> (Song.forward (B.a.budget m) U pact Chi.canonical (B.kin.alpha N m) C' O rfl hA hg he V).symm
  have hh:= Song.loaded (B.a.budget m) U pact Chi.canonical (B.kin.alpha N m) C' rfl hA rfl hg he hB hC hM (show WilsonStartup.Decent T.low (B.a.budget m) from hv ▸ hy.decent) hΞ
  obtain ⟨z,hz,hZ⟩ := hh.cheap
  obtain ⟨k,hF,hK⟩ := hh.expensive
  exact ⟨hh.smooth,hh.family,hh.transforms,⟨_,hz,fun q=>budget_loosen (hZ q) (mul_le_mul_of_nonneg_left (add_le_add_left h₃ _) (turnFee_pos _).le)⟩, ⟨k,hF,fun q=>budget_loosen (hK q) (backing B R hr hb)⟩⟩
end YM.PhysicalNext.Repeat.Opera
