import YM.FullVolume.Florid.Drape
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Jams
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Empire
open FullVolume.Ray
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open ConnectedActivityE6.Empire.Imago Crew Mallow Extra.Iteration Ovens Ovens.Pipes Progress.DirectedRecipe Rack FullVolume.Ray.Weigh
open Testing Push.PriceCompiler Org Marlin Time Next.Scheduling.Clock Next.Scheduling.Instrument
variable {G: Gauge} {X: Metals G} {D: Rolls X.p} {A:Alloy X D} {R:Roost.Factor A} {c f :Side} {N n m d:ℕ} {t v t₂ q:ℝ}
open Alabaster Rain Roof Chord Empire Boulevard Mallow
local notation "O"=> Chi.canonical
local notation "Ω"=>A.B.a.clock.hatBeta m
local notation "K"=>(A.B.a.clock.J (m+1))
local notation "J"=>(A.B.a.clock.J m)
local notation "Q"=>(R.target K J)
local notation "L"=> (D.L K)
local notation "B"=>(A.B.a.budget m)
local notation "Z"=>X.p.profile J
local notation "φ"=>fire G L Ω
local notation "ε"=>thaw G L Ω
local notation "r"=>Rain.lint R.target A m
local notation "γ"=>A.B.kin.alpha N m
local notation "δ"=>wind G L Z Ω
local notation "S"=>A.B.a.S
variable (H:Chord R N m n t t)(h:Degree R.shape R.scout A.delay)
variable {F:sun→ Chord.Flight A N m n} {Y:Mist A.B.a m (fire G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m)) (thaw G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m))}(hV:SectorOn (A:=A) F Y)
variable (hQ: Savvy R.scout R.target A.delay q v t₂ t) (he:PaysW R.shape v A.delay) {U:Type}[Fintype U]
local notation "V₀" => pass_zero (F:=F) (Y.base:ℝ) Y.base.property
local notation "Q'"=> Jams.guitar H hV
local notation "p"=> Chord.pitch H V₀
local notation "e"=> Trio.base r (radiusB Ω)
local notation "Pz"=> (Rain.screens R.target A m)
local notation "W"=> H.tone
set_option quotPrecheck false
local notation "Dp"=> fun x:sun=> (W).offers p (Y.peak x.val)
open ConnectedActivityE6.Empire.Imago Crew Mill Merge.Palette
local notation "U₀"=> H.sight V₀
local notation "X'"=> Marlin.lodge (H.crewD V₀) e (2*e)
local notation "f'"=> Jams.donation Pz Dp B Q' γ p e
local notation "hq!" => (R.shape.o K J)
local notation "μ"=> R.shape.μ K J
open Refrain Lotus YM.Merge Mallow.Many Daisy.Charity
local notation "E₀"=> Marlin.pluck B X'
local notation "p₁"=> A.B.kin.path N m
local notation "Rx" => shelves (E₀) (p₁) B
local notation "S₀"=> A.B.a.S.side m n
local notation "T'"=>fun t:sun=> Collection.branch (E₀) (p₁) (Z).clip B (H.source (F t)) γ
variable {M:Mill (Jams.guitar H hV)}
-- Raw along Chord BUS. V prior layout identical for all including pole.Family.ALL
local notation "hs"=> U₀
local notation "ν"=> (Q').notes
local notation "l₁"=> Refrain.Leaf
local notation "C₀"=> M
variable (g:G.Simple)
variable (hA:Arrives R.shape A.delay)
open Daisy Merge Palette Match Lotus Ovens Ovens.Pipes Progress.DirectedRecipe Rack FullVolume.Ray.Weigh
open Cryst
section facts
open Match
open scoped Classical
lemma entrant {c f lb:Side}{w:ℝ}{Sx:StepData c f} {P:Teller G} {T:Tube G Sx}{R R':Rep G f}{Qj:Target G P}{o:Target.Order G v}
    {H:Cash v q t lb Qj o w T R} {I:Cash v q t lb Qj o w T R'} -- L must arbitrary
   (A : Alliance H I 1 0)(he:A.units=Equiv.refl _)(hx:R.path=R'.path)(hr:R.activities.reg=R'.activities.reg)(hf:R.activities.forced=R'.activities.forced) (i:H.fragrances):Blush.enter I (A.furrow i)=Blush.enter H i:=by
   obtain ⟨u,c,⟨s,v,e1,k1⟩,px,bx,t⟩:=R; obtain ⟨u',c',⟨s',v',e2,k2⟩,p',b',T₁⟩:=R'
   cases hx;cases hr;cases hf; obtain ⟨_,_,_⟩:=A;cases he; cases i; rfl
end facts
variable (M:Mill (Jams.guitar H hV)) (y:Site (A.B.a.S.side m n))
local notation "Zp"=>fun t:sun=> Jams.gate F Y t
local notation "N₀"=> (Q')
set_option quotPrecheck false
abbrev billK (i : ℕ):= Function.extend (Blush.enter (U₀)) (Charity.locus M.pole U₀ y) (fun _=> {y}) i
variable (t₀:sun)
local notation "H0"=> fun t:sun=> H.sight (Jams.gate F Y t.val)
local notation "T0"=>fun t:sun=> Jams.gate F Y t.val
local notation "E0"=> (Q')
set_option maxHeartbeats 380000 in
lemma strains (i:ℕ) : regions H (T0 t₀) (M.flies t₀) y i=billK H hV M y i ∧ Cryst.clocks H (T0 t₀) (M.flies t₀) i=stuff (Blush.enter (U₀)) (Mill.signalAt M Chi.canonical t₀) i :=by
    let Dy:= (Q').seats t₀ ((Q').lay t₀.property); let Xw:= (Q').beams _ ((Q').lay t₀.property); let Kk:=recital Q' t₀
    have hp(s):= entrant (H:=U₀) (I:=Xw) Kk rfl Dy.path Dy.reg Dy.forced s
    by_cases he:i∈Set.range (Blush.enter U₀);swap
    · have hk:i∉Set.range (Blush.enter (H0 t₀)):=by
         rintro ⟨j,hx⟩;obtain ⟨k,hk⟩:=Equiv.surjective Kk.furrow (show Xw.fragrances from j); exact he ⟨k,(hp k).symm.trans ((congr_arg (Blush.enter Xw) hk).trans hx)⟩
      unfold regions billK Cryst.clocks; rw [Function.extend_apply' _ _ _ hk, Function.extend_apply' _ _ _ he,Progress.DirectedRecipe.blank _ _ hk,Progress.DirectedRecipe.blank _ _ he];exact ⟨rfl,rfl⟩
    obtain ⟨p0,rfl⟩:=he
    unfold regions billK Cryst.clocks
    rw [(Blush.enter _).injective.extend_apply]; -- might applies RHS First
    rw [stuffed (Blush.enter (U₀)) (Mill.signalAt M Chi.canonical t₀) p0,← hp p0]
    change _= _∧ stuff (Blush.enter Xw) (fun i=>matin (M.flies t₀) Xw i O) (Blush.enter Xw _) = _; rw [stuffed]
    refine ⟨?_,rfl⟩; exact ((Blush.enter Xw).injective.extend_apply ..).trans (Mill.poleL M t₀ p0 y)
local notation "Ey"=>fun t:sun=> Cryst.clocks H (T0 t) (M.flies t)
 
structure Bills {G:Gauge}{c:Side} (P: BudgetPoint) (o:Site c) (X:ℕ→Support c)(E:sun→ℕ→ Config G c→ ℝ) (v a:ℝ): Prop where
   purchases : ∃ b:ℕ→ℝ, SumBudget (fun i=> Push.Local.reservedMass P (X i) (b i)) a ∧ ∀ i:ℕ,∀ (w:Rung) (η:ℝ),Stripe w v η → P.supBounds o (X i) (mix w E i) (η*b i)
include h he
lemma wealth (hy:y∈ M.pole.crest.image (A.B.a.clock.op m n).ratio.parent): Bills B y (billK H hV M y) Ey (φ/2) (jewelDebt M.pole (Empire.stella (R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m))) (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m)*pottery G L Ω):=by
   obtain ⟨f,hf,hX⟩:= (weather (U:=Unit) H h hV he).1.phases M y hy
   let G' t:= signalAt M Chi.canonical t;let D₀:= Blush.enter (U₀);have hp(t:sun)(i:ℕ): (Ey t) i= stuff D₀ (G' t) i:= (strains H hV _ y t i).2
   refine ⟨stuff D₀ f,?_,fun i w bi hp' => ?_⟩; swap
   · rw [mix_eval]; by_cases hi:i∈ Set.range D₀; swap; · simp_rw [hp,Progress.DirectedRecipe.blank _ _ hi]; rw [mix_z]; rw [mul_zero]; exact AnalyticBridge.VerifiedReset.sup_le («p»:=B) (AnalyticBridge.VerifiedReset.sup_const _) (le_of_eq abs_zero)
     obtain ⟨k,rfl⟩:=hi; simp_rw [hp,stuffed];unfold billK;rw [D₀.injective.extend_apply]; rw [show mix w (fun t=>G' t k)= (fun x=>mix w (fun t=>G' t k x)) from funext fun x=>mix_eval ..];exact hX k w _ hp'
   refine transfer_budget D₀ ?_ ?_ hf
   · intro j;unfold billK Push.Local.reservedMass;rw [D₀.injective.extend_apply,stuffed];exact mul_comm ..
   intro j hj; unfold Push.Local.reservedMass;rw [Progress.DirectedRecipe.blank _ _ hj];simp

end YM.PhysicalNext.Repeat.Jams
