import YM.FullVolume.Luna.Berries
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Luna
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
open Jams Alabaster Rain Roof Chord Empire Boulevard Mallow
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
local notation "V'"=> (V₀)
-- exact real-input sectors `guitar`. Does NOT identify with physically-selected data until strokes after.
open Labels MergeProof MergeProof.Matric Planned.GuardedAtom
local notation "T0" => fun t:sun=> Jams.gate F Y t.val
local notation "H0" => fun t:sun=> H.sight (Jams.gate F Y t.val)
variable (P:Mill (Jams.guitar H hV))(y₀:Site (A.B.a.S.side m n)) (hy:y₀∈ P.pole.crest.image (A.B.a.clock.op m n).ratio.parent)
local notation "B₀"=> (A.B.a.budget m)
local notation "B₁"=> (A.B.a.budget (m+1))
abbrev Nbudget := jewelDebt P.pole (Empire.stella (R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m))) (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m)
abbrev Watch := billK H hV P y₀
local notation "b'"=>Watch H hV P y₀
local notation "l"=> Nbudget H hV P
-- spring-clock roots support inherited, so K can be booked ALL addresses instead of local Ac.Hit
local notation "fY"=> fun i:sun=> P.flies i
lemma station (x:sun) (i:ℕ): Cryst.regions H (T0 x) (fY x) y₀ i=b' i:= (Jams.strains H hV P y₀ x i).1
include h he hA hy
lemma priceW (z:ℂ):
    let ft:= fun (t:sun) => Cryst.clocks H (T0 t) (P.flies t)
    Wires B y₀ b' (fun t i=> z • (Complex.ofReal ∘ (ft t i))) (φ/2) ((B₀).supportExponent+2) (‖z‖*(l*pottery G L Ω)) ∧ ∀ t i,(B).Regular (b' i) (z • (Complex.ofReal ∘ (ft t i))):=by
    intro f₂; obtain ⟨c,hC,hP⟩:= (Jams.wealth H h hV he P y₀ hy).purchases
    let q:=‖z‖; let y:= A.B.a.clock.hatBeta m; have hp(k):0≤c k:=nonneg_of_mul_nonneg_right (hC.1 k) (Real.exp_pos _)
    have hv(t:sun)(i): (B).Regular (b' i) (f₂ t i):=by
        let Vt:=H.sight (T0 t)
        let b:=Blush.enter Vt; let M:= fY t
        obtain ⟨p',t₃,qz,d',y₁,gP,v₀,Y',g',«e»,uC,hX,hY,N'',hη⟩:= hA _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)|>.1.2 _ _ _ _ (Opera.protocol A.B H.paid H.earns.conducts.full) _ _ Vt
        have hz: (f₂ t)=stuff b (fun i=>Daisy.Charity.matin M Vt i O):= rfl
        rw [hz]; by_cases hi:i∈Set.range b
        · obtain ⟨i,rfl⟩:=hi; rw [stuffed]
          rw [← station H hV P _ t,Cryst.regions,b.injective.extend_apply]
          exact scops M Vt N'' hη B ( (Mill.crests (U:=Q') P t).symm ▸ hy) rfl (Rain.jersey (A:=A) (m:=m)|>.1.le) i
        rw [Progress.DirectedRecipe.blank _ _ hi]; exact VerifiedReset.reg_const _
    refine ⟨⟨q • c,br_scale hC (norm_nonneg z),fun i=>mul_nonneg (norm_nonneg z) (hp i),?_⟩,fun x i=>Next.Foundations.regular_smul z (Blush.ornate (hv x i))⟩
    intro i w η hh
    have hP:(B).supBounds y₀ (b' i) (mix w (fun t=>f₂ t i)) (η*c i):=(mix_eval (f₂) i) ▸ (show (B).supBounds _ _ (mix w f₂ i) _ from hP i _ η hh)
    have h(φx): mix w (fun t=> z • (Complex.ofReal ∘ f₂ t i)) φx= z * Complex.ofReal (mix w (fun t=> f₂ t i) φx):= by
       rw [mix_eval]; unfold mix; rw [Finset.sum_apply]; push_cast;rw [mul_sum];apply sum_congr rfl; intro j _; simp only [smul_eq_mul,Pi.smul_apply,Complex.ofReal_mul,Complex.real_smul, Function.comp_apply]; ring
    rw [show mix w _= z • (Complex.ofReal ∘ mix w (fun t=>f₂ t i)) from funext h,show η*((q • c) i)= q*(η*c i) from (by simp only [Pi.smul_apply,smul_eq_mul];ring)]; exact Next.Foundations.bound_smul _ (Blush.pricingG (reg_mix _ (fun t=> hv t i)) hP)
end YM.PhysicalNext.Repeat.Luna
