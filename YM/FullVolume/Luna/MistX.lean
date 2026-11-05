import YM.FullVolume.Luna.Mazes
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
local notation "b'"=>Watch H hV P y₀
local notation "l"=> Nbudget H hV P
-- spring-clock roots support inherited, so K can be booked ALL addresses instead of local Ac.Hit
local notation "fY"=> fun i:sun=> P.flies i
include h he hA hy
local notation "R0"=> fun t:sun=> H.moment (T0 t)
local notation "fG"=> fun t:sun=> Mallow.nectar (Jams.Cryst.tree H (T0 t) (P.flies t))
local notation "Vh"=> straw μ L G Ω
include g hQ
lemma gusts (z:ℂ) : RollsUp B (Local.patch ((R0 tip).activities)) (fun i=> z • nectar (Cryst.tree H (Jams.gate F Y i) (P.flies i))) (q/2) ((B₀).supportExponent) (‖z‖*(l*Vh)) :=by
   obtain ⟨f,hf,hX⟩:= Jams.muses H h hV hQ he g hA P
   let x:= R0 tip; let Z₀(i):= if y₀∈ Local.patch x.activities i then f i else 0
   let t:=(B₀).supportExponent; have ht : 1 ≤ q/2:= (by linarith [hQ.sphere.2.1]);have h0:0≤f:=fun i=> (hX i 1).nonneg
   have hP :Brill B (Local.patch x.activities) Z₀ ((B₀).supportExponent) (l*Vh):= by
      have he : SumBudget (fun i=> if y₀∈Local.patch x.activities i then f i * Real.exp (t*coverNumber (B₀).B (Local.patch x.activities i)) else 0) (l*Vh):= hf y₀; convert he using 2 with i; unfold Z₀; split
      next hb=> exact mul_comm ..
      next hb=> rw [mul_zero]
   let k i:= ‖z‖*Z₀ i
   refine ⟨k,br_scale hP (norm_nonneg z),fun i u=>?_⟩; by_cases hv:y₀∈ Local.patch x.activities i;swap
   · have hz2 : (k i)=0:=by unfold k Z₀; rw [if_neg hv,mul_zero]
     have hp(t:sun): nectar (Cryst.tree H (T0 t) (P.flies t)) i=0:=by
        let v:= H.sight (T0 t)
        obtain ⟨p',t₃,qz,d',y₁,gP,v₀,Y',g',«e»,uC,hB,hY,N'',hη⟩:= hA _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)|>.1.2 _ _ _ _ (Opera.protocol A.B H.paid H.earns.conducts.full) _ _ v
        let F₀:=Glitz.footprints g H.paid H (T0 t) (P.flies t) y₀ ((P.crests t).symm ▸ hy) N'' hA hη hB
        exact not_not.mp (fun ht=>hv ((show y₀∈Local.patch (R0 t|>.activities) i from (real_force F₀).carried _ ht)))
     rw [hz2]; refine ((Scout.still ht (0:ℂ)).enlarged (norm_zero.le)).replace ?_; intro s hsF; change (0:ℂ)= z* nectar (Cryst.tree H (T0 (pinch s)) (P.flies (pinch s))) i u; rw [hp]; exact (mul_zero z).symm
   unfold k Z₀; rw [if_pos hv]
   have hh:= mult (Scout.still ht z) (goes_complex (hX i u)); refine hh.replace ?_
   intro s hq₃; let w:=pinch s; have h: (fun a=>stamen H hV w (P.flies w) a i u)=fun a=>Cryst.tree H (T0 w) (P.flies w) a i u:= reaches H hV w i P y₀ u  -- needs y
   change z*Complex.ofReal (deriv (fun a=>stamen H hV w (P.flies w) a i u) 0)=z*_ -- infer rank
   rw [h];rfl
end YM.PhysicalNext.Repeat.Luna
