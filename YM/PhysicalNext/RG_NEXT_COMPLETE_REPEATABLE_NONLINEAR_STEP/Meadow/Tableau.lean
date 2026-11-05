import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Coset
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Fiona
/-! # Full kinetic barony, transported EXACT when flags are not clipped. Pick masks in later nodes.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' j m: ℕ} {K : Teller G} {p a W U V : ℝ} {χ:Chi} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}

section mint
variable {S:StepData c f} {T:Tube G S} {R : RG.Rep G f} (H : Cash W p a L₀ X o U T R)
local notation "B" => radiusB p

def barony (χ:Chi) (k:ℕ) (γ:ℝ) := Meadow.atlas (echoing H χ k + garner T.down T.low R.beta γ B k)
lemma rotates (χ:Chi) (k:ℕ) (γ:ℝ) (x:Site c) (V:Config G c) (s:Signed) (b:Site c): barony H χ k γ (Lattice.affine s b x) V= barony H χ k γ x (pull s b V):=(astrolabe _ x V (s,b)).symm
lemma covers_field (s: Seat c) (V:Config G c) (he: RG.flags a V= ∅): RG.flags a (s.view V)=∅ := by
  have hf := Work.H03.flags_send s.1 s.2 a V; rw [he] at hf; exact Finset.image_eq_empty.mp hf
end mint

section roll
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q: KernelChoices} {hC:C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T : Tube G (stepped Q h)} {T' : Tube G (stepped Q H)} {R:RG.Rep G f} {R':RG.Rep G F}
    {I : Cash W p a L₀ X o U T R} {I' : Cash W p a L₀ X o V T' R'}
    (hC he) (Tq : T'=Deck.re T) (hp:R'.path=R.path) (ha:R'.p= R.p) (hz:R'.beta=R.beta) (x : Site C) (hX:4*roomSize X.halo (radiusB p)<c.val) {b ℓ : ℕ}
    {C' d z T'' A B r V' u s₁ a' b' c' d' e' D Z q' :ℝ}
    (N : Captain I b C' d z T'' A B r V' u m χ) (N' : Captain I' j s₁ a' b' c' d' e' D Z q' ℓ χ)
    (f' : Config G c) (hV: RG.flags (Pressure.temp p) f'= ∅)
local notation "R₀" => radiusB p
local notation "D'" => roomSize X.halo R₀
local notation "x'" => (Macrame.splitter (Deck.divides hC) x)
include hC he Tq hp ha hz hX N N' hV
lemma replay (γ' : ℝ) (k:ℕ) : barony I' χ k γ' x ((L).low.links f')=barony I χ k γ' x' f':= by
  let b (θ:Seat c):=echoing I χ k ((spin θ).symm x') (θ.view f') + garner T.down T.low R.beta γ' R₀ k ((spin θ).symm x') (θ.view f')
  unfold barony atlas; change _=likely b
  rw [← revolving hC b]
  apply congr_arg likely; funext θ
  simp only [b,Pi.add_apply]
  rw [show θ.view ((L).low.links f')=(L).low.links ((pinch hC θ).view f') from estuary hC f' θ]
  apply congr_arg₂ HAdd.hAdd
  · rw [← inverts hC θ]; exact arranges hC he Tq hp ha hz _ hX N N' ((pinch hC θ).view f') (covers_field (pinch hC θ) f' hV) k
  rw [hz,← inverts hC θ]; subst T'; exact garner_pack hC ..
end roll
end YM.PhysicalNext.Repeat.Meadow
