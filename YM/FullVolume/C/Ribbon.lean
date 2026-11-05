import YM.FullVolume.C.Dawn
import YM.FullVolume.C.Prime
import YM.FullVolume.C.Light
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Pediment

/-! Real step expression with deterministic dictionary and prices. Publishes ANY number rule satisfying universal retirement by incoming layout. Relevant for Prescription before Bar tuning. Nothing in price uses a history at a finer level (Lives still needed for actual Moves). -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Roof
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Mallow Marlin Trio
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {X:Metals G} {D: Rolls X.p} {A : Alloy X D}
    (R: Factor A) {N m n:ℕ}
local notation "X'" => A.B.a.S
local notation "I" => Rep G (A.B.a.S.side (m+1) n)
local notation "Ω" => A.B.a.clock.hatBeta m
local notation "B" => (A.B.a.budget m)
local notation "e" => Trio.base (Rain.lint R.target A m) (radiusB Ω)
local notation "k" => Rain.lint R.target A m
local notation "γ"=> A.B.kin.alpha N m
-- callback PAID contracts at c,c₁
abbrev Roofing (R: Factor A) (c c₁:ℝ):= Roof.Sheltered (C:=R.prices) («B»:=R.rider) A R.house R.v R.t R.span R.booth R.menu R.recordP R.auxiliary R.shape R.scout c c₁ (1/8) R.exchange R.post R.scoutL
structure Chord (R:Factor A) (N m n:ℕ) (c c₁:ℝ) where
    paid: m<N
    earns:Roofing R c c₁
    tone : Zeal R.target R.shape A N m
    order : Collection.Listing G (A.B.a.S.side (m+1) n)→ ℕ
    city (u) : Retired R.shape A tone n (1/16) (1/16) u (order u)
    credit (u) : Retired R.shape A tone n c c₁ u (order u)
    towards u: N≤ order u
variable {R} {c c₁:ℝ} (W:Chord R N m n c c₁)
namespace Chord
lemma acquires (h:Roofing R c c₁)(ht:m<N): Nonempty (Chord R N m n c c₁):=by
  obtain ⟨W⟩:= Rain.learns (C:=R.target) (A:=A) (R:=R.shape) ht h.conducts.income.grow.1 h.conducts.full
  choose d hu h' hv using fun (v:Listing G (A.B.a.S.side (m+1) n))=> ((Rain.celebrates R.pledging ht R.inn (R.settles _ _) R.floor W v).and ((Rain.celebrates h ht R.inn (R.settles _ _) R.floor W v).and (eventually_ge_atTop N))).exists
  exact ⟨⟨ht,h,W,d,hu,h',hv⟩⟩
abbrev Flight (A : Alloy X D) (N m n) := {U: Rep G (A.B.a.S.side (m+1) n) // Lives (spatial A).bake N (m+1) n U ∧ U.beta∈band A.B.a (m+1)}
variable (Y:Flight A N m n)
local notation "B₀"=> A.B.a.budget (m+1)
def pitch:= W.order (listIn Y.val)
def sight: Guide A.B R.shape N m n Y.val:= (prepares W.earns.conducts W.paid Y.property.1 Y.property.2).choose
lemma capacity: Opera.Price A.B R.shape N m n Y.val (W.sight Y):= (prepares W.earns.conducts W.paid Y.property.1 Y.property.2).choose_spec
local notation "H₀" => W.sight Y
abbrev termF := Match.staple (H:=H₀) (J:=H₀) rfl rfl rfl
abbrev marker := Rain.screens R.target A m
abbrev rates := W.tone.offers (W.pitch Y) ⟨Y.val.beta,Y.property.2⟩
def crewD := Beam.marquee (H₀) B
def lens := Marlin.lodge (W.crewD Y) e (2*e)
def listing := pluck (B) (W.lens Y)
def offerT := Marlin.bison (Meadow.timbres (W.termF Y) (χ:=Chi.canonical) γ (W.pitch Y)) (Trio.ornament (Chord.marker (R:=R) (m:=m)) (W.rates Y)) (Trio.insight B (W.termF Y) γ (W.pitch Y) (Chord.marker (R:=R) (m:=m)) e (W.rates Y))
def source:= poursP (B) (W.lens Y) (W.offerT Y)
def moment:= Return.result A.B N (fun _=> Y.val) (W.listing Y) (fun _=> W.source Y) 0
lemma instant (x:ℝ) : Return.result A.B N (fun _=> Y.val) (W.listing Y) (fun _=> W.source Y) x=W.moment Y:=rfl
set_option maxHeartbeats 600000 in
lemma same_story {m p} {Q: CouplingReset.In A.B.a m p} (N y) (X:Listing G (A.B.a.S.side m p)) (M:ℝ→ Collection.Source G (A.B.a.S.side m p)): Return.result A.B N (fun _=> Q y) X (fun _=> M y) 0 = Return.result A.B N Q X M y := by
  unfold Return.result Template.install Template.trial board Return.ledger VerifiedReset.terms predictor UVNext.CouplingReset.scalar UVNext.CouplingReset.target; rfl
section reprices
variable {Y} {a x:ℝ} {s:Set ℝ} {Q: CouplingReset.In A.B.a m n} (U:Roof.Embrasure (N:=N) (Y:=R.shape) Q s a)
variable (hx:x∈s) (hv:Curve (A.B.a.budget (m+1)) Q s) (he:∀ x∈s,Lives (spatial A).bake N (m+1) n (Q x)∧ (Q x).beta∈band A.B.a (m+1))
set_option quotPrecheck false
local notation "Y'" => (⟨Q x,he x hx⟩ :Flight A N m n)
local notation "n₀" => W.order (listIn (Q a))
private lemma argsss {A Bn C D:Type} (f:A→Bn→C→D){x x':A} {y y':Bn}{z z':C} (he:x=x') (hf:y=y')(hg:z=z'):f x y z=f x' y' z':=by rw [he,hf,hg]
include U hx hv he
lemma agrees_pay : W.pitch (Y')= n₀:= by unfold pitch; congr 1; exact congr_arg₂ _ (hv.reg _ hx _ U.he) (hv.forced _ hx _ U.he)
lemma sight_layout : W.crewD (Y')=U.doors:= Meadow.signage (show (Q x).path=(Q a).path from (he x hx).1.path.trans (he a U.he).1.path.symm) (hv.reg _ hx _ U.he) (hv.forced _ hx _ U.he) _
lemma sight_graph : W.offerT (Y')= Rain.tuneT U he W.tone n₀ x:=by
  have ht:= U.click x hx; let z:=W.sight (Y'); let c:= n₀; let Ξ:=U.sister (U.latch x)
  unfold offerT tuneT rates; dsimp only; simp_rw [agrees_pay W U hx hv he]
  apply argsss Marlin.bison
  · unfold Rain.uptick; rw [ht]
    have hu := ((he a U.he).1.path).trans (he x hx).1.path.symm
    have hp:= Meadow.written (I':=z) Chi.canonical (U.sister ⟨x,hx⟩) (U.agrees ⟨x,hx⟩) hu (hv.reg _ U.he _ hx) (hv.forced _ U.he _ hx) γ n₀
    exact hp.symm
  · unfold Rain.beams; rw [show minute U he x= ⟨(Q x).beta,(he x hx).2⟩ from Subtype.ext (congr_arg (fun i:s=> (Q i).beta) ht)]
  unfold Rain.nights; dsimp only; rw [show minute U he x= ⟨(Q x).beta,(he x hx).2⟩ from Subtype.ext (congr_arg (fun i:s=> (Q i).beta) ht), ht]
  have hu := ((he a U.he).1.path).trans (he x hx).1.path.symm
  exact (Meadow.summits (U.sister ⟨x,hx⟩) (U.agrees _) hu (hv.reg _ U.he _ hx) (hv.forced _ U.he _ hx) (Chord.marker (R:=R) (m:=m)) e _ (I':=z) (B) γ n₀).symm
lemma at_turn : W.listing (Y')=Rain.opening U ∧ W.source (Y')=Rain.charmT U he W.tone n₀ x ∧
    W.moment (Y')= Return.result A.B N Q (Rain.opening U) (Rain.charmT U he W.tone n₀) x:=by
  have hK : W.lens (Y')=Rain.lens U:= by unfold lens Rain.lens; rw [W.sight_layout U hx hv he]
  have hE : W.listing (Y')=Rain.opening U:= by unfold listing opening; rw [hK]
  have hH : W.source (Y')= Rain.charmT U he W.tone n₀ x:= by unfold source charmT; rw [hK,W.sight_graph U hx hv he]
  refine ⟨hE,hH,?_⟩
  unfold moment; simp only [hE,hH]; exact same_story (A:=A) (Q:=Q) N x _ _
end reprices
end Chord
end YM.PhysicalNext.Repeat.Roof
