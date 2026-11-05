import YM.FullVolume.Nectar.Laid
import YM.FullVolume.Reel.Split
import YM.FullVolume.Relay.Raw
/-!
 Static roster trick. Bundle an Armada across the WHOLE real arc and the
 corresponding coherent family of inputs. Leaf.weight needn't be uniform
 (it is not used as an analytic assertion); earn with the *ingredient*
 instead. Use redundant fares stored with the bundle so combining multiple
 bundles doesn't have to rechoose anything.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Muse.Veil
set_option quotPrecheck false
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Animals
open MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Height Input Org Supply Pane Slide
open Push.PriceCompiler Progress.DirectedRecipe Jams Apse Empire Time Roof Chord Ovens
open FullVolume.Ray FullVolume.Urns FullVolume.Amp Pass Tent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}
variable {v q d t c t':ℝ}{N n m:ℕ}{L:Lyrics R t t}
open UniformSpace
set_option maxHeartbeats 420000
set_option synthInstance.maxHeartbeats 140000
variable (H:Chord R N m n t t){T:Team (stageP A.B.a (m+1) n)}
local notation "P"=> (stageP A.B.a (m+1) n)
local notation "Q"=> A.B.a.budget (m+1)
local notation "S"=> A.B.a.S.side (m+1) n
local notation "α'"=> A.B.a.S.side m n
open Board MergeProof Marker
variable {V I J:Type}[Fintype I][Fintype V][Fintype J][DecidableEq V]
open Luna Frets Empire Imago
open Luna.Aank Lotus
variable {B: Marker.Census V}
open FullVolume.Nectar Menu Accent
-- Ship: fixed turns; need variance over Board.Motion proof Ω. All have unit charge! split of E+K hats. Pose via p(T).
structure Ship (p:Booker A N m n T)(Z:sun→ Booker A N m n T)(o:V→ Site (A.B.a.S.side (m+1) n))(B:Marker.Census V) (I:Type) where
   arm : ArmadaP A N m n T p o B I
   crew (s:sun): I→Leaf (Z s).val.val.val
   fare : I→ℝ -- for `Feel`.
   shares s i : (crew s i).turn= arm.track i
   earns i : Feel (fun s=> (crew s i).ingredient) (fare i)
   unitC i : ‖arm.charge i‖ = 1
namespace Ship
variable (p:Booker A N m n T)(Z:sun→ Booker A N m n T)(o:V→ Site (A.B.a.S.side (m+1) n))
variable (M: Ship p Z o B I)(U: Ship p Z o B J)
variable (w:V→ℝ)
abbrev stamp := ArmadaP.laid p o M.arm Z M.crew
-- compacts at E_total and per K box, not tracking each Support bubble
abbrev allE (x:sun)(y:Config G (A.B.a.S.side (m+1) n)):=∑ i,Menu.odour (M.stamp p Z o x i) y
abbrev allK (x:sun)(i:Box (A.B.a.S.side (m+1) n))(y:Config G (A.B.a.S.side (m+1) n)):= ∑ j,Menu.fragrance (M.stamp p Z o x j) y i
abbrev oweK (x:sun)(j:V) (i:Box (A.B.a.S.side m n))(y:Config G (A.B.a.S.side m n)):=∑ l,Menu.owl (M.stamp p Z o x l) (Orchard.portal H (Z x).val.val) j i y
/-- Weighted global fare at possibly lowered rate e. -/
abbrev total (e:ℝ):= ∑ i, Real.exp (e*coverNumber (Q).B ((M.arm.track i).support (p.val.val.val))) * Poly.toll w (M.arm.mode i) * M.fare i
/-- At B.fire(j), exact exponent w/o marker toll. -/
abbrev slot (j:V):= ∑ i, if M.arm.mode i=B.fire j then (A.B.a.budget (m+1)).mass ((M.arm.track i).support p.val.val.val) (M.fare i) else 0
variable (hw:∀ i,0<w i) (a:ℝ) (z:V→ℝ)
omit hw
lemma folded (hp: M.total p Z o w ((Q).supportExponent-4) /a + ∑ j:V,(M.slot p Z o j)/(z j) ≤ v): ArmadaP.FoldT p M.arm w a z v M.fare:=by
    unfold ArmadaP.FoldT; simp_rw [M.unitC,mul_one,one_mul,← mul_assoc]; exact hp
include hw
lemma lower_cap {e d:ℝ}(h:e≤d): M.total p Z o w e ≤ M.total p Z o w d:= by
    apply sum_le_sum; intro i _; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _))) (Poly.worth hw _).le) (M.earns i|>.positives)
omit hw
-- bundling disjoint
abbrev ballast : Ship p Z o B (I ⊕ J) :=
     ⟨⟨Sum.elim M.arm.track U.arm.track, Sum.elim M.arm.mode U.arm.mode, Sum.elim M.arm.charge U.arm.charge, fun i=> match i with | .inl i=> M.arm.sizes i| .inr i=> U.arm.sizes i, fun i=> match i with | .inl i=> M.arm.roots i| .inr i=> U.arm.roots i,fun i x=> match i with | .inl i=> M.arm.earns i x| .inr i=> U.arm.earns i x⟩, fun s=> Sum.elim (M.crew s) (U.crew s),Sum.elim M.fare U.fare, fun s i=> match i with | .inl i=> M.shares s i| .inr i=> U.shares s i, fun i=> match i with | .inl i=> M.earns i| .inr i=> U.earns i, fun i=> match i with | .inl i=> M.unitC i| .inr i=> U.unitC i⟩
local notation "XU"=> (M.ballast p Z o U)
variable (k:Finset B.Mode)
lemma paying : (XU).total p Z o w a = M.total p Z o w a+U.total p Z o w a:=by unfold total;rw [Fintype.sum_sum_type];rfl
lemma payingE (j:V): (XU).slot p Z o j=M.slot p Z o j+U.slot p Z o j:=by unfold slot;rw [Fintype.sum_sum_type];rfl
lemma sphereE (s:sun)(y:Config G (A.B.a.S.side (m+1) n)): (XU).allE p Z o s y=M.allE p Z o s y+U.allE p Z o s y:=by unfold allE; rw [Fintype.sum_sum_type];rfl
lemma sphereK (s:sun)(i:Box (A.B.a.S.side (m+1) n))(y:Config G (A.B.a.S.side (m+1) n)): (XU).allK p Z o s i y=M.allK p Z o s i y+U.allK p Z o s i y:=by unfold allK; rw [Fintype.sum_sum_type];rfl
lemma sphereO (s:sun)(j:V)(i:Box (A.B.a.S.side m n))(y:Config G (A.B.a.S.side m n)):(XU).oweK H p Z o s j i y=M.oweK H p Z o s j i y+U.oweK H p Z o s j i y:=by unfold oweK; rw [Fintype.sum_sum_type];rfl
lemma remains (h:∀ i,M.arm.mode i∈k)(ht:∀ i,U.arm.mode i∈k):∀ i,(XU).arm.mode i∈ k:=fun i=> match i with| .inl i=> h i| .inr i=> ht i
end Ship
end YM.PhysicalNext.Repeat.Muse.Veil
#print axioms YM.PhysicalNext.Repeat.Muse.Veil.Ship.sphereO
