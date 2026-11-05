import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Graces.Eagles
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Graces.Maya
/-!
 # One FULL raw promise issued on regular operand. True supports, PV/Eq. Unit even empties. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Graces
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels Peak Mercury
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c:Side}{B:BudgetPoint}{X:Support c}{f:Config G c→ℂ} {o:Site c}
lemma readings (A: ℂ→L[ℝ] ℝ)(h:B.Regular X f):B.Regular X (A∘f):=by
  have hg V (hp:Healthy B.threshold X V) : Push.Local.Chart B.order (A∘f) V:= A.contDiff.contDiffAt.comp _ (h.smooth V hp)
  exact ⟨fun _ _ hp=> congr_arg A (h.sites _ _ hp), A.continuous.measurable.comp h.borel,fun _ _=> congr_arg A (h.symmetry _ _),hg,fun U hx v l h' => left_has v h' (hg U hx)⟩
lemma pricesL (A:ℂ→L[ℝ] ℝ)(h:B.Regular X f)(hp:∀ t, ‖A t‖ ≤ ‖t‖) (t:ℝ)(ht:B.supBounds o X f t) : B.supBounds o X (A∘f) t:=by
   refine ⟨ht.1,fun U hU l hv hh=>?_⟩; rw [Push.Local.left_linear A l (show Push.Local.Chart B.order f U from h.smooth U hU) hv]; exact (hp _).trans (ht.2 _ hU _ hv hh)
variable (g:G.Simple) {M : Metals G} {D:Rolls M.p} {A:Alloy M D}
    {R: Factor A} {l v:ℝ} {N m n k d:ℕ} (hm:m<N) {Z:Bolt A} (h:Nest R Z) {Q: In A.B.a m n}
local notation "H" => Issue.trail Z
local notation "i₀" => A.B.a.clock.J m
local notation "j₀" => A.B.a.clock.J (m+1)
local notation "B" => A.B.a.budget m
local notation "ΔB" => A.B.a.budget (m+1)
local notation "L₀" => D.L j₀
local notation "f₀"=> A.B.a.clock.hatBeta m
local notation "P" => M.p.profile i₀
local notation "pT" => R.prices j₀ i₀
local notation "S0" => ships A.B N m n
local notation "N'" => A.B.a.clock.op m n
local notation "O" => Chi.canonical
local notation "V" => A.B.a.S.side m n
set_option quotPrecheck false
local notation "U!" => ((H).rep N n (m+1))
local notation "O'" => ((H).rep N n m)
local notation "ip"=> A.B.a.params m
variable (hC:Mallow.Arrives R.shape A.delay) (hM : Moms R.prices M.K R.span M.p.floorL)(hV: Cruise R.prices D R.recordP R.span R.shape A.delay) (hd:d+3 ≤ A.B.a.clock.J m) {K:ℕ → ℝ}{W:Bid.Worth}(hp : Doors.Budget A.B.a K W)(hh : Comply R.shape A.delay)
include hp hd
lemma feet : goodD M.p j₀ i₀ d:= by
  refine ⟨step_paid A.B.a m,?_,?_,?_⟩
  · have he:= (hp.stage m).1; rw [params_eq A.B.valid] at he; omega
  · have ht:= (hp.stage (m+1)).2; rw [params_eq A.B.valid] at ht; have hi:= step_paid A.B.a m|>.1; omega
  have ht:= step_paid A.B.a m|>.1; omega
include g hC hM hV hh h hm

end YM.PhysicalNext.Repeat.Graces
