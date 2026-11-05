import YM.MergeProof.Motion
import YM.MergeProof.Steps
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Seminal

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow.Many
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} (g:G.Simple) {X:Metals G} {D: Rolls X.p} {A : Alloy X D}
    {R: Factor A} {l v:ℝ} {N m n:ℕ}(hm:m<N) {Q: In A.B.a m n} (H: Spring R N m n l v Q)
local notation "I" => Icc l v
local notation "L" => D.L (A.B.a.clock.J (m+1))
local notation "Θ" => A.B.a.S
local notation "J" => A.B.a.clock.J (m+1)
local notation "Jp" => A.B.a.clock.J m
local notation "K" => A.B.a.params m
local notation "wT" => radiusB (A.B.a.clock.hatBeta m)
local notation "k" => Rain.lint R.target A m
local notation "e" => Trio.base k wT
local notation "gV" => A.B.kin.alpha N m
local notation "B" => A.B.a.budget m
local notation "d" => H.ordinal
local notation "Y" => R.target J Jp
local notation "Ze" => R.expense J Jp
local notation "Cμ" => (R.shape.μ J Jp)
local notation "y" => A.B.a.clock.hatBeta m
local notation "O" => Chi.canonical
local notation "X₀" => H.H.base
variable (x: Icc l v)
local notation "hx" => x.property
local notation "W" => houseS H x
local notation "f'" => H.H.sister x
local notation "Tap0" => graft H.H H.knows H.W d x.val
open YM.Merge
variable {ι:Type}[Fintype ι](M:ι→Lotus.Leaf (Q x))(rA:ι→ℝ)
local notation "V" => Palette.shoot M W Chi.canonical rA H.H.base f'
local notation "D₀" => lens H.H
local notation "T₀" => Collection.shelves H.X' (A.B.kin.path N m) B
set_option quotPrecheck false
local notation "T'" => Collection.branch H.X' (A.B.kin.path N m) (A.B.a.params m|>.clip) B (H.V' x) gV
local notation "M₁" => A.B.kin.path N m
local notation "g₂" => tempe (A:=A) (Z:=R.expense) (C:=R.target) (m:=m)
local notation "p" => (Marlin.tithe (2*e) g₂ B (Trio.coverTicket k))
local notation "P!" => (X.p.profile Jp)
-- base.χ.f tilt. R anchor. fuel from Verge
variable {b v₁ b₁ t q t₁ t₂ A₁ b₂ w : ℝ}{n':ℕ} (T:Captain (houseS H x) (X.p.profile (A.B.a.clock.J m)).order t q v₁ t₁ A₁ b₂ t₂ b₁ b n' Chi.canonical)
variable (hR: Arrives R.shape A.delay) (h:Herd (houseS H x) T.conduit A₁ b₁ n')
    (hp:Bikes (R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (D.L (A.B.a.clock.J (m+1))) (R.shape.μ (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (A.B.a.clock.hatBeta m) (R.expense (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)|>.earn) w b₁ (X.p.profile (A.B.a.clock.J m)|>.order) n')
-- actual exponent/weather includes Beam supports.We leverage T.renewed exactly. term at latch.
local notation "z₀" => (Real.exp (-(Y).mark L Cμ y)*(2*Daisy.pledgeQ L Y Cμ y b₁ (P!).order n'))
variable (h₀:Palette.Plot M (houseS H x) rA)

include hp h₀ T
lemma money2 : Motion.Pays ((D₀).pours Tap0) (raiser (raiser B)) V z₀ ((raiser (raiser B)).supportExponent+1):=by
  let U:= Palette.ready M W Chi.canonical rA h₀ hp T.balance H.H.base f' (raiser (raiser B)) (D₀).reg (Sum.elim (uptick H.H d x|>.logRead) (choir (beacons H.H H.knows H.W d x)) ∘ Marlin.leanU _) rfl
  let B₁:=raiser (raiser (B))
  let uE:= (Sum.elim (uptick H.H d x|>.logRead) (choir (beacons H.H H.knows H.W d x)) ∘ Marlin.leanU _)
  let s:=Refrain.read H.H.base f' O (D₀).reg uE
  refine ⟨fun j=> ?_,fun t r ht=> ?_,?_⟩
  · unfold Palette.shoot; rw [show (Palette.ways rA 0 j)=(fun _=>0) from (by ext; simp [Palette.ways]),Palette.at0 (t':=uE) (E:=(D₀).reg)]; change s.K=(Tap0).forced
    unfold graft uptick; rw [Embrasure.click H.H _ hx]; rfl
  · have h':= Palette.earned M W Chi.canonical H.H.base f' B₁ (D₀).reg uE rfl (Palette.ways rA t r) -- order
    exact ⟨h'.sym,h'.symtest,h'.meas,h'.meas_test,h'.reads,h'.reads_test,h'.permit⟩
  obtain ⟨c,hC,hU⟩:=U
  have hi : ((raiser (raiser B)).supportExponent+1) ≤ (Ze).earn:= by
    change (B).supportExponent+1+1+1 ≤ _; have he':= R.pledging.agenda _ _ (step_paid A.B.a m)|>.1; rw [Rain.jersey (A:=A) (m:=m)|>.2.2.1]; linarith
  change Ac.Hit (fun i=> (((D₀).pours Tap0).forced i).support) _ _ _ _ at hU
  refine ⟨c,hC, fun i=> budget_mono (hU i) ?_ ?_⟩
  · intro i; split; exact mul_nonneg (Switch.Paid.rocket (hC _)) (Real.exp_pos _).le; rfl
  intro i; split
  next h=> exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hi (by positivity))) (Switch.Paid.rocket (hC _))
  rfl

local notation "p3"=> (Marlin.tithe (2*e) g₂ (raiser B) (Trio.coverTicket k))
include hm
omit h₀ hp T [Fintype ι] in
lemma fan2 : (Vapor (D₀) (Tap0) (raiser (raiser B)) (p3)) ∧ 0≤ p3 ∧ p3 ≤ Real.exp (Trio.coverTicket k) * betaF G y L ^ (-(1/8):ℝ):=by
  have ht (i: Site (A.B.a.S.side m n)):= Rain.worthy R.pledging hm H.H H.waves H.knows R.inn (R.settles _ _) H.W d x i
  have hh i:= (ht i).1
  have hk: 0≤ tempe (A:=A) (Z:=R.expense) (C:=R.target) (m:=m):=(norm_nonneg _).trans ((ht 0).2.2 1)
  let Dr:= Tap0; let U:= D₀; let v:= beacons H.H H.knows H.W d x; let a:= uptick H.H d x; let t:=lights H.H H.knows H.W d x
  have hw (i):= estateP H.H.doors e (2*e) a v t hh i
  have hω:= Marlin.failedP H.H.doors e (2*e) a v t (fun i=> (ht i).2.1)
  have hf : Vapor U Dr (raiser (raiser B)) p3:= by
    refine ⟨fun i=> (hw i).uses,fun i U hU=> by by_contra h; exact hω i U h hU,fun i=> (hw i).invariant,fun i=>(hw i).borel, ?_⟩; refine ⟨_, Marlin.caps _ _ _ _ _ hk (fun i=> ?_),Marlin.softly a t _ (fun i=> (ht i).2.2) v⟩ -- args
    unfold Trio.coverTicket; apply Nat.cast_le.mpr; apply le_trans (Trio.scaleMeters k wT (B).B_pos i _ le_rfl); rw [two_mul]
  refine ⟨hf,(by obtain ⟨f,hf,-⟩:= hf.funds; exact budget_nonneg (hf.2 0)),?_⟩
  have hp: p3=Real.exp (Trio.coverTicket k) * p:=by
    unfold Marlin.tithe; rw [show (raiser B).supportExponent+1+1=(B).supportExponent+1+1+1 from rfl,add_mul,one_mul,Real.exp_add]; ring
  rw [hp]; exact mul_le_mul_of_nonneg_left (Mallow.fanning hm H x|>.2.2) (Real.exp_pos _).le
end YM.PhysicalNext.Repeat.Mallow.Many
