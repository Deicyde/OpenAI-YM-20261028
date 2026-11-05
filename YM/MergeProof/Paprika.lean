import YM.MergeProof.Pep
import YM.MergeProof.Signed
import YM.MergeProof.Tray
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
variable (hR: Pungent R.shape A.delay) (h:Herd (houseS H x) T.conduit A₁ b₁ n')
    (hp:Bikes (R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (D.L (A.B.a.clock.J (m+1))) (R.shape.μ (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (A.B.a.clock.hatBeta m) (R.expense (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)|>.earn) w b₁ (X.p.profile (A.B.a.clock.J m)|>.order) n')
-- actual exponent/weather includes Beam supports.We leverage T.renewed exactly. term at latch.
local notation "z₀" => (Real.exp (-(Y).mark L Cμ y)*(2*Daisy.pledgeQ L Y Cμ y b₁ (P!).order n'))
variable (h₀:Palette.Plot M (houseS H x) rA)

include hp h₀ T
local notation "p3"=> (Marlin.tithe (2*e) g₂ (raiser B) (Trio.coverTicket k))
include hR hm
lemma corps2 : Motion.Pays ((T₀).pours T') (raiser B) (shiftK H x M rA) (stems Cμ L G y) ((raiser B).supportExponent+1):=by
  have hi:=hR _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)|>.1
  obtain ⟨hz,hb,hV⟩:= fan2 hm H x
  have hf:= money2 H x M rA T hp h₀
  have hp' : z₀ ≤ Real.exp (-(Y).mark L Cμ y):= mul_le_of_le_one_right (Real.exp_pos _).le (by linarith only [hp.gains])
  have hb' : 0 ≤ z₀:=by obtain ⟨u,hu,hB⟩:=hf.bought; exact budget_nonneg (hB 0)
  obtain ⟨u,hξ⟩:= hi z₀ p3 hb' hb hV hp'
  obtain ⟨he,hh,hp''⟩:=Motion.harvest hf hz hξ (Marlin.hak D₀)
  exact ⟨he,fun t j ht=> let hA:=hh t j ht; ⟨hA.sym,hA.symtest,hA.meas,hA.meas_test,hA.reads,hA.reads_test,hA.permit⟩,hp''⟩
include g
local notation "f₂" => Spicy.opens G B (K).clip (K).width (K).paths gV (Time.forecastE A.B.a m)
lemma crowd2 : Motion.Pays (H.result x).activities (raiser B) (pupilK H x M rA) (straw Cμ L G y) (raiser B).supportExponent := by
  have hf : (K)=P!:=params_eq A.B.valid m
  have he:=hR _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)|>.2
  have hh := UVNext.CouplingReset.within_alpha («B»:=A.B) hm
  have hz : Time.Same (K) (B):= ⟨rfl,rfl,rfl⟩
  set f0:=f₂ with hM
  have hv:=H.core hm _ hx; have hu:=(R.machine.passes hm H.knows).1
  have hZ : Vapor T₀ T' (raiser B) f₂:=Spicy.june g (Return.enough_room ..) hv (A.B.support.cap N m hm.le) hu.width hu.decent
  have hS:= he (B) rfl rfl (hf ▸ hz) _ hh
  have hp' : 0 ≤ f0:= by obtain ⟨f,hp,-⟩:= hZ.funds; exact budget_nonneg (hp.2 0)
  have hv:f0= Spicy.opens G B (P!).clip (P!).width (P!).paths gV (Time.credit G P! * δE y):=by rw [hM, ← hf]; rfl
  obtain ⟨u,hU⟩:= hS (hv ▸ hp')
  change Payments.Rates _ _ _ (Spicy.opens G B _ _ _ gV _) _ at hU; rw [← hv] at hU
  rw [Spring.owns g hm H hx]; exact Motion.harvest (Motion.widening (corps2 hm H x M rA T hR hp h₀)) (shown hZ) hU (folio G _)
end YM.PhysicalNext.Repeat.Mallow.Many
