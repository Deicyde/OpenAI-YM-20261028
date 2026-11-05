import YM.MergeProof.Cachet
import YM.MergeProof.Courier
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Brisk


set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
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
variable {s:Signed}{x':Site (A.B.a.S.side m n)}
local notation "B₀" => H.H.doors
local notation "Vk" => uptick H.H d x
variable (π : (Q x).activities.Moves s ((A.B.a.clock.op m n).ratio.embed x'))
local notation "b₀" => Merge.dart π W H.H.base f'
lemma paintedUp : (B₀).read Vk= Refrain.read H.H.base f' Chi.canonical (B₀).reg (Vk).logRead:=by
  unfold uptick; rw [Embrasure.click H.H _ hx]; rfl
lemma vests : ∃ Y': Progress.DirectedRecipe.Layout D₀ s x', Y'.Follows Tap0 ∧ Y'.hard= b₀ :=by
  let v:= Vk; let Z:= (B₀).read Vk
  have hp : Nonempty (Z.Moves s x') := Beam.moves _ _ Chi.canonical _ s x' _
  obtain ⟨hP⟩:= hp; obtain ⟨e',he⟩: (∃ e' : Z.Moves s x',e'.kp= b₀):= by
     unfold Z; rw [paintedUp]; exact Merge.depart π W Chi.canonical H.H.base f' _ _ (by apply Nonempty.some; rw [← paintedUp]; exact ⟨hP⟩)
  let F:= lens H.H; let D:=Tap0
  let g:= beacons H.H H.knows H.W d x; let t:=lights H.H H.knows H.W d x
  obtain ⟨J'⟩ : Nonempty ((F.pours D).Moves s x'):= Marlin.reeds (B₀) e (2*e) v g t _ _ hP
  obtain ⟨q,hh,hf⟩:= Marlin.gander (B₀) e (2*e) v g t _ _ hP
  rw [← he]
  exact YM.Merge.courier e' J' rfl rfl q hh hf
include hm g
lemma met : ∃ π':(H.result x).activities.Moves s x', ∀ (M:Lotus.Leaf (Q x))(t:ℝ)(i:ℕ) (U),
    pupil H x (M.route π) t (π'.kp i) U= pupil H x M t i (pull s x' U):=by
  obtain ⟨F,hF,hv⟩:=vests H x π
  have hp':=(R.machine.passes hm H.knows).1
  let f₀:=Tap0
  let R':= T'
  have hf:(Mallow.Spring.X' H)=pluck B D₀:=rfl
  have ht:= (H.core hm x hx).fittings g (A.B.support.cap N m hm.le) hp'.decent (Return.enough_room ..) gV (AnalyticBridge.VerifiedReset.Averaging.delta (H.X'.read (H.V' x)))
  -- get from field proofs
  let m₀ := F.motion (Marlin.hak D₀) B hF
  let m':=(ht.moves s x'|>.some)
  obtain ⟨q,h,hB⟩:= ht.carries s x'
  have m₂: ((T₀).pours R').Moves s x':= m'
  obtain ⟨Z,hZ,hM⟩:= Merge.courier m₀ m₂ rfl rfl q h hB
  rw [H.owns g hm hx]; let Y':= Z.inflate
  refine ⟨Progress.DirectedRecipe.Layout.motion Y' (folio G _) (B) (Z.inflates R' hZ),fun M t i U=>?_⟩
  have ha(j:ℕ)(V):shifting H x (M.route π) t (Z.hard j) V=shifting H x M t j (pull s x' V):=by
    rw [hM]; exact Merge.ticket F hF (veranda M W O H.H.base f' t) (veranda (M.route π) W O H.H.base f' t) (by intro i U;rw [hv]; exact Merge.egress M π W O U t H.H.base f' i) (Marlin.hak D₀) j V
  exact Merge.ticket Y' (Z.inflates _ hZ) _ _ (fun i U=> Merge.inflate_ticket Z _ _ ha i U) (folio G _) i U
end YM.PhysicalNext.Repeat.Mallow
