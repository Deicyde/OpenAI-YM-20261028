import YM.FullVolume.Mark.Mint
import YM.MergeProof.Thimble
import YM.MergeProof.Cloudlet
import YM.MergeProof.Coffer
import YM.MergeProof.Visit


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
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}(g:G.Simple) {X : Metals G} {D:Rolls X.p} {A:Alloy X D}
    {R: Factor A} {l v:ℝ} {N m n d:ℕ} (hm:m<N)  {meshT :ℕ→∀ p, Trail A.B.a p} (choice : (A.B.bake.make meshT).Selected) {Q: In A.B.a m n}
local notation "H" => A.B.bake.make meshT
set_option quotPrecheck false
local notation "O" => (H).rep N n m
local notation "S" => (H).rep N n (m+1)
local notation "i₀" => A.B.a.clock.J m
local notation "j₀" => A.B.a.clock.J (m+1)
local notation "B" => A.B.a.budget m
local notation "ΔB" => A.B.a.budget (m+1)
local notation "Q'" => R.target j₀ i₀
local notation "P" => X.p.profile i₀
local notation "o" => (0:Site (A.B.a.S.side m n))
local notation "L₀" => D.L j₀
local notation "f₀"=>A.B.a.clock.hatBeta m
local notation "δ" => A.B.a.clock.forcedAllowance m
local notation "ξ" => (R.shape.μ j₀ i₀)
local notation "T₀" => YM.Labels.frames G
local notation "F" => ((YM.Labels.frames G).level d)
local notation "S'" => A.B.a.clock.op m n
variable (hC:Mallow.Arrives R.shape A.delay)(U: Spring R N m n l v Q)(x:Icc l v)
    (he: (A.B.bake.make meshT).rep N n m = U.result x.val) (ht: (A.B.bake.make meshT).rep N n (m+1) = Q x.val) -- careful Hull.L
variable {a:ℝ}{K: ℕ→ℝ} {W:Bid.Worth} (hp : Doors.Budget A.B.a K W)(hh : Comply R.shape A.delay)
    (hd : d ≤ A.B.a.clock.J m) (T:Cloud (Q x)) (hω: (0:Site (A.B.a.S.side m n))∈T.live.crest.image (A.B.a.clock.op m n).ratio.parent)
local notation "T!" => houseS U x
local notation "V₁" => pupil U x T.live
local notation "V₂" => pupil U x T.pale
set_option quotPrecheck false
local notation "v'" => ((D.L (A.B.a.clock.J (m+1))).val:ℂ)^d
local notation "X!" => Blush.scope (T!) T o
local notation "M" => Blush.screen (T!) T V₁ V₂ v' F
local notation "w" => authors A.B.a m
local notation "κ" => Real.sqrt δ
local notation "fi" => coinFee G P d L₀ -- ambig
local notation "vh" => vigors G P d
include hd hp
open MergeProof
local notation "sandbox" => sandboxK U x
omit hd hp
abbrev eventK (seatK:Guard.Keeper ((A.B.bake.make meshT).rep N n m).p ((A.B.bake.make meshT).rep N n m).activities) := Guard.mint (seatK.supply (fun i=>Push.Local.joint (localSection G d) o (X! i))) M (hol G)
include hd hp hm hC g choice ht he
lemma thunderJ (S₀:Guard.Keeper ((A.B.bake.make meshT).rep N n m).p ((A.B.bake.make meshT).rep N n m).activities) (Pa:Wing→Prop) (heM:Pa T.live.turn) (ho':(0:Site (A.B.a.S.side (m+1) n))∈T.live.crest)
   (f:Config G (A.B.a.S.side (m+1) n)→ℂ)(F':Config G (A.B.a.S.side (m+1) n)→ℂ)(ρ : Res G (A.B.a.S.side (m+1) n))(t r:ℝ)(v₁:(F).Coeff)
   (hz:F'= prose T.live + Complex.I • prose T.pale)(hr:ρ= entry T.live+Complex.I • entry T.pale)
   (hY: MergeProof.Fancy (localSection G d) (A.B.bake.make meshT) N n m (hol G) f (X!) M v₁ w t r):
   MergeProof.Matric.Span (localSection G d) (A.B.bake.make meshT) N n m (hol G) (eventK U x T (d:=d) S₀) F' ρ 0 (duet _ _ _ _ he ht sandbox) Pa f v₁ t r (2*load T.live):=by
   have hx: (H).Conv N n m:=(choice.represents N n m hm.le)
   have hR : Local.Readable (hol G) (localSection G d) (O).p (A.B.a.S.side m n) w:= (hx.vac.symm ▸ (livelyCard hp hd (n:=n) ): Local.Readable _ _ _ (A.B.a.S.side m n) _)
   let q:= eventK U x T (d:=d) S₀
   obtain ⟨hq,hU,hF⟩:= MergeProof.growing (S₀.supply _) hY hx hR
   have hpq:= hF; change profile (A.B.bake.make meshT|>.rep N n m).activities q.forced=profile (A.B.bake.make meshT|>.rep N n m).activities (M).forced + _ at hpq
   rw [he] at hpq hU -- q depends on h
   refine ⟨hq,?_⟩
   rw [show (A.B.bake.make meshT).S.block m=L₀ from PriceCompiler.block_eq A.B.valid _]
   exact peels (A.B.bake.make meshT) N n m he ht (sandboxK U x) Pa F' ρ q.forced _ _ _ _ _ _ (cloudDrop g hm hC U x hp hd T T.rates Pa heM F' ρ _ ho' hz hr _ hpq hU)
end YM.PhysicalNext.Repeat.Graces
