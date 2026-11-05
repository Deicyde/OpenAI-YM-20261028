import YM.UVExtension.Rainfall.Lovely
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
open YM.UVExtension Eyelet UVExtension.Rainfall Lacing Lacing.RoutesF Guard MergeProof
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}(g:G.Simple) {X : Metals G} {D:Rolls X.p} {A:Alloy X D}
    {R: Factor A} {l v:ℝ} {N m n d:ℕ} (hm:m<N) {Z:Vintage.YM.Org.Bolt A} (h:Vintage.YM.PhysicalNext.Repeat.Graces.Nest R Z) {Q: In A.B.a m n}
local notation "H" => Vintage.YM.Extra.Histories.Issue.trail Z
set_option quotPrecheck false
local notation "O" => (H).rep N n m
local notation "S" => (H).rep N n (m+1)
local notation "i₀" => A.B.a.clock.J m
local notation "j₀" => A.B.a.clock.J (m+1)
local notation "B" => A.B.a.budget m
local notation "ΔB" => A.B.a.budget (m+1)
local notation "P" => X.p.profile i₀
local notation "o" => (0:Site (A.B.a.S.side m n))
local notation "L₀" => D.L j₀
local notation "δ" => A.B.a.clock.forcedAllowance m
local notation "Δ" => Real.sqrt (A.B.a.clock.forcedAllowance (m+1))
local notation "F" => ((YM.Labels.frames G).level d)
local notation "S'" => A.B.a.clock.op m n
variable (hC:Mallow.Arrives R.shape A.delay)(U: Spring R N m n l v Q)(x:Icc l v)
    (he: (Vintage.YM.Extra.Histories.Issue.trail Z).rep N n m = U.result x.val) (ht: (Vintage.YM.Extra.Histories.Issue.trail Z).rep N n (m+1) = Q x.val) -- careful Hull.L
variable {a:ℝ}{K: ℕ→ℝ} {W:Bid.Worth} (hp : Doors.Budget A.B.a K W)(hh : Comply R.shape A.delay)
local notation "T!" => houseS U x
local notation "Rt"=> Q x
local notation "Rc"=> U.result x
local notation "D0"=> sandboxK U x
set_option quotPrecheck false
local notation "v'" => ((D.L (A.B.a.clock.J (m+1))).val:ℂ)^d
local notation "w" => authors A.B.a m
local notation "κ" => Real.sqrt δ
local notation "n₁" => A.B.a.S.side (m+1) n
local notation "n'" => A.B.a.S.side m n
local notation "tu"=> localSection G d
variable (T:Keeper (U.result x|>.p) (U.result x|>.activities))(s:Set Wing)
local notation "r"=> Doors.rate L₀
variable (hd:d+3 ≤ A.B.a.clock.J m)(hΘ:HasSlots (Q x|>.p) (Q x|>.activities))
section
variable (i:StockTag (A.B.a.S.side (m+1) n))
local notation "RtG"=> Eyelet.Bolt (G:=G) (Rt).p i
set_option quotPrecheck false
local notation "c0"=> sink (G:=G) (Rt).p i
local notation "Π"=> Eyelet.fee (Rt).p i.val.1 / Δ
local notation "L0"=> twig (c0)
local notation "N0"=> Eyelet.Stream G (Rt).p i
local notation "J'"=> Eyelet.Bucket (F) (Rc).p (hol G) n'
local notation "N1"=> cart (R:=Rt) (Keeper.sufficient hΘ) i
variable (j:Eyelet.Bolt (G:=G) (Q x|>.p) i)(c:ℝ)(hc:∀ U,‖j.val U‖ ≤ c)
lemma fitsB :SlotFit (Q x) 0 (N1) j.val:=((tailor _ _ _).mp j.property).1

def vaneT := Blush.fan (Q x) 0 (N1) j.val c hc (fitsB x hΘ i j)
lemma hillsK : UVExtension.Rainfall.bulk (vaneT x hΘ i j c hc)=j.val:=by
   funext V; change (↑(j.val V).re:ℂ)+Complex.I*↑(j.val V).im=_; rw [mul_comm Complex.I, Complex.re_add_im]
local notation "u0"=>(Rt).p.mass i.val.1 c
include hm hC g h ht he hp hh hd
lemma pillow (hx:0 ∈ i.val.1)(ha:Wing.gasKey N1∈ s): sparkT U x (vaneT x hΘ i j c hc) d ∧ Flees tu H N n m (hol G) (Rt) (Rc) D0 s 0 (exactGas (Rt).activities N1 j.val) 0 (Extra.Histories.fare (Rt) N1 j.val) 0 (r*(u0/Δ)) (r*(u0/Δ)) (2*u0) (tars U x T (vaneT x hΘ i j c hc) d):=by
   let M:= vaneT x hΘ i j c hc
   have hX:= fitsB x hΘ i j; let E:= (Q x); let J:ℕ:= N1
   have hJ: M.live.crest=i.val.1:= congr_arg Prod.fst (cardK (R:=Q x) _ _)
   have hZ: MergeProof.load M.live=u0:=by unfold MergeProof.load; rw [hJ]; rfl
   have hv := support_zero (S').ratio _ (hJ.symm ▸ hx: 0∈M.live.crest)
   let B':=houseS U x; let t:= r*(u0/Δ); have hf:0≤ u0:= mul_nonneg (Real.exp_pos _).le ((norm_nonneg _).trans (hc 1))
   have hg:= glyphBound A.B.a (m+1)
   have hw : r* ((Q x).p.mass M.live.crest M.live.weight) ≤ t:=by rw [show (Q x).p.mass M.live.crest M.live.weight= u0 from hZ]; exact mul_le_mul_of_nonneg_left (le_div_self hf hg.1 hg.2) (Doors.rate_pos _).le
   have hx: ∃ s': B'.fragrances → ℝ, SumBudget (fun i=> Local.reservedMass (A.B.a.budget m) (locus M.live B' 0 i) (s' i)) (coinFee G (X.p.profile i₀) d L₀ * ((Q x).p.mass M.live.crest M.live.weight)) ∧ ∀ i,prince M.live B' i → (A.B.a.budget m).supBounds 0 (locus M.live B' 0 i) (pane B' M v' i) (s' i):=by
      refine ⟨(fun i=>0),?_,fun i hi=> (never B' M.live J rfl i hi).elim⟩; simp only [Local.reservedMass,mul_zero]; exact Local.sumBudget_zero (mul_nonneg (coin_pos ..|>.le) (by rw [show (Q x).p.mass M.live.crest M.live.weight= u0 from hZ]; exact hf))
   let v:=Extra.Histories.fare (Rt) J j.val; have hu:v=M.milk:=Blush.rose (Q x) 0 J j.val c hc hX
   have hℓ:d ≤ i₀:= by omega
   have hL : Fancy tu H N n m (hol G) v (Blush.scope B' M 0) (Blush.screen B' M (pupil U x M.live) (pupil U x M.pale) v' (F)) 0 (authors A.B.a m) t t:= hu.symm ▸ Vintage.YM.PhysicalNext.Repeat.Graces.sendsCard g hm h hC U x he ht hp hh hℓ M hv hx hw
   nth_rw 3 [← hZ]; apply thunderV g hm hC U x he hp T s M d hℓ ha (hJ.symm ▸ (by assumption)) v _ _ _ _ _ ?_ ?_ hL
   · funext V; change 0=(0:ℂ)+Complex.I*0;simp
   funext z V; let b:=barcode (Rt).activities J
   by_cases he:z=b
   · subst z; change (Pi.single b j.val : Box n₁ → Config G n₁→ℂ) b V= _; rw [Pi.single_eq_same]; unfold entry; rw [show M.live.turn = .gasKey J from rfl, show M.pale.turn = .gasKey J from rfl]; change j.val V=(if barcode (Q x|>.activities) J=b then _ else (0:ℂ))+Complex.I*(if barcode (Q x|>.activities) J=b then _ else 0); simp only [b, if_true]; rw [mul_comm Complex.I]; exact (Complex.re_add_im _).symm
   unfold entry; rw [show M.live.turn = .gasKey J from rfl, show M.pale.turn = .gasKey J from rfl, exactGas]; change (Pi.single b j.val : Box n₁ → Config G n₁ →ℂ) z V = _; erw [Pi.single_eq_of_ne he]; simp;split_ifs <;> first | (exfalso; exact he (Eq.symm (by assumption))) | (exact (add_zero (0:ℂ)).symm)
end
end YM.PhysicalNext.Repeat.Graces
