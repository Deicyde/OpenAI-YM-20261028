import YM.UVExtension.Rainfall.Lanes
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
-- data certificate exact. Tars holds PPX.
structure Glace (L:N0 →L[ℂ] J') : Prop where
   spark (j:RtG) c (hc:∀ U,‖j.val U‖≤ c): sparkT U x (vaneT x hΘ i j c hc) d
   linke (j:RtG) c (hc:∀ U,‖j.val U‖≤ c): tars U x T (vaneT x hΘ i j c hc) d=L ((↑Π:ℂ) • (L0 j))
   funds (j:N0): UVExtension.Rainfall.Wallet (L j) 0 (r*‖j‖) (r*‖j‖)

include g h hm hC he ht hp hh hd hΘ
set_option maxHeartbeats 740000 in
lemma glaceV (hW: (0:Site n₁)∈i.val.1) : ∃ L:N0→L[ℂ] J', Glace U x T hΘ i L:=by
    let P':= (Rt).p; let u(j:RtG):= ‖c0 j‖; have hu(j:RtG):= (debts P' i j).2 (le_refl ‖c0 j‖); let T' (j:RtG):=vaneT x hΘ i j (u j) (hu j); let D'(j:RtG):= tars U x T (T' j) d
    have hh'(j c hc):= pillow g hm h hC U x he ht hp hh T Set.univ hd hΘ i j c hc  hW (Set.mem_univ _)
    have ht(j:RtG) c hc {ι:Type} [Fintype ι](v:ι→ℂ)(w':ι→RtG)(hv:j=∑ i,v i • w' i) : tars U x T (vaneT x hΘ i j c hc) d =∑ i,v i • D' (w' i):=by
       apply tarsOrbit hm hC U x he hp T (vaneT x hΘ i j c hc) d (T' ∘ w') v (le_trans (Nat.le_add_right d _) hd) (fun i=>rfl) _ (hh' .. |>.1) (fun i=> (hh' ..|>.1))
       intro V; unfold Function.comp T'; simp_rw [hillsK]; let Q:= (Eyelet.Bolt (G:=G) P' i).subtype; change Q j V= ∑ i,v i* Q (w' i) V; rw [hv,map_sum,Finset.sum_apply]; exact Finset.sum_congr rfl fun j _=> congr_fun (map_smul ..) _
    let A':RtG→ₗ[ℂ] J' := ⟨⟨D', fun X Y=> by
           let Z(i: Bool):RtG:= if i then X else Y; let f:= (X+Y); change D' f= _
           have hp:D' f=∑ i:Bool,(1:ℂ) • D' (Z i):= ht f _ _ (fun _:Bool=>1) Z (by simp [f,Z]); simpa [Z] using hp⟩, fun a X=>by
           have h:D' (a • X)=∑ _i:Unit,a • D' X:= ht _ _ _ (fun _:Unit=> a) (fun _=>X) (by simp)
           convert! h using 1;simp⟩ -- constructor structure
    have hu':0< Π:=div_pos (Eyelet.toll_pos ..) (glyphBound ..|>.1)
    have hp' (j:RtG): UVExtension.Rainfall.Wallet (A' j) 0 (r*‖(↑Π:ℂ) • L0 j‖) (r*‖(↑Π:ℂ) • L0 j‖):=by
       have heK : ‖(↑Π:ℂ) • L0 j‖= P'.mass i.val.1 (u j) / Δ:=by rw [norm_smul,Complex.norm_real, Real.norm_of_nonneg hu'.le]; rw [div_mul_eq_mul_div]; rfl
       rw [heK]; exact UVExtension.Rainfall.alarm _ _ _ _ _ _ _ _ he.symm T (hh' j (u j) (hu j)).2
    obtain ⟨L,hL,hZ⟩:= UVExtension.Rainfall.Wallet.vault L0 A' (↑Π:ℂ) (by exact_mod_cast hu'.ne') (Eyelet.steams _) r hp'
    refine ⟨L,fun j c hc=> (hh' j c hc).1, fun j c hc=>?_,hZ⟩
    have hx:tars U x T (vaneT x hΘ i j c hc) d= D' j:= by simpa using ht j c hc (fun _:Unit=>(1:ℂ)) (fun _=>j) (by simp)
    exact hx.trans (hL j).symm
end
end YM.PhysicalNext.Repeat.Graces
