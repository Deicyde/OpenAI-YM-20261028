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
    {R: Factor A} {l v:ℝ} {N m n d:ℕ} (hm:m<N) {Z:Bolt A} (h:Nest R Z) {Q: In A.B.a m n}
local notation "H" => Issue.trail Z
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
    (he: (Issue.trail Z).rep N n m = U.result x.val) (ht: (Issue.trail Z).rep N n (m+1) = Q x.val) -- careful Hull.L
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
include hm g hC
lemma cloudDrop (hk: T.live.weight=T.pale.weight) 
   (Pa: Wing→Prop)(heM:Pa T.live.turn) (F':Config G (A.B.a.S.side (m+1) n)→ℂ)(ρ : Res G (A.B.a.S.side (m+1) n)) (ψ : MergeProof.Response G (A.B.a.S.side m n)) (ho:(0:Site (A.B.a.S.side (m+1) n))∈T.live.crest)
   (hz:F'= prose T.live+ Complex.I • prose T.pale)
   (hr:ρ = entry T.live+ Complex.I • entry T.pale)
   (βp:Res G (A.B.a.S.side m n))
   (hb:βp= profile (U.result x|>.activities) (M).forced + hook (U.result x|>.activities) (U.result x|>.p.threshold) ψ)
   (hl:Attainment (U.result x|>.p) o ψ a):
    Tale Pa 0 o v' F' ρ βp 0 (2*load T.live) a (sandboxK U x):=by
    have hs:= sounds g hm U x hC
    let J:Bool→Leaf (Q x):= fun i=> if i then T.live else T.pale; let f(i:Bool):ℂ:= if i then 1 else Complex.I
    have he':(M).forced= v' • ((fun i=> Complex.ofReal ∘ (sandbox).hinge T.live i) + Complex.I • (fun i=> Complex.ofReal ∘ (sandbox).hinge T.pale i)):=rfl
    let Vx(i:Bool) j Uq:= v'*f i*( (sandbox).hinge (J i) j Uq:ℝ)
    have hP:(M).forced=fun i Uq=> ∑' j:Bool,Vx j i Uq:=by funext i Uq; rw [he']; simp [Pi.smul_apply,Vx,f,J,tsum_fintype]; ring
    have hv: SumBudget (fun i=> ‖v'*f i‖*load (J i)) (∑ i, ‖v'*f i‖*load (J i)):=⟨fun i=> mul_nonneg (norm_nonneg _) ((Leaf.profit _).trans ((Q x).p.loMass _ _ (Leaf.profit _))),Summable.of_finite,(tsum_fintype _).le⟩
    have hm: Dominated (fun i: Bool×ℕ=>Vx i.1 i.2):=supplyLine _ hs (s:=fun i=> v' *f i) («M»:=J) hv
    have ht: Odyssey Pa 0 o v' F' ρ βp 0 (2*load T.live) a (sandboxK U x) J f ψ:=by
       have hx: load T.live = load T.pale:=by unfold load;rw [T.turnout,hk]
       refine ⟨fun i=>?_, ⟨fun i=> mul_nonneg (norm_nonneg _) ((Leaf.profit _).trans ((Q x).p.loMass _ _ (Leaf.profit _))), Summable.of_finite,?_⟩,hl,fun i=>?_,fun j Uq=>?_,fun p Uq=>?_⟩
       · cases i; exact ⟨T.turnout ▸ ho,T.together ▸ heM⟩; exact ⟨ho,heM⟩
       · rw [tsum_fintype,Fintype.sum_bool]; change  ‖(1:ℂ)‖*load T.live + ‖Complex.I‖*load T.pale≤ _; rw [← hx, norm_one,Complex.norm_I,one_mul,two_mul]
       · simpa only [hz,f,J, sub_zero,Pi.add_apply,Pi.smul_apply, Fintype.sum_bool, Bool.false_eq_true,if_false, if_true, one_mul, smul_eq_mul] using! hasSum_fintype (fun q=> f q* prose (J q) i)
       · simpa only [hr,f,J,Pi.add_apply,Pi.smul_apply, Fintype.sum_bool, Bool.false_eq_true,if_false, if_true, one_mul, smul_eq_mul] using! hasSum_fintype (fun q=> f q*entry (J q) j Uq)
       rw [hb, Pi.add_apply,Pi.add_apply,add_sub_cancel_right,hP]
       have hh:= profile_shop (f:=Vx) (U.result x|>.activities) hm p Uq
       exact hh.congr_fun fun i=> by unfold profile cram Vx; rw [tsum_mul_left]; rfl
    exact ht.tale
include hm hC g h ht he
lemma thunder (Pa:Wing→Prop) (heM:Pa T.live.turn) (ho':(0:Site (A.B.a.S.side (m+1) n))∈T.live.crest)
   (f:Config G (A.B.a.S.side (m+1) n)→ℂ)(F':Config G (A.B.a.S.side (m+1) n)→ℂ)(ρ : Res G (A.B.a.S.side (m+1) n))(t r:ℝ)(v₁:(F).Coeff)
   (hz:F'= prose T.live + Complex.I • prose T.pale)(hr:ρ= entry T.live+Complex.I • entry T.pale)
   (hY: MergeProof.Fancy (localSection G d) (Issue.trail Z) N n m (hol G) f (X!) M v₁ w t r):
   MergeProof.Coupon (localSection G d) (Issue.trail Z) N n m (hol G) F' ρ 0 (duet _ _ _ _ he ht sandbox) Pa f v₁ t r (2*load T.live):=by
   have hx: (H).Conv N n m:=(Z.choice.represents N n m hm.le)
   have hR : Local.Readable (hol G) (localSection G d) (O).p (A.B.a.S.side m n) w:= (hx.vac.symm ▸ (livelyCard hp hd (n:=n) ): Local.Readable _ _ _ (A.B.a.S.side m n) _)
   obtain ⟨q,hq,hU,hA⟩:= MergeProof.grow hY hx hR
   rw [he] at hU hA
   apply MergeProof.border (localSection G d) (H) _ _ _ _ he ht (sandbox) Pa F' ρ f t r _ v₁ L₀ (show (Issue.trail Z).S.block m=L₀ from PriceCompiler.block_eq A.B.valid _) q hq
   apply cloudDrop g hm hC U x hp hd T T.rates Pa heM F' ρ _ ho' hz hr (profile _ q.forced) hA hU -- edit
end YM.PhysicalNext.Repeat.Graces
