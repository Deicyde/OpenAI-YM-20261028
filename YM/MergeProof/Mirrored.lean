import YM.MergeProof.Rim
import YM.MergeProof.Signed
import YM.MergeProof.Silo
import YM.MergeProof.Trio


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
local notation "P!" => (X.p.profile Jp)
-- base.χ.f tilt. R anchor. fuel from Verge
variable {b v₁ b₁ t q t₁ t₂ A₁ b₂ w : ℝ}{n':ℕ} (T:Captain (houseS H x) (X.p.profile (A.B.a.clock.J m)).order t q v₁ t₁ A₁ b₂ t₂ b₁ b n' Chi.canonical)
variable (hR: Arrives R.shape A.delay) (h:Herd (houseS H x) T.conduit A₁ b₁ n')
    (hp:Bikes (R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (D.L (A.B.a.clock.J (m+1))) (R.shape.μ (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (A.B.a.clock.hatBeta m) (R.expense (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)|>.earn) w b₁ (X.p.profile (A.B.a.clock.J m)|>.order) n')
-- actual exponent/weather includes Beam supports.We leverage T.renewed exactly. term at latch.
local notation "z₀" => (Real.exp (-(Y).mark L Cμ y)*(2*Daisy.pledgeQ L Y Cμ y b₁ (P!).order n'))
variable (h₀:Palette.Plot M (houseS H x) rA)

omit [Fintype ι] in
lemma scenery {τ:Type}[Countable τ](F:Lotus.Leaf (Q x))(t:τ→ ℝ)(Z:τ→ Lotus.Leaf (Q x))(h:Grouped F t Z)(i:ℕ)(U:Config G (A.B.a.S.side m n)):
    Joins F t (fun F θ=> pupil H x F θ i U) Z:= Joins.in_final B T₀ T' (fun i u=> (Joins.harvest B D₀ (Marlin.hak D₀) Tap0 (fun i u=> h.verses W O u H.H.base f' i) i u)) i U -- implicit
lemma v0 (t:ℝ) (i:ι) : V t ∅=veranda (M i) W O H.H.base f' 0:=by unfold Palette.shoot Palette.shootK veranda; simp_rw [Palette.offWays,Palette.muted, color0]
lemma v1 (t:ℝ) (i:ι) : V t {i}= veranda (M i) W O H.H.base f' (rA i*t):=by unfold Palette.shoot Palette.shootK veranda; simp_rw [Palette.active M]
omit [Fintype ι] in -- remove unused inst? scenery already. 
private lemma loner (a : ℕ)(Dp : Lotus.Leaf (Q x))(U:Config G (A.B.a.S.side m n)) : DifferentiableAt ℝ (fun t=> pupil H x Dp t a U) 0:= by
   let G:= fun _:Unit=> Dp; have h':Grouped Dp (fun _:Unit=> (1:ℝ)) G:= by
     constructor; exact fun _=> rfl; exact Summable.of_finite; intro u; simp [G] -- check
   exact (scenery H x Dp (fun _:Unit=>1) _ h' a U).atx Dp
lemma live {i:ι} (a:ℕ) (U:Config G (A.B.a.S.side m n)) {g:Switch.Ways ι} (h:Switch.Models (fun t p=> pupilK H x M rA t p a U) g):
    Switch.jet (fun t p=> pupilK H x M rA t p a U) {i}= rA i* tonic (pupil H x (M i)) a U:=by
  let q t:= pupil H x (M i) t a U; let f t:= q (rA i*t)
  refine h.heading i (f:=f) ?_ ?_ ?_
  · simpa [f,q, tonic,Function.comp_def] using! (loner H x a (M i) U).hasDerivAt.scomp_of_eq 0 ((hasDerivAt_id' (0:ℝ)).const_mul (rA i)) (show 0= rA i * 0 from (mul_zero _).symm)
  · intro t; unfold f q; rw [mul_zero]; unfold pupilK pupil final.frigid shiftK shifting; simp_rw [v0 _ _ _ _ _ i]
  intro t; unfold f q pupilK pupil final.frigid shiftK shifting; simp_rw [v1 H]
end YM.PhysicalNext.Repeat.Mallow.Many
