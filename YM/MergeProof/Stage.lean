import YM.MergeProof.Echo
import YM.MergeProof.Limb
import YM.MergeProof.Record

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
include hR h₀ g hm hp T
local notation "Xs"=> A.B.a.clock.op m n
open Switch
omit T hR hp h₀ in
lemma listens (u:Site (A.B.a.S.side m n))(i:ι)(he:u∈ (M i).crest.image (Xs).ratio.parent) : Motion.Hush i u (fun j=> ((H.result x).activities.forced j).support) (pupilK H x M rA):=by
  have hr : Motion.Hush i u (fun j=> ((D₀).kernel j).support) (Palette.shoot M W O rA H.H.base f'):=by
    intro j t z ht
    by_cases h: j∈Set.range (Refrain.visa H.H.base f')
    · obtain ⟨j,rfl⟩:=h; funext U; change u∉ (Refrain.reserve H.H.base (Refrain.badge H.H.base (Refrain.visa H.H.base f' j))).support at ht
      unfold Palette.shoot Palette.shootK;dsimp only; rw [stuffed,stuffed]; exact Palette.limbs M W O rA U i u he _ (fun h=>ht ((Refrain.admitted H.H.base f' j).1.symm ▸ h)) t z
    unfold Palette.shoot Palette.shootK; dsimp only; rw [blank _ _ h,blank _ _ h]
  have he : Motion.Hush i u (fun j=> ((T₀).kernel j).support) (shiftK H x M rA):= Motion.quiet_fusion _ u hr (Marlin.hak D₀)
  rw [Spring.owns g hm H hx]; exact Motion.quiet_fusion («d»:=Rack.widen T₀ T') (P:=B) _ u (Motion.quiet_up i u he) (folio G _)

local notation "r4"=> (Ze).earn+w
local notation "d4"=> (pledgeA L Y Cμ y b₁ (P!).order n')*(1-sailUp Y L y)⁻¹
local notation "Rq"=> H.result x
local notation "τ"=> Photo.tones M W O rA

lemma usable : Photo.Usable M W O Rq rA (pupilK H x M rA) r4 (2*d4) (straw Cμ L G y):=by
  have hk:(Rq).p=B:=rfl
  let p':=Palette.lace M W rA n'; have hW(i):= Palette.fair M W O rA h₀ i n'
  have he':Summable p':= (Palette.sizes M W O rA h₀ hp T.balance).2
  have h₁ : Ac.Hit (fun i:(W).fragrances=> (W).bookFoot (.inr i)) ((Rq).p.B) (fun i=> 2*p' i) r4 (2*d4):=by
     intro i; have he:=budget_scale zero_le_two (Palette.lucent M W O rA h₀ hp T.balance i); convert! he using 2; rename_i j; rw [hk]; split_ifs <;> ring_nf; rfl
  refine ⟨h₀,rfl,⟨_,fun i=>?_,he'.mul_left 2,h₁⟩, crowd g hm H x M rA T hR hp h₀,listens g hm H x M rA,fun U t j h=>?_⟩
  · have he:= Switch.constant (ι:=ι) (fun U=>Palette.song M W O rA i U 0 ∅) (hW i|>.rocket) (fun U=> Switch.Paid.tasting (hW i) U 0 ⟨le_rfl,zero_le_one⟩ ∅);change Switch.Paid _ (2*p' i); rw [two_mul]; exact Switch.Paid.sub (hW i) he
  rw [← valueP g hm H x M rA T hR hp h₀ t j h U]; have he₁ q r (hc:q∈ Set.Icc (0:ℝ) 1): Summable (fun i=> Palette.song M W O rA i U q r):= he'.of_norm_bounded fun i=> Switch.Paid.tasting (hW i) U _ hc _
  simp_rw [hk,Photo.tones,Summable.tsum_sub (he₁ t j h) (he₁ _ _ ⟨le_rfl,zero_le_one⟩)]; rfl
end YM.PhysicalNext.Repeat.Mallow.Many
