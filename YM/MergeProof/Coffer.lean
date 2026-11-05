import YM.MergeProof.Gallery
import YM.MergeProof.Stanza
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Drip


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
local notation "P!" => (X.p.profile Jp)
open YM.MergeProof
abbrev sandboxK : GaugeDoor (Q x) (H.result x):= ⟨fun M=>fun j U=>deriv (fun θ=> pupil H x M θ j U) 0⟩
include g hm
lemma sounds (hR:Arrives R.shape A.delay): SoundDoor (A.B.a.clock.op m n) (sandboxK H x):=by
   refine ⟨?_,fun s yQ π=>?_⟩
   · let B₀:=A.B.a; have hC:=hR _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)
     have hΞ:= Opera.protocol A.B hm R.pledging.conducts.full (n:=n); obtain ⟨A₀,b,q,t',z,F'₀,t₃,t₄,t₅,t₆,k',hB,hX,N',hN'⟩:=hC.1.2 _ _ _ _ hΞ (Q x) _ (houseS H x)
     let g':= (Y).goal L y; let s:= straw Cμ L G y; let p:=s / |g'|
     refine ⟨p,fun M=>?_⟩
     let E:=(H.result x); have hE:E.p=B:=rfl
     have hx': M.crest.Nonempty :=by
        change (M.turn.support (Q x)).Nonempty; cases M.turn -- dependent
        next i=> exact ⟨_, ((Q x).activities.reg i).anchor⟩
        next i=> let p:= (Q x).activities.forced i; exact p.inventory_ne.mono p.inventory_sup
     obtain ⟨i,hp⟩:= hx'; let S:= A.B.a.clock.op m n
     rw [show (H.result x).p= _ from hE]
     have ht:= (Mallow.guardN g hm H x M (S.ratio.parent i) (Finset.mem_image_of_mem _ hp) N' hR hN' hB).2
     obtain ⟨eQ,hs,Hf⟩:=ht; refine ⟨eQ,⟨hs.1,hs.2.1,hs.2.2.trans ?_⟩,Hf⟩
     unfold jewelDebt; let g'' := Real.exp (-(Y).ε *coverNumber (Q x).p.B M.crest)
     have h': g'' ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Y).usable.le) (by positivity)); let d':= YM.MergeProof.load M; have he':0≤ d':=(M.profit).trans ((Q x).p.loMass _ _ M.profit)
     have hs':0 ≤ s:=by exact mul_nonneg zero_le_two (Real.exp_pos _).le
     calc _ ≤ |d'*g''/g'| *s:=mul_le_mul_of_nonneg_right (le_abs_self _) hs'
          _ ≤ d' / |g'| *s:=by rw [abs_div,abs_of_nonneg (mul_nonneg he' (Real.exp_pos _).le)]; exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (mul_le_of_le_one_right he' h') (abs_nonneg g')) hs'
          _ = _:= by unfold p; rw [div_mul_eq_mul_div,div_mul_eq_mul_div,mul_comm d']
   obtain ⟨p,hyP⟩:= met g hm H x π
   exact ⟨p,fun i j U => by unfold sandboxK; simp only; exact congr_arg (fun f:ℝ→ℝ=>deriv f 0) (funext fun kQ=> hyP i kQ j U)⟩
end YM.PhysicalNext.Repeat.Mallow
