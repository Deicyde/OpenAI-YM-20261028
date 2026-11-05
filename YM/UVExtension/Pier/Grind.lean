import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Blush.Parcel
import YM.UVExtension.Pier.Loom
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Pier
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open PhysicalNext PhysicalNext.Repeat Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera Mallow
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} (g:G.Simple) {X:Metals G} {D: Rolls X.p} {A : Alloy X D}
    {R: Factor A} {l v:ℝ} {N m n:ℕ}(hm:m<N) {Q: In A.B.a m n} (H: Spring R N m n l v Q)
local notation "J" => A.B.a.clock.J (m+1)
local notation "Jp" => A.B.a.clock.J m
local notation "Ω" => A.B.a.budget m
local notation "d" => H.ordinal

local notation "Ze" => R.expense J Jp
local notation "Cμ" => (R.shape.μ J Jp)
local notation "y" => A.B.a.clock.hatBeta m
local notation "O" => Chi.canonical
variable (x: Icc l v)
local notation "W" => houseS H x
local notation "a0"=> (0:Site (A.B.a.S.side m n))
local notation "S" => A.B.a.clock.op m n
open Labels YM.Planned.GuardedAtom
local notation "Z₀" => H.result x
variable {ι:Type} (E: ι ≃ Cash.fragrances (houseS H x))(M:Leaf (Q x))
local notation "T₁"=> pupil H x M
variable (F: ι→ Support (A.B.a.S.side m n))(he:∀ i,locus M (houseS H x) 0 (E i)=F i)(hy:∀ i,(0:Site (A.B.a.S.side m n))∈ F i)
local notation "Π"=> land G (A.B.a.S.side m n) Ω
variable (h: Mallow.Arrives R.shape A.delay) (ha:(0:Site (A.B.a.S.side m n))∈M.crest.image (A.B.a.clock.op m n).ratio.parent)

def Address {ι:Type}{n:Side}(X:ι→Support n)(he:∀ i,(0:Site n)∈X i)(i:ι):Wing:= .logKey (Blush.found 0 (X i) (he i))
lemma heldK {n:Side} (Z : Rep G n)(p:BudgetPoint)(hk:Z.p=p)(hp:HasSlots Z.p Z.activities)(F:ℕ→ Config G n→ℂ)(h:Local.ForceFormat p Z.activities 0 F) (i:ℕ)(v:ℝ)(hv:∀ U,‖F i U‖≤v): Held p (.gasKey i) (F i) := by
    refine ⟨?_,fun U hU=> ?_,fun hi=> (whereAt (Wing.gasKey i) hk hp) ▸ (show _∈ Wing.support (Wing.gasKey i) Z from h.carried i hi),h.borel i,h.invariant i, v,hv⟩
    · rw [← whereAt _ hk hp]; exact h.supported i
    apply (sortBit _ hk hp U).mp
    change (Z.activities.forced i).eligible Z.p.threshold U; rw [hk]; exact h.forcing i U hU
lemma heldE {n:Side}(Y:Support n)(hs: (0:Site n)∈Y)(R : Rep G n)(Z:BudgetPoint)(hR:R.p=Z)(hp:HasSlots R.p R.activities)(F:Config G n→ℂ)(hc: LocalOn Y F)(hz: GaugeInvariant F)(hx: Measurable F)(u:ℝ)(hu:∀ U, ‖masked Z.threshold Y F U‖ ≤ u): Held Z (.logKey (Blush.found 0 Y hs)) (masked Z.threshold Y F):=by
    let e:= Blush.found 0 Y hs; have ht: land G n Z (.logKey e)= Y:=stamp Y hs hR hp
    refine ⟨?_,fun U hU=> ?_,fun _=> ht.symm ▸ hs,masked_measurable _ _ _ hx, Local.invariant_mask hz _ _,u,hu⟩
    · rw [show land G n _ _= _ from ht]; exact Local.uses_mask _ hc
    have he : Healthy Z.threshold Y U:= by by_contra he; exact hU (masked_ne _ _ _ _ he)
    change Healthy Z.threshold (land G n Z (.logKey e)) U; rwa [ht]
include h ha hm g he hy
local notation "b₀"=> nectar T₁
set_option quotPrecheck false
local notation "W0"=> Address F hy
lemma swept (hp: HasSlots (A.B.a.budget m) (H.result x).activities) (V:ι→ Config G (A.B.a.S.side m n)→ ℂ) (ht:∀ i,V i= Complex.ofReal ∘ masked ((A.B.a.budget m).threshold) (F i) (matin M (houseS H x) (E i) Chi.canonical)) (hV:Dominated V) (hM:Dominated (nectar (pupil H x M))) :
   (∀ i,Held Ω (W0 i) (V i)) ∧ (∀ i,Held Ω (.gasKey i) (b₀ i)) ∧ (Complex.ofReal ∘ ((S).push (Q x).beta M.cicada))=(fun U:Config G (A.B.a.S.side m n)=> ∑' i, port (H.result x) (W0 i) U* V i U)+(fun U=>∑' i,port (H.result x) (.gasKey i) U* nectar (pupil H x M) i U):=by
   let B:=Ω; have hC := h J y (A.B.valid.pays m) _ (step_paid A.B.a m)
   have hΞ:= Opera.protocol A.B hm R.pledging.conducts.full (n:=n); obtain ⟨A₀,b,q,t',z,F'₀,t₃,t₄,t₅,t₆,k',hB,hX,N',hN'⟩:=hC.1.2 _ _ _ _ hΞ (Q x) _ (W)
   have hv:= (H.moves g hm).2 x x.2 |>.1.bundle; let Z:= Z₀; have hF : Z.p=B:=hv.point
   have hZ : Push.Local.ForceFormat Ω (Z₀).activities 0 (nectar T₁) := (Mallow.guardN g hm H x M _ ha N' h hN' hB).1
   refine ⟨fun i=> ?_,fun i=> ?_,?_⟩
   · have hyi : B.Regular (F i) (Complex.ofReal ∘ matin M (W) (E i) O):= he i ▸ Blush.ornate (scops M W N' hN' B ha rfl (Rain.jersey (A:=A) (m:=m)|>.1.le) (E i))
     have hi: V i=masked B.threshold (F i) (Complex.ofReal ∘ matin M (W) (E i) O):= by rw [ht]; exact funext fun U=> (Blush.liquid ..).symm
     obtain ⟨u,-,hu⟩:=hV; specialize hu i; rw [hi] at hu ⊢; exact heldE _ _ Z B hF (hF.symm ▸ hp) _ hyi.sites hyi.symmetry hyi.borel (u i) hu
   · obtain ⟨M',hM,hu⟩:=hM; exact heldK Z B hF (hF.symm ▸ hp) (b₀) hZ i (M' i) (hu i)
   funext U
   let f j:= masked ((A.B.a.budget m).threshold) (locus M W (a0) j) (matin M W j O) U; let G' : ℝ := ∑' j,f j; let F' := ∑' i, petals Ω Z.activities (tonic T₁) U i
   rw [Function.comp_apply, show (S).push _ _ U= Z.eval U*G'+Real.exp (Z.exponent U)*F' from Mallow.gust g hm H x M (a0) ha N' h hN' hB U, Complex.ofReal_add, Pi.add_apply]
   congr 1
   · have hi i: port Z (W0 i) U * V i U= (Z.eval U:ℂ)* (f (E i):ℂ):=by rw [ht i]; unfold f; rw [he i]; rfl
     change _ = ∑' i, port Z (W0 i) U * _; simp_rw [hi]; rw [tsum_mul_left, E.tsum_eq (fun j=>(f j:ℂ)), Complex.ofReal_mul]; exact congr_arg (fun t=> (Z.eval U:ℂ)*t) (Complex.ofReal_tsum ..)
   rw [Complex.ofReal_mul]; change _= ∑' i,port Z (.gasKey i) U*_; rw [carded Z hv.valid (b₀) hM]; unfold salaryP F'; congr 1; rw [Complex.ofReal_tsum]; exact tsum_congr (fun i=> (herbs ..).symm)
end YM.UVExtension.Pier
