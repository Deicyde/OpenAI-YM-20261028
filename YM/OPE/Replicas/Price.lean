import YM.MergeProof.North.Price
import YM.OPE.Replicas.Quiet

/-!
# Many slots per cell: port of YM/MergeProof/North/Price.lean

Most of the proof can be shared verbatim with that for pairs. Costs at every step
use the same register though the group being transported can now be quite different.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice Wilson RG MeasureTheory Finset Push Local Extra.Histories PhysicalNext.Repeat Lotus Merge Merge.Palette Accent Marker
open Extra.Multi GridApprox.Nil Menu Ribbon
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{f c:Side}{R:Rep G f}{A:Rep G c}
-- packaged law for ALL selected transforms, any number of constituents. unmarked unchanged every.
def Unites (S:StepData c f)(D:GaugeDoor R A)(N:ℕ) (d c' a k s u:ℝ):Prop:=∀ (V slotsZ:Type) (_:Fintype slotsZ)(_:DecidableEq slotsZ) (_: DecidableEq V) (_:Fintype V) (ι:Type)(_ : Fintype ι) (o:(V×slotsZ)→Site f) (r: (V×slotsZ)→ℝ) (q:ι→Hat (Names V slotsZ) R),
    (∀ i,0< r i)→Occupancy (S.ratio.parent ∘ o) N →Offer o q r R.p.B d c'→ ∃ F K, Towed r id F A.p.B a s ∧ (∀ i,Burns (S.ratio.parent ∘ o) i (F i) A.p.threshold) ∧ Towed r Prod.fst K A.p.B k u∧(∀ i,Flow (S.ratio.parent ∘ o) i (K i) A.p.threshold)∧ S.push R.beta (Expense q r S)=play A (Names V slotsZ) K (fun U=>∑ i,F i U)∧ (∀ i U,(K i U).part (Names V slotsZ).quiet=profile A.activities (fun j=>Complex.ofReal ∘ A.activities.K j) i U) ∧ (∀ i U j,(K i U).part ((Names V slotsZ).fire j)=∑ l,owl (q l) D j i U) ∧ ∀ (v w:V)(b:Equiv.Perm V)(m:Extra.Histories.Motion)(x:Site c)(π:R.activities.Moves m.1 (S.ratio.embed x))(E:Equiv.Perm ι), Ribbons.ManyCopies.Kin q v w b m (S.ratio.embed x) π E → (∀ i:slotsZ,r (v,i)=r (w,i))→∀ U, (∀ i,Harm v b m (F i (pull m.1 x U)) (F (sky m x i) U)) ∧ ∀ i,Harm v b m (K i (pull m.1 x U)) (K (puff m x i) U)
end YM.MergeProof.Ribbons.ManyCopies
end
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
open MergeProof Menu
variable (hE : (Q x).p.supportExponent≥100)(hN : 100≤(H.result x).p.supportExponent) (hS: Arrives R.shape A.delay) (hF:Pungent R.shape A.delay)
include g hm
local notation "P₀"=> A.B.a.params m
local notation "V"=> A.B.a.clock.op m n
local notation "d0"=> sandboxK H x
set_option quotPrecheck false
local notation "b'"=> (B).supportExponent
include hS hE hN hF
set_option maxHeartbeats 640000 in
lemma vastN (hZ:HasSlots ((Q x).p) ((Q x).activities)) {N':ℕ}{v':ℝ}(hp:0≤v')(hc:Palette.shipPrice L Y y N' v') : MergeProof.Ribbons.ManyCopies.Unites (V) d0 N' ((Q x|>.p.supportExponent)-4) v' (b'+1/2) (b'+1) 1 (straw Cμ L G y):=by
   let Z:= V; let Rπ:= houseS H x; have hC:=hS _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)
   let X':= P₀; have hD : SoundDoor Z d0:=sounds g hm H x hS
   intro P Zslots hiZ hdZ hpP hP ι hι o r b hb hQ ht
   let C:= MergeProof.Ribbons.ManyCopies.Names P Zslots

 
   have hΞ:= Opera.protocol A.B hm R.pledging.conducts.full (n:=n); obtain ⟨A₀,ba,q,t',z,F'₀,t₃,t₄,t₅,t₆,k',hB,hX,N₀,hN'⟩:=hC.1.2 _ _ _ _ hΞ (Q x) _ (houseS H x) -- b' conflict
   let M(i):= (b i).M; let a(i):= sumFee (b i) r
   have he : (B).supportExponent+3 ≤ (Ze).earn :=by
      have he':= R.pledging.agenda _ _ (step_paid A.B.a m)|>.1; rw [Rain.jersey (A:=A) (m:=m)|>.2.2.1]; linarith
   have hV:Palette.Plot M Rπ a := Photo.bidding _ C r hb b o hC.1.1 (by rw [Rπ.laws.intake.sizes, Rπ.laws.data.funds.length_eq]; exact hB.covers) (by
      change 4 ≤ (Y).exp+_+_; change 100 ≤ b' at hN; linarith only [he,hN,(Ze).worth,(Ze).first,(Ze).second,(Y).usable,(Y).pos]) hE hp ht hQ hc
   let F:=pupilK H x M a; let P':=(Q x).p
   have hv := Many.usable g hm H x M a N₀ hS hB hV
   obtain ⟨hR,hX,hb',hP',he',hZ',hW'⟩ := (Photo.hue _ _ _ F _ _ _ hb d0 b hD (fun i=>by intro j hj; obtain ⟨i',hi,hj⟩:= mem_image.mp hj; subst j; exact mem_image_of_mem _ (ht.sites _ (mem_image_of_mem _ hi))) hv (crowd2 g hm H x M a N₀ hF hB hV) rfl (add_nonneg (B).exponent_pos.le zero_le_one) (fun i U j=> (by obtain ⟨v,h,_⟩:=hv.gas.bought; exact live H x M a i U (((h i).works U).choose_spec)))) -- order etc
   refine ⟨_,_,hR.shrink ?_ ?_ hb,hX,hb',hP',he',hZ',hW',?_⟩
   · linarith only [he,hB.allow]
   ·
     --  E0 log bill ≤1.
     obtain ⟨_,ha,_,_,hτ⟩:= Palette.field M Rπ O a hV hB N₀.balance
     have hz := mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (Real.exp_pos ((Y).mark L Cμ y)).le) (show 0 ≤ (1-1/2:ℝ)⁻¹ by norm_num)) (budget_nonneg (ha 0)); linarith only [hB.gains,hz,hτ]
   intro v w D mA x' π E hi hwA U
   obtain ⟨P,hP⟩:= metPair g hm H x π M a E
   refine ⟨fun i=> Photo.cloudN b _ _ _ r F hi hv hb hwA U i,fun i=> Photo.nightN b _ _ _ r F hi hv hb hwA U P ?_ i⟩
   intro t u he j; exact hP t u (fun i h=>⟨(hi.plot i (he i h)).2.1,hi.fares hwA i (he i h)⟩) j U
end YM.PhysicalNext.Repeat.Mallow.Many
