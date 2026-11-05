import YM.FullVolume.Umbra.Docks
import YM.FullVolume.Panel.Dress
-- one real mark among any two epoch carpets at the same stamp
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
open Matrix Window Progress.StationaryScenes Green Census Control Flux FullVolume.Shadow
open Gate Frond Vine Mask
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{J: Ultrafilter ℕ}{Q:ConnectedActivityE6.Target G P}{W x μ C₀ a b e ℓ v :ℝ}{o:Target.Order G W}
    {Λ: Era G S}{U:ℕ→ E→ Config G c}{Z: Draft F G} {K H:ℕ→ Epoch Λ}{j:ℕ}{p:E}
open FullVolume.Neptune Flux Shield Eider Packets Polar
namespace Umbra
open Lotus
open Draft
variable {Υ:ℕ→ Draft F G} {V:ℕ→ Config G c} {M:Bank}(I:Depot Q o x μ L C₀ K) (T:Depot Q o x μ L C₀ H){χ: Chi}(R:∀ n, Station M χ (I n) j)(P':∀ n,Station M χ (T n) j)
variable {F₀:BatchK K} {F₁:BatchK H}{δ δ':ℕ→ Molecule S→ℝ}{Δ Δ':ℕ} (h:Seats I (F₀:=F₀) (χ:=χ) (M:=M) (j:=j) δ Δ) (hq: Seats T (F₀:=F₁) (χ:=χ) (M:=M) (j:=j) δ' Δ') {k:Wing}(hm:Rhyme F₀ F₁ k)(hM:Mirror K H)(hJ:(J:Filter ℕ)≤ atTop) (m:Molecule S)
set_option quotPrecheck false
open Daisy Charity
include I h R
local notation "W'"=>fun n=> (F₀ n).lotus (K n).tubes x χ o.K W o.a Q.table Q.halo
local notation "R'"=>fun n=> (F₁ n).lotus (H n).tubes x χ o.K W o.a Q.table Q.halo
private lemma likelyN {ι:Type}[Fintype ι][Nonempty ι](f:ι→ℝ) {b:ℝ}(h:∀ i,‖f i‖ ≤ b):‖likely f‖ ≤ b:=by
    unfold likely; rw [norm_mul,Real.norm_of_nonneg (by positivity : 0≤ (Fintype.card ι:ℝ)⁻¹)]; have ht:= sum_le_sum (s:=Finset.univ) fun i _=> h i; rw [sum_const,nsmul_eq_mul,card_univ] at ht; exact (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans ht) (by positivity : 0≤ (Fintype.card ι:ℝ)⁻¹)).trans_eq (by field_simp)
lemma lotus_bound (n:ℕ)(p:Config G c):‖W' n p m‖ ≤ δ n m:=by
    letI : Nonempty (Forest S.ratio):= Tree.select _ S.patch.odd_side; refine likelyN I R h _ (fun r=> ?_)
    change ‖(F₀ n).bloom (prism (K n).tubes x χ o.K p (allot r)) W o.a Q.table Q.halo m‖ ≤ _; unfold Leaf.bloom; split; swap; · rw [norm_zero]; exact h.bud.value ..
    unfold Leaf.steep; exact likelyN I R h _ (fun i=> h.closeH I R n ((planted (prism (K n).tubes x χ o.K p (allot r)) m).taggedL i) rfl rfl rfl rfl m)
include T hq P' hM hm hJ
lemma lotusGlints (V:ℕ→ Config G c): Glints J (fun n=> W' n (V n) m) (fun n=> R' n (V n) m):=by
    unfold Leaf.lotus; let f n r:=(F₀ n).bloom (prism (K n).tubes x χ o.K (V n) (allot r)) W o.a Q.table Q.halo m; let g n r:= (F₁ n).bloom (prism (H n).tubes x χ o.K (V n) (allot r)) W o.a Q.table Q.halo m
    refine (Glints.every Finset.univ fun r _=> (?_:Glints J (fun n=> f n r) (fun n=>g n r))).bin (fun x _=>continuousAt_const.mul continuousAt_id)
    let X n:= planted (prism (K n).tubes x χ o.K (V n) (allot r)) m
    let X' n:=planted (prism (H n).tubes x χ o.K (V n) (allot r)) m
    unfold f g Leaf.bloom; apply (switch («a»:=fun i=> Leaf.steep (F₀ i) (X i) _ _ _ _ _ _) («b»:=fun i=> Leaf.steep (F₁ i) (X' i) _ _ _ _ _ _) (?_) ⟨(0:ℝ),tendsto_const_nhds,tendsto_const_nhds⟩ (fun n=>standsIn (prism (K n).tubes x χ o.K (V n) (allot r)) (K n).kin Q.halo m)); unfold Leaf.steep
    let u(n:ℕ) k:=(F₀ n).tithe ((X n).taggedL k) (own m) W o.a Q.table Q.halo m; let v n k:= (F₁ n).tithe ((X' n).taggedL k) (own m) W o.a Q.table Q.halo m
    refine (Glints.every Finset.univ fun k _=> (?_:Glints J (fun n=>u n k) (fun n=>v n k))).bin (fun x _=>continuousAt_const.mul continuousAt_id); obtain ⟨b,hb⟩:=h.bud.bound; let A n:= mount (allot r) G x (V n) χ k m o.K
    refine Glints.time (flowers (x:=0) (b:=b) (f:=fun n=>u n k) ?_) ((bornT I T R P' h hq hm hM m (Υ:=A) (fun _=>⟨rfl,rfl⟩) (fun _=>rfl) (fun i=> show (A i).Viable (V i) from rfl)).mono_left hJ)
    exact Eventually.of_forall fun i=> by rw [dist_zero_right]; exact (h.closeH I R i ((X i).taggedL k) rfl rfl rfl rfl m).trans (budget_single (hb i) m)
section leisure
variable [FiniteDimensional ℝ E](i:(I 0).ThinP)
local notation "g0"=> fun n=> Charity.libs (F₀ n) (I n) χ
local notation "g1"=> fun n=> Charity.libs (F₁ n) (T n) χ
lemma escortG (he:∀ n,Healthy (Pressure.temp x) ((I 0).smallAt i) (U n p))(hp:∀ n,Mode (U n) p j M.v): Frill J j p (fun n s=> g0 n (U n s) i) (fun n s=>g1 n (U n s) i):=by
    refine (Frill.still _).times (Frill.buds Finset.univ fun u _=>?_); let X n:=prism (K n).tubes x χ o.K (U n p) (allot u);let Y n:=prism (H n).tubes x χ o.K (U n p) (allot u); let m:= i.val
    let f n s:=(F₀ n).grove (vary (X n) (U n s)) m W o.a Q.table Q.halo; let g n s:=(F₁ n).grove (vary (Y n) (U n s)) m W o.a Q.table Q.halo
    refine Frill.alter (F:=f) (H:=g) ?_ (Eventually.of_forall fun n=> EventuallyEq.symm ((F₀ n).arc (X n) m (I n) (R n|>.N.oboe) rfl rfl rfl i.property.2 (he n) (hp n) rfl)) (Eventually.of_forall fun n=>EventuallyEq.symm ((F₁ n).arc (Y n) m (T n) (P' n|>.N.oboe) rfl rfl rfl i.property.2 (he n) (hp n) rfl))
    by_cases hh : Ac.Spark (I 0).supportP m ∧ troupe (K 0).tubes (K 0).kin Q.halo (radiusB x) m
    swap;· exact (Frill.still (0:ℝ)).alter (Eventually.of_forall fun n=> Eventually.of_forall fun z=> (if_neg hh).symm) (Eventually.of_forall fun n=>Eventually.of_forall fun z=> (if_neg hh).symm)
    let a n s k:=(F₀ n).cinema ((preps (vary (X n) (U n s)) (roster m)).taggedL k) m W o.a Q.table Q.halo (podium S G ((I 0).unionP m) (radiusB x));let a' n s k:= (F₁ n).cinema ((preps (vary (Y n) (U n s)) (roster m)).taggedL k) m W o.a Q.table Q.halo (podium S G ((T 0).unionP m) (radiusB x)); let b:= (Fintype.card S.Choices:ℝ)⁻¹
    have hz k: Frill J j p (fun n s=> a n s k) (fun n s=> a' n s k):=by
       let V n:= mount (allot u) G x (U n p) χ k m o.K
       refine (plume I T R P' h hq hm hM hJ m (Υ:=V) (fun n=>⟨rfl,rfl⟩) (fun _=>rfl) (fun _=>rfl) hp he).alter ?_ ?_
       · exact Eventually.of_forall fun n=> Eventually.of_forall fun v=> (F₀ n).casin (X n) m (I n) rfl i.property.2 (he n) k _ _ (show Agrees _ (U n v) (U n v) from fun _ _ _=>rfl)
       exact Eventually.of_forall fun n=> Eventually.of_forall fun v=> (F₁ n).casin (Y n) m (T n) rfl i.property.2 (he n) k _ _ (show Agrees _ (U n v) (U n v) from fun _ _ _=>rfl)
    refine ((Frill.still b).times (Frill.buds Finset.univ (F:=a) (H:=a') (fun i _=>hz i))).alter (Eventually.of_forall fun n=> Eventually.of_forall fun y=> (show f n y=b*∑ i,a n y i from ?_).symm) (Eventually.of_forall fun n=> Eventually.of_forall fun y=> (show g n y=b*∑ i,a' n y i from ?_).symm)
    all_goals exact if_pos hh
-- slot not necessarily branch step.S.G. raw.E elders
end leisure
omit T hq P' hM hm hJ
lemma sky :∃ f:ℕ→ (I 0).ThinP→ℝ, Sparse f∧ ∀ n v z, Healthy (Pressure.temp x) ((I 0).smallAt z) v→ Ore v (fun V=> Charity.libs (F₀ n) (I n) χ V z) M.v (f n z) j:=by
    letI : Nonempty (Forest S.ratio):= Tree.select _ S.patch.odd_side
    obtain ⟨q,hq,hQ⟩:= h.opal I R; let f n (k:(I 0).ThinP):=q n k.val
    refine ⟨f,hq.pull (Embedding.subtype _),fun n y i he=>?_⟩; intro E _ _ _ V p hy ht
    let M' n:=F₀ n; let k:= i.val; let F r:=prism (K n).tubes x χ o.K y (allot r); let g(r:Reserve S)z:= (M' n).picture (vary (F r) (V z)) k W o.a Q.table Q.halo; apply Captain.avgBrush g; intro r; let X:= F r
    refine Brush.shimmy ?_ ((F₀ n).arc X k (I n) (R n|>.N.oboe) rfl rfl rfl i.property.2 he ht hy)
    unfold Leaf.grove; simp_rw [show ∀ z:E,(vary X (V z)).B=radiusB x from fun _=>rfl];split_ifs
    swap; · exact Brush.zi EventuallyEq.rfl (hq.value ..) zero_le_one
    let u (k':S.Choices)(z:E):=(M' n).cinema ((preps (vary X (V z)) (roster k)).taggedL k') k W o.a Q.table Q.halo (podium S G ((I n).unionP k) (radiusB x)); apply Captain.avgBrush u; intro k'
    let Y:=(planted X k).taggedL k'; refine (hQ n (allot r) Y rfl rfl rfl rfl k he E V p ht hy).shimmy (Eventually.of_forall fun z=> ((F₀ n).casin X k (I n) rfl i.property.2 he k' (V z) (V z) (fun _ _ _=> rfl)).symm)
end Umbra
end YM.ConnectedActivityE6.Lim
