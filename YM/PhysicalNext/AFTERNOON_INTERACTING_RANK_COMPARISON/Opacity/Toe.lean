import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Shield
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Soles
/-!
# Roster for the unmarked VAT. Optional parts carry detector rents.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump
open Function Lattice RG Pressure Tree Wilson AnalyticBridge.GaussianFieldAlignment Locations Channels
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Oriented Push.AbsoluteSums Pressure.Stores
    AnalyticNext.ConnectedActivity GaugeRoute
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {x : ℝ} {A B : Stores S}
    {F F' : Forest S.ratio} {k k' : S.Choices} {X X' : Support c} {p q : Pilot G S x} {P : Teller G}
variable (W : ℝ)

def spanFoot (S : StepData c f) (x) (i : Fleck S):= halo (320*radiusB x) (foot S i)
def runUp (p : Stores S) x (i:Fleck S):= Disjoint (foot S i) (p.dome (300*radiusB x))

lemma runAt (e : Wheel c) (x : ℝ) (i): runUp (book e.1 e.2 A) x i↔ runUp A x (pursuit S e i):= by
  unfold runUp; rw [← foot_ship, ← show pushed e ((book e.1 e.2 A).dome (300*radiusB x)) = A.dome (300*radiusB x) from ?_]; exact (Finset.disjoint_map _).symm
  ext z; obtain ⟨z,rfl⟩:= (orient e).surjective z; simp only [pushed,mem_map_equiv,Equiv.symm_apply_apply]; exact dome_map ..
lemma push_walk (e : Wheel c) (B : ℕ) : pushed e (halo B X)=halo B (pushed e X):= by
  ext j; obtain ⟨j,rfl⟩:= (orient e).surjective j; simp only [pushed, mem_map_equiv,Equiv.symm_apply_apply, halo_spec]; nth_rw 2 [(orient e).surjective.exists]; simp only [Equiv.symm_apply_apply,moving e]
lemma flight (S : StepData c f) (e : Wheel c) (x : ℝ) (i) : spanFoot S x (pursuit S e i)= pushed e (spanFoot S x i):= by rw [spanFoot,spanFoot,push_walk,foot_ship]
namespace Dyed
variable (v : Dyed G S)

def sock (i : Fleck S) (p : Pilot G S x):= if runUp p.key x i then ask v W p i-1 else 0
lemma sock_ship (h : P.Funds S v.things) (i : Fleck S) (e : Wheel c) (p : Pilot G S x): sock W v (pursuit S e i) p=sock W v i (spires e p):= by
  unfold sock; refine if_congr (runAt (A:=p.key) _ _ _).symm ?_ rfl; rw [footship v W e h]
lemma sock_budget (h : Boosted v.things P x) (i : Fleck S) (hv : Coverage.shutters S.patch+1 ≤ radiusB x) (hd : 0<v.arc) (hr : 2*v.arc<firstRadius G) :
    Pulled (sock W v i (x:=x)) (spanFoot S x i) ∧ Tinted (sock W v i (x:=x)):= by
  let X:= spanFoot S x i
  have hh : Pulled (fun p : Pilot G S x=> ask v W p i) X:= footage_read v W i h hv hd hr (fun j hj k hk=> halo_spec.mpr ⟨j,hj,hk.trans (by change _ ≤320*radiusB x; omega)⟩)
  refine ⟨⟨fun A F k=> ?_,?_⟩,fun p hp u=> ?_⟩
  · obtain ⟨f,h,H⟩:=hh.enter A F k
    unfold sock; by_cases he : runUp A x i
    · dsimp only; simp_rw [if_pos he]; exact ⟨fun p=> f p-1,h.sub measurable_const,fun V hv y=>congr_arg (·-1) (H _ hv y)⟩
    dsimp only; simp_rw [if_neg he]; exact ⟨fun _=>0,measurable_const,fun _ _ _=>rfl⟩
  · intro p q he hf hx; unfold sock
    apply if_congr; swap; · exact congr_arg (·-1) (hh.agreed he hf hx)
    swap; · rfl
    unfold runUp; simp_rw [disjoint_left]
    refine forall_congr' fun j=>?_ -- notation ∀ ⦃j⦄
    apply imp_congr_right; intro hj; apply not_congr
    exact hx.reads.dome_agrees _ _ (fun k hk=>halo_spec.mpr ⟨j,hj,hk.trans (by omega)⟩)
  unfold sock; rw [← bootup v W h p i u hp]; rfl
lemma attrition (h : S.patch.Branches S.kernel G) (i : Fleck S) (p : Pilot G S x): |ask v W p i|+1≤ Jewels.attrition S.patch:= by
  suffices hz : |ask v W p i| ≤ 1+(Fintype.card S.patch.FrameTag:ℝ)+(Fintype.card S.patch.Points:ℝ) by unfold Jewels.attrition; linarith only [hz]
  have hv : 1≤1+(Fintype.card S.patch.FrameTag:ℝ)+(Fintype.card S.patch.Points:ℝ):=by linarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card S.patch.FrameTag),Nat.cast_nonneg (α:=ℝ) (Fintype.card S.patch.Points)]
  unfold ask
  rcases i with i|i|i|i|i <;> simp only [Sum.elim_inr,Sum.elim_inl]
  · unfold Aff.fine; split; next he=> exact (sub _).trans hv
    exact (hold _).trans hv
  · unfold Aff.wireMask; split; next he=> exact (sub _).trans hv
    exact (hold _).trans hv
  · apply ((Aff.tollKit (v.top p) p.tag h).1 _).trans; linarith only [Nat.cast_nonneg (α:=ℝ) (Fintype.card S.patch.Points)]
  · apply ((Aff.tollKit (v.top p) p.tag h).2 _).trans; linarith only [Nat.cast_nonneg (α:=ℝ) (Fintype.card S.patch.FrameTag)]
  unfold door; split; next hx=> exact (hold _).trans hv
  rwa [abs_one]
where
  sub (x:ℝ) : |1-v.chi.read x|≤1:= (abs_of_nonneg (sub_nonneg.mpr (v.chi.range x).2)).trans_le (by linarith only [(v.chi.range x).1])
  hold (x:ℝ) : |v.chi.read x|≤1:=(abs_of_nonneg (v.chi.range x).1).trans_le (v.chi.range x).2
lemma little_sock (h : S.patch.Branches S.kernel G) (i : Fleck S) (p : Pilot G S x): |sock W v i p|≤ Jewels.attrition S.patch:= by
  unfold sock; split; next hx=> exact (abs_sub ..).trans ((show _≤ _ from by rw [abs_one]; exact attrition W v h i p))
  rw [abs_zero]; exact Jewels.attrition_nn _
end Dyed
open Milk
-- Economics: Toned grants can cover *all* masks simultaneously.
def DeepDoors (P : Teller G) (S : StepData c f) (C : ℝ) (W : ℝ) (x : ℝ):= ∀ (F : Forest S.ratio) (T : Tube G S),
    P.Funds S T → 100*(1+radiusB x) ≤ c.val → ∀ (A : Stores S) (V : Config G c) Z Y (p : Active A x F),
      let U := physical A F V Y (tape Z)
      (∃ k : S.Choices, Outposts S U V k x W (Aff.home S p.val.val)) → ‖tape Z p‖ < firstRadius G → ‖tape Z p‖ ≤ C*fiery G x S.patch.L

lemma putAway (v : Dyed G S) (W : ℝ) (hw : 0<W) {C ε : ℝ} (h : Beacons P S.patch W ε x)
    (he : DeepDoors P S C W x) (hs : C * fiery G x S.patch.L ≤ v.arc) (hp : P.Funds S v.things) (hd : 0<v.arc) (hβ : 0<v.source.beta)
    (hv : 0<fiery G x S.patch.L) (hr : 2 ≤ radiusB x) (hM : 100*(1+radiusB x)≤c.val)
    (hL : Bid.Larger (G:=G) S) {H K} (hQ : Aff.Alongside H K v.things) (hX : Lift.Booth P S v.things)
    (p : Pilot G S x) (i : Fleck S) (ht : Matched p) (hy : Toned (2*radiusB x) (toes S i) p.y.2 (ε*fiery G x S.patch.L/coupling v.source.beta)) : v.sock W i p=0:= by
  unfold Dyed.sock
  split; swap; rfl
  rename_i hI
  let Z:= Local.portrait v.things p.key p.park p.tag x p.view .endpoint v.chi v.arc p.y.1+coupling v.source.beta • p.y.2
  let q:= toes S i; let U:= v.top p; let B:=radiusB x; let V:=p.view
  have heq : Aff.cert S x p.key p.view:=⟨hM,ht⟩
  have hh : q∉ p.key.dome (50*B):= fun hx=>Finset.disjoint_left.mp hI (footfall S i) (Aff.placed _ _ _ (by omega) hx)
  have ht:=h.fires c f S v.things hp rfl hL H K hQ hX p.park p.key p.view p.tag heq v.chi v.arc p.y v.source.beta hβ q (fun hx=>hh (Aff.placed _ _ _ (by omega) hx)) (hy.shift (by dsimp only [q]; simp only [separation_self,Nat.zero_add]; omega))
  have H' : Outposts S (v.top p) p.view p.tag x W q:= blaze (d:=v.arc) (V:=p.view) h hp rfl hL hQ hX heq p.tag v.chi p.y hβ hr hh hy
  suffices hz : v.ask W p i=1 by rw [hz,sub_self]
  let t:=fiery G x S.patch.L
  rcases i with i|i|i|i|i
  · change Aff.fine p.key _ _ _ _=1; unfold Aff.fine
    have hq: i∉p.key.costs:= fun he=> hh (halo_subset _ _ (mem_union_left _ (mem_union_left _ (mem_biUnion.mpr ⟨_,he,Packets.contains S (.inl i)⟩))))
    rw [if_neg hq]; exact share_one v.chi (toll U i) _ (by change 0<t/4; positivity) (G.chord_nonneg _) (ht.2.1 i rfl).le
  · change Aff.wireMask p.key _ _ _ _ _ _ _=1; unfold Aff.wireMask
    have hq : i∉ p.key.aisles:= fun he=> hh (halo_subset _ _ (mem_union_left _ (mem_union_right _ (mem_biUnion.mpr ⟨_,he,Packets.contains S (.inr (.inl i))⟩))))
    rw [if_neg hq]; exact share_one v.chi (wire (S.prediction U p.tag) p.view i) (W*t) (mul_pos hw hv) (G.chord_nonneg _) ((ht.2.2 i rfl).1.le)
  · exact (ht.2.2 (i,0) rfl).2.1
  · exact (ht.2.2 i rfl).2.2
  change v.door p i=1; unfold Dyed.door; split
  next hx=> let y:=fundedB i hx; apply Next.SectorChange.broad_one _ hd
            have hu : ‖tape Z y‖ < firstRadius G:= ht.1 y rfl
            have hp': physical p.key p.park p.view p.y.1 (tape Z)=v.top p:=rfl
            have hZ : v.tapeAt p y=tape Z y:= by unfold Dyed.tapeAt; rw [mean_endpoint];rfl
            rw [hZ]; exact (he _ _ hp hM _ _ Z _ y ⟨p.tag,hp'.symm ▸ H'⟩ hu).trans hs
  rfl
where
  share_one (q : Chi) (r d : ℝ) (h : 0<d) (hr : 0≤r) (he : r≤d): q.innerShare d r=1:=q.to_one _ (by have hp := (div_le_one h).mpr he; have ht := div_nonneg hr h.le; nlinarith)
end YM.PhysicalNext.InteractingRank.Pump
