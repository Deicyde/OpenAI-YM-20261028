import YM.AnalyticBridge.RESET_INCOME_PORT.Slips
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Registration
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Museum
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Quaver

/-!
# Recovering the locally predicted shift and law on E's prior support

Before AND after-output masking, on separate uses. No frozen argument
from the surrounding sector dropped inside E. It doesn't enter these reads
at all. Distribution and model equalities proved at one corner of the
same sector **jointly over indices** (subarray of the covariance, not a
subarray of the precision). Includes the comparison with a full true-flag
record whenever purchasing further operator estimates at a PARTIAL sector.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Lattice Wilson Pressure RG Tree Next Next.SectorChange Next.SectorChange.Rows Wisps
    Precision Next.Fluctuations Exterior Bloch Bid AnalyticBridge.LocalGaussianLaws Push.SectorMeasure
    AnalyticBridge.NonflatCovarianceLocality AnalyticBridge.NonflatCovarianceLocality.Matching AnalyticBridge.NonflatCovarianceLocality.Placement
open AnalyticBridge.SectorAffine (Offset.mean Offset.b reader_field)
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {o : Site f} {p : Site c} {S : StepData c f} {A : Stores S} {F : Forest S.ratio} {I : Type}
    {x : ℝ} {X : Support f} {Y : Support c} {V W : Config G c} {k : S.Choices} {P : Teller G} {T : Tube G S} {q : Chi} {d u : ℝ}

namespace Museum
variable (T) (M : Museum F x A X Y I) (k)

abbrev twilight (V : Config G c) := (fog A F T x V k).submatrix (M.colorSeat G) (M.colorSeat G)
abbrev bareSeat (i : Active A x F) : clear S x F := ⟨i.val, notChilled S F x _⟩

variable [Fintype I] (q d u)

def deposited (V : Config G c) (U : Config G f) (z : Prices G I) (i : Active A x F) :=
  (tape (Offset.mean T x k A F q d (Folio.leaf A F x U) V)) i + u • (Function.extend M.seat (tape z) 0 i)
def received (V : Config G c) (U : Config G f) (z : Prices G I) :=
  physical A F V (Folio.leaf A F x U) (M.deposited k T q d u V U z)

variable {T k q d u} (b : Folio.Bulletin x P T)
include b M
omit [Fintype I] in
lemma bare_read (h : Station Y x p) (he : AgreeNear id p (reach x) V W) (i : Active A x F) (hi : separation p (S.ratio.parent i.val.val.1) ≤ 7*(1+radiusB x))
    (j : G.ColorIndex) (U : Config G f) :
    Offset.mean T x k A F q d (Folio.leaf A F x U) V (i,j) = Offset.mean T x k (bareStores S) F q d (Folio.leaf (bareStores S) F x U) W (bareSeat i,j) := by
  simp_rw [← b.m_shared]; apply b.m_agrees (M.reads_bare h he k) (fun _ _ => rfl) (i.val.val,j)
  have hh := b.clearance_size; change separation p (S.ratio.parent i.val.val.1)+_≤_; unfold Folio.settleR at hh; unfold reach; omega
omit [Fintype I] in
lemma near_forecast (h : Station Y x p) (v : Directions G c) (he : AgreeNear id p (reach x) V (increment 1 v)) (i : Active A x F) (hi : separation p (S.ratio.parent i.val.val.1) ≤ 7*(1+radiusB x)) (U : Config G f) :
    tape (Offset.mean T x k A F q d (Folio.leaf A F x U) V) i = expandBare F x (forecast T x F k v) i.val.val := by
  ext j; rw [forecast,Function.comp_apply,school_eq b.priced F x k q d (Folio.leaf (bareStores S) F x U),reader_field]
  have heq : ∀ v, expandBare (G:=G) F x v i.val.val = gaugeCount v (bareSeat i) := fun v => by change awaken _ _ _ _ = _; rw [awaken,dif_pos i.val.property]
  rw [heq]; exact M.bare_read b h he i hi j U
omit [Fintype I] in
lemma seat_mean (hi : Agrees Y V W) (i : I) (U U' : Config G f) :
    tape (Offset.mean T x k A F q d (Folio.leaf A F x U) V) (M.seat i) = tape (Offset.mean T x k A F q d (Folio.leaf A F x U') W) (M.seat i) := by
  let o := S.ratio.parent (M.address i).1
  have h : Station Y x o := (Corona.halo_mono (Nat.le_add_right ..) (Finset.Subset.refl _)).trans (M.stores i)
  have he : AgreeNear id o (reach x) V W := by
    intro j hj; refine hi j (h (halo_spec.mpr ⟨_,Finset.mem_singleton_self _,hj⟩))
      (M.stores i (halo_spec.mpr ⟨_,Finset.mem_singleton_self _,?_⟩))
    change separation o j.1 ≤ _ at hj; change separation o _ ≤ _; have he := separation_triangle o j.1 (j.1+step j.2); have hh := Work.E03.sep_step j.1 j.2; omega
  ext j
  have hf : Folio.leaf (bareStores S) F x U=Folio.leaf (bareStores S) F x U' := funext (fun k => (notChilled S F x k.val k.property).elim)
  change Offset.mean .. = Offset.mean ..
  rw [M.bare_read b h he (M.seat i) (show separation o o ≤ _ by simp),M.bare_read b h (V:=W) (fun _ _ => rfl) (M.seat i) (show separation o o ≤ _ by simp),hf]

lemma variations (hi : Agrees Y V W) (U U' : Config G f) (z : Prices G I) : Agrees (inspected X) (M.received k T q d u V U z) (M.received k T q d u W U' z) := by
  intro e he hj
  have h₁ p (hp : p∈inspected X) : S.ratio.parent p∈Y := M.asks p hp (halo_subset _ _ (Finset.mem_singleton_self _))
  have he' : replica S.ratio V e = replica S.ratio W e := by
    unfold replica; split; · rfl
    next h =>
    have he := Ratio.parents_hop S.ratio S.patch.odd_side e.1 e.2; split at he
    · exact hi _ (h₁ _ ‹e.1 ∈ (↑(inspected X) : Set _)›) (he ▸ (h₁ _ hj))
    · exact (h he).elim
  unfold received physical SectorChange.returned thaw
  by_cases ht : e∈F.trunks
  · exact (F.on_tree _ ⟨e,ht⟩).trans (F.on_tree _ ⟨e,ht⟩).symm
  let a : Active A x F := ⟨⟨e,ht⟩,M.admits he hj⟩
  change F.drape _ a.val.val=F.drape _ a.val.val
  rw [F.off_tree,F.off_tree, freeze_regular,freeze_regular]; obtain ⟨j,hj'⟩ := M.covers a he hj
  unfold release deposited
  have h := M.seat_mean (k:=k) (q:=q) (d:=d) b hi j U U'
  rw [hj'] at h
  rw [h]; exact congr_arg (_*·) he'

omit [Fintype I] in
lemma m_actual (h : Healthy (temp x) Y V) (U : Config G f) (i : I) :
    tape (Offset.mean T x k A F q d (Folio.leaf A F x U) V) (M.seat i) = tape (meanLog A F T x V k q d (Folio.leaf A F x U)) (M.seat i) := by
  ext j; exact b.m_correct (M.relays h i) _ (M.seat i,j) (by rw [show front A F (M.seat i,j)=S.ratio.parent (M.address i).1 from rfl,separation_self]; have he := b.clearance_size; unfold Folio.settleR at he; unfold reach; omega)

lemma masked_reads (h : Healthy (temp x) Y V) (U : Config G f) (z : Prices G (Active A x F)) : Agrees (inspected X) (M.received k T q d u V U (z ∘ M.colorSeat G))
    (physical A F V (Folio.leaf A F x U) (displaced (meanLog A F T x V k q d (Folio.leaf A F x U)) u z)) := by
  intro e he hj; unfold received physical SectorChange.returned thaw
  by_cases ht : e∈F.trunks
  · exact (F.on_tree _ ⟨e,ht⟩).trans (F.on_tree _ ⟨e,ht⟩).symm
  let a : Active A x F := ⟨⟨e,ht⟩,M.admits he hj⟩
  change F.drape _ a.val.val=F.drape _ a.val.val
  rw [F.off_tree,F.off_tree, freeze_regular,freeze_regular]; obtain ⟨j,hj⟩ := M.covers a he hj
  rw [← hj,release,release,deposited,M.seat.injective.extend_apply,M.m_actual b h U j]
  rfl

omit [Fintype I] in
private lemma twilight_read {i j : I × G.ColorIndex} {A' : Stores S} (i' j' : Active A' x F) (hi : M.address i.1 = i'.val.val) (hj : M.address j.1=j'.val.val)
    (h : ReadsWithin (S.ratio.parent i'.val.val.1) (reach x) A A' F F V W k k) : twilight k T M V i j = fog A' F T x W k (i',i.2) (j',j.2) := by
  have he := (cloud_local b.priced b.geometry).both h (i'.val.val,i.2) (by change separation _ (S.ratio.parent i'.val.val.1)+_≤_; rw [separation_self]; unfold reach; have hh := b.clearance_size; unfold Folio.shiftR Folio.settleR at hh; omega) (j'.val.val,j.2) |>.1
  change fog A F T x V k (M.colorSeat G i) (M.colorSeat G j)=_; rw [← b.clouds_shared,← b.clouds_shared]
  change Folio.clouds x T A F V k (M.address i.1,i.2) (M.address j.1,j.2) = _; rw [hi,hj]; exact he
omit [Fintype I] in
lemma twilight_local (h : Agrees Y V W) : twilight k T M V=twilight k T M W := by
  ext i j
  apply twilight_read M b (M.seat i.1) (M.seat j.1) rfl rfl
    (Folio.postal_receipt (A:=A) (B:=A) ⟨h,(fun _ _ => Iff.rfl),(fun _ _ => Iff.rfl),(fun _ _ => Iff.rfl), (fun _ _ => rfl),(fun _ _ => rfl),(fun _ _ => rfl)⟩ (M.stores _))

omit [Fintype I] in
lemma twilight_price (h : Healthy (temp x) Y V) : twilight k T M = fun W =>
    (fog (amended x A V) F T x W k).submatrix ((M.forwarded V h).prodMap (Embedding.refl G.ColorIndex)) ((M.forwarded V h).prodMap (Embedding.refl G.ColorIndex)) := by
  funext W; ext i j
  exact M.twilight_read b _ _ rfl rfl (Folio.completion_reads (M.relays h _) F k W)
end Museum
end YM.PhysicalNext.JointLoad.Heir
