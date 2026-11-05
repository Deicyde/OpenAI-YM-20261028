import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Hard
import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.FiniteRange
import YM.AnalyticBridge.RESET_INCOME_PORT.Journal
import YM.Extra.MULTISOURCE_TRAJECTORIES.Sublayers
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Base

/-!
# Localization actually charged for the ratio chains, II

Full-address presentations and projection to the SAME sector data. Works
also for uses where output-flag tests are *only* matched locally: replace
bits away from the genuine price patch to EARN bounds, not in the
integrated quantity or its queries. The complete flagged/freezing/f0
support reads every instrument of `ReadsWithin` and the genuine `Y`
on that footprint; sector randomness still with its original law. Tree
and sector arguments may change OUTSIDE these registration disks. T,
its path data, all stage parameters fixed. Negative/junk terms do not
allow shrinkage of footprints in these currencies. Numerical use of
true source only at the purchased points of agreement; its jets on the
fixed good version in `Offset`, not on a threshold-straddling actual selector.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Folio
open Filter Function Set Lattice RG Wilson Pressure Precision Tree Matrix
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Wisps Schur Push.SectorMeasure Completion
open AnalyticBridge.NonflatCovarianceLocality
open AnalyticBridge.NonflatCovarianceLocality.Matching 
open AnalyticBridge.NonflatCovarianceLocality.Full (point groupWindow board aboard active_any cover_reads)
open AnalyticBridge.SectorAffine (Offset.b Offset.f0 Offset.mean Offset.fixedBase)
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {A B : Stores S} {F H : Forest S.ratio}
    {k k' : S.Choices} {V W Y : Config G c} {T : Tube G S} {P : Teller G} {x : ℝ} {o : Site c} {r : ℕ} {q : Chi} {d g : ℝ}

abbrev full_b (x : ℝ) (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (q : Chi) (d : ℝ) (Y : Config G f) (V : Config G c) :=
  (feature x T A F k V)ᵀ *ᵥ Offset.f0 T x A F k V q d (leaf A F x Y)
abbrev tray (x : ℝ) (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (V : Config G c) (k : S.Choices) := Schur.per (groupWindow G S x) (here x T A F V k)
abbrev clouds (x : ℝ) (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (V : Config G c) (k : S.Choices) := clouded (groupWindow G S x) (here x T A F V k)
abbrev gaps (x : ℝ) (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (V : Config G c) (k : S.Choices) := deviation (here x T A F V k) (clouds x T A F V k)
def full_m (x : ℝ) (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (q : Chi) (d : ℝ) (Y : Config G f) (V : Config G c) :=
  -(tray x T A F V k).transpose *ᵥ full_b x T A F k q d Y V



structure Bulletin (x : ℝ) (P : Teller G) (T : Tube G S) : Prop where
  priced : P.Funds S T
  geometry : 120 ≤ radiusB x
  rooms : enough S x ≤ 15*radiusB x ∧ extent S.patch x ≤ radiusB x/100
  apply_base A F V k : A.flags=RG.flags (temp x) V → Rows.restrict x (shots S x) A F (Offset.fixedBase T x V k) = Rows.restrict x (shots S x) A F (Rows.base T x V k)

lemma subscribe (P : Teller G) (H : Patch) : ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), P.Funds S T → S.patch=H → Bulletin x P T := by
  filter_upwards [local_extent H, AnalyticBridge.SectorAffine.Offset.correct_base G H P,
    Work.E01.radiusB_tendsto.eventually_ge_atTop 120] with x ⟨hx,_⟩ hb hv c f S T hP hS
  rw [← hS] at hx; change 2*span S.patch x ≤ _ at hx
  exact ⟨hP,hv,⟨by unfold enough; omega,hx⟩,fun A F V k he => hb S T hS hP A F V he k⟩

variable (b : Bulletin x P T)
namespace Bulletin
include b
lemma tray_local : Matching.Local (tray x T) (radiusB x/20) (mass x S) := by
  simpa only [panes_zero] using paned (accessible b.priced x) 0 b.geometry
lemma panes_shared (V : Config G c) (i j : In x A F (G:=G)) : tray x T A F V k (pointer A F i) (pointer A F j)=
    Schur.per (panels A F) (gramAt T x A F k V) i j := by
  simpa only [panes_zero] using! active_any x A F G b.geometry (u:=0) le_rfl (gramAt T x A F k V) i j
lemma clouds_shared (V : Config G c) (i j : In x A F (G:=G)) : clouds x T A F V k (pointer A F i) (pointer A F j)=fog A F T x V k i j := by
  exact congr_arg ((1/2:ℝ)*·) (congr_arg₂ (·+·) (b.panes_shared (k:=k) V i j) (b.panes_shared (k:=k) V j i))
end Bulletin

variable (T x A F V k)




variable {T x A F V k}
namespace Bulletin
include b

end Bulletin

section full
variable (q d) (Y₀ : Config G f)
lemma b_shared (i : In x A F (G:=G)) : full_b x T A F k q d Y₀ V (pointer A F i) = Offset.b T x k A F q d (leaf A F x Y₀) V i := by
  unfold Offset.b; exact Finset.sum_congr rfl (fun j _ => congr_arg (·*_) (side_active x T A F V k i j))
lemma b_null (i : vacant A F x G) : full_b x T A F k q d Y₀ V i.val = 0 := by
  rw [full_b,mulVec,dotProduct]
  exact Finset.sum_eq_zero fun j _ => by rw [transpose_apply,side_unused,zero_mul]

namespace Bulletin
include b
lemma m_shared (V : Config G c) (i : In x A F (G:=G)) : full_m x T A F k q d Y₀ V (pointer A F i) =
    AnalyticBridge.SectorAffine.Offset.mean T x k A F q d (leaf A F x Y₀) V i := by
  rw [full_m,Offset.mean,mulVec,dotProduct]; rw [← Equiv.sum_comp (sorted A F (G:=G) (x:=x)),Fintype.sum_sum_type]
  change _ + (∑ j:vacant A F x G, _ * full_b _ _ _ _ _ _ _ _ _ j.val) = _
  simp_rw [b_null,mul_zero,Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl; intro j _
  change -tray x T A F V k (pointer A F j) (pointer A F i) * full_b _ _ _ _ _ _ _ _ _ (pointer A F j) = _
  rw [b.panes_shared,b_shared]; rfl

end Bulletin
end full

variable {Y₀ Y₁ : Config G f}
section agreement
variable (hp : P.Funds S T) (h : ReadsWithin o r A B F H V W k k') (hY : AgreeNear S.ratio.parent o r Y₀ Y₁)
include hp h hY
lemma b_agrees (i : Index G f) (he : separation o (point S i)+enough S x+span S.patch x ≤ r) (q : Chi) (d : ℝ) :
    full_b x T A F k q d Y₀ V i = full_b x T B H k' q d Y₁ W i := by
  apply Finset.sum_congr rfl
  intro j _; dsimp only [Matrix.transpose_apply,Matrix.neg_apply]
  by_cases hx : separation (down S j) (point S i) ≤ span S.patch x
  · have ht := separation_triangle o (point S i) (down S j); rw [separation_comm] at hx
    rw [f0_agrees hp h Y₀ Y₁ hY j (by omega) q d,h.feature_eq hp j (by unfold enough at *; omega)]
  rw [feature_range (funds_branch hp) A j i hx, feature_range (funds_branch hp) B j i hx, zero_mul,zero_mul]
end agreement

abbrev shiftR (S : StepData c f) (x : ℝ) := mass x S + enough S x + span S.patch x + radiusB x/20
abbrev settleR (x : ℝ) := 36 * radiusB x
abbrev padR (x : ℝ) := 40 * radiusB x
namespace Bulletin
include b
lemma clearance_size : shiftR S x + extent S.patch x ≤ settleR x := by
  have h₀ := b.rooms.1; have he := b.rooms.2; unfold shiftR mass Matching.room settleR extent at *; unfold enough at *; omega
variable (h : ReadsWithin o r A B F H V W k k') (hY : AgreeNear S.ratio.parent o r Y₀ Y₁)
include h hY
lemma m_agrees (i : Index G f) (he : separation o (point S i)+shiftR S x ≤ r) (q : Chi) (d : ℝ) :
    full_m x T A F k q d Y₀ V i = full_m x T B H k' q d Y₁ W i := by
  apply Finset.sum_congr rfl; intro j _; dsimp only [Matrix.transpose_apply,Matrix.neg_apply]
  by_cases hn : separation (point S j) (point S i) ≤ radiusB x/20
  · have ht := separation_triangle o (point S i) (point S j); rw [separation_comm] at hn
    rw [(b_agrees b.priced h hY j (by unfold shiftR at he; omega) q d),
      (b.tray_local.both h i (by unfold shiftR at he; omega) j).2]
  simp [b.tray_local.far A F V k j i hn, b.tray_local.far B H W k' j i hn]

end Bulletin
end YM.PhysicalNext.JointLoad.Folio
