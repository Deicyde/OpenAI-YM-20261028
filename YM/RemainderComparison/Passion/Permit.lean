import YM.RemainderComparison.Passion.Prisms
import YM.RemainderComparison.Solos.Huts
import YM.RemainderComparison.Solos.Heaven
/-!
# Drawing from all stars

This class takes only *one* valuation of each test when feeding physical push;
retains names and supports for arbitrary further test use. θ names of one or
several physical slots including addresses. Remove dead choices on labels with
proof. No resumming disconnected columns. Positive mark grants only; unmarked
sector has already gone into the Riss photon.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Passion
open Function Filter Set Finset Lattice RG Wilson MeasureTheory Push Push.AbsoluteSums Marker
open Solos Mosaic Verse Serif Flues WickReps Ethereal Lacuna Lobby
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {θ ι:Type}{D :ι→ Finset θ}{Q:θ→Type*} [∀ i,NormedAddCommGroup (Q i)][∀ i,NormedSpace ℝ (Q i)]
variable {G:Gauge}{n:Side}{I:Type} [Countable I]
variable (T:Manor G n ι (Audited Q) I)(p:BudgetPoint)(R:ι→Support n)(Z:Set ι)
def legitim (i:I) := ∀ k∈ T.marks i,R k ⊆ T.halls i
def crewK (D:ι→Finset θ) := {i:↥(night T Z)ᶜ | (mapWord D (T.marks i.val)).Nodup ∧ legitim T R i}
abbrev Roll (D:ι→Finset θ):= ↥(crewK T R Z D)
variable (b:Roll T R Z D)
set_option quotPrecheck false
local notation "Q₀"=> (mapWord D (T.marks b.val.val)).toFinset
-- Initial (possibly non-MAIN yet)
def stem (b:Roll T R Z D): Audited Q→ Config G n →ℝ:= Solos.lyric (fun x=> T.solvent x b.val.val) ((mapWord D (T.marks b.val.val)).toFinset)
local notation "L'"=> stem T R Z b
variable {σ h:ℝ}
omit [Countable I]
structure Precepts (D:ι→Finset θ) (σ h :ℝ): Prop where
   funds : T.Spinal (night T Z)ᶜ R p σ h
   lineage : Angel D p T (night T Z)ᶜ
variable (hp: Precepts T p R Z D σ h)
include hp
local notation "I'"=> b.val.val
lemma current : ∀ x, Healthy p.threshold (T.halls I') x→ ∀ᶠ v in 𝓝 x, LinearP ((mapWord D (T.marks I')).toFinset) fun i=> T.solvent i I' v:= fun x h=> (hp.lineage.wink I' b.val.prop x h).mono fun _ h=> h b.prop.1
lemma holds (q:Audited Q) : p.Regular (T.halls I') (L' q):=
    Solos.epode _ _ _ _ (hp.funds.grants.choose_spec.2.1 _ b.val.prop|>.1.angle) _ (current T p R Z b hp)
lemma onNote (i:Audited Q) (V:Config G n)(h:Healthy p.threshold (T.halls I') V) : L' i=ᶠ[𝓝 V] T.solvent i I':= Solos.sung _ _ _ _ _ _ (current T p R Z b hp) h -- term

open PhysicalNext.Repeat Boulevard
lemma absolute (i:Audited Q)(he:T.total I')(V:Config G n): L' i V=T.solvent i I' 1:=by
    have hf:= (hp.funds.grants.choose_spec.2.1 _ b.val.prop).1.stall
    have hk(V:Config G n) : LinearP Q₀ (fun j=> T.solvent j I' V):=by
         rw [funext (show ∀ j:Audited Q,T.solvent j I' V=T.solvent j I' 1 from fun j=>hf j he V)]; apply (current T p R Z b hp 1 ?_).self_of_nhds
         unfold Healthy; rw [Boulevard.smoky (P:=p) (show (1:Config G n)∈ Boulevard.sunny p from by intro i; simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read,posDir,negDir] using p.threshold_pos)]; simp
    unfold stem Solos.lyric Solos.promise; rw [Set.indicator_of_mem (mem_interior_iff_mem_nhds.mpr ?_)]
    · exact hf i he V
    exact (Eventually.of_forall hk : ∀ᶠ x in 𝓝 _,LinearP _ _ )
lemma masked_sound (i:Audited Q)(h: ¬ T.total I'):
     T.wet p i I'= masked p.threshold (T.halls I') (L' i):=by
    ext V; unfold Manor.wet; rw [if_neg h]; by_cases he: Healthy p.threshold (T.halls I') V
    · rw [masked_eq _ _ _ _ he, masked_eq _ _ _ _ he]; exact (onNote T p R Z b hp i V he).self_of_nhds.symm
    rw [masked_ne _ _ _ _ he,masked_ne _ _ _ _ he]
variable [DecidableEq θ] {J:Census θ} (z:ι→Poly J)(hx:Passion.Oriented D J Z z)
include hx
lemma dead (i:Audited Q)(V:Config G n)(x:↑(night T Z)ᶜ)(ht:x∉ crewK T R Z D): T.paint p Z z i V x.val=0:=by
    unfold Manor.paint; by_cases hl:(mapWord D (T.marks x.val)).Nodup
    · have he : ¬ legitim T R x.val:=fun h=>ht ⟨hl,h⟩; unfold legitim at he; push Not at he
      obtain ⟨a,ha,hN⟩:=he; have hz:= hp.funds.grants.choose_spec.2.1 x.val x.prop; rw [show T.wet p i x.val V=0 from Classical.byContradiction (fun hh=> hN ((hz.1.travels i) a ha V hh))]; simp
    rw [Passion.silence hx _ hl,smul_zero]
lemma marches (i:Audited Q)(V:Config G n) : day J Z T p z i V= ∑' j : Roll T R Z D, T.paint p Z z i V j.val.val := by
    symm; refine tsum_subtype_eq_of_support_subset (f:=fun j:↑(night T Z)ᶜ=> T.paint p Z z i V j.val) (fun j h=> ?_); by_contra ht; exact h (dead T p R Z hp z hx i V j ht)
omit hx
open Flues Manor
omit [DecidableEq θ] in
lemma visits : ∃ f: Roll T R Z D→ℝ, (∀ i, 0≤ f i) ∧ Ac.Hit (fun i:Roll T R Z D=> T.halls i.val.val) p.B f σ h ∧ ∀ i a x,x∈ T.halls i.val.val → p.supBounds x (T.halls i.val.val) (stem T R Z i a) (f i):=by
    obtain ⟨f,hf,hH,hV⟩:= hp.funds.grants; let F i:= (i: Roll T R Z D).val.val
    refine ⟨f∘F,fun _=> hf _,fun i=>?_,fun i a x h=>?_⟩
    · exact budget_pull F ((Subtype.val_injective (p:=fun j=> j∈ (night T Z)ᶜ)).comp Subtype.val_injective) (hV i)
    exact Solos.poet _ _ _ _ _ (current T p R Z i hp) ((hH _ i.val.prop).2 _ _ h)
end YM.RemainderComparison.Passion
