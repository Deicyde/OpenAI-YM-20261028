import YM.RemainderComparison.WickReps.Anchoring
import YM.RemainderComparison.Flues.Kettle
/-!
# Expose structural regular ledger (Probe α spectra, full marked loci).
 Explicit support & global scalars entries. Centered power-loss statements on Rough & analytics.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.WickReps
open Function Filter Lattice RG Pressure Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide Trio
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open YM.RemainderComparison.Aux Portal
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace

structure Manor (G:Gauge) (c:Side) (ι : Type) (α: Type*) (J : Type) where
   rooms : J→ RegularAddress c
   solvent : α→ J→ Config G c→ℝ
   marks : J→ Multiset ι
   /- whether scalar-valued completely DARK/material (pred evaluator no flag).
      Useful for preserving global contributions, their tests/mask alignment. -/
   total : J→ Prop

namespace Manor
variable {G:Gauge} {c : Side}{ι J J' ν θ:Type} {α:Type*} [DecidableEq θ]{C:Marker.Census θ}
variable (T:Manor G c ι α J)(P:BudgetPoint)(S: Set J)(a:α) (U:Config G c)
def halls (i:J):= (T.rooms i).support
def port (i:J):= (T.rooms i).site
lemma call (i:J) : T.port i∈T.halls i := (T.rooms _).anchor
def wet (i:J)(U:Config G c):ℝ:= if T.total i then T.solvent a i U else masked P.threshold (T.halls i) (T.solvent a i) U
open Mosaic Serif
variable (root:ι→Support c)(Z:Set ι) (z:ι→ Marker.Poly C)
def paint (a:α)(U:Config G c):J→Marker.Poly C:=fun i=> (↑(T.wet P a i U):ℂ) • Mosaic.Verse.controls Z z (T.marks i)
def basin (a:α)(U:Config G c): Marker.Poly C:= ∑' i:S,T.paint P Z z a U i.val

structure Sees (i:J): Prop where
    angle a : P.Regular (T.halls i) (T.solvent a i)
    travels a : Flues.apex root (T.halls i) (T.marks i) (T.wet P a i)
    stall a : T.total i →∀ V, T.solvent a i V=T.solvent a i 1

-- Pre-extraction, anchored at for-unmarked comparison. Vac costs q:in
structure Templary (root:ι→Support c)(P:BudgetPoint)(σ b:ℝ):Prop where
    grants : ∃ f:J→ℝ,(∀ i, 0≤ f i) ∧ (∀ i∈S,T.Sees P root i∧∀ a,P.supBounds (T.port i) (T.halls i) (T.solvent a i) (f i))∧ Footprint.Anchored T.port f (fun i=> coverNumber P.B (T.halls i)) σ b
-- Strong mark-root grant ALL x on paid supports, tests. Addresses can duplicate and names can map to same variables. Later states consume.
structure Spinal (root:ι→Support c)(P:BudgetPoint)(σ b:ℝ):Prop where
    grants : ∃ f:J→ℝ,(∀ i, 0≤ f i) ∧ (∀ i∈S,T.Sees P root i∧∀ a x,x∈ T.halls i→P.supBounds x (T.halls i) (T.solvent a i) (f i))∧ Ac.Hit T.halls P.B f σ b
variable {T P S root} {σ σ' b b' d:ℝ}{p: Set J}
variable {i:J}
lemma wet_le (h:T.Sees P root i) (hp:P.supBounds (T.port i) (T.halls i) (T.solvent a i) d): ‖T.wet P a i U‖ ≤ d:=by
    unfold wet; split
    next he=> rw [h.stall _ he]; apply hp.2 1 (by
       unfold Healthy; rw [smoky (P:=P) (show (1:Config G c) ∈ Boulevard.sunny P from (by intro i; simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read,posDir,negDir] using P.threshold_pos))]; simp) [] (List.length_nil ▸ (Nat.zero_le _)) (by simp)
    next=> exact CouplingShape.mask_cost hp U
lemma onView (h: Healthy P.threshold (T.halls i) U): T.wet P a i U= T.solvent a i U:= by
     unfold wet; split
     · rfl
     exact masked_eq _ _ _ _ h
lemma Stem {g : Config G c→ℝ} {o : Site c} {X:Support c}(hx:P.supBounds o X g b)(h : b ≤ d): P.supBounds o X g d:= ⟨hx.1.trans h,fun U hu v hv ht=> (hx.2 U hu v hv ht).trans h⟩
lemma chooseGr {w:J→ℝ}(hp:∀ i,0 ≤ w i)(h:Ac.Hit T.halls P.B w σ b): Footprint.Anchored T.port w (fun i=>coverNumber P.B (T.halls i)) σ b:=by
   intro x; refine budget_mono (h x) (fun i=>by split; exact mul_nonneg (hp i) (Real.exp_pos _).le; exact le_rfl) fun i=>?_
   split; next hh=> rw [if_pos (show x∈T.halls i from hh ▸ T.call i)]
   next=> exact (h x).1 i
lemma Spinal.templary (H:T.Spinal S root P σ b): T.Templary S root P σ b:=by obtain ⟨f,h,hp,hB⟩:=H.grants; exact ⟨f,h,fun i hi=>⟨(hp i hi).1,fun a=>(hp i hi).2 a _ (T.call i)⟩,chooseGr h hB⟩
lemma Spinal.skim (H:T.Spinal S root P σ b)(hs: p⊆ S)(he:b ≤ b')(ht:σ' ≤ σ): T.Spinal p root P σ' b':=by
    obtain ⟨f,h,hp,hh⟩:= H.grants; refine ⟨f,h,fun i hi=> hp i (hs hi),fun x=> budget_loosen (budget_mono (hh x) (fun i=>?_) fun i=>?_) he⟩
    · split; exact mul_nonneg (h _) (Real.exp_pos _).le; exact le_rfl
    split; next=>exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg _))) (h _)
    next=>rfl
lemma Spinal.swell (H:T.Spinal S root P σ b)(h:T.Spinal p root P σ b'): T.Spinal (S∪p) root P σ (b+b'):=by
    obtain ⟨f,hf,hG,hS⟩:=H.grants; obtain ⟨g,hg,hH,hS'⟩:=h.grants; refine ⟨fun i=> f i+g i,fun i=>add_nonneg (hf i) (hg i),fun i hi=>?_,RecursiveSecants079.BothSides.hit_plus hS hS'⟩
    rcases hi with hi|hi
    · exact ⟨(hG i hi).1,fun a x hx=> Stem ((hG i hi).2 a x hx) (le_add_of_nonneg_right (hg i))⟩
    exact ⟨(hH i hi).1,fun a x hx=> Stem ((hH i hi).2 a x hx) (le_add_of_nonneg_left (hf i))⟩
lemma Templary.skim (H:T.Templary S root P σ b)(hs: p⊆ S)(he:b ≤ b')(ht:σ' ≤ σ): T.Templary p root P σ' b':=by
    obtain ⟨f,h,hp,hh⟩:= H.grants; refine ⟨f,h,fun i hi=> hp i (hs hi),fun x=>budget_loosen (budget_mono (hh x) ?_ ?_) he⟩
    · intro i; split; exact mul_nonneg (h _) (Real.exp_pos _).le; exact le_rfl
    intro i; split; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg _))) (h _); exact le_rfl
lemma Templary.swell (H:T.Templary S root P σ b)(h:T.Templary p root P σ b'): T.Templary (S∪p) root P σ (b+b'):=by
    obtain ⟨f,hf,hG,hS⟩:=H.grants; obtain ⟨g,hg,hH,hS'⟩:=h.grants; refine ⟨fun i=> f i+g i,fun i=>add_nonneg (hf i) (hg i),fun i hi=>?_,fun x=>?_⟩
    · rcases hi with hi|hi
      · exact ⟨(hG i hi).1,fun a=> Stem ((hG i hi).2 a) (le_add_of_nonneg_right (hg i))⟩
      exact ⟨(hH i hi).1,fun a=> Stem ((hH i hi).2 a) (le_add_of_nonneg_left (hf i))⟩
    convert budget_plus (hS x) (hS' x) using 1; ext i; split<;> ring
lemma arrival {f:J→ℝ}(hv:Footprint.Anchored T.port f (fun i=>coverNumber P.B (T.halls i)) σ b)(h:∀ i,0≤ f i)(hz:0≤ σ): Summable f:=by
    let w i:= f i*Real.exp (σ*coverNumber P.B (T.halls i)); have hk : Summable w :=by
       have he (x:Site c): Summable (fun i=> if T.port i=x then w i else 0):=(hv x).2.1
       simpa only [Finset.sum_ite_eq,mem_univ, if_true] using! summable_sum (s:= (univ:Finset (Site c))) (fun i _=>he i)
    exact hk.of_nonneg_of_le h (fun i=> le_mul_of_one_le_right (h i) (Real.one_le_exp (mul_nonneg hz (by positivity))))
lemma standing {k:ℕ}{v:θ→ℝ}(hp:T.Templary S root P σ b)(hg: Chorus C v Z z k)(hz:0≤ σ): Summable (fun i:S=> T.paint P Z z a U i.val):=by
    obtain ⟨f,h,hF,hh⟩:= hp.grants; refine (Marker.Poly.budgeted hg.votes ((arrival hh h hz).subtype S) ?_).1; rintro ⟨i,hi⟩; unfold paint; rw [Marker.Poly.adapted,Complex.norm_real]; exact (mul_le_of_le_one_right (norm_nonneg _) (Serif.bought hg _)).trans (wet_le a U (hF _ hi|>.1) ((hF i hi).2 a)) -- T.wet_le namespace
end Manor
end YM.RemainderComparison.WickReps
