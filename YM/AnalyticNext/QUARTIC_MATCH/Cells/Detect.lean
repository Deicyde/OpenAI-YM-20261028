import YM.AnalyticNext.QUARTIC_MATCH.Cells.Per
import YM.AnalyticNext.QUARTIC_MATCH.Multiples
import YM.Next.FREE_KERNELS.Bank
import YM.Org.Theatre
import YM.Work.B04



/-!
# Read convergent periodisations

No inductive forcing of tree paths on nonrelated periods. Detect exact Laurent
identities from compatible ALL admitted periods. Absolute sums include repeated
arguments.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.BoxChain
open Lattice Exterior Function Finset Topology Laurent Filter Sheets
open scoped Topology BigOperators

variable {V : Type} [NormedAddCommGroup V]
variable {I : Type} [Fintype I] (i : I) {A : ArrayC I ℤ V} {σ C : ℝ}

section detect

/-- Common space to test whether a kernel reads zero from a schedule of
unbounded periods. -/
def flatDeck {I : Type} (i : I) : Set (I → Cover) := {w|w i=0}

variable [CompleteSpace V]

theorem fixed (h : Pricing A σ C) {ι : Type} (n : ι→Side) {f : Filter ι} (hn : Tendsto (fun i => (n i).val) f atTop)
    (X : I → Cell ℤ) : Tendsto (fun j => scene (n j) i A (tor (n j) ∘ X)) f (𝓝 (A X)) := by
  classical
  let T j (w : I→Cover) := ((sheets (n j) i : Set _) : Set _).indicator (fun w => A (sway w X)) w
  let H (w : I→Cover) := if w=(0 : I→Cover) then A X else 0
  have hg (w : I→Cover) : Tendsto (fun j => T j w) f (𝓝 (H w)) := by
    by_cases e : w=(0:I→Cover)
    · subst w
      have he j : T j 0=A X := by simp [T,show sway 0 X=X by funext i; simp [sway,move]]
      simp only [he,H,if_pos rfl]; exact tendsto_const_nhds
    apply Filter.EventuallyEq.tendsto
    obtain ⟨k,hv⟩ := Function.ne_iff.mp e
    filter_upwards [Next.Free.eventually_unfold n hn (w k)] with j hj
    have hp : w∉(sheets (n j) i : Set _) := by
      intro hz; have hm := sheet_wrap (n j) i ⟨w,hz⟩ k
      change wrap _ _ = 0 at hm; rw [hm] at hj
      apply hv; change w k=0; rw [← hj]; ext a; simp [lift]
    unfold T H; rw [Set.indicator_of_notMem hp,if_neg e]
  let D w := (flatDeck i).indicator (fun w : I→Cover => ‖A (sway w X)‖) w
  have hs : Summable D := by
    -- sum only the relative placements
    change Summable ((flatDeck i).indicator _)
    apply (summable_subtype_iff_indicator).mp
    let U (w : flatDeck i) (j : I) := (sway w.val X j).1-(sway w.val X i).1
    have hz (w : flatDeck i) (j) : U w j=(X j).1+w.val j-(X i).1 := by
      unfold U; simp [move,sway]; exact w.property
    have he : Injective U := fun x y H => Subtype.ext <| funext fun j => by simpa only [hz,sub_left_inj,add_right_inj] using congr_fun H j
    refine Summable.of_nonneg_of_le (fun w : flatDeck i => norm_nonneg (A (sway w.val X))) (fun w => pricing_anchor h i _) ?_
    exact ((pays_all (I:=I) (positive_rate h.rate i)).2.1.mul_left C).comp_injective he
  have hp : ∀ j w, ‖T j w‖≤D w := by
    intro j w; unfold T D
    by_cases H : w ∈ (sheets (n j) i : Set _)
    · rw [Set.indicator_of_mem H, Set.indicator_of_mem (show w∈flatDeck i from sheet_here (n j) i ⟨w,H⟩)]
    rw [Set.indicator_of_notMem H, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) _
  have ht := tendsto_tsum_of_dominated_convergence hs hg (Eventually.of_forall hp)
  have hz j : (∑' w : I→Cover,T j w)=scene (n j) i A (tor (n j) ∘ X) := by
    rw [scene_tor _ _ h.same]; exact (_root_.tsum_subtype (sheets (n j) i : Set _) (fun w => A (sway w X))).symm
  simp_rw [hz,show (∑' w : I→Cover,H w)=A X by simp [H]] at ht; exact ht
end detect

section mates
omit [Fintype I]
variable {c d : Side} (h : c.val∣d.val)
def upperDeck : AddSubgroup (I → Site d) where
  carrier := {F | (∀ j, project h (F j)=0) ∧ F i=0}
  zero_mem' := by simp
  add_mem' := fun {a b} ⟨ha,ht⟩ ⟨hb,hm⟩ => by simp [ha,ht,hb,hm]
  neg_mem' := fun {a} ⟨ha,ht⟩ => by simp [ha,ht]

/-- Given larger-torus shifts, place in the standard representative nearest the
chosen anchor for each relative coordinate. -/
def pointDown (q : sheets c i) : ↥(upperDeck i h) :=
    ⟨fun j => wrap d (q.val j), by
      refine ⟨fun j => ?_,?_⟩
      · rw [project_wrap, sheet_wrap]
      change wrap d _=0; rw [sheet_here,map_zero]⟩

def distanceL (X : I → Cell ℤ) (w : sheets c i) := fun j => (X j).1+w.val j-(X i).1
lemma distanceS (X : I → Cell ℤ) (w : sheets c i) (j : I) :
    (sway w.val X j).1-(sway w.val X i).1=distanceL i X w j := by simp [sway,move,distanceL,sheet_here]
lemma distanceI (X : I → Cell ℤ) : Injective (distanceL (c:=c) i X) := by
  intro w v h; refine Subtype.ext (funext fun j => ?_)
  simpa [distanceL] using congr_fun h j

def short (c d : Side) (X : I → Cell ℤ) (w : sheets c i) :=
    ∀ j, lift (wrap d (distanceL i X w j))=distanceL i X w j

def pointUp (X : I→Cell ℤ) (v : upperDeck i h) : sheets c i := by
  let dX j := (X j).1-(X i).1
  let R j := wrap d (dX j)+v.val j
  let U j := lift (R j)-dX j
  refine ⟨U,?_⟩
  refine ⟨fun j => ?_,?_⟩
  · unfold U
    rw [map_sub, ← Sheets.project_wrap h,wrap_lift]
    unfold R; rw [map_add, show project h _=0 from (v.property.1 j),project_wrap,add_zero,sub_self]
  change lift _ - _ = _
  rw [show dX i=0 from sub_self _, show R i=0 from ?_]
  · ext k; simp [lift]
  simp only [R,dX,sub_self,map_zero,zero_add]; exact v.property.2

lemma ones (X : I→Cell ℤ) (v : upperDeck i h) (j : I) : wrap d ((pointUp i h X v).val j)=v.val j := by
  change wrap d (lift (_+ v.val j)- _)=_
  rw [map_sub,wrap_lift]; abel
lemma once (X : I→Cell ℤ) (v : upperDeck i h) : pointDown i h (pointUp i h X v) = v :=
  Subtype.ext (funext fun j => ones i h X v j)
lemma in_front (X : I→Cell ℤ) (v : upperDeck i h) : short i c d X (pointUp i h X v) := by
  intro j
  let x := lift (wrap d ((X j).1-(X i).1)+v.val j)
  rw [show distanceL i X (pointUp i h X v) j=x from ?_,wrap_lift]
  change (X j).1+(x-((X j).1-(X i).1))-(X i).1=_; abel
lemma redo (X : I→Cell ℤ) (v : sheets c i) (hp : short i c d X v) : pointUp i h X (pointDown i h v)=v := by
  apply distanceI i X; funext j
  rw [← hp j, ← in_front i h X (pointDown i h v) j]
  unfold distanceL; congr 1; rw [map_sub,map_add,ones]
  change _ = wrap d (_ + _ - _); rw [map_sub,map_add]; rfl

def signpost (X : I→Cell ℤ) : ↥(upperDeck i h) ≃ {v : sheets c i // short i c d X v} where
  toFun v := ⟨pointUp i h X v,in_front i h X v⟩
  invFun v := pointDown _ h v.val
  left_inv := once i h X
  right_inv v := Subtype.ext (redo i h X v.val v.property)
end mates
end YM.AnalyticNext.QuarticMatch.BoxChain
