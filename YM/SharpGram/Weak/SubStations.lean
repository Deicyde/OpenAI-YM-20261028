import YM.SharpGram.Weak.Inspect
import YM.Next.UV_STRESS.Vary
/-! Choose REAL labels of subsequential limits of the FULL microscope matrix
for each D,k. On arbitrary common ultrafilter; retains orientation & unit,
not asserting no further null relation. Not shrinking a cut filter inside the
proof of one read. -/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Weak
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage MergeProof MergeProof.East
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{d n D k N p m:ℕ} {ι:Type} {H:C.Makes}
  {P:ι → Tapes.Panel D} {B:Binding C}{O:HaarBudget G}{J:ChartRatio G}{z:ℝ}
local notation "A" => C.path.levels
local notation "S"=> standard C
open Analysis Next.UVStress Climb Ward
variable (b : ℝ)
variable (φ : Ultrafilter (ℕ × ℕ))
set_option quotPrecheck false
local notation "φ'" => (φ : Filter (ℕ × ℕ))
variable {Y : ℕ → ℕ → TableL C D} {f : Extraction.Order}
  (hp : Poised P B H O J n z k Y) (hf : (φ : Filter (ℕ × ℕ)) ≤ f.fuse)

lemma alongUltra {α : Type} {X : Type*} [NormedAddCommGroup X][ProperSpace X]
    (φ : Ultrafilter α) (v : α → X) (r : ℝ) (h : ∀ᶠ i in φ, ‖v i‖ ≤ r) :
    ∃ x, Tendsto v (φ : Filter α) (𝓝 x) := by
    obtain ⟨u,hu,H,x,hx⟩:= finite_extract v r h
    exact ⟨x, (φ.unique hu H) ▸ hx⟩
include H hp hf
lemma framesBounded (d : Fin (D+1)) (x : C.label d) :
    ∃ P : ℝ, ∀ᶠ i in φ, ‖microscope C b k Y d i x‖ ≤ P := by
  obtain ⟨P,hP⟩:= sun H (hp.early d (Nat.le_of_lt_succ d.isLt)) (mag A b k) x
  exact ⟨P, (((Push.RelayDifference.cutoff_grows f).mono_left hf).eventually_gt_atTop k).mono
    fun i hi=> hP i.1 i.2 (Y i.1 i.2 d) (show k ≤ i.1 from hi.le) (hp.charts i.1 i.2 hi d).1⟩

def SubLimits (C : Family G) (D k : ℕ) (b : ℝ) (q : Filter (ℕ × ℕ)) (Y : ℕ → ℕ → TableL C D)
    (Z : TableL C D) := ∀ d : Fin (D+1), ∀ x : C.label d, Tendsto (fun i => microscope C b k Y d i x) q (𝓝 (Z d x))
lemma subChoices : ∃ Z : TableL C D, SubLimits C D k b φ' Y Z := by
  have ht (d : Fin (D+1))(x : C.label d) : ∃ y, Tendsto (fun i => microscope C b k Y d i x) φ' (𝓝 y) := by
    obtain ⟨c,hc⟩ := framesBounded b φ hp hf d x
    exact alongUltra φ _ c hc
  choose y hy using ht
  let Z (d : Fin (D+1)) : Module.End ℂ (C.label d) :=
    { toFun := y d
      map_add' := fun x v=> tendsto_nhds_unique_of_eventuallyEq (hy d (x+v)) ((hy d x).add (hy d v))
        (Eventually.of_forall fun _ => map_add ..)
      map_smul' := fun c x=> tendsto_nhds_unique_of_eventuallyEq (hy d (c•x)) ((tendsto_const_nhds (x:=c)).smul (hy d x))
        (Eventually.of_forall fun _ => map_smul ..) }
  exact ⟨Z, hy⟩

section orientation
omit hp hf H
variable {φ b} {T : Table C.book} (U : Spec.Final C f T) {Z : TableL C D} {u : Filter (ℕ × ℕ)} [u.NeBot]
  (hF : u ≤ f.fuse) (hZ : SubLimits C D k b u Y Z)
include hF hZ hp U H
local notation "σ"=> U.room.kernel.spin

lemma commutesTurn (s : Signed) (d : Fin (D+1)) (x : C.label d) :
    T.project d (Z d (C.book.mirrorGroup d s x)) = T.mirror σ d s (T.project d (Z d x)) := by
  rw [T.mirror_project]; apply congr_arg
  apply tendsto_nhds_unique_of_eventuallyEq (hZ d (C.book.mirrorGroup d s x))
    ((C.book.mirrorGroup d s).continuous_of_finiteDimensional.continuousAt.tendsto.comp (hZ d x))
  exact (((Push.RelayDifference.cutoff_grows f).mono_left hF).eventually_gt_atTop k).mono
    fun i hi => rider H (hp.early d (Nat.le_of_lt_succ d.isLt)) (Nat.le_of_lt hi) _ _
      (hp.charts i.1 i.2 hi d).1 (hp.charts i.1 i.2 hi d).2 s _
lemma realStar (d : Fin (D+1)) (x : C.label d) :
    T.project d (Z d (star x)) = T.conj σ d (T.project d (Z d x)) := by
  rw [T.conj_project]; apply congr_arg
  apply tendsto_nhds_unique_of_eventuallyEq (hZ d (star x)) (hZ d x).star
  exact (((Push.RelayDifference.cutoff_grows f).mono_left hF).eventually_gt_atTop k).mono
    fun i hi=> purer H (hp.early d (Nat.le_of_lt_succ d.isLt)) (Nat.le_of_lt hi) _ _ (hp.charts i.1 i.2 hi d).1 _
omit U in
lemma constant (d : Fin (D+1)) : Z d (C.labels.level d).e0 = C.refUnit d := by
  apply tendsto_nhds_unique_of_eventuallyEq (hZ d (C.labels.level d).e0) tendsto_const_nhds
  exact (((Push.RelayDifference.cutoff_grows f).mono_left hF).eventually_gt_atTop k).mono
    fun i hi=> pure_start H (hp.early d (Nat.le_of_lt_succ d.isLt)) (Nat.le_of_lt hi) _ _ (hp.charts i.1 i.2 hi d).1
lemma lendsAdj (d : Fin (D+1)) (x : C.label d) :
    T.project d (Z d (C.book.adj d timeAxis x)) = T.adj σ d timeAxis (T.project d (Z d x)) := by
  simp only [Register.adj,Table.adj,LinearMap.comp_apply,Register.bar_apply]
  rw [commutesTurn hp U hF hZ _,realStar hp U hF hZ]
end orientation
end YM.SharpGram.Weak
