import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Funnel
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.Push.PRICE_COMPILER.Suppression

set_option warningAsError false

/-!
# Summing tangent readings on the actual coefficient alphabet
No exchanging unconditioned multi-body draws or densities. Compile to
linear evaluation at each config incl the constrained gas (possible
finite volume cost! use differently for attenuation). `Pack` trick after
B70Connected: press same zone & inventory WITH actual values and flags,
regardless how many indices share them.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource
open Function Filter MeasureTheory RG Wilson Lattice Labels Source
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open Body Multi Push.RelayDifference
variable {G : Gauge} {n : Side} {e : ℕ} {F : Frame G e} {R : Rep G n} {o : Site n}
variable {U : GridU n} {κ r : ℝ}

section
variable (R) (x : Config G n)

def porter (C : SectionData F) (o : Site n) : F.Coeff →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    { toFun v := v 0 + masked R.p.threshold (C.footprint o)
                (C.places (F.scaled R.p.threshold⁻¹ (F.core v)) o) x
      map_add' v w := by
        by_cases hh : Healthy R.p.threshold (C.footprint o) x <;> simp [hh,SectionData.places,SectionData.evaluate]; ring
      map_smul' z v := by
        by_cases hh : Healthy R.p.threshold (C.footprint o) x <;> simp [hh,SectionData.places,SectionData.evaluate]; ring }

def punch : (Multi.Pack n → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    { toFun v := (Real.exp (R.exponent x):ℂ) * ∑ b∈Multi.Pack.clears (flags R.p.threshold x),
          ∑ i∈b,v i * ∏ k∈b.erase i, Multi.incumbent R x k
      map_add' := by intros; simp [add_mul,Finset.sum_add_distrib,mul_add]
      map_smul' := by intros; simp [mul_assoc,←Finset.mul_sum]; ring }
abbrev press (D : Body F n) (q : Multi.Pack n) := Multi.Pack.collect R (fun i => flag D i x) q

lemma billed_reduces (D : Body F n) (C : SectionData F) {a b c d w : ℝ} (h : R.Lawful a b c d w) (he : cap o R U D κ r) :
    density D o C R U x=(R.eval x:ℂ)*(porter R x C o (coord D)+∑' i,masked R.p.threshold (U i) (payload D i) x)+
      punch R x (press R x D) := by
  rw [Body.density,← Multi.BranchOne.present (serves ..) C o h he]; rfl
end

section Supply
variable {I : Type*} {c : I→ℝ} (D : I → Body F n) (S : I → GridU n)
variable (κ) (T : ∀ i,Tally o R (S i) (D i) κ (c i)) (hc : Summable c)
include T hc
lemma flag_book (x : Config G n) :
    Summable (Function.uncurry fun i j => ‖flag (D i) j x‖) := by
  have hk i : ∑' j, (T i).stamp j ≤ κ*c i := ((T i).bare_cost.2.2.2).trans (mul_le_mul_of_nonneg_left
    (((le_add_of_nonneg_left (T i).e_nn).trans (T i).pay)) (T i).k_pos.le)
  have he := sumcast (f:=fun i j => (T i).stamp j) (fun i =>
    ⟨fun j => ((T i).tag j).1, (T i).bare_cost.2.2.1, hk i⟩) (hc.mul_left κ)
  exact he.2.1.of_nonneg_of_le (fun _ => norm_nonneg _) fun ⟨i,j⟩ => ((T i).tag j).2 x
lemma flag_gather (x : Config G n) (q : Pack n) :
    Summable fun y : I×ℕ => if Pack.ofAddress R.activities y.2=q then flag (D y.1) y.2 x else 0 :=
  Summable.of_norm ((flag_book κ D S T hc x).of_nonneg_of_le
    (fun y => norm_nonneg (if Pack.ofAddress R.activities y.2=q then flag (D y.1) y.2 x else 0)) (fun i => by
      split <;> change _ ≤ ‖flag (D i.1) i.2 x‖ <;> simp))
lemma pressed (x : Config G n) (f : I × ℕ ↪ ℕ) :
    press R x (rollup f D) = ∑' i, press R x (D i) ∧ Summable (fun i => press R x (D i)) := by
  have ht (q) := (flag_gather κ D S T hc x q).prod
  have hh : Summable (fun i => press R x (D i)) := Pi.summable.mpr ht
  refine ⟨funext (fun q => ?_),hh⟩
  rw [tsum_apply hh]; unfold press Pack.collect
  have he (k : ℕ) : (if Pack.ofAddress R.activities k=q then flag (rollup f D) k x else 0) =
      ∑' i, if Pack.ofAddress R.activities k=q then flag (D i) k x else 0 := by
    split <;> rename_i h
    · rfl
    simp
  simp_rw [he]; apply Summable.tsum_comm
  exact flag_gather κ D S T hc x q

lemma mask_book (x : Config G n) :
    Summable (Function.uncurry fun i j => ‖masked R.p.threshold (S i j) (payload (D i) j) x‖) := by
  have he := sumcast (f:=fun i j => (T i).seed j) (u:=c) (fun i =>
    lower_budget (T i).bare_cost.1 ((le_add_of_nonneg_right (T i).b_nn).trans (T i).pay) ((T i).bare_cost.1.1) (fun _ => le_rfl)) hc
  apply he.2.1.of_nonneg_of_le (fun i => norm_nonneg _) fun ⟨i,j⟩ => ?_
  dsimp
  have hh := (T i).sexp j
  by_cases h : Healthy R.p.threshold (S i j) x
  · rw [masked_eq _ _ _ _ h]
    exact hh.2 x h [] (by simp) (by simp)
  rw [masked_ne _ _ _ _ h,norm_zero]; exact hh.1
lemma mask_gather (x : Config G n) (f : I × ℕ ↪ ℕ) (hf : ∀ k : I × ℕ,U (f k)=S k.1 k.2) :
    (∑' i, masked R.p.threshold (U i) (payload (rollup f D) i) x)=
      ∑' i,∑' j,masked R.p.threshold (S i j) (payload (D i) j) x := by
  let g i := masked R.p.threshold (U i) (payload (rollup f D) i) x
  have he : support g ⊆ Set.range f := by
    intro i hi; by_contra ht
    apply hi
    unfold g
    change masked _ _ (hang f (fun j => payload (D j.1) j.2) _) _ = _; rw [hang_out _ _ _ ht]
    by_cases h : Healthy R.p.threshold (U i) x <;> simp [h]
  have hx (v : I × ℕ) : g (f v)=masked R.p.threshold (S v.1 v.2) (payload (D v.1) v.2) x := by
    unfold g; rw [hf]; exact congr_arg (fun h => masked R.p.threshold (S v.1 v.2) h x) (hang_at f (fun k => payload (D k.1) k.2) v)
  change ∑' i,g i=_; rw [← f.injective.tsum_eq he]; simp_rw [hx]
  have hq := (mask_book κ D S T hc x).of_norm.tsum_prod
  exact hq
end Supply

variable {I : Type*} [Countable I]
variable (f : I × ℕ ↪ ℕ) (D : I → Body F n) (S : I → GridU n)
variable (hf : ∀ k : I × ℕ,U (f k)=S k.1 k.2)
include hf

omit [Countable I] in
lemma density_rollup {a b d g w : ℝ} (h : R.Lawful a b d g w) (X : SectionData F) {c : I → ℝ}
    (T : ∀ i,Tally o R (S i) (D i) κ (c i)) (hh : ∀ i,F.coeffSize (coord (D i)) ≤ c i)
    (hc : SumBudget c r) (hk : 0 < κ) (x : Config G n) :
    density (rollup f D) o X R U x = ∑' i, density (D i) o X R (S i) x := by
  let y i := coord (D i)
  have hs : Summable y := (count_many hh hc).1.of_norm
  have hp : Summable (Function.uncurry fun i j => masked R.p.threshold (S i j) (payload (D i) j) x) :=
    (mask_book κ D S T hc.2.1 x).of_norm
  obtain ⟨hP,hK⟩ := pressed κ D S T hc.2.1 x f
  rw [billed_reduces R x _ X h (Tally.rollup f D S hf T hk hc),hP, mask_gather κ D S T hc.2.1 x f hf,
    (punch ..).map_tsum hK, show coord (rollup f D) = ∑' i, y i from rfl,(porter ..).map_tsum hs]
  have hv i := billed_reduces R x (D i) X h (T i).billed
  let u := porter R x X o
  let v := punch R x
  have h1 := (hs.hasSum.map u u.continuous).summable
  have h2 := (hK.hasSum.map v v.continuous).summable
  have h3 := (h1.add hp.prod).mul_left (R.eval x:ℂ)
  simp_rw [hv]; exact Eq.symm ((h3.tsum_add h2).trans (by rw [tsum_mul_left,h1.tsum_add hp.prod]; rfl))
end YM.MultiNext.SignedSource
