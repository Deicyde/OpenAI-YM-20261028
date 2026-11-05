import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.RingTheory.RootsOfUnity.Complex
import YM.Next.MULTISOURCE.Curves
import YM.Next.MULTISOURCE.Journey
import YM.Org.Theatre
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B06


set_option warningAsError false

/-!
# Compulsory attachment receipt from the nonrepeating tree

After the support-threshold, need the output forced sources still at κ
scale, although site prices of the flag corrections can be MUCH larger.
Use spare pack input smallness at an extra exponent, and tree at inflated
pack prices. Decode an actual K occurrence from every recipe. No price
per marker count (retaining calendar rather than volume). Valid also for
buying other attaching Mayer uses without order divisions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Harvest
open Filter Function MeasureTheory RG Marker Wilson Lattice Multi Multi.Couples Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {I : Type} [Fintype I] [DecidableEq I] {G : Gauge} {n : Side} (Y : I → Support n)

/-- Per-site pack weights. Defined for finite alphabets in this extraction
only. All supports come from retained physical addresses. -/
def crate {I : Type*} [Fintype I] (X : I → Support n) (B : ℕ) (a : ℝ) (F : I → ℝ) (x : Site n) :=
    ∑ i∈univ.filter (fun i => x∈X i), Real.exp (a*coverNumber B (X i))*F i

def storage (f : Pack n → ℝ) (g : I → ℝ) (p : Pack n) := ∑ i∈trays Y p,∏ v∈ i, Sum.elim f g v

omit [DecidableEq I] in
/-- Sum bill of all merges. #I and #recipes free float. λPROD division
not used. Requires small volume-per-cover-ball times BOTH hit budgets at
stronger exponent. κ*M wins even if the exp growth under gating invocation
is used on flag ingredients and not available for Pack. -/
theorem garage (M : ℕ) (f : Pack n → ℝ) (g : I→ℝ) {a κ : ℝ} (ha : 0 ≤ a) (hk : 0 < κ)
    (hA : ∀ i,0≤f i) (hg : ∀ i,0≤g i)
    (hB : (M+M+1:ℕ)^4*(κ:ℝ) ≤ 1/32)
    (hF : ∀ x : Site n,crate (Pack.zone (n:=n)) M (a+1) f x ≤ 2*κ)
    (hH : ∀ x : Site n,crate Y M (a+1) g x ≤ 1/(2*((M+M+1:ℕ)^4:ℕ))) :
    ∀ x : Site n,crate Pack.zone M a (storage Y f g) x ≤ 128*κ := by
  classical
  intro x
  let B := (((M+M+1:ℕ)^4:ℕ):ℝ)
  have h : 0 < B := by unfold B; exact_mod_cast (by positivity : 0 < (M+M+1:ℕ)^4)
  let k := 32*B*κ
  have hx : 0<k := by positivity
  let p := (1:ℝ)/k
  have he : 1 ≤ p := (le_div_iff₀ hx).mpr (by
    have : B*κ≤1/32 := by simpa [B] using hB
    unfold k; linarith)
  let d := Sum.elim (p • f) g
  have hs (q : Atom n I) : 0 ≤ d q := by cases q; exact mul_nonneg (zero_le_one.trans he) (hA _); exact hg _
  let τ := 1/B
  have ht : 0 < τ := div_pos zero_lt_one h
  have hτ : τ ≤ 1 := (div_le_iff₀ h).mpr (by rw [one_mul]; unfold B; exact_mod_cast (one_le_pow₀ (by omega : 1≤M+M+1) (n:=4)))
  have hQ : Ac.Hit (span Y) M d (a+1) τ := by
    intro i
    let m (z : Atom n I) := if i∈span Y z then d z*Real.exp ((a+1)*coverNumber M (span Y z)) else 0
    refine ⟨fun j => by change 0 ≤ m j; unfold m; split; exact mul_nonneg (hs _) (Real.exp_pos _).le; exact le_rfl,Summable.of_finite,?_⟩
    rw [tsum_fintype]; change ∑ z,m z ≤ _
    rw [Fintype.sum_sum_type]
    have hi : (∑ j : Pack n, m (Sum.inl j)) = p*crate (Pack.zone (n:=n)) M (a+1) f i := by
      rw [crate, Finset.sum_filter, Finset.mul_sum]; apply sum_congr rfl; intro j _
      change (if i∈j.zone then p*f j*_ else 0)=_
      split
      · simp [span]; ring
      simp
    have hy : (∑ j : I, m (Sum.inr j)) = crate Y M (a+1) g i := by
      rw [crate, Finset.sum_filter]; apply sum_congr rfl; intro j _
      change (if i∈Y j then g j*Real.exp _ else 0)=_
      split <;> rename_i e <;> simp [span,mul_comm]
    rw [hi,hy]
    refine (add_le_add (mul_le_mul_of_nonneg_left (hF i) (zero_le_one.trans he)) (hH i)).trans ?_
    change p*(2*κ)+1/(2*B) ≤ τ
    unfold p k τ; field_simp; linarith
  have hb : ((M+M+1:ℕ):ℝ)^4*τ ≤ 1 := by unfold τ B; push_cast; field_simp; exact le_rfl
  have hT := Ac.forest (span Y) M ha hs hQ hb ht.le x
  have hbill : Real.exp τ-1 ≤ 3*τ := by
    have hi : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
    have hu := Real.add_one_le_exp (-τ)
    rw [Real.exp_neg,←one_div,le_div_iff₀ (Real.exp_pos _)] at hu
    nlinarith only [hu, Real.exp_monotone hτ, hi, ht]
  refine (le_trans (b:= k*∑' i,Ac.roots (span Y) M d a x i) ?_ ((mul_le_mul_of_nonneg_left ((hT.2.2.trans hbill)) hx.le).trans ?_))
  swap
  · unfold k τ; field_simp; linarith
  change crate Pack.zone M a (storage Y f g) x ≤ k*∑' i,Ac.roots (span Y) M d a x i
  rw [tsum_fintype]
  unfold crate storage trays -- sum reorder
  simp_rw [mul_sum, Finset.sum_filter]
  let V (i : Pack n) (j : Recipe n I) := if x∈i.zone then
    if j∈ boxes Y ∧ fused Y j=i then Real.exp (a*coverNumber M i.zone)*∏ v∈ j, Sum.elim f g v else 0
    else 0
  -- rw sum_filter differently
  change (∑ i : Pack n, (if x∈i.zone then ∑ j∈boxes Y, if fused Y j=i then _ else 0 else 0)) ≤ _
  calc
    _ = ∑ j∈boxes Y,∑ i : Pack n,V i j := by
      rw [sum_comm]; refine sum_congr rfl fun i _ => ?_; unfold V
      split; exact sum_congr rfl fun j hj => by simp [hj]
      exact (sum_eq_zero fun _ _ => rfl).symm
    _ ≤ _ := by
      let T (j : Recipe n I) := k*Ac.roots (span Y) M d a x j
      change (∑ j∈boxes Y,∑ i,V i j) ≤ ∑ i,T i
      apply le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (boxes Y)) (f:=T) (fun i _ _ => ?_))
      · apply sum_le_sum; intro j hj
        rw [sum_eq_single (fused Y j)]
        · unfold V T; simp only [hj,and_self,if_true]; unfold Ac.roots
          by_cases he' : x∈(fused Y j).zone
          · rw [if_pos he',if_pos ⟨((owns ..).mp hj).2.2,show x∈ground Y j from (merged_zone Y hj) ▸ he'⟩,merged_zone Y hj]
            obtain ⟨z,hz⟩ := ((owns ..).mp hj).1
            obtain hZ := mem_toLeft.mp hz
            let e := Sum.elim f g
            have hr := Finset.prod_le_prod (s:=j.erase (Sum.inl z)) (f:=e) (g:=d)
              (fun i _ => by cases i; exacts [hA _,hg _]) (fun i _ => by cases i; exacts [le_mul_of_one_le_left (hA _) he,le_rfl])
            rw [← mul_prod_erase j d hZ,← mul_prod_erase j e hZ]
            change _ ≤ k*(Real.exp _*(p*f z * ∏ i∈j.erase (Sum.inl z),d i))
            have ht : k*p=1 := by unfold p; field_simp
            conv_rhs => rw [show Real.exp (a*(coverNumber M (Finset.biUnion j (span Y)):ℝ))*(p*f z*∏ i∈j.erase (Sum.inl z),d i) = p*(Real.exp (a*(coverNumber M (Finset.biUnion j (span Y)):ℝ))*(f z*∏ i∈j.erase (Sum.inl z),d i)) by ring, ← mul_assoc,ht,one_mul]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr (hA z)) (Real.exp_pos _).le
          rw [if_neg he',if_neg (fun H => he' ((merged_zone Y hj) ▸ H.2)),mul_zero]
        · intro i _ hi; unfold V; split; exact if_neg (fun H => hi H.2.symm); rfl
        simp
      unfold T Ac.roots; split; exact mul_nonneg hx.le (mul_nonneg (Real.exp_pos _).le (prod_nonneg (fun j _=> hs _))); exact (mul_zero k).ge
end YM.AnalyticNext.GridStop.Harvest
