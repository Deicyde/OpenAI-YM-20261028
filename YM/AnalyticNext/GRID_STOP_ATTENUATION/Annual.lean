import YM.AnalyticNext.GRID_STOP_ATTENUATION.Catalog
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Folders
import YM.Next.MULTISOURCE.Curves

set_option warningAsError false

/-! Prices on the catalog.

One important distinction: the incoming radial bill on forced hits
(from a birth estimate) need not have paid `forcedAllowance`'s sqrt.
We explicitly charge that in converting the costs to `Multi.Credit`; don't
just charge the factorial. In the stop planner it will be paid ONCE at birth
if not reserved in the radial already.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Compile
open Function Finset RG Lattice Wilson Marker Overlay Multi MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {n : Side} {G : Gauge} {P : Rep G n}
variable (A : Bands R P) {w : V → ℝ} {u c f b : ℝ}

/-- Individual envelope requests at a fork. -/
structure Figures (A : Bands R P) (w : V → ℝ) (u c hit : ℝ) where
  h : ℕ → ℝ
  k : ℕ × ℕ → ℝ
  hn i : 0 ≤ h i
  kn i : 0 ≤ k i
  capped i : ∀ x∈ (A.rays i).val,P.p.supBounds (A.origins x) (A.support i) (A.H i) (h i)
  quoted i j U : ‖A.entries i j U‖ ≤ k (i,j)
  rays : Folder A.rays (fun i => P.p.mass (A.support i) (h i)) w c
  flags : Folder (fun i : ℕ × ℕ => A.marks i.1 i.2)
    (fun i => P.p.mass (P.activities.forced i.1).support (k i)) w hit
  sold i : w i * ‖A.units i‖ ≤ u

omit [Fintype V] in
lemma opening (hA : A.Active) (hR : A.Radial w u c f b) : Nonempty (Figures A w u c (f*b)) := by
  obtain ⟨g,hg,hG⟩ := hR.bulk
  obtain ⟨t,ht,hT⟩ := hR.hits
  have he (i : ℕ × ℕ) : 0 ≤ t i := (ht i.1 i.2).1
  refine ⟨⟨g,t,(fun i => (hg i).1),he,(fun i => (hg i).2), fun i j U => (ht i j).2 _,
    ⟨hA.proper,hR.pure,fun i => mul_nonneg (Real.exp_pos _).le ((hg i).1),hG⟩,
    ⟨fun i => hA.occurs _ _,hR.pure, fun i => mul_nonneg (Real.exp_pos _).le (he i), hT⟩,hR.localU⟩⟩

namespace Figures
variable {A} (Q : Figures A w u c f)

def rayPrice (x : Hot R) := file A.rays (fun i => P.p.mass (A.support i) (Q.h i)) x
def hitPrice (x : Hot R) := file (fun i : ℕ × ℕ => A.marks i.1 i.2)
  (fun i => P.p.mass (P.activities.forced i.1).support (Q.k i)) x
omit [Fintype V] in
lemma nnRay (x : Hot R) : 0 ≤ Q.rayPrice x := Q.rays.file_nonneg _
omit [Fintype V] in
lemma nnHit (x : Hot R) : 0 ≤ Q.hitPrice x := Q.flags.file_nonneg _

omit [Fintype V] in
/-- Keep one unmasked germ per occurrence before adding the rays in each
mode. -/
lemma grain (hA : A.Active) (x : Hot R) : Banked P.p 0 (x.sites.image A.origins)
    (fun U => ∑' j,rayPiece A x j U) (Q.rayPrice x) := by
  let X := x.sites.image A.origins
  let legal (j : ℕ) := A.rays j=x.val
  let S (j) := if legal j then A.support j else X
  let H (j) := if legal j then A.H j else (0 : Config G n → ℂ)
  let p := slice A.rays Q.h x
  have h j : X ⊆ S j ∧ P.p.Regular (S j) (H j) ∧ 0 ≤ p j ∧ ∀ y∈X,P.p.supBounds y (S j) (H j) (p j) := by
    by_cases hj : legal j
    · have hEq : A.rays j=x.val := hj
      simp only [S,H,p,slice,hj,↓reduceIte,hEq]
      refine ⟨?_,hA.regular j,Q.hn j,?_⟩
      · intro y hy; obtain ⟨i,hi,rfl⟩ := mem_image.mp hy; exact hA.pins j i (hEq.symm ▸ hi)
      intro v hv; obtain ⟨i,hi,rfl⟩ := mem_image.mp hv; exact Q.capped j i (hEq.symm ▸ hi)
    have hEq : A.rays j≠x.val := hj
    simp only [S,H,p,slice, if_neg hj,if_neg hEq]
    exact ⟨by rfl,(null_path ..).1,le_rfl,fun y _ => (null_path ..).2 y⟩
  have he (j) : burn P.p 0 (S j)*p j=slice A.rays (fun i => P.p.mass (A.support i) (Q.h i)) x j := by
    rw [burn_zero]; unfold S p legal slice; split <;> simp_all [BudgetPoint.mass]
  refine ⟨S,H,p,h,?_,fun U => ?_⟩
  · simp_rw [he]; exact ⟨Q.rays.slice_nonneg _, Q.rays.slice_series _, le_rfl⟩
  refine tsum_congr fun j => ?_; unfold rayPiece S H legal
  by_cases hv : x.val=A.rays j
  · rw [if_pos hv, if_pos hv.symm, if_pos hv.symm]
  simp [hv,Ne.symm hv,masked]

private def retail (x : Hot R) (i : ℕ × ℕ) := slice (fun i => A.marks i.1 i.2) Q.k x i
private def taggedBill (x : Hot R) (i : ℕ) := ∑' j, retail Q x (i,j)
def grouped (x : Hot R) (q : Pack n) := Pack.collect P (taggedBill Q x) q

omit [Fintype V] in
private lemma ret_nn (x : Hot R) (i) : 0 ≤ Q.retail x i := by
  unfold retail slice; split <;> first | exact Q.kn _ | exact le_rfl
omit [Fintype V] in
private lemma ret_series (x : Hot R) : Summable (Q.retail x) := by
  apply (Q.flags.slice_series x).of_nonneg_of_le (Q.ret_nn x)
  intro i; unfold retail slice; split_ifs
  · exact P.p.loMass _ _ (Q.kn i)
  exact le_rfl
omit [Fintype V] in
private lemma tag_price (x : Hot R) : Summable (Q.taggedBill x) := (Q.ret_series x).prod

omit [Fintype V] in
private lemma tagged_hi (x : Hot R) (U : Config G n) (i : ℕ) : ‖hitVolume A x i U‖ ≤ Q.taggedBill x i := by
  let g (j : ℕ) := Q.retail x (i,j)
  let v (j : ℕ) := hitPiece A x i j U
  have hG : Summable g := (Q.ret_series x).prod_factor i
  have h (j : ℕ) : ‖v j‖ ≤ g j := by
    unfold v hitPiece g retail slice; by_cases he : x.val=A.marks i j
    · simp only [he,↓reduceIte]; exact Q.quoted i j U
    simp only [if_neg he,if_neg (Ne.symm he),norm_zero,le_refl]
  have hx := hG.of_nonneg_of_le (fun j => norm_nonneg (v j)) h
  exact (norm_tsum_le_tsum_norm hx).trans (hx.tsum_le_tsum h hG)

omit [Fintype V] in
private lemma group_total (x : Hot R) : (∑ p : Pack n, burn P.p 0 p.zone * Q.grouped x p) = Q.hitPrice x := by
  let K := Pack.ofAddress P.activities
  let T (i : ℕ × ℕ) := P.p.mass (K i.1).zone (retail Q x i)
  have he i : T i=slice (fun i => A.marks i.1 i.2) (fun i => P.p.mass (P.activities.forced i.1).support (Q.k i)) x i := by
    unfold T retail slice; split; rfl; exact mul_zero _
  have hS : Summable T := by rw [funext he]; exact Q.flags.slice_series x
  let g := Q.taggedBill x
  have hg (p : Pack n) : Summable (fun i : ℕ => if K i=p then g i else 0) := Pack.access P g (Q.tag_price x) p
  unfold grouped Pack.collect; simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun i _ => (hg i).mul_left (burn P.p 0 i.zone))]
  unfold hitPrice file; simp_rw [← he]; rw [hS.tsum_prod]; refine tsum_congr fun i => ?_
  rw [sum_eq_single (K i)]
  · rw [if_pos rfl,burn_zero]; unfold g taggedBill T BudgetPoint.mass
    exact tsum_mul_left.symm
  · intro p _ hp; rw [if_neg (show Pack.ofAddress P.activities i≠p from Ne.symm hp),mul_zero]
  simp


end Figures
end YM.AnalyticNext.GridStop.Compile
