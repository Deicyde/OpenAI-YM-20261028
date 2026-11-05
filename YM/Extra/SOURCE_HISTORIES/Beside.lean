import YM.Extra.SOURCE_HISTORIES.Clusters
import YM.Extra.SOURCE_HISTORIES.Motion

/-! Preparation for downstream isolated discrepancy matching. Same dictionary,
linear snapshot + residual decomposition. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories.Relay
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels Bid Motion
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {d : ℕ} {n : Side} {F : Labels.Frame G d}

def twain {X : Type*} (P Q : X) (i : Bool) : X := if i then P else Q

def beside (P Q : Coefficient F n) := merge (code Bool) (twain P Q)

lemma reckon (P Q : Coefficient F n) : (beside P Q).x=P.x+Q.x := by
  simp [beside,merge,tsum_fintype,twain]


lemma sideK (P Q : Coefficient F n) : (beside P Q).forced=P.forced+Q.forced := by
  funext i U; simp [beside,merge,tsum_fintype,twain]

lemma presentation {P Q : Coefficient F n} {R : Rep G n} {A o} {p q k : ℝ} (h : P.Format o A R)
    (hp : P.remBound o R k p) (hx : Q.Format o A R) (hq : Q.remBound o R k q) :
    (beside P Q).Format o A R ∧ (beside P Q).remBound o R k (p+q) := by
  have hr (i : Bool) : (twain P Q i).remBound o R k (twain p q i) := by cases i; exact hq; exact hp
  have hu : 0 < k := by obtain ⟨_,_,-,-,-,hk,-⟩ := hq; exact hk
  refine ⟨merge_format _ _ (fun i => ?_),?_⟩
  · cases i; exact hx; exact h
  have hL := (merge_budget (code Bool) (twain P Q) hu hr (hasSum_fintype _).summable).1
  rwa [tsum_fintype,Fintype.sum_bool] at hL

lemma plus {P Q : Coefficient F n} {R : Rep G n} {o} {p q k σ C Λ δ w : ℝ}
    (hk : R.Lawful σ C Λ δ w) (hp : P.remBound o R k p) (hq : Q.remBound o R k q) (B : SectionData F) :
    (beside P Q).density o B R = P.density o B R + Q.density o B R := by
  have hr (i : Bool) : (twain P Q i).remBound o R k (twain p q i) := by cases i; exact hq; exact hp
  have hu : 0 < k := by obtain ⟨_,_,-,-,-,hk,-⟩ := hq; exact hk
  funext U
  have hL := (merge_density (code Bool) _ hu hk hr (hasSum_fintype _).summable (hasSum_fintype _).summable B U).tsum_eq
  rw [tsum_fintype,Fintype.sum_bool] at hL
  exact hL.symm

variable (B : SectionData F) (H : History G) (N p i : ℕ) (A : Hol G) (W : Worth)



end YM.Extra.Histories.Relay
