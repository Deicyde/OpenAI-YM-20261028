import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Amount
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Connectors
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Schur


/-!
# Physical covariance prices and native RG cover weight

Both the term bound and the rooted sum, paid also BEFORE integration and
cancellation. Can leave some of the actual row decay as rate `μ`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.GCC
open MeasureTheory Function Set Finset Marker
open YM.Multi.Vacuum.Gauss Probe Grove Fused Moment Expansion Charge Connector Lattice
open YM.Next.SectorChange.Schur YM.Next.SectorChange.Wisps YM.Extra.Trajectories
open scoped Topology BigOperators
variable {V I J : Type} [Fintype I] [Fintype J] [DecidableEq V]
namespace Price

variable {n : Side} {q : Rows V I J}
-- read ALL Schur bounds in true positions, both directions.
def gram (q : Rows V I J) (i j : V) : Matrix I I ℝ := Matrix.of fun a b => crossed (q i a) (q j b)
structure Bank (T : Finset V) (q : Rows V I J) (p : I → Site n) (σ K : ℝ) : Prop where
  width : 0 ≤ σ
  balance : 0 ≤ K
  crossedRows i (hi : i∈T) j (hj : j∈T) : Pours (gram q i j) p p σ K

def node (α : ℝ) (B : ℕ) (X : Support n) := rate α (coverNumber B X)

def cents (α : ℝ) (i : ℕ) : ℝ := Real.exp (α * if i=0 then 0 else 2)

/-- Assign the optional `cents` for traversing to disjoint supports. Pay
only the cheaper of the counting argument costs at ends per edge, or use
the child budget at most once for each child. -/
def border (S : V → Finset I) (X : V → Support n) (α μ K : ℝ) (i j : V) :=
    let u := gap (X i) (X j)
    rate (-μ) u * ((min ((S i).card:ℝ) (S j).card)*K)*cents α u

omit [DecidableEq V] in
lemma mass {p : I → Site n} (q : Rows V I J) {v K : ℝ} {i j : V} (hv : 0 ≤ v)
    (hx : Pours (gram q i j) p p v K) (X : V → Support n) (S : V → Finset I) (hi : ∀ a∈S i,p a∈X i) (hj : ∀ a∈S j,p a∈X j) :
    rate v (gap (X i) (X j))*contact q S i j ≤ min ((S i).card:ℝ) (S j).card * K := by
  let d := gap (X i) (X j)
  let f a b := rate v d * |crossed (q i a) (q j b)|
  let F a b := rate v (separation (p a) (p b)) * |crossed (q i a) (q j b)|
  have he a (ha : a∈S i) b (hb : b∈S j) : f a b ≤ F a b := mul_le_mul_of_nonneg_right
    (rate_le hv (gap_le (hi a ha) (hj b hb))) (abs_nonneg _)
  unfold contact; simp_rw [Finset.mul_sum]; apply le_trans (b:=∑ a∈S i,∑ b∈S j,F a b)
    (sum_le_sum fun a ha => sum_le_sum fun b hb => he a ha b hb)
  have hp a b : 0 ≤ F a b := mul_nonneg (rate_pos ..).le (abs_nonneg _)
  have hh : ∑ a∈S i, ∑ b∈S j,F a b ≤ (S i).card*K := by
    apply le_trans (b:=∑ _∈S i,K) (sum_le_sum fun a ha => ?_) (by simp)
    exact (sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun b _ _ => hp a b).trans (hx.row a)
  have hl : ∑ b∈S j, ∑ a∈S i,F a b ≤ (S j).card*K := by
    apply le_trans (b:=∑ _∈S j,K) (sum_le_sum fun b hb => ?_) (by simp)
    exact (sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun a _ _ => hp a b).trans (hx.col b)
  by_cases he : ((S i).card:ℝ) ≤ (S j).card
  · rw [min_eq_left he]; exact hh
  rw [min_eq_right (le_of_not_ge he),sum_comm]; exact hl

omit [DecidableEq V] in
lemma thread {p : I → Site n} {σ α K μ : ℝ} {i j : V} (S : V → Finset I) (X : V → Support n)
    (B : ℕ) (hx : Pours (gram q i j) p p σ K) (hσ : 0≤σ) (hα : 0≤α) (hn : μ+α/(B+1) ≤ σ)
    (hi : ∀ a∈S i,p a∈X i) (hj : ∀ a∈S j,p a∈X j) :
    rate α (joins X B j i)*contact q S i j ≤ border S X α μ K i j := by
  let d := gap (X i) (X j)
  let C := min ((S i).card:ℝ) (S j).card *K
  have he := ratio B d
  let u : ℝ := if d=0 then 0 else 2
  have hi' : rate α (joins X B j i) ≤ rate (-μ) d * cents α d * rate σ d := by
    unfold rate cents; change Real.exp (α*(toll B d)) ≤ Real.exp (-μ * _) * _ * _
    rw [← Real.exp_add,← Real.exp_add]; apply Real.exp_monotone
    have h1 : α*((d:ℝ)/(B+1))=α/(B+1)*d := by ring
    nlinarith [mul_le_mul_of_nonneg_left he hα,mul_le_mul_of_nonneg_right hn (show (0:ℝ) ≤ d by positivity)]
  have ht : rate σ d * contact q S i j ≤ C := mass q hσ hx X S hi hj
  calc
    _ ≤ (rate (-μ) d * cents α d) * (rate σ d * contact q S i j) := (mul_le_mul_of_nonneg_right hi' (contact_nn ..)).trans_eq (by ring)
    _ ≤ (rate (-μ) d * cents α d)*C := mul_le_mul_of_nonneg_left ht (mul_nonneg (rate_pos ..).le (Real.exp_pos _).le)
    _ = _ := by unfold border; dsimp only; unfold C d; ring

variable (X : V → Support n) (S : V → Finset I)
-- Geometry statement separately on arbitrary support valuations so future
-- raw proofs can feed it a covering label at any timestamp.
omit [DecidableEq V] in
private lemma rate_sum (z : Finset V) (α : ℝ) (b : V → ℕ) :
   rate α (∑ i∈z,b i)=∏ i∈z,rate α (b i) := by unfold rate; simp [Finset.mul_sum,Real.exp_sum]

lemma multiplier (T : Finset V) {o : V} (ho : o ∈ T) (B : ℕ) {p : I → Site n} {σ α K μ : ℝ}
    (hc : ∀ i∈T,(X i).Nonempty) (hu : ∀ i∈T, ∀ a∈S i,p a∈X i)
    (h : Bank T q p σ K) (hα : 0 ≤ α) (hn : μ+α/(B+1) ≤ σ)
    (f : Parent V) (hf : Good T {o} f) :
    node α B (T.biUnion X) * beams T {o} f (contact q S) ≤
      (∏ i∈T,node α B (X i))*beams T {o} f (border S X α μ K) := by
  let R := T \ {o}
  have hz j (hj : j∈R) : j∈T := (mem_sdiff.mp hj).1
  have he j (hj : j∈R) : rate α (joins X B j (f j)) * contact q S (f j) j ≤ border S X α μ K (f j) j :=
      thread S X B (h.crossedRows (f j) (hf.goes _ hj) j (hz j hj)) h.width hα hn (hu _ (hf.goes _ hj)) (hu _ (hz j hj))
  have hh := rate_le hα (coverage X B T hc ho f hf)
  rw [rate_add,rate_sum,rate_sum] at hh
  apply (mul_le_mul_of_nonneg_right hh (prod_nonneg fun j _ => contact_nn q S (f j) j)).trans
  unfold node beams
  rw [mul_assoc]; apply mul_le_mul_of_nonneg_left ?_ (prod_nonneg (fun _ _ => (rate_pos ..).le))
  rw [← prod_mul_distrib]; exact prod_le_prod (fun i _ => mul_nonneg (rate_pos ..).le (contact_nn ..)) he

def loan (T : Finset V) (o : V) (B : ℕ) (α μ K : ℝ) (q : Rows V I J) (H : V → ℕ → ℝ)
    (w : V → Row I) (f : Parent V) :=
    ((∏ i∈T,node α B (X i))*beams T {o} f (border S X α μ K))*tags T {o} f H*Real.exp (2*due T q w)

section
variable [Fintype V] [DecidableEq I] {T : Finset V} (o : V) (ho : o ∈ T)
variable (B : ℕ) {p : I → Site n} {σ α K μ : ℝ} {v : Probes V I} {H : V → ℕ → ℝ} {w : V → Row I}
variable (hc : ∀ i∈T,(X i).Nonempty) (hu : ∀ i∈T, ∀ a∈S i,p a∈X i)
    (h : Bank T q p σ K) (hα : 0 ≤ α) (hn : μ+α/(B+1) ≤ σ) (hx : base q T w)
    (hv : Valid T T.card v w H) (hS : ∀ i∈T,Reads (S i) (v i))
include X S o ho B hc hu h hα hn hx hv hS

omit [Fintype V] in
theorem receipt (f : Parent V) (hf : Good T {o} f) :
    let k := (T \ {o}).card
    ‖report T id k {o} f q v‖ ≤ cost T {o} k f q v ∧
    node α B (T.biUnion X) * cost T {o} k f q v ≤ loan X S T o B α μ K q H w f := by
  intro k
  have ha : ({o}:Finset V)⊆T := Finset.singleton_subset_iff.mpr ho
  have ht : Valid T k v w H := hv.lower (card_le_card Finset.sdiff_subset)
  have he := tree_cost T k {o} ha rfl f hf q v S w H hx ht hS
  have hg := multiplier X S T ho B hc hu h hα hn f hf
  refine ⟨signed T k {o} ha f hf q v w H hx ht, (mul_le_mul_of_nonneg_left he (rate_pos ..).le).trans ?_⟩
  let A := beams T {o} f (contact q S)
  let P := tags T {o} f H
  let r := Real.exp (2*due T q w)
  have hh : 0 ≤ P := prod_nonneg fun i hi => (hv.guard i hi).fees _
  change _*(A*P*r) ≤ _*P*r
  rw [← mul_assoc,← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hg hh) (Real.exp_pos _).le
end


end Price
end YM.Primitives.GCC
