import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Census
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Gram
import YM.Next.FREE_KERNELS.Lifts
import YM.Progress.STATIONARY_SCENES.Green


/-!
# Counting coordinates uniformly in sectors

Pay via parents EVEN on wrapping lattice. Useful for Gram: far
operators uniform β cost in all sectors/k, post-L. Do not specialize
to thermodynamic limit nor store period-dependent max degrees.
Coordinates carry halo queries not shown here. `localCharges` later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Census
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Coat Green Animals
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

def mentionPrice (L : Side) := Fintype.card Signed*(L.val^4*Fintype.card PlaqAxes*2+Fintype.card Axis)
def tubularPrice (G : Gauge) (L : Side) := L.val^4*Fintype.card Axis*Fintype.card G.ColorIndex
def aim (S : StepData c f) (x : Target c f G) := root S x.1
def along (S : StepData c f) (x : Tubular f G) := atEdge S x.1
lemma motion (S : StepData c f) : Census (mentionPrice S.patch.L) (root S) := by
  have he : Census (S.patch.L.val^4*Fintype.card PlaqAxes*2+Fintype.card Axis) (focus S) := by
    convert added (withType Bool (withType PlaqAxes (homeland S))) (withType Axis (ordinary (c:=c))) using 1; rfl
    funext x; cases x <;> rfl
  apply prefix_counts (p := fun s p => root S (s,p))
  intro s; exact permute he s.actEquiv.toEquiv

lemma aims (S : StepData c f) : Census (mentionPrice S.patch.L*Fintype.card G.ColorIndex) (aim (G:=G) S) :=
    withType _ (motion S)
lemma entering (S : StepData c f) : Census (tubularPrice G S.patch.L) (along (G:=G) S) := withType _ (perch S)

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {m : ℕ} {o : ι → Site c}

def withinH (o : ι→Site c) (x : Site c) (n : ℕ) := univ.filter fun j => separation x (o j) ≤ n
lemma joins (j : ι) (x : Site c) (n : ℕ) : j∈withinH o x n ↔ separation x (o j)≤n := by simp [withinH]
lemma count_near (h : Census m o) (x : Site c) (n : ℕ) : (withinH o x n).card ≤ ballCost n*m := by
  apply (le_trans ?_ (h (neighbors n x))).trans (Nat.mul_le_mul_right _ (neighbors_card ..))
  exact Finset.card_le_card (fun i hi => mem_filter.mpr ⟨mem_univ _, (neighbors_mem ..).mpr ((joins ..).mp hi)⟩)

lemma for_neighbors (h : Census m o) (g : κ → ℝ) (hg : ∀ i, 0≤g i) (p : κ → Site c) (n : ℕ) :
    ∑ i : ι, (∑ j∈withinH p (o i) n,g j) ≤ ((ballCost n:ℝ)*m)*(∑ j,g j) := by
  unfold withinH; simp_rw [Finset.sum_filter]; rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  simp_rw [separation_comm _ (p i),← sum_filter]; rw [sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast count_near h (p i) n) (hg _)

def rates0 (η : ℝ) (n : ℕ) := (ballCost n:ℝ)*Real.exp (-η*n)
def price0 (η : ℝ) := ∑' n, rates0 η n

lemma summons {η : ℝ} (h : 0 < η) : Summable (rates0 η) := by
  let u (n : ℕ) := ((n+1:ℝ)^ (4:ℕ))*Real.exp (-η*n)
  have ht := (summable_nat_add_iff 1).2 (Real.summable_pow_mul_exp_neg_nat_mul 4 h)
  have hu : Summable u := by
    refine (ht.mul_right (Real.exp η)).congr ?_
    intro b; unfold u; push_cast; rw [mul_assoc, ← Real.exp_add]; ring_nf
  refine Summable.of_nonneg_of_le (fun i => by unfold rates0; positivity) (fun i => ?_) (hu.mul_left 16)
  unfold u rates0 ballCost; push_cast
  rw [← mul_assoc, show (16:ℝ)=2^4 by norm_num,←mul_pow]; gcongr; ring_nf; linarith

lemma pays_count (h : Census m o) (x : Site c) {η : ℝ} (he : 0 < η) :
    ∑ i : ι, wt (-η) x (o i) ≤ price0 η * m := by
  let d (i : ι) := separation x (o i)
  let X := univ.image d
  have hk i : ∑ j∈X,(if d i=j then wt (-η) x (o i) else 0)=wt (-η) x (o i) := by simp [X]
  calc
    _ = ∑ j∈X,∑ i, (if d i=j then wt (-η) x (o i) else 0) := by rw [sum_comm]; simp_rw [hk]
    _ ≤ ∑ j∈X, rates0 η j*m := by
      apply sum_le_sum; intro j _; rw [← sum_filter]
      let K := univ.filter fun i : ι => d i=j
      have hv : K.card ≤ ballCost j*m :=
        (card_le_card (show K ⊆ withinH o x j from fun i hi => (joins ..).mpr ((mem_filter.mp hi).2.le))).trans (count_near h x j)
      calc
        _ = ∑ _i∈K,Real.exp (-η*j) := Finset.sum_congr rfl fun i hi => congr_arg (fun n : ℕ => Real.exp (-η*n)) ((mem_filter.mp hi).2 : d i=j)
        _ ≤ ((ballCost j:ℝ)*m)*Real.exp (-η*j) := by rw [sum_const,nsmul_eq_mul]; gcongr; exact_mod_cast hv
        _ = _ := by unfold rates0; ring
    _ ≤ _ := by
      rw [← Finset.sum_mul]; gcongr; exact (summons he).sum_le_tsum _ fun i _ => by unfold rates0; positivity

omit [Fintype κ] in
lemma rows (h : Census m o) (x : κ → Site c) (A : Matrix κ ι ℝ) {r η Q : ℝ} (hQ : 0 ≤ Q) (hr : r < η)
    (ht : ∀ i j, wt η (x i) (o j)*|A i j| ≤ Q) : Rows x o A r (price0 (η-r)*m*Q) := by
  intro i
  apply le_trans _ (mul_le_mul_of_nonneg_right (pays_count h (x i) (sub_pos.mpr hr)) hQ)
  rw [sum_mul]; apply sum_le_sum; intro j _
  have hs : wt r (x i) (o j)=wt (-(η-r)) (x i) (o j)*wt η (x i) (o j) := by
    unfold wt; rw [← Real.exp_add]; congr 1; ring
  rw [hs,mul_assoc]; exact mul_le_mul_of_nonneg_left (ht i j) (wt_pos ..).le
end YM.ConnectedActivityE6.Census
