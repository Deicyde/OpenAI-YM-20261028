import YM.Slice.Sequence

/-!
# Drives and hops

A trace tour with singleton insertions and gaps. Fold as an actual torus probe.
All normalized by cutoff partition.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Slice.Time
open MeasureTheory Measure Filter Function Set Wilson Lattice TimeKernel Analysis
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {a : Axis} {m : ℕ} {n : Side} {G : Gauge}
variable (V : Braid a G n)

@[simp] lemma duration_nil : duration ([] : Braid a G n) = 0 := rfl
@[simp] lemma duration_append (W : Braid a G n) : duration (V++W)=duration V+duration W := by simp [duration]

@[simp] lemma word_nil (b : Per n) (F : Config G n) : word (a := a) [] b F=1 := by simp [word]
lemma distributed (W : Braid a G n) (t : Per n) (F : Config G n) :
    word (V++W) t F=word V t F * word W (t+ ↑(duration V)) F := by
  induction V generalizing t with
  | nil => simp
  | cons b V ih => rw [List.cons_append,read,ih, read]; simp only [starts,Nat.cast_add,add_assoc,mul_assoc]

@[simp] lemma duration_temp (N) : duration (List.replicate N (Brick.step a G n))=N := by
  induction N <;> simp_all [List.replicate_succ, add_comm]
lemma crossing (N) (b : Per n) (F : Config G n) : word (List.replicate N (Brick.step a G n)) b F=1 := by
  induction N generalizing b with
  | zero => simp
  | succ N ih => rw [List.replicate_succ,read]; simp [ih]

lemma partition_seen (β : ℝ) : closed (trans n G a) (List.replicate n.val (heat (G := G) (n := n) a β)) =
    (partition G n β:ℂ) := by
  have ht := closed_eval (List.replicate n.val (Brick.step a G n)) β 0 (duration_temp _)
  simpa only [cores,List.map_replicate,Brick.step_pulse, funext (crossing _ _), moment, integral_const,
    probReal_univ,one_smul,mul_one] using ht.symm

def drive (B : Fin m → Brick a G n) (Y : Fin m → ℕ) :=
    (List.ofFn fun i => B i :: List.replicate (Y i) (Brick.step a G n)).flatten

lemma welded (B : Fin (m+1) → Brick a G n) (Y : Fin (m+1) → ℕ) : drive B Y =
    B 0 :: List.replicate (Y 0) (Brick.step a G n) ++ drive (Fin.tail B) (Fin.tail Y) := by
  simp [drive,List.ofFn_succ];rfl

lemma drive_time (B : Fin m → Brick a G n) (Y : Fin m → ℕ) : duration (drive B Y)=∑ i, ((B i).width+Y i) := by
  induction m with
  | zero => simp [drive]
  | succ m ih => rw [welded]; simp_rw [duration_append]; rw [ih, Fin.sum_univ_succ,starts,duration_temp]; rfl

lemma B_start (B : Fin m → Brick a G n) (Y : Fin m → ℕ) (β) : cores (drive B Y) β=along
    (heat a β) (fun i => (B i).pulse β) Y := by
  induction m with
  | zero => simp [drive,cores,along]
  | succ m ih =>
    have hs := ih (Fin.tail B) (Fin.tail Y)
    rw [welded,cores,List.map_append]
    unfold cores at hs; rw [hs]; simp [along,List.ofFn_succ];rfl

def column (X : Brick a G n) (p : ℕ) := (List.replicate p [X.reflect,X]).flatten
lemma colony (X : Brick a G n) (p : ℕ) (β) : cores (column X p) β=multiply (X.pulse β) p := by
  simp [column, cores,multiply]
lemma clockTime (X : Brick a G n) (p : ℕ) : duration (column X p)=(p+p)*X.width := by
  induction p with
  | zero => simp [column,duration]
  | succ p ih => rw [show column X (p+1)=[X.reflect,X]++column X p from by simp [column,List.replicate_succ]]
                 simp [ih]; ring

/-- Normalized estimates direct using primitive columns of this Tour.
`p_s=2p`. -/
theorem powering (β : ℝ) (hβ : 0 ≤ β) (B : Fin m → Brick a G n) {p l w : ℕ}
    (he : n.val=(p+p)*w) (hp : 0 < p) (hw : 0 < w) (hW : ∀ i, (B i).width=w)
    {Y Z : Fin m → ℕ} (hY : m*w+∑ i, Y i=n.val) (hZ : m*w+∑ i, Z i=n.val)
    (i j : Fin m) (hij : i≠j) (hu : Y i+l=Z i) (hv : Z j+l=Y j)
    (hm : ∀ z : Fin m, z≠i → z≠j → Y z=Z z)
    (r : ℝ) (hy : 0<r) (hO : ∀ i : Fin m, 2*r < Y i) (hs : (l:ℝ) ≤ r)
    (b c : Per n) (H : Fin m → Per n) (K : Fin m → ℝ)
    (hK : ∀ x : Fin m, ‖moment β (word (column (B x) p) (H x))‖ ^ (Holder.rate p) ≤ K x) :
    ‖moment β (word (drive B Z) b) - moment β (word (drive B Y) c)‖ ≤ (∏ i, K i)/r*l := by
  have hi (v : Fin m → ℕ) (h : m*w+∑ i, v i=n.val) : duration (drive B v)=n.val := by
    simp_rw [drive_time,hW,Finset.sum_add_distrib]; simp [h]
  let f (x : Fin m) := (B x).pulse β
  let R := partition G n β
  have hr : 0<R := partition_pos _
  have hC x : ‖closed (trans n G a) (multiply (f x) p)‖^(Holder.rate p) ≤ K x * R ^ (Holder.rate p) := by
    unfold f; rw [← colony _ _ β, ← closed_eval _ _ (H x) (show duration (column _ _)=_ by rw [clockTime,hW]; exact he.symm)]
    rw [norm_mul,Real.mul_rpow (norm_nonneg _) (norm_nonneg _),mul_comm]
    rw [Complex.norm_real, Real.norm_eq_abs,abs_of_pos hr]
    exact mul_le_mul_of_nonneg_right (hK x) (Real.rpow_nonneg hr.le _)
  letI : @BorelSpace (Leaf G a n) (MetricSpace.toPseudoMetricSpace (α := Leaf G a n)).toUniformSpace.toTopologicalSpace (inferInstance : MeasurableSpace _) := instBorelSpaceLeaf _
  letI : @SecondCountableTopology (Leaf G a n) (MetricSpace.toPseudoMetricSpace (α := Leaf G a n)).toUniformSpace.toTopologicalSpace := instSecondCountableTopologyLeaf _
  letI : @CompactSpace (Leaf G a n) (MetricSpace.toPseudoMetricSpace (α := Leaf G a n)).toUniformSpace.toTopologicalSpace := (inferInstance : CompactSpace (Leaf G a n))
  have hx := passage (trans n G a) _ f (step_positive a (n := n) hβ) (heat_cont ..) (fun i =>
    testB_cont β _ (B i).reads) he hp hw _ (partition_pos β (G := G) (n := n)) (partition_seen β) hY
    i j hij hu hv hm r hy hO hs K hC
  rw [← show cores (drive B Z) β = _ from B_start B Z β,← show cores (drive B Y) β = _ from B_start B Y β,
    ← closed_eval _ _ b (hi Z hZ),← closed_eval _ _ c (hi Y hY), ← mul_sub] at hx
  rw [norm_mul, Complex.norm_real,Real.norm_eq_abs, abs_of_pos hr] at hx
  apply le_of_mul_le_mul_left _ hr
  apply hx.trans_eq
  ring
end YM.Slice.Time
