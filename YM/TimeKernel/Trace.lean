import YM.Analysis.Quadrature
import YM.Complex.Gaps



/-!
# From cyclic kernel integrals to finite trace

Use SAME quadrature choice for A & B slab powers etc; proves
adjoints and traces converge with regulator fixed. No finite-period
Schatten theorem. Kernel diagonal padded sqrt masses at both endpoints for
positive T.
-/
set_option autoImplicit false
noncomputable section
namespace YM.TimeKernel
open Filter Function Set Analysis Matrix MeasureTheory
open scoped Topology BigOperators ComplexOrder InnerProductSpace
variable {X Y : Type*} {n : ℕ}

abbrev K (X : Type*) := X → X → ℂ

def segment (k : Fin n → K X) (p : Fin (n+1) → X) := ∏ i, k i (p i.castSucc) (p i.succ)

def cycle (k : Fin n → K X) (p : Fin n → X) := ∏ i, k i (p i) (p (finRotate n i))

def packet (a : Fin n → X) (x y : X) := Fin.snoc (Fin.cons x a) y (α := fun _ => X)

lemma starts (x : X) (a : Fin n → X) (k : Fin (n+1) → K X) :
    cycle k (Fin.cons x a) = segment k (packet a x x) := by
  refine Finset.prod_congr rfl ?_
  intro i _
  rw [packet,Fin.snoc_castSucc]
  congr 1
  rw [← Fin.cons_snoc_eq_snoc_cons, Fin.cons_succ,Fin.snoc_eq_cons_rotate]

lemma cut_head (x y : X) (k : Fin (n+1+1) → K X) (p : Fin n → X) (v : X) :
    segment k (packet (Fin.cons v p) x y) = k 0 x v * segment (Fin.tail k) (packet p v y) := by
  rw [packet, ← Fin.cons_snoc_eq_snoc_cons]
  simp only [segment, Fin.prod_univ_succ,Fin.castSucc_zero,Fin.cons_zero,Fin.cons_succ,← Fin.succ_castSucc,
    Fin.snoc_apply_zero]
  rfl

private lemma sum_peel [Fintype X] (F : (Fin (n+1) → X) → ℂ) :
    ∑ x, ∑ v : Fin n → X, F (Fin.cons x v) = ∑ i, F i :=
  calc
    _ = ∑ p : X × (Fin n → X), F (Fin.consEquiv _ p) := by rw [Fintype.sum_prod_type]; rfl
    _ = _ := Equiv.sum_comp (Fin.consEquiv (fun _ => X)) F

lemma walk_prod [Fintype X] [DecidableEq X] (k : Fin (n+1) → K X) (x y : X) :
    Holder.combine (fun i => Matrix.of (k i)) x y = ∑ i, segment k (packet i x y) := by
  induction n generalizing x y with
  | zero =>
    rw [Holder.stem, Holder.blank,mul_one]
    simp [segment,packet]
    rfl
  | succ n ih =>
    rw [Holder.stem,Matrix.mul_apply]
    have ha : (Fin.tail (fun i => Matrix.of (k i))) = (fun i => Matrix.of (Fin.tail k i)) := rfl
    simp_rw [ha, ih (Fin.tail k), Finset.mul_sum]; symm
    rw [← sum_peel (fun i => segment k (packet i x y))]
    simp only [cut_head]; rfl

lemma walk_trace [Fintype X] [DecidableEq X] (k : Fin (n+1) → K X) :
    (Holder.combine (fun i => Matrix.of (k i))).trace = ∑ i, cycle k i := by
  simp only [Matrix.trace,Matrix.diag_apply,walk_prod,← starts]
  apply sum_peel

lemma cont_cycle [TopologicalSpace X] (k : Fin n → K X) (hk : ∀ i, Continuous (Function.uncurry (k i))) : Continuous (cycle k) :=
  continuous_finsetProd _ (fun i _ => (hk i).comp (show Continuous (fun p : Fin n→X => (p i,p (finRotate n i))) from
    ((continuous_apply i).prodMk (continuous_apply (finRotate n i)))))

variable [MeasurableSpace X] (μ : Measure X)

/-- Empty list: junk returns count on empty Pi. Need nonempty to use for traces. -/
def closed (k : List (K X)) := ∫ x, cycle k.get x ∂(Measure.pi fun _ => μ)

section
variable (Q : Quad X)
def piece (x : Fin Q.size) : ℂ := ↑√(Q.mass μ x)
def sample (k : K X) : Holder.M (Fin Q.size) := Matrix.of fun i j => piece μ Q i * k (Q.tag i) (Q.tag j) * piece μ Q j

def op (k : K X) : K X := fun x y => star (k y x)

lemma weights (x : Fin Q.size) : piece μ Q x * piece μ Q x = (Q.mass μ x : ℂ) := by
  unfold piece; rw [← Complex.ofReal_mul, ← sq]; simp [Q.mass_nonneg μ x]

lemma oriented (k : K X) : (sample μ Q k).conjTranspose = sample μ Q (op k) := by ext1 i j; simp [sample,piece,op]; ring

lemma safe (k : K X) (h : Analysis.NNKernel k) : (sample μ Q k).PosSemidef := by
  let W : Holder.M (Fin Q.size) := Matrix.diagonal (piece μ Q)
  rw [show sample μ Q k=Wᴴ*Matrix.of (fun i j => k (Q.tag i) (Q.tag j))*W by
    ext1 i j; simp [W,diagonal_conjTranspose,sample,piece]]
  exact Matrix.PosSemidef.conjTranspose_mul_mul_same (h _ Q.tag) _

lemma measureWeight (n) (k : Fin (n+1) → K X) :
    (Holder.combine (fun i => sample μ Q (k i))).trace =
      ∑ p : Fin (n+1) → Fin Q.size, (∏ j, Q.mass μ (p j)) • cycle k (Q.tag ∘ p) := by
  rw [show (Holder.combine fun i => sample μ Q (k i)).trace=∑ i, cycle (fun j => Matrix.of.symm (sample μ Q (k j))) i from walk_trace _]
  refine Finset.sum_congr rfl fun i _ => ?_
  have he : ∏ a : Fin (n+1), piece μ Q (i (finRotate _ a)) = ∏ a, piece μ Q (i a) := Equiv.prod_comp (finRotate _) (fun a => piece μ Q (i a))
  unfold cycle sample
  simp only [Equiv.symm_apply_apply, Finset.prod_mul_distrib,Function.comp_apply, he]
  rw [mul_right_comm, ← Finset.prod_mul_distrib]; simp [weights,Complex.real_smul]
end

variable [MetricSpace X] [BorelSpace X] [CompactSpace X] [SecondCountableTopology X] [IsFiniteMeasure μ]

theorem learns (k : List (K X)) (hp : k≠[]) (h : ∀ i ∈ k, Continuous (Function.uncurry i)) :
    Tendsto (fun i => ((k.map (sample μ (Quad.shrink X i))).prod).trace) atTop (𝓝 (closed μ k)) := by
  rcases k with _|⟨k,l⟩; cases hp rfl
  let V : Fin (l.length+1) → K X := List.get (k::l)
  have he : List.ofFn V = k::l := List.ofFn_get _
  have ht (i) : ((List.map (sample μ (Quad.shrink X i)) (k::l)).prod).trace=(∑ p : Fin (l.length+1) → Fin (Quad.shrink X i).size,
    (∏ j, Quad.mass (Quad.shrink X i) μ (p j)) • cycle V ((Quad.shrink X i).tag ∘ p)) := by
    rw [← measureWeight μ _ _ _,Holder.combine]
    change _ = ((List.ofFn ((sample μ (Quad.shrink X i)) ∘ V)).prod).trace; rw [← List.map_ofFn]
    rw [he]
  simp_rw [ht]; exact Quad.approximation μ _ (cont_cycle V fun i => h _ (List.get_mem ..))

end YM.TimeKernel
