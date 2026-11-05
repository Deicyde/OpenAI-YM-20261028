import YM.Push.STATIONARY_UNIFORM.Array
import YM.Push.STATIONARY_UNIFORM.Resolvent
import YM.Push.STATIONARY_UNIFORM.Scatter


/-!
# Counting slope and Hessian on domains of score tensors

`Slope` has the coordinates of the partial real derivative; same column and
row convention as Stationed. No assuming a counting-size derivative bound on
the whole extensive action w.r.t. the Pi norm. Get Lipschitz precision error
from cubic cost, also in positions before summing. All estimates uniform in
ball-size and K multiplicity inputs (pre-L when paid upstream).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Lattice Matrix Filter Function Set Metric
open scoped Topology ContDiff BigOperators Classical

variable {n : Side} {ι τ : Type} [Fintype ι] [Fintype τ] {a C r ρ m : ℝ} {N K : ℕ}

lemma combine (v : Positions ι) : ∑ i, v i • bolt i = v := by
  funext i; rw [Finset.sum_apply, Finset.sum_eq_single i]; simp [bolt]; intro j _ hj; simp [bolt,Ne.symm hj]; simp

lemma by_row {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : Positions ι →L[ℝ] E) (v : Positions ι) :
    L v = ∑ i, v i • L (bolt i) := by
  conv_lhs => rw [← combine v,map_sum]
  simp_rw [map_smul]

section Increment
variable {f : Positions ι → ℝ} {p x : Positions ι} {l : ι → Site n}
lemma tend_entry (hf : ContDiffAt ℝ ω f p) {k : ℕ} (q : Fin k → ι) :
    ContDiffAt ℝ ω (fun z => entry f z q) p ∧ ∀ i, fderiv ℝ (fun z => entry f z q) p (bolt i)=entry f p (Matrix.vecCons i q) := by
  let L := ContinuousMultilinearMap.apply ℝ _ ℝ (fun j => bolt (q j))
  let g := iteratedFDeriv ℝ k f
  have hg : ContDiffAt ℝ ω g p := hf.iteratedFDeriv_right (by simp)
  refine ⟨L.contDiff.contDiffAt.comp p hg,?_⟩
  intro i; change fderiv ℝ (L ∘ g) p _ = _
  rw [fderiv_comp p L.differentiableAt (hg.differentiableAt (by simp)), L.fderiv,entry,iteratedFDeriv_succ_apply_left]
  change (fderiv ℝ g p (bolt i)) (fun j => bolt (q j)) = (fderiv ℝ g p (bolt i)) (Fin.tail (α:=fun _ : Fin (k+1) => Positions ι) (fun j=>bolt (Matrix.vecCons i q j)))
  congr 1

lemma Scatter.taper (ha : 0<a) (hp : 0≤C) (hK : Multiplicity l K) (hf : ContDiffAt ℝ ω f p) (h : Scatter l a N f p C)
    {k : ℕ} (hk : k<N) (q : Fin k → ι) (t : Fin k) :
    ‖fderiv ℝ (fun z => entry f z q) p‖ ≤ C*((K:ℝ)*countCost a)*Real.exp (-a*spanSites l (l (q t)) q) := by
  let y := l (q t); let T := Real.exp (-a*spanSites l y q)
  let F := fderiv ℝ (fun z => entry f z q) p
  have hs i : ‖F (bolt i)‖ ≤ Decay a y (l i)*(C*T) := by
    let Q := Matrix.vecCons i q
    rw [show F (bolt i)=_ from (tend_entry hf q).2 i]
    have hh : spanSites l y Q = separation y (l i)+spanSites l y q := by simp [spanSites,Q,Fin.sum_univ_succ]
    apply le_trans (h _ hk Q t.succ); apply le_of_eq
    change C*Real.exp (_*(spanSites l y Q:ℝ))=_
    rw [hh,Nat.cast_add, mul_add, Real.exp_add]; unfold T Decay; ring
  have hv := count_pos ha
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [by_row]
  apply le_trans (norm_sum_le ..)
  have hL : 0≤C*T*‖v‖ := by unfold T; positivity
  calc
    _ ≤ ∑ i, Decay a y (l i)*(C*T*‖v‖) := Finset.sum_le_sum fun i _ => by
      rw [norm_smul]
      exact (mul_le_mul (norm_le_pi_norm v _) (hs i) (norm_nonneg _) (norm_nonneg _)).trans_eq (by ring)
    _ = (∑ i, Decay a y (l i))*(C*T*‖v‖) := by rw [Finset.sum_mul]
    _ ≤ _ := (mul_le_mul_of_nonneg_right (hK.count l ha y) hL).trans_eq (by unfold T y; ring)

lemma scatter_difference {s : Set (Positions ι)} (ha : 0<a) (hp : 0≤C) (hK : Multiplicity l K)
    (hs : Convex ℝ s) (hf : ∀ p∈s, ContDiffAt ℝ ω f p ∧ Scatter l a N f p C) (hx : x∈s) (hh : p∈s)
    {k : ℕ} (hk : k<N) (q : Fin k → ι) (t : Fin k) :
    ‖entry f p q-entry f x q‖ ≤ ‖p-x‖*(C*((K:ℝ)*countCost a))*Real.exp (-a*spanSites l (l (q t)) q) := by
  rw [mul_assoc ‖p-x‖, mul_comm ‖p-x‖]
  exact hs.norm_image_sub_le_of_norm_fderiv_le
    (fun y hy => ((tend_entry (hf y hy).1 q).1).differentiableAt (by simp)) (fun y hy => (hf y hy).2.taper ha hp hK (hf y hy).1 hk q t) hx hh
end Increment

section Positions
variable {f : Positions (ι ⊕ τ) → ℝ}
variable {p : Positions (ι ⊕ τ)} {x : Positions ι} {v : Positions τ}

def meetVar (x : Positions ι) (v : Positions τ) := (partSpace ι τ).symm (x,v)
lemma norm_meet (x : Positions ι) (v : Positions τ) : ‖meetVar x v‖ = max ‖x‖ ‖v‖ := by
  rw [← parts_isometry,meetVar,(partSpace ..).apply_symm_apply]; rfl
lemma meet_columns (x : Positions ι) (v : Positions τ) : meetVar x v = meetVar x (0:Positions τ) + meetVar (0:Positions ι) v := by
  unfold meetVar; rw [← map_add, Prod.mk_add_mk, add_zero,zero_add]

def lowerCol : Positions τ →L[ℝ] Positions (ι ⊕ τ) :=
  (partSpace ι τ).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Positions ι) (Positions τ))
lemma lower_bolt (i : τ) : lowerCol (ι:=ι) (bolt i) = bolt (Sum.inr i) := by
  funext j; cases j with
  | inl j => change (0:ℝ) = bolt (Sum.inr i) (Sum.inl j); simp [bolt]
  | inr j => change bolt i j = bolt (Sum.inr i) (Sum.inr j); by_cases he : j=i <;> simp [bolt,he]

lemma meet_derivative (x : Positions ι) (v : Positions τ) : HasFDerivAt (meetVar x) lowerCol v := by
  have hh := (lowerCol (ι:=ι) (τ:=τ)).hasFDerivAt (x:=v)
  exact (hh.const_add (meetVar x (0:Positions τ))).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => meet_columns x y))

def Slope (f : Positions (ι ⊕ τ) → ℝ) (p : Positions (ι ⊕ τ)) : Positions τ := fun i =>
  entry f p ![Sum.inr i]

def block (f : Positions (ι ⊕ τ) → ℝ) (p : Positions (ι ⊕ τ)) : Matrix τ τ ℝ := of fun i j =>
    entry f p ![Sum.inr j,Sum.inr i]

lemma slope_zero_test (hf : ContDiffAt ℝ ω f (meetVar x v)) :
    Slope f (meetVar x v)=0 ↔ HasFDerivAt (fun y => f (meetVar x y)) (0 : Positions τ →L[ℝ] ℝ) v := by
  let p := meetVar x v
  let L := (fderiv ℝ f p).comp lowerCol
  have he : HasFDerivAt (fun y => f (meetVar x y)) L v :=
    (hf.differentiableAt (by simp)).hasFDerivAt.comp v (meet_derivative x v)
  have hh (i : τ) : Slope f p i=L (bolt i) := by
    unfold Slope entry; rw [iteratedFDeriv_one_apply]; unfold L; rw [ContinuousLinearMap.comp_apply,lower_bolt]; rfl
  constructor
  · intro hx; suffices ht : L=0 by rwa [ht] at he
    ext z; rw [by_row]; change Slope f p=0 at hx; simp only [← hh,hx]; simp
  intro hx; funext i; change Slope f p i=_; rw [hh,he.unique hx]; rfl

lemma block_hermitian (hf : ContDiffAt ℝ ω f p) : (block f p).IsHermitian := by
  apply IsHermitian.ext; intro i j
  simp only [block,Matrix.of_apply,star_trivial,entry,iteratedFDeriv_two_apply]; exact hf.isSymmSndFDerivAt (by simp) _ _

lemma slope_block (hf : ContDiffAt ℝ ω f (meetVar x v)) :
    ContDiffAt ℝ ω (Slope f) (meetVar x v) ∧ ∀ w, fderiv ℝ (Slope f ∘ meetVar x) v w = block f (meetVar x v) *ᵥ w := by
  let p := meetVar x v
  have ht (i : τ) := tend_entry hf ![Sum.inr i]
  have hg : ContDiffAt ℝ ω (Slope f) p := contDiffAt_pi.mpr (fun i => (ht i).1)
  refine ⟨hg,fun w => ?_⟩
  have he : HasFDerivAt (Slope f ∘ meetVar x) ((fderiv ℝ (Slope f) p).comp lowerCol) v :=
    (hg.differentiableAt (by simp)).hasFDerivAt.comp v (meet_derivative x v)
  rw [he.fderiv]; funext i
  let L := (ContinuousLinearMap.proj (φ:=fun _ => ℝ) (R:=ℝ) i).comp ((fderiv ℝ (Slope f) p).comp lowerCol)
  change L w=_
  have hu (j : τ) : L (bolt j)=block f p i j := by
    let Q := ContinuousLinearMap.proj (φ:=fun _ => ℝ) (R:=ℝ) i
    have hb := (ht i).2 (Sum.inr j)
    change fderiv ℝ (Q ∘ Slope f) p (bolt _) = _ at hb
    rw [fderiv_comp _ Q.differentiableAt (hg.differentiableAt (by simp)), Q.fderiv] at hb
    unfold L; rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,lower_bolt]; exact hb
  rw [by_row]; unfold mulVec dotProduct; simp_rw [hu,smul_eq_mul,mul_comm (w _)]; rfl

variable {l : ι ⊕ τ → Site n}
lemma block_rows (h : Scatter l a N f p C) (hn : 2≤N) : Sealed (l ∘ Sum.inr) a (block f p) C := by
  intro i j
  have he := h 2 hn ![Sum.inr j,Sum.inr i] 1
  simpa [spanSites,Fin.sum_univ_succ,block,Decay] using he

lemma block_near {s : Set (Positions (ι ⊕ τ))} (ha : 0<a) (hp : 0≤C) (hK : Multiplicity l K)
    (hs : Convex ℝ s) (hf : ∀ p∈s, ContDiffAt ℝ ω f p ∧ Scatter l a N f p C)
    {b c : Positions (ι ⊕ τ)} (hb : b∈s) (hc : c∈s) (hr : ‖b-c‖≤r) (h : 3≤N) :
    Sealed (l ∘ Sum.inr) a (block f b-block f c) (r*(C*((K:ℝ)*countCost a))) := by
  intro i j
  have he := scatter_difference ha hp hK hs hf hc hb (k:=2) h ![Sum.inr j,Sum.inr i] 1
  let Z := C*((K:ℝ)*countCost a)
  have hz := count_pos ha
  have h : |(block f b-block f c) i j| ≤ ‖b-c‖*Z*Decay a (l (Sum.inr i)) (l (Sum.inr j)) := by
    simpa [block,Decay, Z, spanSites,Fin.sum_univ_succ,Real.norm_eq_abs] using he
  exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr (by positivity)) (decay_pos ..).le)
lemma slope_range {s : Set (Positions (ι ⊕ τ))} (ha : 0<a) (hp : 0≤C) (hK : Multiplicity l K)
    (hs : Convex ℝ s) (hf : ∀ p∈s, ContDiffAt ℝ ω f p ∧ Scatter l a N f p C)
    {b c : Positions (ι ⊕ τ)} (hb : b∈s) (hc : c∈s) (hn : 2 ≤ N) :
    ‖Slope f b-Slope f c‖ ≤ ‖b-c‖*(C*((K:ℝ)*countCost a)) := by
  have hp := count_pos ha
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ ‖b-c‖*(C*((K:ℝ)*countCost a)))).mpr
  intro i
  simpa only [Pi.sub_apply, Slope,spanSites, Fin.sum_univ_one,separation_self,Nat.cast_zero,mul_zero,Real.exp_zero,mul_one] using
    scatter_difference ha ‹0≤C› hK hs hf hc hb (k:=1) hn ![Sum.inr i] 0
end Positions
end YM.Push.Uniform
