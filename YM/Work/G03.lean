import YM.Bid.Source
import YM.Extraction.Round
import YM.Maxwell.Exterior


/-!
# Linearized plaquette sampler

Work on the infinite cover. Each unit square circulation of the integrated potential
is a difference of two iterated averages (no interchange of integrals needed).
Shrink the grid after extracting the highest degree by homogeneity. The different
orders of integration in the two averages become immaterial in the zero mesh limit.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.G03
open Lattice Labels RG Source Source.Drops Filter Set Function MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {k d : ℕ}

def castPos (x : Cover) : E4 := WithLp.toLp 2 fun i => (x i : ℝ)

theorem castPos_step (x : Cover) (i : Axis) : castPos (x + step i) = castPos x + basis i := by
  apply PiLp.ext; intro j
  change (((x + step i : Cover) j : ℤ) : ℝ) = ((x j : ℤ) : ℝ) + basis i j
  by_cases h : j = i <;> simp [h]

def edgeInt (A : Taylor G k) (i : Axis) (x : E4) := ∫ s : ℝ in 0..1, A.value i (x + s • basis i)

theorem continuous_value (A : Taylor G k) (i : Axis) : Continuous (A.value i) :=
  (Tensor.diag_smooth (A.val i) ∞).continuous

theorem continuous_grad (A : Taylor G k) (i j : Axis) :
    Continuous (Maxwell.grad i (A.value j)) := by
  refine (contDiff_iff_contDiffAt.mpr fun x => Maxwell.grad_smooth (f:=A.value j) (m:=1) (n:=∞) i ?_ ?_).continuous
  · exact (Tensor.diag_smooth _ ∞).contDiffAt
  · exact WithTop.coe_le_coe.mpr (le_top (a := (1+1 : ℕ∞)))

theorem grad_scale (A : Taylor G k) (i j : Axis) (v : E4) (t : ℝ) :
    Maxwell.grad i (A.value j) (t • v) = t^k • Maxwell.grad i (A.value j) v := by
  unfold Maxwell.grad Analysis.D Taylor.value
  simp only [Tensor.differential_diagonal _ (A.property.1 j)]
  change (k+1) • Tensor.diagonal _ (t • v) = t^k • ((k+1) • Tensor.diagonal _ v)
  rw [Tensor.homogeneous, smul_comm]

def meanPartial (A : Taylor G k) (i j : Axis) (x : E4) (t : ℝ) :=
  ∫ s : ℝ in 0..1, ∫ r : ℝ in 0..1,
    Maxwell.grad i (A.value j) (x + (t*s) • basis j + (t*r) • basis i)

def net (A : Taylor G k) (i j : Axis) (x : E4) (t : ℝ) :=
  meanPartial A i j x t - meanPartial A j i x t

theorem continuous_partial (A : Taylor G k) (i j : Axis) :
    Continuous fun p : E4 × ℝ => meanPartial A i j p.1 p.2 := by
  unfold meanPartial
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold uncurry
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (continuous_grad A i j).comp (by fun_prop)

theorem continuous_net (A : Taylor G k) (i j : Axis) :
    Continuous fun p : E4 × ℝ => net A i j p.1 p.2 :=
  (continuous_partial A i j).sub (continuous_partial A j i)

theorem net_at_zero (A : Taylor G k) (i j : Axis) (x : E4) :
    net A i j x 0 = Tensor.diagonal (Maxwell.takeCurl A i j) x := by
  rw [Maxwell.takeCurl_diag]
  simp [net, meanPartial]

theorem scale_partial (A : Taylor G k) (i j : Axis) (x : E4) (t : ℝ) :
    meanPartial A i j (t • x) t = t^k • meanPartial A i j x 1 := by
  have he (s r : ℝ) : t • x + (t*s) • basis j + (t*r) • basis i =
      t • (x + s • basis j + r • basis i) := by simp only [smul_add, smul_smul]
  simp only [meanPartial, he, grad_scale, intervalIntegral.integral_smul, one_mul]

theorem scale_net (A : Taylor G k) (i j : Axis) (x : E4) (t : ℝ) :
    net A i j (t • x) t = t^k • net A i j x 1 := by rw [net, scale_partial, scale_partial, net, smul_sub]

theorem partial_eq_diff (A : Taylor G k) (i j : Axis) (x : E4) :
    meanPartial A i j x 1 = edgeInt A j (x + basis i) - edgeInt A j x := by
  have hdiff (z : E4) : DifferentiableAt ℝ (A.value j) z :=
    (Tensor.diag_smooth (A.val j) ∞).differentiable (by simp) z
  have hf (z : E4) (r : ℝ) : HasDerivAt (fun u : ℝ => A.value j (z + u • basis i))
      (Maxwell.grad i (A.value j) (z + r • basis i)) r := by
    have hu : HasDerivAt (fun u : ℝ => z + u • basis i) (basis i) r := by
      simpa only [Pi.add_apply, one_smul, zero_add] using! (hasDerivAt_const r z).add ((hasDerivAt_id' r).smul_const (basis i))
    exact (hdiff _).hasFDerivAt.comp_hasDerivAt r hu
  have he (s : ℝ) : (∫ r : ℝ in 0..1, Maxwell.grad i (A.value j) (x + s • basis j + r • basis i)) =
      A.value j (x + basis i + s • basis j) - A.value j (x + s • basis j) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hf (x + s • basis j) u)]
    · simp [add_right_comm]
    exact ((continuous_grad A i j).comp (by fun_prop)).intervalIntegrable ..
  have ht (z : E4) : IntervalIntegrable (fun s : ℝ => A.value j (z + s • basis j)) volume 0 1 :=
    ((continuous_value A j).comp (by fun_prop)).intervalIntegrable ..
  simp_rw [meanPartial, one_mul, he, intervalIntegral.integral_sub (ht _) (ht _), edgeInt]

theorem square_sum (f : Edge Cover → G.Color) (x : Cover) (i j : Axis) :
    Exterior.linkSum f x (square i j) = f (x,i) + f (x+step i,j) - f (x+step j,i) - f (x,j) := by
  have he : x + step i + step j - step i = x + step j := by abel
  have ht : x + step i + step j + -step i - step j = x := by abel
  simp only [Exterior.linkSum, square, Step.used, Step.vec, negDir, posDir,
    Bool.false_eq_true, ↓reduceIte, add_zero, he, ht]
  abel

theorem edge_sum (A : Snap G d) (x : Cover) (i : Axis) :
    access A (x,i) = ∑ k ∈ Finset.range (d-1), edgeInt (expand d A k) i (castPos x) := by
  unfold access partConnection potential
  simp only [one_smul]
  apply intervalIntegral.integral_finsetSum
  intro k hk
  exact ((continuous_value (expand d A k) i).comp (by fun_prop)).intervalIntegrable ..

theorem glow_sums {A : Snap G d} (h : ∀ b, glow A b = 0) (x : Cover) {i j : Axis} (hi : i < j) :
    ∑ k ∈ Finset.range (d-1), net (expand d A k) i j (castPos x) 1 = 0 := by
  let b : Slot := ⟨route 0 x 1,⟨(i,j),hi⟩⟩
  have he : b.offset = x := route_end ..
  have hh := h b
  unfold glow at hh
  rw [he] at hh
  change Exterior.linkSum _ _ (square i j) = 0 at hh
  rw [square_sum] at hh
  simp only [edge_sum, castPos_step] at hh
  simp_rw [net, partial_eq_diff, Finset.sum_sub_distrib]
  rw [← hh]; abel

theorem net_zero (i j : Axis) (x : E4) (t : ℝ) : net (0 : Taylor G k) i j x t = 0 := by
  unfold net meanPartial Maxwell.grad Analysis.D
  change (∫ s : ℝ in 0..1, ∫ r : ℝ in 0..1, fderiv ℝ (fun _ : E4 => (0:G.Color)) _ _) -
    (∫ s : ℝ in 0..1, ∫ r : ℝ in 0..1, fderiv ℝ (fun _ : E4 => (0:G.Color)) _ _) = _
  simp

/-- If the zero-mesh antisymmetric partials vanish even just in plaquette order, the
homogeneous radial variable is zero. -/
theorem zero_of_zero_partials (A : Taylor G k)
    (h : ∀ (i j : Axis) (x : E4), i < j → net A i j x 0 = 0) : A = 0 := by
  have hc (i j : Axis) (x : E4) : Tensor.diagonal (Maxwell.takeCurl A i j) x = 0 := by
    rw [← net_at_zero]
    rcases lt_trichotomy i j with h'|h'|h'
    · exact h i j x h'
    · simp [net,h']
    · have hh := h j i x h'
      rw [net, ← neg_sub, ← net, hh, neg_zero]
  apply Taylor.value_ext; funext i x
  nth_rw 1 [← Maxwell.potential_recover A]
  rw [Maxwell.contracted_diag]
  simp only [hc, smul_zero, Finset.sum_const_zero]
  rfl

def index (t : ℝ) (x : E4) : Cover := Extraction.address t (points (n:=1) fun _ => x) 0

theorem shrink_grid (x : E4) : Tendsto (fun t : ℝ => t • castPos (index t x)) (𝓝[>] 0) (𝓝 x) := by
  let y := points (n:=1) fun _ => x
  have hh : Tendsto (fun t : ℝ => Extraction.tag t (Extraction.address t y)) (𝓝[>] 0) (𝓝 y) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg))
      (eventually_nhdsWithin_of_forall (fun t ht => Extraction.approximate (x:=y) ht)) ?_
    have ht : Tendsto id (𝓝[>] (0:ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using ht.const_mul (4*(1:ℕ) : ℝ)
  exact ((PiLp.continuous_apply _ _ (0 : Fin 1)).tendsto y).comp hh

/-- Rescale term `l` by `t^k` (pay `t^(k-l)` after homogeneity) and let the mesh go to zero. -/
theorem top_term (A : Jet G) (k : ℕ)
    (h : ∀ (x : Cover) (i j : Axis), i < j → ∑ l ∈ Finset.range (k+1), net (A l) i j (castPos x) 1 = 0) : A k = 0 := by
  apply zero_of_zero_partials
  intro i j x hij
  let f (p : E4 × ℝ) := ∑ l ∈ Finset.range (k+1), p.2^(k-l) • net (A l) i j p.1 p.2
  have he (t : ℝ) (y : Cover) : f (t • castPos y, t) = 0 := calc
    _ = ∑ l ∈ Finset.range (k+1), t^k • net (A l) i j (castPos y) 1 := by
      unfold f; apply Finset.sum_congr rfl
      intro l hl; rw [scale_net, smul_smul, ← pow_add, Nat.sub_add_cancel (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hl)]
    _ = 0 := by rw [← Finset.smul_sum, h y i j hij, smul_zero]
  have hx : f (x,0) = net (A k) i j x 0 := by
    unfold f
    rw [Finset.sum_range_succ, Finset.sum_eq_zero]
    · simp
    intro l hl; rw [zero_pow (Nat.sub_ne_zero_of_lt (Finset.mem_range.mp hl)), zero_smul]
  have hcf : Continuous f := by
    apply continuous_finsetSum
    exact fun l _ => (continuous_snd.pow _).smul (continuous_net ..)
  have ht : Tendsto (fun t : ℝ => f (t • castPos (index t x),t)) (𝓝[>] 0) (𝓝 (f (x,0))) :=
    (hcf.tendsto _).comp ((shrink_grid x).prodMk_nhds (tendsto_id.mono_left nhdsWithin_le_nhds))
  simp only [he, hx] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

theorem all_terms (A : Jet G) (k : ℕ)
    (h : ∀ (x : Cover) (i j : Axis), i < j → ∑ l ∈ Finset.range k, net (A l) i j (castPos x) 1 = 0) :
    ∀ l < k, A l = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := top_term A k h
    intro l hl
    obtain hl|rfl := (Nat.le_of_lt_succ hl).lt_or_eq
    · apply ih ?_ l hl; simpa only [Finset.sum_range_succ, hk, net_zero, add_zero] using h
    exact hk

theorem detects_all (H : Hol G) (d : ℕ) (peg : Peg H d) (A : Snap G d)
    (h : ∀ i, Blurb H d i A = 0) : A = 0 := by
  simp only [peg.initial] at h
  have he := all_terms (expand d A) (d-1) (fun x i j hij => glow_sums h x hij)
  funext ⟨i,hi⟩
  simpa only [expand, dif_pos hi, Pi.zero_apply] using he i hi

def kernel (H : Hol G) (d : ℕ) {m} (B : Fin m → Slot) : Submodule ℝ (Snap G d) :=
  ⨅ i, LinearMap.ker (Blurb H d (B i)).toLinearMap

theorem mem_kernel (H : Hol G) (d : ℕ) {m} (B : Fin m → Slot) (A : Snap G d) :
    A ∈ kernel H d B ↔ ∀ i, Blurb H d (B i) A = 0 := Submodule.mem_iInf _

theorem answer : YM.Bid.G03 := by
  intro G H d peg
  let r {m : ℕ} (B : Fin m → Slot) := Module.finrank ℝ (kernel H d B)
  let s : Set ℕ := {k | ∃ (m : ℕ) (B : Fin m → Slot), r B = k}
  obtain ⟨n,⟨m,B,rfl⟩,hmin⟩ := wellFounded_lt.has_min s ⟨_,0,Fin.elim0,rfl⟩
  refine ⟨m,B,fun A ha => detects_all H d peg A (fun b => ?_)⟩
  let B' : Fin (m+1) → Slot := Fin.cons b B
  have hh : kernel H d B' ≤ kernel H d B := by
    intro x hx; rw [mem_kernel] at hx ⊢; exact fun i => by simpa only [B', Fin.cons_succ] using hx i.succ
  have he : kernel H d B = kernel H d B' := Eq.symm (hh.eq_of_not_lt (fun hl =>
    hmin (r B') ⟨_,B',rfl⟩ (Submodule.finrank_lt_finrank_of_lt hl)))
  have hA : A ∈ kernel H d B' := he ▸ (mem_kernel ..).2 ha
  exact (mem_kernel ..).1 hA 0

/- Degree checks without Peg: weights below 2 have nothing to sample; for d=2,
every positive plaquette sees the same oriented constant curl, independently of the walk. -/
example (d : ℕ) (h : d < 2) (A : Snap G d) : A = 0 := by
  funext i
  have := i.isLt
  omega

example (A : Snap G 2) (b : Slot) : glow A b =
    Tensor.diagonal (Maxwell.takeCurl (A ⟨0, by decide⟩) b.plaq.val.1 b.plaq.val.2) 0 := by
  let p : Taylor G 0 := A ⟨0, by decide⟩
  let x := castPos b.offset
  change glow A b = Tensor.diagonal (Maxwell.takeCurl p _ _) _
  rw [← net_at_zero, show net p b.plaq.val.1 b.plaq.val.2 0 0 =
    net p b.plaq.val.1 b.plaq.val.2 x 1 by simpa using scale_net p b.plaq.val.1 b.plaq.val.2 x 0]
  simp only [glow, square_sum, edge_sum, castPos_step, net, partial_eq_diff]
  simp [expand, p, x]; abel
end YM.Work.G03
