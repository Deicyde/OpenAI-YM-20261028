import YM.Next.FOUNDATIONS.SU2
import YM.Push.GRID_APPROXIMATION.Estimate
import YM.Push.GRID_APPROXIMATION.Picture

/-!
# Bounded local candidates from signed stop estimates

These basis requests are substantial many-source RG inputs; see Estimate.
Here apply them to clusters of all copies of one actual weight family member
at the fixed h grid, with actual canonical probes matched at k (`x` supplied
by the hypotheses). All `C.localSection` stencils and physical, unnormalized
`a_k^{-d}` prescriptions stay in the selected path . Construct
bounded probes on FINE links, keeping the tag choices used for the mixed
comparison.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.GridApprox
open RG Lattice Wilson Labels Source Cells MeasureTheory Function Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} (C : Family G)

def stencilRadius (d : ℕ) := (C.localSection d).stencil.sup (fun x => Finset.univ.sup (fun i => (x i).natAbs))

def candidate (k p d : ℕ) (v : C.label d) : Config G (C.side k p) → ℂ :=
    initial (C.localSection d) C.path k p v 0

lemma stencil_fits {n : Side} (d : ℕ) (o : Site n) :
    (↑((C.localSection d).footprint o) : Set (Site n)) ⊆ window o (stencilRadius C d) := by
  intro x hx; obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  have he i : (y i).natAbs ≤ stencilRadius C d :=
    le_trans (Finset.le_sup (f:=fun i => (y i).natAbs) (Finset.mem_univ i))
      (Finset.le_sup (f:=fun x => Finset.univ.sup (fun i => (x i).natAbs)) hy)
  exact ⟨y,box_test.mpr ⟨fun i => by have := he i; omega, fun i => by have := he i; omega⟩,rfl⟩

lemma candidate_fits (h : C.Makes) (k p d : ℕ) (v : C.label d) :
    Interior (window 0 (stencilRadius C d)) (candidate C k p d v) := by
  let D := C.localSection d
  unfold candidate initial
  let w := (C.labels.level d).scaled (C.path.levels.clock.threshold k)⁻¹ v
  have hp := D.continuous_places (n:=C.side k p) w 0
  have he : Interior (D.footprint (0:Site (C.side k p))) (D.places w 0) :=
    ⟨D.placed_invariant (h.sections d) 0 w,hp.measurable,D.placed_local 0 w,(Envelope.compactC hp).cost⟩
  exact (he.enlarges (stencil_fits C d 0)).scale _

lemma candidate_star (h : C.Makes) (k p d : ℕ) (v : C.label d) (V) :
    star (candidate C k p d v V)=candidate C k p d (star v) V := by
  unfold candidate initial SectionData.places
  have hs (t : ℝ) : (C.labels.level d).scaled t (star v)=star ((C.labels.level d).scaled t v) := by
    funext i; simp [mul_comm]
  simp only [hs,(h.sections d).ordinary_real]; simp

lemma coeff_sum {d : ℕ} (v : C.label d) : (∑ i, v i • (Pi.single i 1 : C.label d))=v := by
  simp only [← Pi.single_smul, smul_eq_mul, mul_one]
  exact Finset.univ_sum_single _

/-- Genuine pointwise full-group bound, uniform in N,p at fixed k. -/
lemma candidate_bounded (d k : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    ∃ A : ℝ, 0 < A ∧ ∀ p (v : C.label d), ‖v‖ ≤ D → ∀ V, ‖candidate C k p d v V‖ ≤ A := by
  let s := C.localSection d
  let F := (C.labels.level d)
  let f : C.label d →ₗ[ℂ] (CoverConfig G → ℂ) :=
    ((C.S.a k:ℂ)^d)⁻¹ • ((s.eval_linear.mk' s.evaluate).comp (F.scaled (C.path.levels.clock.threshold k)⁻¹))
  have ht (i : F.Index) : Continuous (f (Pi.single i 1)) := by
    refine continuous_const.mul (s.continuous_evaluate _)
  have hB (i : F.Index) : ∃ A : ℝ, 0 ≤ A ∧ ∀ V, ‖f (Pi.single i 1) V‖ ≤ A := by
    obtain ⟨A,hA⟩ := (Envelope.compactC (ht i)).cost
    exact ⟨max 0 A,le_max_left ..,fun V => (hA V).trans (le_max_right ..)⟩
  choose a ha he using hB
  have hA : 0 ≤ ∑ i, D * a i := Finset.sum_nonneg fun i _ => mul_nonneg hD (ha i)
  refine ⟨1+∑ i, D*a i,by linarith,fun p v hv V => ?_⟩
  let U := expandAt 0 V
  have hx : candidate C k p d v V = ∑ i, v i * f (Pi.single i 1) U := by
    change f v U = _
    conv_lhs => rw [← coeff_sum C v,map_sum]
    simp
  rw [hx]
  apply le_trans (norm_sum_le ..) (le_trans (Finset.sum_le_sum ?_) (le_add_of_nonneg_left zero_le_one))
  intro i _; rw [norm_mul]; exact mul_le_mul ((norm_le_pi_norm v i).trans hv) (he i _) (norm_nonneg _) hD

/-- Earlier events common to any cutoff choices of probes, from literal
fine support. No price assumptions. -/
lemma original_late (hC : C.Makes) (f : Extraction.Order) (h : ℕ) (v : C.book.Token) :
    f.late fun N p => C.ref v.1 ≤ N ∧ ∃ hN : h ≤ N,
      Interior ((tilesAt C.S p hN).chamber 0) (C.seen v (0:Site (C.side N p))) := by
  unfold Extraction.Order.late
  filter_upwards with k
  filter_upwards [f.mesh.cofinal.eventually_ge_atTop (C.ref v.1),
    f.mesh.cofinal.eventually (Stock.clear_interior C hC h v.1)] with i hi hh
  obtain ⟨hp,hX⟩ := hh; exact ⟨hi,hp,hX (f.per k) 0 v.2⟩

/-- A concrete sufficient quantitative *input*, entirely on C. Calls for
representation/norm receipts from the k-birth signed match at a fixed stop
r; no assumption of convergence nor of proximity of cutoff correlations to
bounded plots. Assume for one real basis direction of the reference field at
fixed h. For arbitrary M need arbitrarily large k and marker radius W at
r, while the charges at r stay fixed. Coefficients matching the probe can vary
on the cutoff torus but must really give this scaled signal and respect fixed
bounds D at a fixed station. If believing that 's exponentially falling
`H^{Δ}` envelopes can be implemented at all these h's, would still need, for
example, prove precisely the actual `Bands` implication such as this (or
supply some other input) including compatibility/scheduling. Nothing in the
accepted unmarked or extraction/phase results purports to give this.
`late` estimate, doesn't require any uniform mesh-after-tuning for all p. -/
def Supplies (f : Extraction.Order) (h : ℕ) (v : C.book.Token) : Prop :=
    ∃ r : ℕ, ∃ hh : h ≤ r, ∃ u c d' b : ℝ, 0 < u ∧ 0 < c ∧ 0 < d' ∧ 0 < b ∧
    ∀ M : ℕ, ∃ k ≥ M, ∃ hr : r ≤ k, ∃ W D : ℝ, (((M+1):ℕ):ℝ) ≤ W ∧ 0 ≤ D ∧
      ∃ x : ℕ → ℕ → C.label v.1,
      f.late fun N p => ∃ hN : k ≤ N, star (x N p)=x N p ∧ ‖x N p‖ ≤ D ∧
        Joint.Receipt C.path N p (hh.trans hr) hN (C.seen v 0) (candidate C k p v.1 (x N p)) hh hr v.1 W u c d' b

namespace Candidates

/-- The plotted fine observable at the requested (fixed) station. -/
def query {k N : ℕ} (p d : ℕ) (hN : k ≤ N) (v : C.label d) :=
    backTo C.path N p hN (candidate C k p d v)

private lemma anchor_zero (S : Schedule) {h m p : ℕ} (q : h≤m) : anchor S p q 0=0 := (S.toDepth q p).root.map_zero

/-- Quantitative price before changing any subsequences. Keep the same
observable `query`, support budget and bounds. -/
lemma adequate (hC : C.Makes) (v : C.book.Token) {h r k N : ℕ} (p : ℕ) (hh : h ≤ r) (hr : r ≤ k)
    (hN : k ≤ N) (x : C.label v.1) (hx : star x=x) (A W u c d' b : ℝ)
    (hc : ∀ V, ‖candidate C k p v.1 x V‖ ≤ A)
    (hW : 0 < W) (he : C.ref v.1 ≤ N) (hO : Interior ((tilesAt C.S p ((hh.trans hr).trans hN)).chamber 0) (C.seen v 0))
    (hRoom : room C.path.levels h k (stencilRadius C v.1))
    (ht : Joint.Receipt C.path N p (hh.trans hr) hN (C.seen v 0) (candidate C k p v.1 x) hh hr v.1 W u c d' b) :
    PictureAt C v h N p (query C p v.1 hN x) A (Joint.cost C.path h r v.1 u c d' b / W)
      (C.S.a k * stencilRadius C v.1 + tail C.path.levels k) := by
  let q := hh.trans hr
  let w := stencilRadius C v.1
  let L := C.path.levels
  let Z := candidate C k p v.1 x
  have hF : Interior (window 0 w) Z := candidate_fits C hC k p v.1 x
  have hh' : Interior (window (anchor C.S p q 0) w) Z := by rw [anchor_zero]; exact hF
  have hi := backTo_local C.path N p q hN 0 w hh'
  let g := grows L k w hN
  have ha : Interior (window 0 g) (query C p v.1 hN x) := by
    rw [anchor_zero] at hi; exact hi
  refine ⟨q.trans hN,he,hO,hi.enlarges (room_fits p L w q hN hRoom _),⟨g,?_,ha⟩,
    backTo_bound C.path N p hN hF.borel A hc, ?_,?_⟩
  · exact le_trans (le_add_of_nonneg_right (tail_pos L N).le) (scales_budget L k w hN)
  · have hb := backTo_star C.path N p hN (cylinder_env hF)
    rw [show (fun U => star (Z U))=Z from funext fun V => (candidate_star C hC k p v.1 x V).trans (by rw [hx])] at hb
    exact fun U => (congr_fun hb U).symm
  exact Joint.receipt_root C.path N p q hN hC.wilson (cylinder_env hO) w hF hRoom hh hr v.1 W u c d' b hW ht

lemma provided (hC : C.Makes) (f : Extraction.Order) (h : ℕ) (v : C.book.Token) (hp : star v.2=v.2)
    (H : Supplies C f h v) : HasFigures C v h f := by
  obtain ⟨r,hh,u,c,d',b,hu,hc,hd,hb,hR⟩ := H
  let w := stencilRadius C v.1
  obtain ⟨m,hm⟩ := eventually_atTop.1 (plenty C.path.levels h w)
  choose k hk hr W D hW hD x hx using fun q : ℕ => hR (max q m)
  choose a ha hA using fun q : ℕ => candidate_bounded C v.1 (k q) (D q) (hD q)
  let Y : Figures C v h :=
    { plot q N p := if he : k q ≤ N then query C p v.1 he (x q N p) else 0
      cap := a
      err q := Joint.cost C.path h r v.1 u c d' b / W q
      radius q := C.S.a (k q)*w+tail C.path.levels (k q) }
  have hkq (q) : q ≤ k q := (le_max_left _ _).trans (hk q)
  have hw (q : ℕ) : (q:ℝ) < W q := lt_of_lt_of_le (by exact_mod_cast (by omega : q < max q m+1)) (hW q)
  have hw' (q) : 0<W q := lt_of_le_of_lt (by positivity : (0:ℝ) ≤ (q:ℝ)) (hw q)
  have hK : Tendsto k atTop atTop := tendsto_atTop_mono hkq tendsto_id
  refine ⟨Y,hp,ha,(fun q => (div_pos (Joint.cost_pos ..) (hw' q)).le),fun q => ?_,?_,?_,?_⟩
  · exact add_nonneg (mul_nonneg (C.S.a_pos _).le (by positivity)) (tail_pos ..).le
  · have hh' : Tendsto W atTop atTop := tendsto_atTop_mono (fun i => (hw i).le) tendsto_natCast_atTop_atTop
    simp only [Y,div_eq_mul_inv]; simpa only [mul_zero,comp_apply] using (tendsto_inv_atTop_zero.comp hh').const_mul (Joint.cost C.path h r v.1 u c d' b)
  · simpa only [zero_mul,add_zero] using! (((C.S.shrinks.comp hK).mul_const (w:ℝ)).add ((tail_zero C.path.levels).comp hK))
  intro q
  have he := hx q
  have ht := original_late C hC f h v
  unfold Extraction.Order.late at *
  filter_upwards [he,ht] with i hi hs
  filter_upwards [hi,hs] with j hj hh'
  obtain ⟨hkN,hreal,hcap,he⟩ := hj
  dsimp only [Y]; rw [dif_pos hkN]
  obtain ⟨hsuff,hN,ho⟩ := hh'
  exact adequate C hC v _ hh (hr q) hkN (x q _ _) hreal _ _ u c d' b (hA q _ _ hcap) (hw' q) hsuff ho
    (hm _ (le_trans (le_max_right _ _) (hk q))) he


end Candidates
end YM.Push.GridApprox
