import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Bid.Craft
import YM.Bid.Fuels
import YM.Bid.Loan
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B06
import YM.Work.B17
import YM.Work.G07.Stencil

/-!
# Same-section/torus readout checks

Further RAuthors lemmas for use in producers.

In particular, compare
`Sound.projects` against the **actual tests used by Format**, on finite
tori, including the support and the wrapping convention of the code.

The readout is on the pre-mask function.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Foundations

open Lattice Wilson RG Source Labels
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff

variable {G : Gauge}

section Scale

/-! ### Two different scalings

Separate **engineering** (= scale in h) and **slot** (= scale jet amplitudes,
threshold in credits).
-/

private lemma monomial_scales (J K : Jet G) (w : Key G → ℕ) (t : ℝ)
    (h : ∀ i, coord K i = t^(w i) • coord J i) (m : Key G →₀ ℕ) (c : ℂ) :
    read K (MvPolynomial.monomial m c) = t^(Finsupp.weight w m) • read J (MvPolynomial.monomial m c) := by
  classical
  simp only [Labels.read, MvPolynomial.aeval_monomial, Algebra.algebraMap_self, RingHom.id_apply,
    Complex.real_smul, Complex.ofReal_pow, Finsupp.prod]
  have he (i : Key G) : coord K i ^ (m i) =
      (t : ℂ)^(m i * w i) * coord J i ^ (m i) := by
    rw [h]; simp only [Complex.real_smul, Complex.ofReal_pow, mul_pow, ← pow_mul]
    rw [mul_comm (m i) _]
  simp_rw [he, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [Finsupp.weight_apply]
  simp only [Finsupp.sum, smul_eq_mul]
  ring

lemma coord_scales (J : Jet G) (t : ℝ) (i : Key G) :
    coord (scaleJet J t) i = t^(generation i) • coord J i := by
  simp [scaleJet, Labels.coord, generation, Complex.real_smul]

lemma read_smooth (J : Jet G) (p : Pol G) (k : WithTop ℕ∞) :
    ContDiff ℝ k (fun h => read (scaleJet J h) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [Labels.read, MvPolynomial.aeval_C]; exact contDiff_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, Labels.read, MvPolynomial.aeval_X, coord_scales]
    exact hp.mul ((contDiff_id.pow _).smul contDiff_const)

def tier (k : ℕ) : Pol G →ₗ[ℂ] Pol G := MvPolynomial.weightedHomogeneousComponent generation k

lemma deriv_read (J : Jet G) (p : Pol G) (k : ℕ) :
    iteratedDeriv k (fun h => read (scaleJet J h) p) 0 = (k.factorial : ℝ) • read J (tier k p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial m c =>
    simp_rw [monomial_scales J _ generation _ (coord_scales J _)]
    have hs : ContDiffAt ℝ k (fun t : ℝ => t^(Finsupp.weight generation m)) 0 := contDiffAt_id.pow _
    rw [iteratedDeriv_smul_const hs, iteratedDeriv_fun_pow_zero]
    have hh := MvPolynomial.isWeightedHomogeneous_monomial (generation (G:=G)) m c (m:=Finsupp.weight generation m) rfl
    by_cases he : k = Finsupp.weight generation m
    · rw [tier, if_pos he, he, hh.weightedHomogeneousComponent_same]
    rw [tier, if_neg he, hh.weightedHomogeneousComponent_ne k he]; simp
  | add p q hp hq =>
    simp only [map_add]
    rw [iteratedDeriv_fun_add (read_smooth J p _).contDiffAt (read_smooth J q _).contDiffAt, hp, hq,
      smul_add]

/-- Truncate engineering weight. -/
def capRead (d : ℕ) (p : Pol G) := ∑ k ∈ Finset.range (d+1), tier k p

lemma coeff_capRead (d : ℕ) (p : Pol G) (m) :
    (capRead d p).coeff m = if height m ≤ d then p.coeff m else 0 := by
  simp [capRead, height, MvPolynomial.coeff_sum, tier, MvPolynomial.coeff_weightedHomogeneousComponent]

lemma tier_capRead (d : ℕ) (p : Pol G) (k : ℕ) (hk : k ≤ d) :
    tier k (capRead d p) = tier k p := by
  ext m
  simp only [tier, MvPolynomial.coeff_weightedHomogeneousComponent, coeff_capRead, height]
  split_ifs <;> first | rfl | omega

lemma cap_limited (d : ℕ) (p : Pol G) : capRead d p ∈ limited G d := by
  classical
  apply (MvPolynomial.mem_restrictSupport_iff ℂ).mpr
  intro i hi
  change height i ≤ d
  by_contra hh
  exact MvPolynomial.mem_support_iff.mp (Finset.mem_coe.mp hi) (by rw [coeff_capRead, if_neg hh])

lemma limited_cap (d : ℕ) (p : Pol G) (h : p ∈ limited G d) : capRead d p = p := by
  classical
  ext m
  rw [coeff_capRead]
  split_ifs with he
  · rfl
  symm
  by_contra hh
  exact he ((MvPolynomial.mem_restrictSupport_iff ℂ).mp h
    (Finset.mem_coe.mpr (MvPolynomial.mem_support_iff.mpr hh)))

lemma jet_test_ext {d} (p q : Label G d)
    (h : ∀ (J : Jet G) k, k ≤ d → iteratedDeriv k (fun x => read (scaleJet J x) p.val) 0 =
      iteratedDeriv k (fun x => read (scaleJet J x) q.val) 0) : p = q := by
  have ht (k : ℕ) (hk : k ≤ d) : tier k p.val = tier k q.val := by
    refine eval_ext _ _ fun J => ?_
    have he := h J k hk
    rw [deriv_read, deriv_read] at he
    exact smul_right_injective ℂ (show ((k.factorial:ℝ)) ≠ 0 by positivity) he
  apply Subtype.ext
  show p.val = q.val
  rw [← limited_cap d _ p.property.1, ← limited_cap d _ q.property.1]
  exact Finset.sum_congr rfl fun k hk => ht k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

lemma read_pure (J : Jet G) {d : ℕ} {p : Label G d} {m : ℕ × ℕ} (h : p ∈ Grade m)
    (θ : ℝ) : read (θ • J) p.val = θ^m.2 • read J p.val := by
  classical
  have hw : MvPolynomial.IsWeightedHomogeneous (fun _ : Key G => (1:ℕ)) p.val m.2 := by
    intro q hq
    have he := (pure_grade _ p).1 h hq
    rw [weight_slot] at he
    simpa [Finsupp.weight_apply, smul_eq_mul] using congr_arg Prod.snd he
  have ht (i : Key G) : coord (θ • J) i = θ^(1:ℕ) • coord J i := by
    simp [Labels.coord, Complex.real_smul]
  have hsum := p.val.as_sum
  rw [hsum, map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [monomial_scales J _ (fun _ => 1) θ ht, hw (MvPolynomial.mem_support_iff.mp hi)]

/-- Diagonal threshold powers in the basis are *slot* scaling. -/
theorem read_frame_scaled (J : Jet G) {d : ℕ} (F : Labels.Frame G d) (v : F.Coeff) (θ : ℝ) :
    read J (F.coords.symm (F.scaled θ v)).val = read (θ • J) (F.coords.symm v).val := by
  let p := F.coords.symm v
  have h0 : v = F.coords p := (F.coords.apply_symm_apply v).symm
  rw [h0, LinearEquiv.symm_apply_apply, ← F.basis.sum_repr p]
  simp only [map_sum, map_smul, AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul_of_tower]
  apply Finset.sum_congr rfl
  intro i _
  rw [F.scaled_pure _ _ (F.pure i), map_smul, LinearEquiv.symm_apply_apply,
    read_pure (p:=F.basis i) J (F.pure i)]
  simp [Complex.real_smul]

end Scale

section Placement

variable {d : ℕ} {n : Side}

/-- Torus test corresponding to `Source.Projects` and `Hol.PiVanish`.
Total for convenience at an arbitrary torus size; only to be used for
reading fields under appropriate support assumptions (see `Reads`). -/
def JetTest (H : Hol G) (o : Site n) (p : Label G d) (f : Config G n → ℂ) :=
  ∀ J : Jet G,
    let w := fun h => f (H.testLinks d o J h)
    let g := fun h => read (scaleJet J h) p.val
    ContDiffAt ℝ (d : WithTop ℕ∞) w 0 ∧ ContDiffAt ℝ (d : WithTop ℕ∞) g 0 ∧
      ∀ k ≤ d, iteratedDeriv k w 0 = iteratedDeriv k g 0

open scoped Classical in
/-- On wrapping supports (i.e., `¬Nonwrapping X o`) retain only the identity
evaluation, matching the lifted-vs-constant test in Format. As in the
original interface, interpret the nonwrapping case as a genuine embedded
cover stencil **for the intended periods**. There is a degenerate size-one
torus issue outside those: `Nonwrapping` alone wouldn't exclude a self-loop,
and `H.testLinks` there is just the specified formula (see below). -/
def Reads (H : Hol G) (o : Site n) (X : Support n) (p : Label G d) (f : Config G n → ℂ) :=
  if Nonwrapping X o then JetTest H o p f else p = f 1 • unit G d

lemma JetTest.unique {H : Hol G} {p q : Label G d} {o : Site n} {f : Config G n → ℂ}
    (hp : JetTest H o p f) (hq : JetTest H o q f) : p = q :=
  jet_test_ext p q fun J k hk => ((hp J).2.2 k hk).symm.trans ((hq J).2.2 k hk)

lemma Reads.unique {H : Hol G} {p q : Label G d} {o : Site n} {X : Support n}
    {f : Config G n → ℂ} (hp : Reads H o X p f) (hq : Reads H o X q f) : p = q := by
  unfold Reads at *
  split at hp <;> rename_i h
  · rw [if_pos h] at hq
    exact JetTest.unique hp hq
  rw [if_neg h] at hq
  exact hp.trans hq.symm

lemma jetTest_zero_iff (H : Hol G) (o : Site n) (f : Config G n → ℂ) (d : ℕ) :
    JetTest H o (0 : Label G d) f ↔ H.PiVanish d o f := by
  have he (J : Jet G) (k : ℕ) :
      iteratedDeriv k (fun h => read (scaleJet J h) (0 : Label G d).val) 0 = 0 := by
    rw [deriv_read]; simp
  constructor
  · intro h J; exact ⟨(h J).1, fun k hk => ((h J).2.2 k hk).trans (he _ _)⟩
  intro h J
  exact ⟨(h J).1, (read_smooth J _ _).contDiffAt,
    fun k hk => ((h J).2 k hk).trans (he _ _).symm⟩

/-- The endpoints really lift together. -/
theorem lift_end (hn : 2 ≤ n.val) {X : Support n} {o : Site n} (h : Nonwrapping X o)
    (x : Site n) (hx : x ∈ X) (i : Axis) : lift (x+step i-o) = lift (x-o) + step i := by
  refine lift_eq_iff.mpr ⟨?_, fun j => ?_⟩
  · rw [map_add, wrap_lift, wrap_step]; abel
  have ht := h x hx
  have hu : (lift (x-o) j).natAbs ≤ separation x o := component_le _ _
  simp only [Pi.add_apply, step_apply]
  split <;> omega



theorem actual_side_ge (S : Schedule) (N p : ℕ) : 4 ≤ (S.side N p).val :=
  Nat.le_of_dvd (S.side N p).property (S.side_four N p)

private lemma stencil_lift {Y : Finset Cover} (h : ∀ x ∈ Y, ∀ i : Axis,
    20*((x i).natAbs+1) ≤ n.val) {x : Cover} (hx : x ∈ Y) : lift (wrap n x) = x := by
  refine lift_eq_iff.mpr ⟨rfl, fun i => ?_⟩
  have hi := h x hx i; omega

lemma nonwrapping_placement {F : Labels.Frame G d} (T : SectionData F) (o : Site n)
    (h : ∀ x ∈ T.stencil, ∀ i : Axis, 20*((x i).natAbs+1) ≤ n.val) : Nonwrapping (T.footprint o) o := by
  rintro y hy
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  simp only [separation, add_sub_cancel_right, pdist, stencil_lift h hx]
  have hn := n.property
  have hu : (Finset.univ.sup fun i : Axis => (x i).natAbs) ≤ (n.val-1)/10 := by
    refine Finset.sup_le fun i _ => ?_
    have := h x hx i; omega
  apply lt_of_le_of_lt (Nat.mul_le_mul_left 10 hu)
  rw [mul_comm]
  exact lt_of_le_of_lt (Nat.div_mul_le_self _ _) (Nat.sub_lt hn (by decide))

theorem placed_reads {F : Labels.Frame G d} {H : Hol G} (T : SectionData F)
    (o : Site n) (h : ∀ x ∈ T.stencil, ∀ i : Axis, 20*((x i).natAbs+1) ≤ n.val)
    (hT : T.Sound H) (v : F.Coeff) : Reads H o (T.footprint o) (F.coords.symm v) (T.places v o) := by
  rw [Reads, if_pos (nonwrapping_placement T o h)]
  have he (J : Jet G) : (fun x => T.places v o (H.testLinks d o J x)) =
      (fun x => T.evaluate v (H.links d J x)) := by
    funext r
    apply T.cylinder_local v
    intro e hi _
    change H.links d J r (lift (wrap n e.1 + o - o), e.2) = H.links d J r e
    rw [add_sub_cancel_right, stencil_lift h (Finset.mem_coe.mp hi)]
  intro J
  dsimp only
  rw [he]
  exact hT.projects v J

end Placement
end YM.Next.Foundations
