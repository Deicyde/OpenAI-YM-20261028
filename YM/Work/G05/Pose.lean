import YM.Bid.Source
import YM.Work.G05.Taylor


/-!
# Slot polynomials for the truncated recovery map

Each real `Snap` coordinate (cast to complex) of this map is `lumin`
of a complex polynomial on panel coordinates, including if the spaces have
zero dimension. Keep lower degree bounds when substituting these polynomials
into a label monomial.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Work.G05
open Bid Labels Source Drops
open scoped Topology ContDiff BigOperators

variable {G : Gauge} {m d : ℕ}

/-- One of the read coordinates, real-linear in a Snap (also including
those zeroed out in `expand`). -/
def snapCoord (d : ℕ) (v : Key G) : Snap G d →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun x := coord (expand d x) v
      map_add' := by
        intro x y
        by_cases h : v.1 < d-1 <;> simp [coord, expand, h]
      map_smul' := by
        intro a x
        by_cases h : v.1 < d-1 <;> simp [coord, expand, h, Complex.real_smul] }

theorem snapCoord_eq (v : Key G) (x : Snap G d) : snapCoord d v x = coord (expand d x) v := rfl

/-- No need for a generic complex polynomiality theorem: expand the
real multilinear maps in panel coordinates. -/
theorem diagonal_polynomial (n : ℕ) (A : Tensor.T (GaugePanel G m) ℂ n) :
    ∃ p : Pose G m, ∀ x, lumin p x = Tensor.diagonal A x := by
  classical
  induction n with
  | zero =>
    refine ⟨MvPolynomial.C (Tensor.diagonal A 0), fun x => ?_⟩
    simp only [lumin, MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
    exact congr_arg A (Subsingleton.elim (fun _ => 0) (fun _ => x))
  | succ n ih =>
    let b := EuclideanSpace.basisFun G.ColorIndex ℝ
    let V (j : Fin m × G.ColorIndex) : GaugePanel G m := Pi.single j.1 (b j.2)
    choose p hp using fun j : Fin m × G.ColorIndex => ih (A.curryLeft (V j))
    refine ⟨∑ j, MvPolynomial.X j * p j, fun x => ?_⟩
    have hs : (∑ j : Fin m × G.ColorIndex, x j.1 j.2 • V j) = x := by
      funext i
      rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_apply,
        Finset.sum_eq_single i]
      · simp only [V, Finset.sum_apply, Pi.smul_apply, Pi.single_eq_same]; exact b.sum_repr (x i)
      · intro j _ hj
        simp [V, Finset.sum_apply, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hj)]
      · simp
    have ha : Tensor.diagonal A x = Tensor.diagonal (A.curryLeft x) x := by
      apply congr_arg A
      ext1 i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
    rw [ha]
    have he : A.curryLeft x = ∑ j : Fin m × G.ColorIndex, x j.1 j.2 • A.curryLeft (V j) := calc
      A.curryLeft x = A.curryLeft (∑ j : Fin m × G.ColorIndex, x j.1 j.2 • V j) := congr_arg _ hs.symm
      _ = _ := by rw [map_sum]; simp only [map_smul]
    rw [he]
    unfold lumin
    rw [Tensor.diagonal, map_sum, sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, MvPolynomial.aeval_X, smul_apply, Complex.real_smul]
    rw [show MvPolynomial.aeval _ (p j) = _ from hp j x]
    rfl

theorem block_polynomial (f : GaugePanel G m → Snap G d) (j : Key G) :
    ∃ p : Pose G m, ∀ x, lumin p x = coord (expand d (blockTaylor d f x)) j := by
  classical
  let L := snapCoord d j
  choose P h using fun n : ℕ => diagonal_polynomial n
    (L.compContinuousMultilinearMap (Tensor.coeff f n 0))
  refine ⟨∑ n ∈ Finset.range (d+1), P n, fun x => ?_⟩
  change lumin _ x = L (blockTaylor d f x)
  unfold lumin blockTaylor
  rw [map_sum, Finset.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro n _
  exact h n x

/-- Vanishing at zero means every monomial has at least one slot factor. -/
theorem lows_of_zero {p : Pose G m} (h : lumin p 0 = 0) : lows p 1 := by
  classical
  have he : MvPolynomial.coeff 0 p = 0 := by
    unfold lumin at h
    simp only [Pi.zero_apply] at h
    simpa [MvPolynomial.aeval_zero', MvPolynomial.constantCoeff_eq] using h
  intro a ha
  have hz : a ≠ 0 := by
    intro hu
    exact MvPolynomial.mem_support_iff.mp (hu ▸ ha) he
  obtain ⟨i, hi⟩ : a.support.Nonempty := by simpa using hz
  exact (show 1 ≤ a i from Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)).trans
    (Finset.single_le_sum (f := a) (by simp) hi)

theorem lows_mul {p q : Pose G m} {a b : ℕ} (hp : lows p a) (hq : lows q b) :
    lows (p*q) (a+b) := by
  classical
  intro i hi
  obtain ⟨x,hx,y,hy,rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hi)
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
  exact add_le_add (hp x hx) (hq y hy)

theorem lows_pow {p : Pose G m} (hp : lows p 1) (i : ℕ) : lows (p^i) i := by
  induction i with
  | zero => exact fun x _ => Nat.zero_le _
  | succ i ih => rw [pow_succ]; exact lows_mul ih hp

theorem lows_prod {α : Type*} (p : α → Pose G m) (a : α → ℕ) (H : ∀ i, lows (p i) (a i))
    (s : Finset α) : lows (∏ i ∈ s, p i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact fun _ _ => Nat.zero_le _
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]; exact lows_mul (H i) ih

/-- A true support assertion (not just order along a particular curve). -/
theorem lows_substitute (P : Key G → Pose G m) (hP : ∀ i, lows (P i) 1) (v : Pol G) (l : ℕ)
    (hv : ∀ a∈v.support, l = a.sum fun _ j => j) : lows (MvPolynomial.aeval P v) l := by
  classical
  rw [v.as_sum, map_sum]
  intro b hb
  obtain ⟨i,hi,hm⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hb)
  change b ∈ (MvPolynomial.aeval P (MvPolynomial.monomial i _)).support at hm
  rw [MvPolynomial.aeval_monomial] at hm
  have hu : lows (algebraMap ℂ (Pose G m) (MvPolynomial.coeff i v)) 0 := fun _ _ => Nat.zero_le _
  have he : lows (i.prod fun j k => (P j)^k) (i.sum fun _ k => k) :=
    lows_prod (fun j => (P j)^(i j)) _ (fun j => lows_pow (hP j) (i j)) _
  rw [hv i hi, ← Nat.zero_add (Finsupp.sum i _)]
  exact lows_mul hu he _ hm

end YM.Work.G05
