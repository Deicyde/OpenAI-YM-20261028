import YM.Bid.Angular

/-!
# Reality and signed subgroup for the wave polynomial

Compatibility step at any one cap. Conjugating the skew generators by a
signed permutation permutes all ordered planes with signs; in particular we
need not assume that the transported infinitesimal matrices integrate to a
group action. The sign is common to the left/right actions on Hom and occurs
twice in the relative sum of squares.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Work.A11
open Set Function Filter Org Climb Table Ward Spin Bid
open scoped Topology BigOperators Matrix.Norms.Frobenius

private def reindexPlanes (g : Signed) : Spin.Ind ≃ Spin.Ind :=
  Equiv.prodCongr g.perm g.perm

private def axisSign (g : Signed) (i : Axis) : ℝ := if g.flip i then -1 else 1
private def planeSign (g : Signed) (p : Spin.Ind) : ℝ := axisSign g p.1 * axisSign g p.2

private lemma sign_square (g : Signed) (p : Spin.Ind) :
    (↑(planeSign g p) : ℂ) * ↑(planeSign g p) = 1 := by
  cases h : g.flip p.1 <;> cases k : g.flip p.2 <;> simp [planeSign, axisSign, h, k]

private lemma conjugate_entry (g : Signed) (i j : Axis) :
    g.ortho.val * Matrix.single i j 1 * star g.ortho.val =
      (axisSign g i * axisSign g j) • Matrix.single (g.perm i) (g.perm j) 1 := by
  apply Matrix.ext
  intro a b
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ _)]
  · rw [Matrix.mul_single_apply_same, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
    by_cases h : g.perm i = a <;> by_cases k : g.perm j = b <;>
      simp [Signed.ortho, Signed.matrix_at, axisSign, h, k]
  · intro k _ hk
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hk, zero_mul]

private lemma signed_plane (g : Signed) (p : Spin.Ind) :
    orients g (Spin.K p) = planeSign g p • Spin.K (reindexPlanes g p) := by
  apply Subtype.ext
  rcases p with ⟨i,j⟩
  change g.ortho.val * (Matrix.single i j 1 - Matrix.single j i 1) * star g.ortho.val =
    (axisSign g i * axisSign g j) •
      (Matrix.single (g.perm i) (g.perm j) 1 - Matrix.single (g.perm j) (g.perm i) 1)
  rw [mul_sub, sub_mul, conjugate_entry, conjugate_entry, smul_sub,
    mul_comm (axisSign g i) (axisSign g j)]

-- Check with unequal flips and a nontrivial permutation; the sign uses INPUT axes.
example :
    let g : Signed := ⟨Equiv.swap 0 2, fun i => decide (i = 0)⟩
    orients g (Ortho.plane 0 1) = -(Ortho.plane 2 1) := by
  let g : Signed := ⟨Equiv.swap 0 2, fun i => decide (i = 0)⟩
  change orients g (Spin.K (0, 1)) = -(Ortho.plane 2 1)
  rw [signed_plane]
  simp [planeSign, axisSign, reindexPlanes, g]
  rw [show (Equiv.swap (0:Axis) 2) 1 = 1 by decide]
  exact neg_one_smul ℝ (Ortho.plane 2 1)

section Square

/-- One-term calculation. `m` may play the role of signed action OR of real
conjugation. `effect` acts on Hom by left minus right. Even though that effect
may not preserve `fine` by itself, its square has the sign cancellation (it
still carries a permutation of the plane index). -/
private lemma square_action {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (f B C B' C' : Spin.Mat X) (m : X → X) (e : ℂ) (he : e * e = 1)
    (hm : ∀ x y, m (x-y) = m x - m y) (hf : ∀ x, m (f x) = f (m x))
    (hB : ∀ x, m (B x) = e • B' (m x)) (hC : ∀ x, m (C x) = e • C' (m x)) (x : X) :
    m (((effect B C)^2) f x) = ((effect B' C')^2) f (m x) := by
  have h (t : X) : m (effect B C f t) = e • effect B' C' f (m t) := by
    rw [Spin.atAct, Spin.atAct]
    change m (B (f t) - f (C t)) = e • (B' (f (m t)) - f (C' (m t)))
    rw [hm, hB, hf, hf, hC, map_smul, smul_sub]
  rw [pow_two, pow_two]
  change m (B (effect B C f x) - effect B C f (C x)) =
    B' (effect B' C' f (m x)) - effect B' C' f (C' (m x))
  rw [hm, hB, h, h, hC, map_smul, map_smul, smul_smul, he, one_smul, smul_smul, he, one_smul]

end Square

variable {G : Gauge} {L : Register G} {S : Table L}

private def Covariant (a : S.RealSpin) (d : ℕ) (B : Spin.Ind → Spin.Mat (S.Field d)) : Prop :=
  (∀ g p x,
    S.mirror a d g (B p x) =
      (↑(planeSign g p) : ℂ) • B (reindexPlanes g p) (S.mirror a d g x)) ∧
  ∀ p x, S.conj a d (B p x) = B p (S.conj a d x)

private lemma casimir_fine (a : S.RealSpin) (d : ℕ) (B C : Spin.Ind → Spin.Mat (S.Field d))
    (hB : Covariant a d B) (hC : Covariant a d C) :
    (∑ p, effect (B p) (C p)^2) ∈ Spin.preserves (Spin.fine a d) := by
  let E (p : Spin.Ind) := (effect (B p) (C p))^2
  change Set.MapsTo (∑ p, E p : Spin.End (S.Field d)) (Spin.fine a d) (Spin.fine a d)
  intro f hf
  obtain ⟨hu,hv⟩ := hf
  constructor
  · intro g x
    suffices h : S.mirror a d g (∑ p, E p f x) = ∑ p, E p f (S.mirror a d g x) by
      simpa only [_root_.sum_apply] using h.symm
    rw [map_sum]
    calc
      _ = ∑ p : Spin.Ind, E (reindexPlanes g p) f (S.mirror a d g x) := Finset.sum_congr rfl fun p _ =>
        square_action f (B p) (C p) (B (reindexPlanes g p)) (C (reindexPlanes g p)) (S.mirror a d g)
          ((planeSign g p : ℝ) : ℂ) (sign_square g p)
          (map_sub (S.mirror a d g)) (fun t => (hu g t).symm) (hB.1 g p) (hC.1 g p) x
      _ = _ := Equiv.sum_comp (reindexPlanes g) fun p => E p f (S.mirror a d g x)
  · intro x
    suffices h : S.conj a d (∑ p, E p f x) = ∑ p, E p f (S.conj a d x) by
      simpa only [_root_.sum_apply] using h.symm
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ =>
      square_action f (B p) (C p) (B p) (C p) (S.conj a d) 1 (one_mul _) (map_sub (S.conj a d))
        (fun t => (hv t).symm) ?_ ?_ x
    · intro t
      rw [one_smul]
      exact hB.2 p t
    · intro t
      rw [one_smul]
      exact hC.2 p t

private lemma evaluate_fine (a : S.RealSpin) (d : ℕ) (A : Spin.End (S.Field d))
    (hA : A ∈ Spin.preserves (Spin.fine a d)) (z : List ℝ) :
    Spin.evaluate z A ∈ Spin.preserves (Spin.fine a d) := by
  let s := Spin.preserves (Spin.fine a d)
  change Spin.evaluate z A ∈ s
  induction z with
  | nil => exact s.zero_mem
  | cons r z ih =>
    change (r:ℂ) • 1 + A * Spin.evaluate z A ∈ s
    refine s.add_mem ?_ (s.mul_mem hA ih)
    change Set.MapsTo ((r:ℂ) • 1 : Spin.End (S.Field d)) (Spin.fine a d) (Spin.fine a d)
    intro f hf
    obtain ⟨hp,hq⟩ := hf
    constructor
    · intro g x
      change (r:ℂ) • f (S.mirror a d g x) = S.mirror a d g ((r:ℂ) • f x)
      rw [hp, map_smul]
    intro x
    change (r:ℂ) • f (S.conj a d x) = S.conj a d ((r:ℂ) • f x)
    rw [hq, map_smulₛₗ]
    simp

private lemma covariant_leaf (a : S.RealSpin) (D : SpinRows S) (d : ℕ)
    (h : ∀ g u x, S.mirror a d g (D d u x) = D d (orients g u) (S.mirror a d g x))
    (hc : ∀ u x, S.conj a d (D d u x) = D d u (S.conj a d x)) :
    Covariant a d (leaf D d) := by
  constructor
  · intro g p x
    change S.mirror a d g (D d (Spin.K p) x) =
      (↑(planeSign g p) : ℂ) • D d (Spin.K (reindexPlanes g p)) (S.mirror a d g x)
    rw [h, signed_plane, map_smul]
    exact RCLike.real_smul_eq_coe_smul (K := ℂ) (planeSign g p) _
  · exact fun p x => hc (Spin.K p) x

private lemma covariant_transport (A : S.RealSpin) (a : (comparator L).RealSpin)
    (D : SpinRows S) (d : ℕ) (U : Spin.change S d) (hU : realH A a U)
    (h : Covariant A d (leaf D d)) :
    Covariant a d (transport D U) := by
  have moved (p : Spin.Ind) (x : (comparator L).Field d) :
      U (transport D U p x) = leaf D d p (U x) := U.apply_symm_apply _
  obtain ⟨hm,hc⟩ := hU
  constructor
  · intro g p x
    apply U.injective
    rw [hm, moved, h.1 g p, map_smul, moved, hm]
  · intro p x
    apply U.injective
    rw [hc, moved, h.2 p, moved, hc]

/-- Differentiate the Port reality law as an equality of real-parametric
curves; field conjugation is antilinear over ℂ, but real continuous linear. -/
private lemma port_lie_real (H : S.RealSpin) (R : Rotation S) (h : Port R H)
    (d : ℕ) (u : Ortho.Skew) (x : S.Field d) :
    S.conj H d (R.lie d u x) = R.lie d u (S.conj H d x) := by
  let m : S.Field d →L[ℝ] S.Field d :=
    { toFun := S.conj H d
      map_add' := map_add _
      map_smul' := fun c v => by
        change S.conj H d (c • v) = c • S.conj H d v
        simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smulₛₗ]
        simp
      cont := Spin.cont_conj H d }
  have ht : HasDerivAt (fun t : ℝ => S.conj H d (R.act d (Ortho.oneParameter u t) x))
      (S.conj H d (R.lie d u x)) 0 :=
    m.hasFDerivAt.comp_hasDerivAt 0 (h.spinAt d u x)
  simp_rw [h.real] at ht
  exact ht.unique (h.spinAt d u (S.conj H d x))

private lemma covariant_port (A : A10) (H : S.RealSpin) (R : Rotation S) (h : Port R H)
    (d : ℕ) : Covariant H d (leaf R.lie d) := by
  refine covariant_leaf H R.lie d (fun g u x => ?_) (port_lie_real H R h d)
  rw [← h.signed, ← h.signed]
  exact (A H R h).2 d g.ortho u x

theorem answer : YM.Bid.A11 := by
  intro A G C S H K Y hY R d U hU z
  have h := R.lit.turns
  have ht : Port R.T.K R.hT.spin := ⟨h.spin,h.fixes,h.group,h.signed,h.real,h.infinitesimal⟩
  have hv : Covariant H d (leaf Y d) := covariant_leaf H Y d (hY.hex d) (hY.real d)
  apply evaluate_fine
  exact casimir_fine R.hT.spin d (transport Y U) (attach R.T.K d)
    (covariant_transport H R.hT.spin Y d U hU hv) (covariant_port A R.hT.spin R.T.K ht d)
end YM.Work.A11
