import YM.Next.UV_STRESS.Fringe

set_option warningAsError false

/-!
# On-grid to every cutoff placement OFF projection strips

First, the needed quantitative regulator Lipschitz lemma (the proofs of
`sameBox` and `steps` here are adapted from the private `replaces` and
`comparable` in YM/Extraction/Equicontinuity.lean; we want their *result at
fixed detector/parameters*, not `completed`). The hard finite transfer-kernel
step `stepTotal` is already in the project. We pay using exactly the two
`Wheel.Spots` ROOT regimes, including in cyclic geometry at each cutoff.
No assumption of ordinary equicontinuity at our weights. No S arguments; in
particular we do not move cost thresholds past any continuum limit. See  for the heuristic this and the ensuing files implement in the
form of a direct estimate for `Station.paid`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.StationTransfer
open Function Set Filter MeasureTheory Metric Analysis Extraction
open Extraction.Difference Lattice Wilson Climb Ward Table Next.UVStress
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {C : Family G}
section grid
variable {n : ℕ}

private def via (x y : positions n) (s : Finset (Fin n × Axis)) (i : Fin n) (a : Axis) :=
    if (i,a)∈s then x i a else y i a

private theorem norm_tag (x y : positions n) (t : ℝ) :
    dist (tag t x) (tag t y) ^ 2 = ∑ i : Fin n × Axis, (t * (x i.1 i.2 - y i.1 i.2 : ℤ))^2 := by
  rw [dist_eq_norm,← Points.flatten.norm_map,EuclideanSpace.real_norm_sq_eq]; simp only [map_sub,PiLp.sub_apply]
  refine Finset.sum_congr rfl fun i _ => ?_; change (_ * _ - _ * _) ^ 2 = _
  simp only [Int.cast_sub,mul_sub]

private lemma sameBox (x y : positions n) (t : ℝ) (s u : Finset (Fin n × Axis)) :
    dist (tag t (via x y s)) (tag t (via x y u)) ≤ dist (tag t x) (tag t y) := by
  apply (sq_le_sq₀ dist_nonneg dist_nonneg).1
  simp_rw [norm_tag]; apply Finset.sum_le_sum; intro p _
  unfold via; split_ifs <;> simp <;> first | rfl | positivity | ring_nf; rfl

open Gaps
/-- In native lift coordinates, permit a change in the whole tuple. Needs
cyclic margin only on cutoff positions in a ball about one endpoint. -/
theorem steps (h : C.Makes) (v : Fin n→C.book.Token)
    {A r : ℝ} (ha : 0 ≤ A) (hr : 0<r) {p N D : ℕ} (hd : D≤N) (H : Permit v A D N p)
    (hv : C.S.a D < r)
    (x y : positions n)
    (hx : dist (tag (C.S.a N) x) (tag (C.S.a N) y) ≤ r)
    (K : ∀ z∈closedBall (tag (C.S.a N) y) r, allFine C.S p (4*r) z) :
    dist (lifted C N p v x) (lifted C N p v y) ≤
      ((4:ℝ)*n) *((A^n/r)*dist (tag (C.S.a N) x) (tag (C.S.a N) y)) := by
  cases n with
  | zero => rw [Subsingleton.elim x y, dist_self]; simp
  | succ m =>
    let n := m+1
    let a := C.S.a N
    let E := A^n/r
    let R := dist (tag a x) (tag a y)
    let D' := lifted C N p v
    let W := via x y
    have hb (s u) : dist (tag a (W s)) (tag a (W u)) ≤ R := sameBox x y a s u
    have hy' : W ∅=y := by ext; simp [W,via]
    let L := closedBall (tag a y) r
    have hR (s) : tag a (W s)∈L :=
      (hy' ▸ hb s ∅ : dist (tag a (W s)) (tag a y) ≤ R).trans hx
    have he' : 0≤E := div_nonneg (pow_nonneg ha _) hr.le
    have ht {u v' : Finset (Fin n × Axis)} (i j l) (hk : W u = advance (W v') i j l) :
        dist (D' (W u)) (D' (W v')) ≤ E*R := by
      apply le_trans (show dist (D' (W u)) (D' (W v')) ≤ E * dist (tag a (W u)) (tag a (W v')) from by
        rw [hk]; refine stepTotal h v ha hr L p N D hd H K hv i j l (W v') (hR v') ?_
        exact hk ▸ (hb u v').trans hx) (mul_le_mul_of_nonneg_left (hb u v') he')
    have hs (s : Finset (Fin n × Axis)) : dist (D' (W s)) (D' y) ≤ (s.card:ℝ)*(E*R) := by
      induction s using Finset.induction_on with
      | empty => simp [hy']
      | @insert b s hB ih =>
        obtain ⟨i,j⟩ := b
        rw [Finset.card_insert_of_notMem hB,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm ((s.card:ℝ)*_)]
        refine (dist_triangle _ (D' (W s)) _).trans (add_le_add ?_ ih)
        rcases le_total (x i j) (y i j) with h|h
        · rw [dist_comm]; apply ht i j (y i j-x i j).natAbs
          funext u w
          by_cases hu : u=i
          swap; simp [advance,W,via,hu]
          subst u
          by_cases hw : w=j
          · subst w
            simp only [advance,W,via, Function.update_self, hB,Finset.mem_insert_self, Pi.add_apply,Pi.smul_apply,
              ↓reduceIte, step_apply]; simp [abs_of_nonneg (sub_nonneg.mpr h)]
          · simp [advance,W,via,hw]
        apply ht i j (x i j-y i j).natAbs
        funext u w; by_cases hu : u=i
        · subst u; by_cases hw : w=j
          · subst w; simp [W,via,advance,hB,abs_of_nonneg (sub_nonneg.mpr h)]
          simp [W,via,advance,hw]
        simp [W,via,advance,hu]
    convert hs Finset.univ using 1
    · rw [show W Finset.univ=x by ext; simp [W,via]]
    simp only [Finset.card_univ,Fintype.card_prod,Axis,Fintype.card_fin, Nat.cast_mul,Nat.cast_ofNat]
    rw [mul_comm (4:ℝ) ↑(m.succ : ℕ)]

end grid
end YM.UVNext.StationTransfer
