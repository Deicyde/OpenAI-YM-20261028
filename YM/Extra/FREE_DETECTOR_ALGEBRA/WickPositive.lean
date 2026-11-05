import YM.Extra.FREE_DETECTOR_ALGEBRA.PowerGram

set_option warningAsError false

/-!
# Point detector positivity for the real-shell polynomial algebra

Complex convention: `duplex x y` is linear first, barred second, with
reflection in `face (x-y)` on second. Ordinary Wick moments have neither
of these twists. Off diagonals only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell Wick Pair
open scoped Topology ContDiff BigOperators RealInnerProductSpace ComplexOrder Matrix

variable {G : Gauge} {x y z : E4} {n : ℕ}

theorem upright (G : Gauge) (hz : z∈away) (n : ℕ) :
    ∃ (N : ℕ) (b : Module.Basis (Fin N) ℝ (ProbeTower G n)) (d : Fin N → ℝ),
      (∀ i, 0 < d i) ∧ ∀ i j, towerB hz n (b i) (b j) = if j=i then d i else 0 := by
  let B := towerB (G:=G) hz n
  have he : LinearMap.IsSymm B := ⟨towerB_sym hz⟩
  obtain ⟨b,hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis he
  refine ⟨_,b,(fun i => B (b i) (b i)),fun i => (towerB_pos hz _).mpr (b.ne_zero i),fun i j => ?_⟩
  by_cases hi : j=i
  · rw [hi,if_pos rfl]
  rw [if_neg hi]; exact hb (Ne.symm hi)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem norm_script (b : ι→ProbeTower G n) (hx : x≠y) (d : ι→ℝ)
    (he : ∀ i j, towerB (show x-y∈away from sub_ne_zero.mpr hx) n (b i) (b j) = if j=i then d i else 0) (p : MvPolynomial ι ℂ) :
    duplex x y (encode b p) (encode b p) = ((∑ i∈ p.support,Complex.normSq (p.coeff i) * tally d i : ℝ) : ℂ) := by
  simp only [duplex_script b hx d he, Complex.ofReal_sum, Complex.ofReal_mul, Complex.star_def, Complex.mul_conj]

theorem script_pos (b : ι→ProbeTower G n) (hx : x≠y) (d : ι→ℝ) (hd : ∀ i, 0 < d i)
    (he : ∀ i j, towerB (show x-y∈away from sub_ne_zero.mpr hx) n (b i) (b j) = if j=i then d i else 0) {p : MvPolynomial ι ℂ} :
    p≠0 → 0 < duplex x y (encode b p) (encode b p) := by
  intro hp
  have hs : p.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun hc => hp (by simpa using hc)
  rw [norm_script b hx d he,Complex.zero_lt_real]; exact Finset.sum_pos (fun i hi =>
    mul_pos (Complex.normSq_pos.mpr (MvPolynomial.mem_support_iff.mp hi)) (tally_pos d hd _)) hs

/-- All Wick polynomials after imposing ordinary shell constraints. -/
theorem reflected_positive (hx : x≠y) (P : WickPol G) : 0 < duplex x y P P ↔ P≠0 := by
  constructor
  · rintro he hh; simp [duplex,hh] at he
  obtain ⟨n,hn⟩ := from_large P
  obtain ⟨N,b,d,hd,he⟩ := upright G (show x-y∈away from sub_ne_zero.mpr hx) n
  obtain ⟨p,rfl⟩ := hn n le_rfl N b
  intro hp; exact script_pos _ hx d hd he (fun h => hp (by simp [h]))



theorem reflected_symm (hx : x≠y) (p q : WickPol G) : star (duplex x y p q)=duplex x y q p := by
  classical
  obtain ⟨n,hn⟩ := from_large p; obtain ⟨l,hl⟩ := from_large q
  obtain ⟨N,b,d,-,he⟩ := upright G (show x-y∈away from sub_ne_zero.mpr hx) (max n l)
  obtain ⟨p,rfl⟩ := hn _ (le_max_left ..) N b
  obtain ⟨q,rfl⟩ := hl _ (le_max_right ..) N b
  simp_rw [duplex_script _ hx d he]
  let g i := MvPolynomial.coeff i q * star (p.coeff i) * (tally d i:ℂ)
  have ht (i) : star (p.coeff i * star (q.coeff i) * (tally d i:ℂ)) = g i := by unfold g; rw [star_mul,star_mul, star_star]; simp only [Complex.star_def,Complex.conj_ofReal]; ring
  simp_rw [star_sum,ht]
  let I := p.support ∩ q.support
  trans (∑ i ∈ I, g i)
  · symm; apply Finset.sum_subset (Finset.inter_subset_left)
    intro i hi ho
    have he : i ∉ q.support := fun h => ho (Finset.mem_inter.mpr ⟨hi,h⟩)
    simp [g,MvPolynomial.notMem_support_iff.mp he]
  apply Finset.sum_subset (Finset.inter_subset_right)
  intro i hi ho
  have he : i ∉ p.support := fun h => ho (Finset.mem_inter.mpr ⟨h,hi⟩)
  simp [g,MvPolynomial.notMem_support_iff.mp he]



omit [DecidableEq ι] in
/-- General complex minors, first index in the matrix is the reflected
(barred) one, so `aᴴMa` is the norm of the combination with coefficients a. -/
theorem reflected_pd (hx : x≠y) (V : ι → WickPol G) (he : LinearIndependent ℂ V) :
    (Matrix.of (fun i j => duplex x y (V j) (V i))).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j; exact reflected_symm hx ..
  intro a ha
  let P := ∑ i, a i • V i
  have hp : P≠0 := fun h => ha (funext ((Fintype.linearIndependent_iff.mp he) _ h))
  have ht := (reflected_positive hx _).mpr hp
  refine lt_of_lt_of_eq ht ?_
  unfold P duplex Matrix.mulVec dotProduct
  simp only [_root_.map_sum,bar_scaled, _root_.map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Matrix.of_apply,smul_eq_mul,
    Pi.star_apply,Finset.mul_sum]
  -- align orientation
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end YM.Extra.FD
