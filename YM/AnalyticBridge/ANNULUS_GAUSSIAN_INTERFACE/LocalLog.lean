import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Accounts

set_option warningAsError false

/-!
# Window charge of the real Gaussian reference

The log of the principal Gram on the *same* coordinate list, complete
x-block (sum all colors). Use at the actual exponent with the chain / log
*difference* outstanding elsewhere. No replacement of `log det` by a
local sum. Handles no-hole and hole terms on the same conventions. No
matrix spectrum price if zooming to tiny coupling in a different period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Annulus.LocalLog
open Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree
    YM.Push.SectorMeasure Oriented Exterior Bloch Next.SectorChange Set MeasureTheory Matrix Gaussian Rows Schur
open YM.SectorNext.Remainder.Affine
open scoped Topology BigOperators Classical YM.Push.SectorMeasure ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f}

section matrix
variable {n : Type} [Fintype n] [DecidableEq n]

/-- Diagonal in the same panels (weak sector delays ensure i∈W i).
Always numerically defined; interpreted as log only under positive
compression. Zero safe when a malformed geometry lacks the window. -/
def pane (W : n → Set n) (C : Gaussian.Table n) (i : n) : ℝ := if h : i ∈ W i then
    (cfc Real.log (principal C (W i))) ⟨i,h⟩ ⟨i,h⟩ else 0



lemma bounds {p : n → Site c} {C : Gaussian.Table n}
    {K η u : ℝ} (h : Pours C p p u K) (hp : Gapped C η) (hs : C.PosDef) (hv : 0≤u)
    (i : n) : η ≤ hs.isHermitian.eigenvalues i ∧ hs.isHermitian.eigenvalues i ≤ K := by
  let L := hs.isHermitian.eigenvalues i
  let a : Vec n := hs.isHermitian.eigenvectorUnitary.val.col i
  have ha : C *ᵥ a = L • a := hs.isHermitian.mulVec_eigenvectorBasis i
  let U := hs.isHermitian.eigenvectorUnitary.val
  have he : star U*U=1 := Unitary.coe_star_mul_self ..
  have hw := congr_fun (congr_fun he i) i
  have ht : sumSq a = 1 := by
    simp only [Matrix.mul_apply, Matrix.one_apply_eq, star_eq_conjTranspose, Matrix.conjTranspose_apply, star_trivial] at hw
    simp only [sumSq,sq]; exact hw
  obtain hh := estimate (h.weaker hv le_rfl) a a
  obtain hu := hp a
  simp only [ha,dotProduct_smul,smul_eq_mul, ← sumSq_dot, ht,mul_one] at hu hh
  exact ⟨hu,(le_abs_self L).trans (hh.trans_eq (by ring))⟩

lemma diag_paid {p : n → Site c} {C : Gaussian.Table n} {K η u : ℝ}
    (h : Pours C p p u K) (hp : Gapped C η) (hs : C.PosDef) (hv : 0≤u) (he : 0<η) (i : n) :
    |(cfc Real.log C) i i| ≤ |Real.log η| + |Real.log K| := by
  let U := hs.isHermitian.eigenvectorUnitary.val
  have hl j := bounds h hp hs hv j
  let L j := Real.log (hs.isHermitian.eigenvalues j)
  let B := |Real.log η| + |Real.log K|
  have hL j : |L j|≤ B := by
    obtain h1 := (Real.log_le_log he (hl j).1)
    obtain h2 := (Real.log_le_log (hs.eigenvalues_pos j) (hl j).2)
    unfold B L; rw [abs_le]; constructor
    · linarith [neg_abs_le (Real.log η),abs_nonneg (Real.log K)]
    linarith [le_abs_self (Real.log K),abs_nonneg (Real.log η)]
  have hf : U * star U=1 := Unitary.coe_mul_star_self ..
  have ha : ∑ j, U i j ^ 2 = 1 := by
    have he := congr_fun (congr_fun hf i) i
    simp only [Matrix.mul_apply, Matrix.one_apply_eq, star_eq_conjTranspose, Matrix.conjTranspose_apply, star_trivial] at he
    simp only [sq]; exact he
  rw [hs.isHermitian.cfc_eq,Matrix.IsHermitian.cfc,Unitary.conjStarAlgAut_apply]
  change |(U*Matrix.diagonal L*star U) i i| ≤ B
  rw [Matrix.mul_apply]
  refine (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum (g:=fun j => U i j ^ 2*B) fun j _ => ?_).trans_eq ?_)
  · rw [Matrix.mul_diagonal,star_eq_conjTranspose,Matrix.conjTranspose_apply,star_trivial,
      show U i j * L j * U i j = U i j ^2 * L j by ring,abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hL _) (sq_nonneg _)
  rw [← Finset.sum_mul,ha,one_mul]

lemma pane_price {p : n → Site c} {C : Gaussian.Table n} {K η u : ℝ}
    (h : Pours C p p u K) (hp : Gapped C η) (hs : C.PosDef) (hv : 0≤u) (he : 0<η) (W i) :
    |pane W C i| ≤ |Real.log η| + |Real.log K| := by
  unfold pane; split
  next hx =>
    exact diag_paid (h.redact (W i) (W i)) (held_gap hp (W i)) (hs.submatrix Subtype.val_injective) hv he _
  rw [abs_zero]; positivity
end matrix

variable (T : Tube G S) (x : ℝ) (V : Config G c) (A O : Stores S) (k : S.Choices) (F : Forest S.ratio) (D : ℕ)

/-- Use the empty-sector gram, same tags and tree. Solvency only
required in the intact V support term, no changes to plotting or windows.
-/
def bare (S : StepData c f) : Stores S := ⟨∅,∅,∅⟩
def flat := Rows.gram T x (1:Config G c) k (shots S x) (bare S) F

def imprint (i : F.Free) (Q : Gaussian.Table (In x A F (G:=G))) := if h : ¬ chill A x F i then
    ∑ j : G.ColorIndex, pane (panels A F) Q (⟨i,h⟩,j) else 0

lemma imprint_price {K η u : ℝ} (Q : Gaussian.Table (In x A F (G:=G)))
    (h : Pours Q (Wisps.front A F) (Wisps.front A F) u K) (hp : Gapped Q η) (hs : Q.PosDef) (hv : 0≤u) (he : 0<η) (i : F.Free) :
    |imprint x A F i Q| ≤ Fintype.card G.ColorIndex * (|Real.log η| + |Real.log K|) := by
  unfold imprint; split
  · exact (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum (fun j _ => pane_price h hp hs hv he _ _ )).trans_eq (by simp [mul_add]))
  rw [abs_zero]; positivity

def paired (i : F.Free) := -(1/2:ℝ)*(imprint x A F i (Rows.gram T x V k (shots S x) A F)-
    imprint x (bare S) F i (flat T x k F))

/-- cost taken only on its location rule. -/
def write := ∑ i∈pairsAt O F D x, paired T x V A k F i

/-- Not pricing this, keep it explicit. Also keep chain from C.
Here no rearrangement of determinants or trace-log expansion hypothesized. -/
def yet := -(1/2:ℝ)*(Real.log (Rows.gram T x V k (shots S x) A F).det-Real.log (flat T x k F).det) -
    ∑ i, paired T x V A k F i

def LaterCost := yet T x V A k F + ∑ i∈(pairsAt O F D x)ᶜ, paired T x V A k F i



open Filter in
/-- The exact pre-delay purchase for the principal-window ancillary log,
for all A on the given V and trees/periods. Does not pay the chain tail. -/
lemma solvent (G : Gauge) (Q : Patch) (P : Teller G) (hB : Q.Branches P.bind G) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S),
    S.patch=Q → 100*(1+radiusB x) ≤ c.val → P.Funds S T →
    ∀ (A : Stores S) (F : Forest S.ratio) (k:S.Choices) (V : Config G c), A.flags=RG.flags (temp x) V →
    ∀ i : F.Free, |paired T x V A k F i| ≤ E := by
  obtain ⟨u,K,η,b,E,hu,hK,hη,hb,hE,H⟩ := opaqueCost G Q P hB
  let m := Fintype.card G.ColorIndex * (|Real.log η|+|Real.log K|)
  refine ⟨m,by unfold m; positivity,?_⟩
  filter_upwards [H] with x hx
  intro c f S T he hh h A F k V hA i
  have hb : (bare S).flags = RG.flags (temp x) (1:Config G c) := by
    change ∅ = _; symm; apply Finset.eq_empty_of_forall_notMem
    intro j hj; obtain ⟨i,-,hp⟩ := (RG.flags_spec ..).mp hj
    have hi : G.chord (faceValue (1:Config G c) i) ≤ temp x := by simp [faceValue,square,travel,temp_nonneg]
    linarith
  have hl := hx S T he hh h A F k V hA
  have hv := hx S T he hh h (bare S) F k 1 hb
  obtain h1 := imprint_price x A F _ hl.1 hl.2.1 hl.2.2.1 hu.le hη i
  obtain h2 := imprint_price x (bare S) F _ hv.1 hv.2.1 hv.2.2.1 hu.le hη i
  unfold paired
  rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  apply le_trans (mul_le_mul_of_nonneg_left ((abs_sub ..).trans (add_le_add h1 h2)) (by norm_num : (0:ℝ)≤1/2))
  unfold m; linarith
end YM.AnalyticBridge.Annulus.LocalLog
