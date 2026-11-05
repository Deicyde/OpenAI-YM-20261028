import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Completion
import YM.SectorNext.VACUUM_NORMALIZATION.Etch


/-!
# Zeroth-order compressed diagonal log payment for 

Use the *completed* actual counting matrix on this sector, and take the
window option of the accepted covariance (allPanels/meeting). Use Panel's
balance certificate; no invoking a formal power series for a singular
precision. Keep paired terms on the SAME physical color addresses, even if
they shift between active and vacant in the two tables. The controlled
ordered-letter expansion of the remaining global log-change (full minus
window, C ratio etc) is a different project; we'll keep its expression
exactly instead of pricing it as if also local. This is a per-term bound,
not a dependence certificate for recomputing a window (sector data for
numerical entries, even fortuitously zero ones, would have to be retained).
No V derivatives or table changes here.
-/
set_option autoImplicit false
-- Only stylistic lint disabled. All holes/axioms/declaration safety audited at entry.
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.AnalyticBridge.Annulus1AD
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube MeasureTheory Tree
   Axial YM.Push.SectorMeasure Next.Fluctuations Metric Oriented  Exterior Bloch
open YM.Next.SectorChange
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff
open scoped ComplexOrder -- Panel imported Numeric
open Finset Matrix Rows Wisps Schur Next.SectorChange.Completion
open YM.SectorNext.Vacuum.Panel

section pure
variable {J T : Type} [DecidableEq J] [Fintype J] [DecidableEq T] [Fintype T]
variable {c : Side} {p : J → Site c}
variable (A : Matrix J J ℝ) {L μ v : ℝ}

/-- Principal lower and upper in the actual counting norm preserved even
at an arbitrary window membership. -/
lemma numeric_principal (h : Numeric A μ L) (X : Set J) : Numeric (Schur.principal A X) μ L := by
  have hf : Gapped A μ := fun i => (sumSq_dot i).symm ▸ (h i).1
  have hh : Gapped (-A) (-L) := by
    intro b; rw [Matrix.neg_mulVec, dotProduct_neg,sumSq_dot,neg_mul,neg_le_neg_iff]; exact (h b).2
  intro i
  refine ⟨(sumSq_dot i) ▸ held_gap hf X i,?_⟩
  have hb := held_gap hh X i
  have hg : Schur.principal (-A) X = -(Schur.principal A X) := rfl
  rwa [hg,Matrix.neg_mulVec,dotProduct_neg,sumSq_dot,neg_mul,neg_le_neg_iff] at hb

lemma line_balance (hs : A.IsSymm) (h : Numeric A μ L) (hgap : 0 < μ) (hL : μ ≤ L) (i : J) :
    let g := Matrix.isHermitian_iff_isSymm.mpr hs
    priceLine A L i = ∑ j : J,g.eigenvectorUnitary.val i j ^2 * Real.log (g.eigenvalues j) := by
  intro g; unfold priceLine; rw [(balance A g h hgap hL i).tsum_eq]; ring

lemma line_priced (hs : A.IsSymm) (h : Numeric A μ L) (hμ : 0 < μ) (hL : μ ≤ L) (i : J) :
    |priceLine A L i| ≤ amount μ L := by
  have gm : A.IsHermitian := isHermitian_iff_isSymm.mpr hs
  let V := gm.eigenvectorUnitary.val
  have hsq : ∑ j,V i j^2=1 := by
    have hh : V*Vᴴ=1 := gm.eigenvectorUnitary.prop.2
    simpa [Matrix.mul_apply,pow_two] using congr_arg (fun A : Matrix J J ℝ => A i i) hh
  have he (j : J) : |Real.log (gm.eigenvalues j)|≤amount μ L := by
    obtain ⟨hx,hh⟩ := bill_quad gm h j
    refine abs_le.mpr ⟨?_,?_⟩
    · refine le_trans (b:=Real.log μ) ?_ (Real.log_le_log hμ hx)
      unfold amount; linarith only [neg_le_abs (Real.log μ),abs_nonneg (Real.log L)]
    refine (Real.log_le_log (hμ.trans_le hx) hh).trans ?_
    unfold amount; linarith only [le_abs_self (Real.log L),abs_nonneg (Real.log μ)]
  rw [line_balance A hs h hμ hL i]
  change |∑ j : J,V i j^2* Real.log (gm.eigenvalues j)|≤_
  calc
    _ ≤ ∑ j : J, |V i j^2*Real.log (gm.eigenvalues j)| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ j : J, V i j^2*amount μ L := sum_le_sum fun j _ => by
      rw [abs_mul,abs_of_nonneg (sq_nonneg _)]; exact mul_le_mul_of_nonneg_left (he j) (sq_nonneg _)
    _ = amount μ L := by rw [← sum_mul,hsq,one_mul]



include J T in
lemma padded_band (h : Numeric A μ L) (hm : μ ≤ 1) (hl : 1 ≤ L) : Numeric (wide A (1:Matrix T T ℝ)) μ L := by
  intro i
  let u := i ∘ Sum.inl; let w := i ∘ Sum.inr
  rw [wide_cost,one_mulVec]
  have he : i ⬝ᵥ i = u ⬝ᵥ u + w ⬝ᵥ w := by unfold dotProduct; rw [Fintype.sum_sum_type]; rfl
  have hp : 0 ≤ w ⬝ᵥ w := (sumSq_dot w) ▸ sumSq_nn w
  have hP : 1*(w ⬝ᵥ w)=w ⬝ᵥ w := one_mul _
  rw [he,mul_add,mul_add]
  exact ⟨add_le_add (h u).1 ((mul_le_mul_of_nonneg_right hm hp).trans_eq hP),
    add_le_add (h u).2 (hP.ge.trans (mul_le_mul_of_nonneg_right hl hp))⟩


end pure

section assembly
variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S) (V : Config G c)
variable (x : ℝ) (k : S.Choices) (A : Stores S) (F : Forest S.ratio)
open scoped YM.Next.SectorChange.Completion

abbrev completed (G : Gauge) := In x A F (G:=G) ⊕ vacant A F x G

def beacon := sorted A F (G:=G) (x:=x)

def witnessGram : Matrix (completed x A F G) (completed x A F G) ℝ :=
  wide (gram T x V k (shots S x) A F) 1

lemma witnessSymm : (witnessGram T V x k A F).IsSymm := by
  let M := gram T x V k (shots S x) A F;
  have he : M.IsSymm := by unfold M Rows.gram Matrix.IsSymm; rw [transpose_mul,transpose_transpose]
  change Matrix.IsSymm (wide M 1)
  unfold Matrix.IsSymm Completion.wide -- abbrev path issue
  rw [fromBlocks_transpose,transpose_zero,transpose_zero, transpose_one,he]

/-- Read the log diag first: pin even inactive centers (as E requires, before
later price localization or winding comparisons). Return zero if center isn't
in own panel; consumers using a trace law must show that case eliminated at
all centers used in the law; holds uniformly for radiusB≥120. -/
def measured (L : ℝ) (i : Bond f) : ℝ :=
  ∑ j : G.ColorIndex,
    let b := (beacon (G:=G) x A F).symm (i,j)
    let y := allPanels A F b
    if h : b∈y then priceLine (Schur.principal (witnessGram T V x k A F) y) L ⟨b,h⟩ else 0

def noHoles (S : StepData c f) : Stores S := ⟨∅,∅,∅⟩



lemma received_log {μ L : ℝ} (h : Numeric (witnessGram T V x k A F) μ L) (hh : 0<μ) (hx : μ≤L)
    (i : Bond f) : |measured T V x k A F L i| ≤ Fintype.card G.ColorIndex * amount μ L := by
  unfold measured
  refine (Finset.abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun _ => amount μ L) (fun j (_ : j∈Finset.univ)=> ?_)).trans_eq (by simp))
  dsimp only; split
  · apply line_priced _ _ (numeric_principal _ h _) hh hx
    exact (witnessSymm ..).submatrix _
  rw [abs_zero]; exact amount_nonneg ..







/-- E scalar local letter (paired on exact same link i), with sign in the
*integrand* exponent. Global identity `log_form` and window read both
on the scaled principal real log. -/
def couple (L : ℝ) (i : Bond f) := - (1/2:ℝ)*(measured T V x k A F L i - measured T 1 x k (noHoles S) F L i)

lemma couple_amount {L μ : ℝ} (h : Numeric (witnessGram T V x k A F) μ L)
    (h' : Numeric (witnessGram T 1 x k (noHoles S) F) μ L) (hgap : 0<μ) (hg : μ≤L)
    (i : Bond f) :
    |couple T V x k A F L i| ≤ Fintype.card G.ColorIndex * amount μ L := by
  have hh := received_log T V x k A F h hgap hg i
  have he := received_log T 1 x k (noHoles S) F h' hgap hg i
  unfold couple
  have ht := abs_sub (measured T V x k A F L i) (measured T 1 x k (noHoles S) F L i)
  rw [abs_mul, show |(-(1/2:ℝ))|=1/2 from by rw [abs_neg,abs_of_nonneg (by positivity)]]
  linarith only [hh,he,ht]





end assembly
end YM.AnalyticBridge.Annulus1AD
