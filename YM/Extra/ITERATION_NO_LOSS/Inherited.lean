import YM.Extra.ITERATION_NO_LOSS.Factor
import YM.Extra.ITERATION_NO_LOSS.Placement
import YM.Extra.ITERATION_NO_LOSS.Transport

/-!
# The inherited pieces of r34cap and b2loop
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration.Inherited
open Filter Function Lattice Wilson RG Exterior Precision Tree Bloch Bid Placement Matrix
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f L : Side} {k : ℕ} {S : StepData c f}

def carryPrice (η : ℝ) (Ω Ω' : ℝ) (k : ℕ) := wallet η k (psiPrice Ω Ω')
def diffPrice (η σ Ω Ω' : ℝ) := carryPrice η Ω Ω' 2 * momentPrice 2 (σ-(σ/2))

def classicalPart (P Q : Bed) (T : Towers L) (A : ℕ → Atom G k) := padded (book (psi P Q T) (plain ∘ A))
def loopPart (P Q : Bed) (T : Towers L) (A : ℕ → Atom G 2) := padded (book (psi P Q T) (Lift.strip A))

section theory
variable {P Q : Bed} {T : Towers L} {η σ Ω Ω' C : ℝ} {s : ℕ} (hs : 1 ≤ s)
    (hη : 0 < η) (hP : P.dual_diag.strip η Ω) (hQ : Q.diagonal.strip η Ω') (hT : T.Deep η Ω s)

include hP hQ in
private lemma psi_nonneg : 0 ≤ psiPrice Ω Ω' := by
  have u : PlaqAxes := Classical.arbitrary _
  have h1 := Cost.nonneg (hP (plaquette u) (plaquette u)); have h2 := Cost.nonneg (hQ (plaquette u) (plaquette u))
  unfold psiPrice; positivity

lemma classical_sym (P Q : Bed) (T : Towers L) {A : ℕ → Atom G k} (h : SymmetricAtoms A) : SymmetricAtoms (classicalPart P Q T A) :=
  padded_sym (book_symm _ _ h)
lemma loop_sym (P Q : Bed) (T : Towers L) {A : ℕ → Atom G 2} (h : SymmetricAtoms A) : SymmetricAtoms (loopPart P Q T A) :=
  padded_sym (book_symm _ _ (fun _ => Lift.break_symm _ (h _) _))

include hs hη hP hQ hT
private lemma cl_book {A : ℕ → Atom G k} (hA : Charged A σ C) (hk : 2 ≤ k) (hfit : η ≤ σ*L.val) :
    Charged (book (psi P Q T) (plain ∘ A)) η (carryPrice η Ω Ω' k / (L.val:ℝ)^(2*k-4) * C) :=
  book_price _ (psi_nonneg hP hQ) hη.le hfit 2 (by omega) (fun _ _ => psi_strip hη hP hQ hs hT none) hA
lemma classical_price {A : ℕ → Atom G k} (hA : Charged A σ C) (hk : 2 ≤ k) (hfit : η ≤ σ*L.val) :
    Charged (classicalPart P Q T A) η (carryPrice η Ω Ω' k / (L.val:ℝ)^(2*k-4) * C) :=
  padded_cost (cl_book hs hη hP hQ hT hA hk hfit)

private lemma diff_book {A : ℕ → Atom G 2} (hA : Charged A σ C) (hfit : η ≤ σ/2*L.val) :
    Charged (book (psi P Q T) (Lift.strip A)) η (diffPrice η σ Ω Ω' / (L.val:ℝ)^2 * C) := by
  have he : 0 < σ/2 := pos_of_mul_pos_left (hη.trans_le hfit) (by positivity : 0 ≤ (L.val:ℝ))
  have hb := Lift.strip_cost hA he.le (by linarith : σ/2 < σ)
  have hp p i : (psi P Q T ((Lift.strip A p).op i)).strip η (psiPrice Ω Ω' / (L.val:ℝ)^3) := by
    obtain ⟨w,h⟩ := Option.isSome_iff_exists.mp (Lift.break_both _ p.2 i)
    change (Lift.strip A p).op i=some w at h
    rw [h]; exact psi_strip hη hP hQ hs hT (some w)
  convert book_price (Lift.strip A) (psi_nonneg hP hQ) hη.le hfit 3 (by omega) hp hb using 1
  unfold diffPrice carryPrice; norm_num; ring
lemma loop_price {A : ℕ → Atom G 2} (hA : Charged A σ C) (hfit : η ≤ σ/2*L.val) :
    Charged (loopPart P Q T A) η (diffPrice η σ Ω Ω' / (L.val:ℝ)^2 * C) :=
  padded_cost (diff_book hs hη hP hQ hT hA hfit)
lemma loop_silent {A : ℕ → Atom G 2} (hg : Odd L.val) (ht : Harmonic T) (hA : Charged A σ C) (hfit : η ≤ σ/2*L.val) :
    Silent (loopPart P Q T A) := by
  have hp p i : (psi P Q T ((Lift.strip A p).op i)).strip η (psiPrice Ω Ω' / (L.val:ℝ)^3) := by
    obtain ⟨w,h⟩ := Option.isSome_iff_exists.mp (Lift.break_both _ p.2 i)
    change (Lift.strip A p).op i=some w at h
    rw [h]; exact psi_strip hη hP hQ hs hT (some w)
  exact padded_silent (book_silent (Lift.strip A) (fun p => Lift.break_both _ p.2) hη hp
    (psi_cancels hη hP hQ hs hT hg ht) (diff_book hs hη hP hQ hT hA hfit))
end theory

variable {P Q : Bed} {T : Towers S.patch.L} {η σ Ω Ω' C : ℝ} {s : ℕ} (hs : 1 ≤ s)
    (hη : 0 < η) (hP : P.dual_diag.strip η Ω) (hQ : Q.diagonal.strip η Ω') (hT : T.Deep η Ω s)
variable {v D : ℝ} {p : Clip} {H : Forest S.ratio} (hv : 0 < v) (hS : S.patch.Branches S.kernel G)
    (hf : Floor P p f v D) (hb : Sworn P f G) (hd : Towers.Diagonal S P Q T)
include hs hη hP hQ hT hv hS hf hb hd

lemma supports (x : Dir G c) (b : Signed) : Substitution S.ratio (psi P Q T)
    (flux (pulled (Channel.rising H (installed S.ratio T.A0) x) b)) (flux (pulled x b)) := by
  intro op i j u
  have h := Channel.column_signed (H:=H) hS hv hf hb hd.trial x b j
  let y := d 1 c *ᵥ parts G 1 (pulled x b) j
  have he := psi_curl hη hP hQ hs hT S.sizes hf.diagonalInv hd.stays
  have hi := h.trans (congr_arg (fun U => U *ᵥ parts G 1 (pulled x b) j) he.symm)
  rw [← Matrix.mulVec_mulVec] at hi
  change Iteration.read op (fun z => (d 1 f *ᵥ _) (z,plaquette i)) u = _; rw [hi]
  rw [← psi_read hη hP hQ hs hT S.sizes S.patch.odd_side]
  exact ((output_cross S.ratio (psi P Q T op) y
    (Bloch.Row.rights _ _ (psi_strip hη hP hQ hs hT op) hη.le) (plaquette i) u).trans
      (plaqEquiv.sum_comp _).symm)

lemma classical_match {A : ℕ → Atom G k} {ρ} {W : PathData G} (hA : Charged A σ C) (hk : 2 ≤ k) (hfit : η ≤ σ*S.patch.L.val)
    (hr : Critical H p W ρ) (hg : Guessed H (installed S.ratio T.A0) ρ) : ∀ j ≤ k,
    SameJet j (fun y => action A (liftedTo H ρ y)) (fun y => action (classicalPart P Q T A) (represent y)) := by
  have hL := side_pos S.patch.L
  have hσ := pos_of_mul_pos_left (hη.trans_le hfit) hL.le
  have hJ := cl_book hs hη hP hQ hT hA hk hfit
  refine transmit ρ hσ hη hA (padded_cost hJ) hr hg ?_
  intro x b; rw [classicalPart,total_padded hJ hη.le]
  let V := flux (pulled x b)
  exact (book_eq (supports (H:=H) hs hη hP hQ hT hv hS hf hb hd x b) hη (div_nonneg (psi_nonneg hP hQ) (by positivity)) (plain ∘ A)
    (fun _ _ => psi_strip hη hP hQ hs hT none) (net_summable (plain ∘ _) V hη.le hJ)).symm

lemma loop_match {A : ℕ → Atom G 2} {ρ} {W : PathData G} (hA : Charged A σ C) (hz : Silent A) (hfit : η ≤ σ/2*S.patch.L.val)
    (hr : Critical H p W ρ) (hg : Guessed H (installed S.ratio T.A0) ρ) : ∀ j ≤ 2,
    SameJet j (fun y => action A (liftedTo H ρ y)) (fun y => action (loopPart P Q T A) (represent y)) := by
  have hL := side_pos S.patch.L
  have hσ := pos_of_mul_pos_left (hη.trans_le hfit) hL.le
  have hJ := diff_book hs hη hP hQ hT hA hfit
  have hp p i : (psi P Q T ((Lift.strip A p).op i)).strip η (psiPrice Ω Ω' / (S.patch.L.val:ℝ)^3) := by
    obtain ⟨w,h⟩ := Option.isSome_iff_exists.mp (Lift.break_both _ p.2 i)
    change (Lift.strip A p).op i=some w at h
    rw [h]; exact psi_strip hη hP hQ hs hT (some w)
  refine transmit ρ (by linarith) hη hA (padded_cost hJ) hr hg ?_
  intro x b; rw [loopPart,total_padded hJ hη.le,← Lift.strip_total hA hσ.le (by linarith) hz]
  exact (book_eq (supports hs hη hP hQ hT hv hS hf hb hd x b) hη (div_nonneg (psi_nonneg hP hQ) (by positivity)) _
    hp (net_summable (plain ∘ _) _ hη.le hJ)).symm
end YM.Extra.Iteration.Inherited
