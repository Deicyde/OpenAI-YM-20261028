import YM.Next.FLUCTUATIONS.Sector
import YM.SectorNext.LARGE_FIELD_REMAINDERS.WeakTicket


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Coercivity using the output cut crown once, on the actual rows

No global log nor choice of paths near a seed. Width and L losses quantified, and
without expending the earned seed price. We also give the weaker estimate *keeping*
the cut output crown on the bill (coupling to boundary V not yet controlled then).
These are not estimates at analytic/complex continuations.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder
open Filter Function Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure Next.Fluctuations Next.Fluctuations.Sector Scales Bloch Exterior Precision
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure

variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {A : Stores S}

-- Schur for physical matrices including post-transport signs.
lemma schur_cost {I J : Type*} [Fintype I] [Fintype J] (M : I → J → ℝ) (v : J → ℝ)
    {r s : ℝ} (h : ∀ i j, 0≤M i j) (hr : 0≤r)
    (hx : ∀ i, ∑ j, M i j ≤ r) (hy : ∀ j, ∑ i, M i j ≤ s) :
    ∑ i, (∑ j, M i j * v j)^2 ≤ (r*s) * ∑ j, (v j)^2 := by
  have he (i : I) := (Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ (f:=fun j : J => M i j)
    (g:=fun j => M i j * (v j)^2) (r:=fun j => M i j*v j)
    (fun j _ => h i j) (fun j _ => mul_nonneg (h i j) (sq_nonneg _)) (fun j _ => le_of_eq (by ring))).trans
    (mul_le_mul_of_nonneg_right (hx i) (Finset.sum_nonneg (fun j _ => mul_nonneg (h i j) (sq_nonneg _))))
  apply (Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => he i)).trans
  rw [← Finset.mul_sum, mul_assoc, Finset.sum_comm]
  simp_rw [← Finset.sum_mul]; rw [Finset.mul_sum _ _ s]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hy i) (sq_nonneg _)) hr

lemma anchored_squares {I J : Type*} [Fintype I] [Fintype J] {M : I → J → Pay G}
    {r s : ℝ} {i : I → Site c} {j : J → Site c} {b : ℕ} (h : Bid.Anchored M r s i j b) (hr : 0≤r)
    (v : J → G.Color) (E : Finset I) :
    ∑ i ∈ E, ‖zip M v i‖^2 ≤ (r*s)* ∑ j, ‖v j‖^2 := by
  have he := schur_cost (fun i j => ‖M i j‖) (fun j => ‖v j‖) (fun _ _ => norm_nonneg _) hr h.rows h.columns
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E) (fun _ _ _ => sq_nonneg ‖_‖)).trans
    ((Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) ?_ _).trans he)
  exact (norm_sum_le ..).trans (Finset.sum_le_sum fun j _ => (M i j).le_opNorm (v j))

/-- Hash of the fine and noise chord square costs only on rows NOT already charged. -/
def physical (A : Stores S) (x : ℝ) (U : Config G f) (Q V : Config G c) : ℝ :=
  (∑ i ∈ (A.limit x)ᶜ, toll U i^2)+(∑ i ∈ (A.intern x)ᶜ, wire Q V i^2)


def cutOutput (T : Tube G S) (x : ℝ) (V : Config G c) : ℝ :=
  ∑ i, crown T.down T.low (till x) S.patch.L.val (temp x) V i

/-- Cut remainder on rows in this window; pass differently sized windows e.g. annuli, as
long as *disjoint* from assigned rows; includes boundaries iff the user included such exterior
rows. No deletion of any prerequisites. -/
def onWindow (T : Tube G S) (x : ℝ)
    (X : Finset (Cell f)) (Y : Finset (Bond c)) (Z : Finset (Cell c)) (K : Finset (Co c Gain))
    (U : Config G f) (Q V : Config G c) : ℝ :=
  (∑ i ∈ X, T.workF (till x) U V (fiery G x S.patch.L) (temp x) i) +
  (∑ i ∈ Y, T.workI (till x) Q V (temp x) i) +
  (∑ i ∈ Z, (T.workC (till x) V (temp x) i +
    (T.workL (till x) U Q V (temp x) i + T.workD (till x) V (temp x) i))) +
  (∑ i ∈ K, T.workN (till x) V (temp x) i)

lemma unassigned_exterior (T : Tube G S) (x : ℝ) (A : Stores S) (U : Config G f) (k : S.Choices) (V : Config G c) :
    unassigned A T x U k V = onWindow T x (A.limit x)ᶜ (A.intern x)ᶜ (A.outs x)ᶜ (A.coordN x)ᶜ U
      (S.prediction U k) V := by
  dsimp only [unassigned,onWindow]; unfold assessed Pressure.Stores.tally talli tallc talln talll
  have hc {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset ι) (g : ι→ℝ) : ∑ i∈Aᶜ,g i = ∑ i,g i - ∑ i∈A,g i := by linarith only [Finset.sum_add_sum_compl A g]
  simp_rw [Finset.sum_add_distrib,hc]; abel

variable {U : Config G f} {k : S.Choices} {V : Config G c} {x loss d : ℝ} (h : WeakTicket T A x U k V loss d)
include h

lemma clipped_window (X : Finset (Cell f)) (Y : Finset (Bond c)) (Z : Finset (Cell c))
    (K : Finset (Co c Gain)) (hx : Disjoint X (A.limit x)) (hz : Disjoint Z (A.outs x)) :
    -(2*loss*Z.card) ≤ onWindow T x X Y Z K U (S.prediction U k) V := by
  have hm i hi := h.base i (fun he => Finset.disjoint_left.mp hx hi he) 0 (Set.left_mem_Icc.mpr zero_le_one)
  simp only [zero_mul] at hm
  have hn i := workI_lower (T:=T) (till x) (S.prediction U k) V (temp x) i 0 (Set.left_mem_Icc.mpr zero_le_one)
  simp only [zero_mul] at hn
  have hh i hi : i ∉ A.outs x := fun he => Finset.disjoint_left.mp hz hi he
  calc
    _ ≤ (∑ _i ∈ X, (0:ℝ))+(∑ _i ∈ Y, (0:ℝ))+ (∑ _i ∈ Z, (-loss+-loss))+(∑ _i∈K,(0:ℝ)) := by
      simp; linarith
    _ ≤ _ := add_le_add (add_le_add (add_le_add (Finset.sum_le_sum fun i hi => hm i hi) (Finset.sum_le_sum fun i _ => hn i))
      (Finset.sum_le_sum fun i hi => add_le_add (h.clipped i (hh i hi)) (h.defect i (hh i hi))))
      (Finset.sum_le_sum fun i _ => by unfold workN; positivity)

lemma lower_unassigned (hl : 0≤loss) :
    -(2*loss*Fintype.card (Cell c)) ≤ unassigned A T x U k V := by
  rw [unassigned_exterior]
  exact le_trans (neg_le_neg (mul_le_mul_of_nonneg_left
    (Nat.cast_le.mpr (Finset.card_le_univ _)) (by positivity))) (clipped_window h _ _ _ _ disjoint_compl_left disjoint_compl_left)

/-- Stronger estimate in presence of cutOutput ; uniform even on V not close to
flat. ε selectable but admissible without further L-goal because Φ **uses both**
the coarse and fine multiplicities exactly in the \\ell² estimate. -/
lemma strengthened (hd : 0<d) (hl : 0≤loss) {ε : ℝ} (he : ε ∈ Set.Icc (0:ℝ) 1)
    (hε : ε*d^2 ≤ reserve T.low/2) :
    ε*(min T.high.direct S.kernel.penalty/4)*physical A x U (S.prediction U k) V +
      reserve T.low/2*(∑ j : Twin c, ‖T.vision (till x) (temp x) V j‖^2) - loss*Fintype.card (Cell c) ≤
      unassigned A T x U k V + cutOutput T x V := by
  let w := T.vision (till x) (temp x) V
  let W := ∑ j : Twin c, ‖w j‖^2
  have hW : 0≤W := by unfold W; positivity
  let r := till x; let s := temp x
  let t := fiery G x S.patch.L
  let Q := S.prediction U k
  let X := (A.limit x)ᶜ; let Y := (A.intern x)ᶜ; let Z := (A.outs x)ᶜ
  have hsX : ∑ i∈X, ‖T.Mv r s V (i,false)‖^2 ≤ d^2*W := by
    apply le_trans (b:=∑ i : Twin f, ‖T.Mv r s V i‖^2)
    · unfold Twin; rw [Fintype.sum_prod_type]
      apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ X) (fun _ _ _ => sq_nonneg ‖_‖)).trans
      exact Finset.sum_le_sum fun i _ => Finset.single_le_sum (fun j _ => sq_nonneg ‖T.Mv r s V (i,j)‖) (Finset.mem_univ false)
    apply (anchored_squares h.matrixPay.wide (by positivity) w Finset.univ).trans_eq
    have hh : 0 < (S.patch.L.val:ℝ) := by positivity
    unfold W; field_simp
  have hsY : ∑ i∈Y, ‖T.Mw r s V i‖^2 ≤ d^2*W := by
    rw [sq]; exact anchored_squares h.matrixPay.narrow hd.le w Y
  let XF := ∑ i∈X, toll U i^2
  let YF := ∑ i∈Y, wire Q V i^2
  let m := min T.high.direct S.kernel.penalty
  have hm : m*(XF + YF) ≤ T.high.direct*XF + S.kernel.penalty*YF := by
    rw [mul_add]; exact add_le_add (mul_le_mul_of_nonneg_right (min_le_left ..) (by unfold XF; positivity))
      (mul_le_mul_of_nonneg_right (min_le_right ..) (by unfold YF; positivity))
  have hE := mul_le_mul_of_nonneg_left hm he.1
  let FH := ∑ i∈X, T.workF r U V t s i
  let IH := ∑ i∈Y, T.workI r Q V s i
  have hFI : ε*(m/4)*(XF+YF) - ε*d^2*W ≤ FH+IH := by
    have hF := Finset.sum_le_sum fun i (hi : i∈X) => h.base i (Finset.mem_compl.mp hi) ε he
    have hI := Finset.sum_le_sum fun i (_ : i∈Y) => workI_lower (T:=T) r Q V s i ε he
    simp_rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum] at hF hI
    change ε*(T.high.direct*XF/4-_/2) ≤ FH at hF
    change ε*(S.kernel.penalty*YF/4-_/2) ≤ IH at hI
    change ∑ i ∈ X, ‖T.Mv (till x) (temp x) V (i,false)‖^2 ≤ d^2*W at hsX
    nlinarith only [hF,hI,hE,mul_le_mul_of_nonneg_left hsX he.1,mul_le_mul_of_nonneg_left hsY he.1]
  let CH := fun i => T.workC r V s i
  let LH := fun i => T.workL r U Q V s i + T.workD r V s i
  let c0 := fun i => crown T.down T.low r S.patch.L.val s V i
  let CHL := ∑ i∈Z, (CH i + LH i)
  have hZ : reserve T.low * W - loss*Fintype.card (Cell c) ≤ CHL+cutOutput T x V := by
    let hv (i : Cell c) := ∑ j : Bool, ‖w (i,j)‖^2
    have hA : reserve T.low * W ≤ (∑ i∈Z, CH i)+cutOutput T x V := by
      have H : W = ∑ i, hv i := by unfold W Twin; exact Fintype.sum_prod_type _
      have hh : cutOutput T x V = (∑ i∈Z, c0 i) + ∑ i∈Zᶜ, c0 i := by rw [Finset.sum_add_sum_compl]; rfl
      rw [hh,H,Finset.mul_sum,← Finset.sum_add_sum_compl Z (fun i => reserve _ * hv i), ← add_assoc, ← Finset.sum_add_distrib]
      refine add_le_add (Finset.sum_le_sum fun i hi => ?_) (Finset.sum_le_sum fun i _ => crown_pays _ _ _ _ _ (temp_nonneg x) _ i)
      rw [show CH i + c0 i = _ from workC_default r _ _ _ (h.coarse i (Finset.mem_compl.mp hi))]
      exact (mul_le_mul_of_nonneg_right (reserve_le _) (by unfold hv; positivity : 0≤hv i)).trans_eq (by unfold hv r s w; ring)
    have hB : -(loss*Fintype.card (Cell c)) ≤ ∑ i∈Z, LH i := by
      apply le_trans ?_ (Finset.sum_le_sum fun i (he : i∈Z) => h.defect i (Finset.mem_compl.mp he))
      calc
        _ ≤ -(loss*Z.card) := neg_le_neg (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_univ _)) hl)
        _ ≤ _ := by simp; linarith
    unfold CHL; rw [Finset.sum_add_distrib]; linarith
  rw [unassigned_exterior]; unfold onWindow
  have hN : 0≤∑ i ∈ (A.coordN x)ᶜ, T.workN r V s i := by unfold workN; positivity
  change ε*(m/4)*(XF+YF)+reserve _/2*W-loss*_ ≤ FH+IH+CHL+_+_
  nlinarith only [hFI,hN,hZ,mul_le_mul_of_nonneg_right hε hW]

end YM.SectorNext.Remainder
