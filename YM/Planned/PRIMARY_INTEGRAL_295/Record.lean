import YM.Ovens.Coffee
import YM.Planned.PRIMARY_INTEGRAL_295.ZeroPath

/-!
# Finite flat jet transported over the full cover row

`sampled` etc in Place are the input maps. Fix the Prediction here, not
promoting arbitrary analytical costs or single-address output reps to
already having the identity-input column matrix. This is a polynomial
prediction and preserves exact origin charts. Use ONLY on the primary
jet and when explicitly comparing to separately computed actual
normal-form responses. Not a field in the underlying link variables on
its own.
-/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Film
open Filter Function Set Lattice Labels RG Wilson Source Source.Drops MeasureTheory Precision Bloch Next.Free Place Carrier
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {d n : ℕ} {S : Finset Cover} {P : Side}

section linear
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma price_linear {b : Window E} {B} (h : Carries b n B) (M : E→L[ℝ]F) : Carries (fun x i=>M (b x i)) n (‖M‖*B) :=
    ⟨mul_nonneg (norm_nonneg _) h.1,fun x i=> (M.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (h.2 x i) (norm_nonneg _)).trans_eq (mul_assoc ..).symm)⟩

variable [CompleteSpace E]

lemma echo_linear {A : Lines P} (h : Whole A) {b : Window E} (M : E →L[ℝ] F) {C} (hb : Carries b n C) :
    applyLine A (fun x i=>M (b x i)) = fun x i=> M (applyLine A b x i) := by
  obtain ⟨σ,D,hσ,hT⟩ := h
  ext1 x; ext1 i; unfold applyLine stream; rw [map_sum]; apply Finset.sum_congr rfl; intro j _
  have he := stream_income hσ (show Laurent.Width σ D (member A x i j) from hT _ _) (cellar P x) n hb.1 (fun y => hb.2 y j)
  rw [M.map_tsum he.2.1.of_norm]; exact tsum_congr fun z => (map_smul M _ _).symm
end linear
section pays
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*}
omit [NormedSpace ℝ E] in
private lemma budget_common {s : Finset ι} (F : ι → Window E) (a : ℕ) (b : ι→ℝ) (h : ∀ i∈s, Carries (F i) a (b i)) :
    Carries (∑ i∈s,F i) a (∑ i∈s,b i) := by
  classical
  refine ⟨Finset.sum_nonneg fun i hi=> (h i hi).1,fun x i=>?_⟩
  rw [Finset.sum_apply]; simp only [Finset.sum_apply, Finset.sum_mul]; exact
    (norm_sum_le ..).trans (Finset.sum_le_sum fun j hj=> (h j hj).2 x i)

variable [CompleteSpace E]
private lemma sum_along {A : Lines P} (hp : Whole A) (s : Finset ι) (F : ι → Window E) (a : ℕ) (b : ι → ℝ) (h : ∀ i∈s,Carries (F i) a (b i)) :
    applyLine A (∑ i∈s,F i)=∑ i∈s,applyLine A (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext1; ext1; simp [applyLine,stream]
  | insert i s hi ih =>
    have he j (hj:j∈s):=h j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi,Finset.sum_insert hi, addLine hp _ _ (h i (by simp)) (budget_common F a b he), ih he]
end pays

abbrev TensorTape (G : Gauge) (d n : ℕ) := Tensor.T (Snap G d) G.Color n

def rawNeg (G : Gauge) (d n : ℕ) : Window (TensorTape G d n) := fun x i =>
    Tensor.coeff (lane (G:=G) (d:=d) (seat x) i) n 0

lemma raw_paid (G : Gauge) (d n : ℕ) :
    ∃ C, Carries (rawNeg G d n) (d*n) C := by
  obtain ⟨C,hC,H⟩:= mail_cap G d n
  let v := (n.factorial:ℝ)⁻¹
  refine ⟨‖v‖*C,mul_nonneg (norm_nonneg _) hC, fun x i =>?_⟩
  exact (norm_smul_le v (iteratedFDeriv ℝ n (lane (G:=G) (d:=d) (seat x) i) 0)).trans ((mul_le_mul_of_nonneg_left (H x i) (norm_nonneg _)).trans_eq (mul_assoc ..).symm)

/-- Total Taylor cut at every position; may include terms at ordinary
order ≤ d but engineering weight higher, which our read doesn't use. -/
def cut (X : Snap G d) : Window G.Color := fun x i => Work.G05.blockTaylor d (lane (G:=G) (d:=d) (seat x) i) X

private def item (n : ℕ) (X : Snap G d) : Window G.Color := fun x i=> Tensor.diagonal (rawNeg G d n x i) X

lemma cut_eq (X : Snap G d) : cut X= ∑ n∈Finset.range (d+1),item n X := by
  ext1 x; ext1 i; simp only [item,cut,Work.G05.blockTaylor,Finset.sum_apply]; rfl

private lemma item_paid (X : Snap G d) (n : ℕ) (h : n≤d) : ∃ c, Carries (item n X) (d*d) c := by
  classical
  obtain ⟨C,H⟩:= raw_paid G d n
  have he := price_linear H (ContinuousMultilinearMap.apply ℝ _ G.Color fun _=> X)
  refine ⟨_,he.1,fun x i=> (he.2 x i).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ he.1; unfold liftCost; exact pow_le_pow_right₀ (by simp) (Nat.mul_le_mul_left d h)

lemma cut_paid (X : Snap G d) : ∃ C, Carries (cut X) (d*d) C := by
  classical
  choose! b hb using fun n => item_paid X n
  rw [cut_eq]
  exact ⟨_,budget_common (item · X) _ b (fun _ hi=> hb _ (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))⟩

/-- Rolled Taylor tape of the coarse-origin chart. -/
def spool (A : Lines P) (X : Snap G d) : Window G.Color := applyLine A (cut X)

private def slide (G : Gauge) (d n : ℕ) (A : Lines P) : Window (TensorTape G d n) := applyLine A (rawNeg G d n)

lemma spool_read {A : Lines P} (h : Whole A) (X : Snap G d) (x : Cover) (i : Axis) :
    spool A X x i=∑ n∈Finset.range (d+1), Tensor.diagonal (slide G d n A x i) X := by
  classical
  choose! b hb using fun n => item_paid X n
  rw [spool,cut_eq,sum_along h _ (fun n=> item n X) (d*d) b (fun _ hi=> hb _ (Nat.le_of_lt_succ (Finset.mem_range.mp hi))), Finset.sum_apply, Finset.sum_apply]; apply Finset.sum_congr rfl; intro n _
  obtain ⟨C,H⟩:= raw_paid G d n
  have he := echo_linear (E:=TensorTape G d n) h (ContinuousMultilinearMap.apply ℝ _ G.Color fun _ => X) H
  exact congr_fun (congr_fun he x) i

lemma spool_smooth {A : Lines P} (h : Whole A) (x : Cover) (i : Axis) : ContDiff ℝ ω (fun X : Snap G d=>spool A X x i) := by
  rw [show (fun X : Snap G d=>spool A X x i)=_ from funext fun X=>spool_read h X x i]
  apply ContDiff.sum; intros; exact Tensor.diag_smooth ..

private lemma scrolled {A : Lines P} (h : Whole A) (x : Cover) (i : Axis) (v : Fin n→Snap G d) :
    slide G d n A x i v= applyLine A (fun x i=> rawNeg G d n x i v) x i := by
  obtain ⟨C,H⟩:=raw_paid G d n
  exact (congr_fun (congr_fun (echo_linear h (ContinuousMultilinearMap.apply ℝ _ G.Color v) H) x) i).symm

-- The engineering data is seen by mixed log-chart derivatives with
-- exact tensor coefficients, including their actual factorials.
private lemma first_cut {A : Lines P} (h : Whole A) (hn : n ≤ d) (x : Cover) (i : Axis) :
    Tensor.coeff (fun X : Snap G d => spool A X x i) n 0 = slide G d n A x i := by
  classical
  let V (n:ℕ) := slide G d n A x i
  have he : Tensor.Sym (V n) := by
    intro v q; rw [show V n _=_ from scrolled h x i _,show V n _=_ from scrolled h x i _]
    have hq : (fun x i => rawNeg G d n x i (v ∘ q))=(fun x i => rawNeg G d n x i v) :=
      funext fun b => funext fun j => Tensor.coeff_symm ((lane_smooth (G:=G) (d:=d) (seat b) j).of_le le_top) v q
    rw [hq]
  have ht : ContDiffAt ℝ n (fun X : Snap G d=> spool A X x i) 0 := (spool_smooth h x i).contDiffAt.of_le le_top
  apply Tensor.ext_diag _ _ (Tensor.coeff_symm ht) he
  funext v
  have hh (z : ℝ) : spool A (z • v) x i=∑ j∈Finset.range (d+1), z^j • Tensor.diagonal (V j) v := by rw [spool_read h]; simp only [Tensor.homogeneous]; rfl
  rw [← WardBin.leading_tensor _ _ ht,funext hh,WardBin.lead_sum (n:=n) _ _ (fun _ _ => (WardBin.monoSmooth ..).contDiffAt)]
  simp only [WardBin.lead_monomial, Finset.sum_ite_eq]; simp [V,hn]

lemma spool_initial {A : Lines P} (h : Whole A) (hn : n ≤ d) (x : Cover) (i : Axis) (v : Fin n → Snap G d) :
    iteratedFDeriv ℝ n (fun X : Snap G d=> spool A X x i) 0 v=
      applyLine A (fun x i=> iteratedFDeriv ℝ n (lane (G:=G) (d:=d) (seat x) i) 0 v) x i := by
  have he := DFunLike.congr_fun (first_cut h hn x i) v
  rw [scrolled h x i v] at he
  apply smul_right_injective G.Color (show ((n.factorial:ℝ)⁻¹)≠0 from by positivity)
  refine he.trans ?_
  unfold applyLine stream rawNeg Tensor.coeff
  simp only [Finset.smul_sum]; apply Finset.sum_congr rfl
  intro a ha; simp only [smul_apply]; rw [← tsum_const_smul'']; exact tsum_congr fun i=>smul_comm ..

/-- The flat mixed charts only need these spool evaluations on the
actual finite section footprint in the anchored fine cover. -/
def trace (S : Finset Cover) (A : Lines P) (X : Snap G d) : Dev S G := fun i =>
    spool A X (first i).val (beam i)
lemma trace_smooth {A : Lines P} (h : Whole A) (S : Finset Cover) (d : ℕ) : ContDiff ℝ ω (trace S A (G:=G) (d:=d)) :=
    contDiff_pi.mpr fun _=>spool_smooth h _ _

lemma trace_mail {A : Lines P} (h : Whole A) (hn : n≤d) (v : Fin n → Snap G d) (i : Spot S) :
    iteratedFDeriv ℝ n (trace S A (G:=G) (d:=d)) 0 v i=
      applyLine A (fun x i=> iteratedFDeriv ℝ n (lane (G:=G) (d:=d) (seat x) i) 0 v) (first i).val (beam i) := by
  let R : Dev S G →L[ℝ]G.Color := ContinuousLinearMap.proj i
  have hz := R.iteratedFDeriv_comp_left (x:=0) (trace_smooth h S (G:=G) d).contDiffAt (show (n : WithTop ℕ∞) ≤ ω from le_top)
  exact (DFunLike.congr_fun hz v).symm.trans (spool_initial h hn _ _ v)

lemma trace_root (A : Lines P) : trace S A (0 : Snap G d)=0 := by
  unfold trace spool cut; simp [applyLine,stream, Work.G05.blockTaylor_zero,lane_root]; rfl
end YM.Planned.PrimaryIntegral295.Film
