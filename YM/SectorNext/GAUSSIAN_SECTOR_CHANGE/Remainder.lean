import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Affine


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# The meters in the changed sector. E affine subtraction, exact
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange.Rows
open Function Filter Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix Gaussian
open YM.Pressure YM.Pressure.Tube YM.Pressure.Stores YM.Bid YM.Push.SectorMeasure
open YM.Next.Fluctuations.Sector YM.Push.SectorMeasure.Oriented
open scoped Topology BigOperators Classical RealInnerProductSpace ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices)
  (W : Stencils S) (A : Stores S) (F : Forest S.ratio)

abbrev In := Active A x F × G.ColorIndex
abbrev Receipt (G : Gauge) (S : StepData c f) := Slots S × G.ColorIndex

def gram : Gaussian.Table (In (G:=G) x A F) := (move T x V k W A F).transpose * move T x V k W A F
variable (q : Chi) (d : ℝ)
variable (Y : LinkArray G (Frozen A x F))

def blame : Prices G (Active A x F) :=
  (move T x V k W A F).transpose *ᵥ source T x V k W A F q d Y

def direct (a : Prices G (Active A x F)) : Prices G (Slots S) :=
  move T x V k W A F *ᵥ a + source T x V k W A F q d Y

def guide (a : Prices G (Active A x F)) : ℝ := let c := direct T x V k W A F q d Y a; (c ⬝ᵥ c)/2

def lands (a : Prices G (Active A x F)) := base T x V k +
  bump T x V k (input x A F (autoShell q d V Y) + fresh x W A F (tape a))

def chargedUp (a : Prices G (Active A x F)) (s : Signed) (i : Twin f) : ℝ :=
  if curb W A F x s (.inl i.1) then ‖lands T x V k W A F q d Y a (s,.inl i)‖^2/2 else 0

def chargedSide (a : Prices G (Active A x F)) (s : Signed) (i : Bond c) : ℝ :=
  if curb W A F x s (.inr i) then ‖lands T x V k W A F q d Y a (s,.inr i)‖^2/2 else 0

/-- drows with affine squares subtracted. Tail energies not yet here: see
wrapper. -/
def actual (U : Config G f) (s : Signed) :=
  let H := pull s 0 U
  let v := pull s 0 V
  let Q := S.prediction H (choice s k)
  let t := temp x; let r := till x
  ((∑ i, T.workF r H v (fiery G x S.patch.L) t i)+(∑ i,T.workI r Q v t i)+(∑ i,T.workC r v t i)+
    (∑ i,T.workN r v t i)+(∑ i,T.workL r H Q v t i)+(∑ i,T.workD r v t i))

def residual (U : Config G f) (a : Prices G (Active A x F)) (s : Signed) :=
  actual T x V k U s - (∑ i, ∑ t : Bool, chargedUp T x V k W A F q d Y a s (i,t)) -
    ∑ i, chargedSide T x V k W A F q d Y a s i

/-- Unpack for rowwise uses. -/
lemma at_residual (U : Config G f) (a : Prices G (Active A x F)) (s : Signed) :
    let H := pull s 0 U; let v := pull s 0 V; let Q := S.prediction H (choice s k); let t := temp x; let r := till x
    residual T x V k W A F q d Y U a s = ((∑ i, (T.workF r H v (fiery G x S.patch.L) t i -
      ∑ j : Bool, chargedUp T x V k W A F q d Y a s (i,j)))+
      (∑ i,(T.workI r Q v t i-chargedSide T x V k W A F q d Y a s i))+(∑ i,T.workC r v t i)+
      (∑ i,T.workN r v t i)+(∑ i,T.workL r H Q v t i)+(∑ i,T.workD r v t i)) := by
  intro H v Q t r
  unfold residual actual; simp only [H,Q,v,r,t,Finset.sum_sub_distrib]; abel

variable {σ Λ ω₀ : ℝ} {o : Clip}

lemma arrived (h : T.up.Bounds o σ ω₀ Λ) (a : Prices G (Active A x F)) :
    tape (direct T x V k W A F q d Y a) = restrict x W A F (lands T x V k W A F q d Y a) := by
  have he (u v : Prices G (Slots S)) : tape (u+v)=tape u+tape v := colors.map_add ..
  rw [direct,he,moved _ _ _ _ _ _ _ h,source,tape.apply_symm_apply,tape.apply_symm_apply]
  unfold selected lands
  rw [bump_add _ _ _ _ h, ← restrict_add, add_comm, add_assoc]

lemma guide_rows (h : T.up.Bounds o σ ω₀ Λ) (a : Prices G (Active A x F)) :
    guide T x V k W A F q d Y a = averaged (fun s =>
      (∑ i : Cell f, ∑ t : Bool, chargedUp T x V k W A F q d Y a s (i,t)) +
        ∑ i, chargedSide T x V k W A F q d Y a s i) := by
  let u := lands T x V k W A F q d Y a
  unfold guide averaged; dsimp only; rw [price_square, arrived _ _ _ _ _ _ _ _ _ _ h]
  let n := (Fintype.card Signed : ℝ)
  have hn : 0 ≤ n := by positivity
  have hp (i : Slots S) : ‖restrict x W A F u i‖^2 =
      n⁻¹ * (if keep x W A F i then ‖u i‖^2 else 0) := by
    unfold restrict; split
    · rw [norm_smul, Real.norm_of_nonneg slip_pos.le, mul_pow,slip,inv_pow, Real.sq_sqrt hn]
    · simp
  change (∑ i : Slots S, ‖restrict x W A F u i‖^2) / 2 = _
  simp_rw [hp,Fintype.sum_prod_type,Fintype.sum_sum_type,keep,Sum.elim_inl,Sum.elim_inr]
  rw [Finset.sum_div,Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [add_div,mul_add,Finset.sum_div,Finset.mul_sum, chargedUp,chargedSide]
  have he (r : Prop) [Decidable r] (y : ℝ) : (n⁻¹ * if r then y else 0)/2 = (Fintype.card Signed:ℝ)⁻¹ * (if r then y/2 else 0) := by split <;> simp [*,n,mul_div_assoc]
  simp only [he,Fintype.sum_prod_type,u]

lemma compose_residual (h : T.up.Bounds o σ ω₀ Λ) (U : Config G f) (a : Prices G (Active A x F)) :
    averaged (actual T x V k U) = averaged (residual T x V k W A F q d Y U a) + guide T x V k W A F q d Y a := by
  rw [guide_rows _ _ _ _ _ _ _ _ _ _ h, ← av_add]
  apply congr_arg averaged; funext s; unfold residual; abel

def fee (U : Config G f) := meanEnergy A T x U k V + meanRest A T x U k V
lemma exact_fee (U : Config G f) : fee T x V k A U = averaged (actual T x V k U) := by
  unfold fee meanEnergy meanRest; rw [← av_add]; apply congr_arg averaged; funext s; unfold unassigned actual; simp

lemma fee_envelope {P : Teller G} (hT : P.Funds S T) : Envelope (fee T x V k A) := by
  let h₁ (s : Signed) (U : Config G f) :=
    (turnStore s A).assessed T x (pull s 0 U) (S.prediction (pull s 0 U) (choice s k)) (pull s 0 V)
  let h₂ (s : Signed) (U : Config G f) := unassigned (turnStore s A) T x (pull s 0 U) (choice s k) (pull s 0 V)
  change Envelope (fun U => averaged (fun s => h₁ s U)+averaged (fun s => h₂ s U))
  have hu (s : Signed) := (continuous_pull (n:=f) (G:=G) s 0).measurable
  exact Envelope.add (env_mean (F:=h₁) fun s => env_assessed hT x (choice s k) (hu s) measurable_const _) (env_mean
    (F:=h₂) fun s => env_unassigned hT x (choice s k) (hu s) measurable_const _)

-- Compare E eta via D^t; check signs or factor/2 wrong would fail this comparison.
def eta (m : Prices G (Active A x F)) (g : ℝ) :=
  (-g⁻¹) • ((gram T x V k W A F *ᵥ m)+blame T x V k W A F q d Y)

def adjustment (C : Gaussian.Table (In (G:=G) x A F)) (m : Prices G (Active A x F)) (g : ℝ) (z : Prices G (Active A x F)) :=
  -guide T x V k W A F q d Y m/g^2 + ((eta T x V k W A F q d Y m g) ⬝ᵥ z) +
    (z ⬝ᵥ ((C⁻¹ - gram T x V k W A F) *ᵥ z))/2

lemma adjusted (C : Gaussian.Table (In (G:=G) x A F)) (m z : Prices G (Active A x F)) {g : ℝ} (hg : 0<g) :
    adjustment T x V k W A F q d Y C m g z = force C z/2 - guide T x V k W A F q d Y (m+g • z)/g^2 := by
  let L := move T x V k W A F
  let w := direct T x V k W A F q d Y m
  let v := L *ᵥ z
  have he : direct T x V k W A F q d Y (m+g • z)=w+g • v := by
    unfold direct w v L; rw [mulVec_add,mulVec_smul, direct]; abel
  have hh : gram T x V k W A F *ᵥ m + blame T x V k W A F q d Y = L.transpose *ᵥ w := by
    unfold gram blame L w direct; rw [mulVec_add,mulVec_mulVec]
  have hx (a b : Vec (In x A F (G:=G))) : ((gram T x V k W A F *ᵥ a) ⬝ᵥ b) = ((L *ᵥ b) ⬝ᵥ (L *ᵥ a)) := by
    unfold gram L; rw [← mulVec_mulVec,dotProduct_comm,Matrix.dotProduct_transpose_mulVec,dotProduct_comm]
  unfold adjustment eta force guide
  rw [he, hh, smul_dotProduct, dotProduct_comm (L.transpose *ᵥ w), Matrix.dotProduct_transpose_mulVec, sub_mulVec,
    dotProduct_sub,dotProduct_comm z (gram T x V k W A F *ᵥ z),hx]
  simp only [add_dotProduct,dotProduct_add,dotProduct_smul,smul_dotProduct,smul_eq_mul,dotProduct_comm v w]
  change -((w ⬝ᵥ w)/2)/_ + _ + _ = _
  change -((w ⬝ᵥ w)/2)/g^2 + -g⁻¹ * (w ⬝ᵥ v) + ((z ⬝ᵥ _) - (v ⬝ᵥ v))/2 =
    _ - ((w ⬝ᵥ w) + g*(w ⬝ᵥ v) + g*((w ⬝ᵥ v)+g*(v ⬝ᵥ v)))/2/g^2
  field_simp; ring

lemma source_continuous {o : Clip} (hT : T.up.Bounds o σ ω₀ Λ) (hd : 0 < d) (ht : 2*d < firstRadius G) :
    Continuous (source T x V k W A F q d (G:=G)) := by
  let M : Directions G f →ₗ[ℝ] LogArray G (Slots S) :=
    { toFun := bump T x V k
      map_add' := bump_add T x V k hT
      map_smul' := fun w a => bump_smul T x V k hT a w }
  have hm : Continuous (bump T x V k) := M.continuous_of_finiteDimensional
  have hr : Continuous (restrict x W A F (G:=G)) := by
    apply continuous_pi; intro i
    unfold restrict; split <;> fun_prop
  have hi : Continuous (input x A F (G:=G)) := by
    apply continuous_pi; intro i
    unfold input; split
    · split <;> fun_prop
    · fun_prop
  refine gaugeCount.symm.continuous.comp (hr.comp (continuous_const.add (hm.comp (hi.comp ?_))))
  exact (autoShell_continuous q hd ht).comp (continuous_const.prodMk continuous_id)
end YM.Next.SectorChange.Rows
