import YM.Contacts.Tomography

/-! # Grade extraction using the same fixed covariant detectors at every arity

Our prescription is strictly coherent even when changing output horizons or (later) slowing a
smooth radius choice. Extend the detector projection by one grade at a time. Subtract from
this next lift the part already accounted for by the exact older projection. Thus the split
of the actual filtration is fixed, not a truncation-dependent one. Use when there is clearance
to every detector involved. This uses the unselected hierarchy. No assertion here that computing
different detectors separately in each selected phase would give these formulas.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts
open Function Filter Set Metric MeasureTheory Table MultipleContact
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {L : Register G} {S : Table L} {P : DiffPlan S}
variable (M : Devices P)
namespace Devices
local notation "ρ" => M.hierarchy.spin
local notation "D" => M.basis
local notation "R" => M.rotation
local notation "hS" => M.hierarchy.laws.toSymmetric
local notation "B" => M.base
local notation "A" d => S.Field d

def originProjection (d : ℕ) : Expression P →ₗ[ℂ] (A d) := match d with
| 0 => B 0
| n+1 => let F := originProjection n; let t := P.rise (Nat.le_succ n); let H := insertField D 0 (n+1)
         t.comp F + (B (n+1) - (t.comp F).comp (H.comp (B (n+1))))
lemma origin_rule (d) (e : Expression P) : M.originProjection (d+1) e=
    P.rise (Nat.le_succ d) (M.originProjection d e) + (M.base (d+1) e -
       P.rise (Nat.le_succ d) (M.originProjection d (insertField D 0 _ (M.base (d+1) e)))) := rfl
lemma origin_id (d) (x : A d) : M.originProjection d (insertField D 0 d x) = x := by
  cases d with
  | zero => exact M.base_id 0 _
  | succ d => rw [origin_rule, M.base_id]; abel
lemma origin_spin (d) (g : Ortho) (e) : M.rotation.act d g (M.originProjection d e) = M.originProjection d (turnExpr D R g e) := by
  induction d generalizing e with
  | zero => exact M.base_spin ..
  | succ d ih => simp_rw [origin_rule, map_add,map_sub,M.laws.filtered, M.base_spin,ih,turn_field D R M.laws hS M.incl M.coherent,M.base_spin]; rw [← Ortho.motion_at,map_zero]
lemma origin_real (d) (e) : S.conj ρ d (M.originProjection d e) = M.originProjection d (realExpr D ρ e) := by
  induction d generalizing e with
  | zero => exact M.base_real ..
  | succ d ih => simp_rw [origin_rule,map_add,map_sub,M.orientation.realInc,M.base_real,ih,real_field D hS M.incl M.orientation M.coherent, M.base_real]

def splitting : Splitting P where
  down d := (M.originProjection d).comp (insertField D 0 (d+1))
  left d x := by rw [LinearMap.comp_apply, insert_rise D M.coherent hS M.incl]; exact M.origin_id d x
lemma covariant : M.splitting.Covariant R ρ := by
  constructor
  · intro d x; change S.conj ρ _ (M.originProjection d _) = M.originProjection d (insertField _ _ _ _)
    rw [origin_real,real_field D hS M.incl M.orientation M.coherent]
  · intro d k x; change M.rotation.act _ k (M.originProjection d _) = M.originProjection d (insertField _ _ _ _)
    rw [origin_spin,turn_field D R M.laws hS M.incl M.coherent, ← Ortho.motion_at,map_zero]
lemma row_project_succ (d : ℕ) (e : Expression P) : M.originProjection (d+1) e = P.rise (Nat.le_succ d) (M.originProjection d e) + M.splitting.top (d+1) (M.base (d+1) e) := rfl
lemma top_top (d : ℕ) (x : A d) : M.splitting.top d (M.splitting.top d x) = M.splitting.top d x := by
  cases d with
  | zero => rfl
  | succ d =>
    simp_rw [MultipleContact.Splitting.top]; simp [map_sub, M.splitting.left]
lemma top_of_grade (d : ℕ) (x : M.splitting.stratum d) : M.splitting.top d x = x := by
  cases d with
  | zero=> rfl
  | succ d=> rw [Splitting.top]; simp [show M.splitting.down d x=0 from x.property]

lemma origin_cascade (d : ℕ) (e : Expression P) : M.splitting.down d (M.originProjection (d+1) e)= M.originProjection d e := by
  rw [origin_rule, map_add, map_sub,M.splitting.left,M.splitting.left]; change _+(M.originProjection d _ -M.originProjection d _)=_; rw [sub_self,add_zero]
lemma top_reads (d : ℕ) (e : Expression P) : M.splitting.top d (M.originProjection d e)= M.splitting.top d (M.base d e):= by
  cases d with
  | zero=>rfl
  | succ d=>
    rw [row_project_succ,map_add,top_top]
    simp [Splitting.top,M.splitting.left]
lemma origin_grade {d w : ℕ} (h : w ≤ d) (e : Expression P) : M.splitting.part w d (M.originProjection d e)= M.splitting.top w (M.base w e) := by
  induction d,h using Nat.le_induction with
  | base => rw [M.splitting.top_part]; exact M.top_reads w e
  | succ d h ih => rw [MultipleContact.Splitting.part,dif_neg (by omega), LinearMap.comp_apply,M.origin_cascade]; exact ih

/-- On physical words and with centering by translation (not recentering to a surviving slot). -/
def project (x : E4) (d : ℕ) : Expression P →ₗ[ℂ] S.Field d := (M.originProjection d).comp (shiftExpr (-x)).toLinearMap
/-- Component in exact weight w. -/
def row (x : E4) (w : ℕ) : Expression P →ₗ[ℂ] S.Field w :=
   (M.splitting.top w).comp ((M.base w).comp (shiftExpr (-x)).toLinearMap)
lemma select_grade (x : E4) {d w : ℕ} (h : w ≤ d) (e : Expression P) : M.splitting.part w d (M.project x d e)= M.row x w e :=
   M.origin_grade h _
lemma row_mem (x : E4) (w : ℕ) (e : Expression P) : M.row x w e∈ M.splitting.stratum w := by rw [← select_grade (d:=w) M x le_rfl]; exact M.splitting.top_mem _
lemma project_id (x : E4) (d : ℕ) (v : A d) : M.project x d (insertField D x d v)=v := by change M.originProjection d ((shiftExpr _) _) = _; rw [shift_field,add_neg_cancel,M.origin_id]
lemma row_of_field (x : E4) (d w : ℕ) (v : A d) : M.row x w (insertField D x d v)= M.splitting.part w d v:= by
  let h:= le_max_left w d; let h':= le_max_right w d
  rw [← insert_rise D M.coherent hS M.incl _ h' v,← M.select_grade x h,M.project_id,M.splitting.part_rise hS M.incl]
abbrev gradesThrough (n : ℕ) := Fin (n+1)
lemma project_through (d : ℕ) (x : E4) (e : Expression P) :
    ∑ w: Fin (d+1),P.rise (show w.val ≤ d from Nat.le_of_lt_succ w.isLt) (M.row x w e) = M.project x d e := by
  rw [← M.splitting.recombine hS M.incl d (M.project x d e)]
  exact Finset.sum_congr rfl fun i _=> by rw [M.select_grade x (Nat.le_of_lt_succ i.isLt)]
lemma project_spin (d) (x : E4) (g : Ortho) (e) : M.rotation.act d g (M.project x d e)= M.project (Ortho.move g x) d (turnExpr D R g e) := by
  change M.rotation.act d g (M.originProjection d _) = M.originProjection d _
  simp only [AlgHom.toLinearMap_apply]; rw [M.origin_spin,turn_shift, ← Ortho.motion_at, map_neg]; rfl
lemma project_real (d) (x : E4) (e) : S.conj ρ d (M.project x d e)= M.project x d (realExpr D ρ e) := by
  change S.conj ρ d (M.originProjection d _) = M.originProjection d _; simp only [AlgHom.toLinearMap_apply]; rw [M.origin_real, real_shift]
lemma project_moves (d) (x u : E4) (e) : M.project (x+u) d (shiftExpr u e)= M.project x d e := by
  change M.originProjection d _ = M.originProjection d _; simp only [AlgHom.toLinearMap_apply]; rw [shift_add]; congr 2; abel_nf
lemma row_spin (w) (x : E4) (g : Ortho) (e) : M.rotation.act w g (M.row x w e)= M.row (Ortho.move g x) w (turnExpr D R g e) := by
  simp_rw [← select_grade M _ (Nat.le_refl w), Splitting.top_part]; rw [← M.project_spin]
  cases w with
  | zero=>rfl
  | succ w=> rw [Splitting.top]; simp [M.laws.filtered, M.covariant.act]
lemma row_real (w) (x : E4) (e) : S.conj ρ w (M.row x w e)= M.row x w (realExpr D ρ e) := by
  simp_rw [← select_grade M _ (Nat.le_refl w), Splitting.top_part]; rw [← M.project_real]
  cases w with
  | zero=>rfl
  | succ w=> rw [Splitting.top]; simp [M.orientation.realInc, M.covariant.real]
lemma row_moves (w) (x u : E4) (e) : M.row (x+u) w (shiftExpr u e)= M.row x w e := by
  simp_rw [← select_grade M _ (Nat.le_refl w)]; rw [M.project_moves]
def insertRow (x : E4) (w : ℕ) : Expression P →ₗ[ℂ] Expression P := (insertField D x w).comp (M.row x w)
def replaceAt (x : E4) (d : ℕ) : Expression P →ₗ[ℂ] Expression P := (insertField D x d).comp (M.project x d)
def residue (x : E4) (d : ℕ) : Expression P →ₗ[ℂ] Expression P := LinearMap.id - M.replaceAt x d
lemma replace_id (x : E4) {w d : ℕ} (h : w ≤ d) (v : A w) : M.replaceAt x d (insertField D x w v)= insertField D x w v := by
  rw [← insert_rise D M.coherent hS M.incl x h v]; change insertField _ _ _ (M.project x d _) = _; rw [M.project_id]
lemma residue_low (x : E4) {d w : ℕ} (h : w ≤ d) (v : A w) : M.residue x d (insertField D x w v)=0 := by
  rw [residue]; simp [replace_id M _ h]
lemma replace_sum (x : E4) (d : ℕ) (e : Expression P) : ∑ w:Fin (d+1), M.insertRow x w e=M.replaceAt x d e := by
  rw [replaceAt,LinearMap.comp_apply,← project_through M d x e,map_sum]; simp_rw [insert_rise D M.coherent hS M.incl]
  exact Finset.sum_congr rfl fun i _ => rfl
lemma row_replace_le (x : E4) {d w : ℕ} (h : w ≤ d) (e : Expression P) : M.row x w (M.replaceAt x d e)= M.row x w e := by rw [replaceAt,LinearMap.comp_apply,row_of_field,select_grade M x h]
lemma row_replace_gt (x : E4) {d w : ℕ} (h : d < w) (e : Expression P) : M.row x w (M.replaceAt x d e)= 0 := by rw [replaceAt,LinearMap.comp_apply,row_of_field,M.splitting.beyondZero h,LinearMap.zero_apply]
lemma row_diagonal (x : E4) (w : ℕ) (e : Expression P) : M.row x w (M.insertRow x w e)= M.row x w e:= by
  rw [insertRow,LinearMap.comp_apply,row_of_field,M.splitting.top_part]
  exact M.top_of_grade w ⟨_, M.row_mem ..⟩
lemma row_other (x : E4) (w d : ℕ) (h : w≠d) (e : Expression P) : M.row x w (M.insertRow x d e)= 0:= by
  rw [insertRow,LinearMap.comp_apply,row_of_field]
  change (M.splitting.part w d ∘ₗ M.splitting.top d) (M.base d (shiftExpr (-x) e)) = 0; rw [M.splitting.part_top h,LinearMap.zero_apply]

/-- Clearance sufficient for any query through d. -/
def clearance : ℕ → ℝ
 | 0 => M.aperture 0
 | n+1 => min (clearance n) (M.aperture (n+1))
lemma clearance_le (d) : M.clearance d ≤ M.aperture d := by cases d; rfl; exact min_le_right _ _
lemma antitone_clearance : Antitone M.clearance := antitone_nat_of_succ_le (fun _=> min_le_left _ _)
lemma clearance_pos (d : ℕ) : 0 < M.clearance d := by
  induction d with
  | zero => exact M.aperture_pos 0
  | succ d ih => exact lt_min ih (M.aperture_pos _)
end Devices

variable {W I : Type} [TopologicalSpace W] {U : Set W} {A B : W → Set E4} {e : W → Expression P} {y : W → E4}
lemma Displays.move_origin (h : Displays U A e) (hy : ContinuousOn y U) (hv : ∀ t∈ U,∀ a∈ A t, a+y t∈ B t) : Displays U B (fun i=>shiftExpr (y i) (e i)) := by
  induction h with
  | zero => simpa only [map_zero] using (Displays.zero : Displays (P:=P) U B _)
  | atom I x p h h' hp =>
    have he (i:W) : shiftExpr (y i) (letterWord (x i) p)= letterWord (fun j=>x i j+y i) p := by
      change shiftExpr (y i) (∏ j: I,unitLetter (x i j) (p j))=∏ j:I,unitLetter (x i j+y i) (p j); rw [map_prod]; simp_rw [shift_unit]
    simp_rw [he]; refine .atom _ _ _ (continuousOn_pi.mpr (fun j=> (continuousOn_pi.mp h j).add hy))
      (fun i hi a b h=> h' _ hi (add_right_cancel h)) fun i hi=> ?_
    rintro z ⟨j,rfl⟩; exact hv i hi _ (hp i hi (Set.mem_range_self _))
  | plus h h' hx hz => simp only [map_add]; exact hx.plus hz
  | coeff hh h hx => simp_rw [map_smul]; exact .coeff hh hx
  | agree _ h hx => exact hx.agree fun i hi=> congrArg (shiftExpr (y i)) (h hi)
namespace Devices
local notation "D" => M.basis
lemma row_continuous (d : ℕ) (h : Displays U A e) (hy : ContinuousOn y U)
    (hw : ∀ t∈U,A t⊆ closedBall (y t) (M.aperture d)) : ContinuousOn (fun i=> M.row (y i) d (e i)) U := by
  apply ((M.splitting.top d).continuous_of_finiteDimensional).comp_continuousOn (f:= fun t=>M.base d (shiftExpr (-y t) (e t)))
  refine M.base_continuous _ (h.move_origin (B:=fun _=>closedBall 0 (M.aperture d)) hy.neg ?_) (fun _ _=>by rfl)
  intro t ht a ha; simpa [Metric.mem_closedBall,dist_eq_norm,sub_eq_add_neg] using hw t ht ha
lemma project_continuous (d : ℕ) (h : Displays U A e) (hy : ContinuousOn y U)
    (hw : ∀ t∈U,A t⊆ closedBall (y t) (M.clearance d)) : ContinuousOn (fun i=> M.project (y i) d (e i)) U := by
  simp_rw [← M.project_through]
  refine continuousOn_finsetSum _ (fun i _=> ((P.rise (show i.val ≤ d from Nat.le_of_lt_succ i.isLt)).continuous_of_finiteDimensional).comp_continuousOn
      (M.row_continuous i h hy (fun t ht=> (hw t ht).trans (closedBall_subset_closedBall ((M.antitone_clearance (Nat.le_of_lt_succ i.isLt)).trans (M.clearance_le _))))))
lemma project_visible (d : ℕ) (h : Displays U A e) (hy : ContinuousOn y U)
    (hw : ∀ t∈U,A t⊆ closedBall (y t) (M.clearance d)) : Displays U (fun t=>{y t}) (fun t=> M.replaceAt (y t) d (e t)) :=
  Displays.field (fun _ _=>Set.mem_singleton _) hy (M.project_continuous d h hy hw)
lemma residue_visible (d : ℕ) (h : Displays U A e) (hy : ContinuousOn y U)
    (hw : ∀ t∈U,A t⊆ closedBall (y t) (M.clearance d)) (hx : ∀ t∈U,y t∈A t) : Displays U A (fun t=> M.residue (y t) d (e t)) := h.diff
       ((M.project_visible d h hy hw).widen (fun t ht=>singleton_subset_iff.mpr (hx t ht)))
end Devices
end YM.Contacts
