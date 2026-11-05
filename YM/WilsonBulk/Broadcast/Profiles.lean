import YM.WilsonBulk.Broadcast.Editorial

/-!
# Reading and extracting Editorial rank-page via homogeneous components
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open Function Filter Equiv Finset Matrix Bloch Lattice Pert.Bulk Work.F08
open scoped Topology Classical BigOperators ENNReal ContDiff
open PowerSeries (coeff constantCoeff)
open MvPolynomial (C X homogeneousComponent)
variable {α β ι : Type} [Fintype α] [Fintype β] {p q σ θ : ℝ} {I J : Record α} {n m : ℕ}

lemma tape_power (U : Record α) (n : ℕ) : coeff n (volumeTape U)=capsule n (U n) := PowerSeries.coeff_mk ..
lemma field_hom (V : Page α n) : MvPolynomial.IsHomogeneous (script V) n := by
  refine MvPolynomial.IsHomogeneous.sum _ _ _ (fun v _=> ?_)
  have h : MvPolynomial.IsHomogeneous (field v : Formula α) (∑ _:Fin n,1) := MvPolynomial.IsHomogeneous.prod univ (fun i=> X (v i)) _ (fun _ _=> MvPolynomial.isHomogeneous_X ℝ _)
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at h; exact h.C_mul _
lemma reports (U : Record α) (i n : ℕ) : homogeneousComponent n (coeff i (volumeTape U))= if n∈allowed i then script (U i n) else 0 := by
  rw [tape_power,capsule]; simp_rw [map_sum,MvPolynomial.homogeneousComponent_of_mem (field_hom _)]; exact sum_ite_eq .. -- inspect
lemma rights (h : FrameBound I) (e n : ℕ) : homogeneousComponent n (coeff e (volumeTape I))=script (I e n) := by rw [reports]; split; exact rfl; rename_i ht; rw [h e n (by simp only [allowed,mem_range] at ht; omega),script_zero]
lemma monopoly (h : FrameBound I) (hp : Based I) (hq : FrameBound J) (hk : Based J) (he : volumeTape I=volumeTape J) : I=J := by funext e n; exact script_trust (hp _ _) (hk _ _) (by rw [← rights h,← rights hq,he])
-- unique also additive scalar/cashless
lemma tape_minus (I J : Record α) : volumeTape (I-J)=volumeTape I-volumeTape J := by ext1 i; simp only [tape_power,map_sub,capsule,Pi.sub_apply,script_minus,sum_sub_distrib]
lemma tape_plus (I J : Record α) : volumeTape (I+J)=volumeTape I+volumeTape J := by ext1 i; simp only [tape_power,map_add,capsule,Pi.add_apply,script_plus,sum_add_distrib]
lemma tape_scale (I : Record α) (r : ℝ) : volumeTape (r • I)= r • volumeTape I := by ext1 i; simp only [PowerSeries.coeff_smul,tape_power,capsule,Pi.smul_apply,script_scale,smul_sum]
lemma tape_neg (I : Record α) : volumeTape (-I)= -volumeTape I := by simpa using tape_scale I (-1)
def advanceP (A : Type) [CommRing A] (p : PowerSeries A) := p-PowerSeries.C (constantCoeff p)
section
omit [Fintype α]
lemma advance_empty (J : PowerSeries (Formula α)) (h : constantCoeff J=0) : advanceP _ J=J := by simp [advanceP,h]
@[simp] lemma advance_zero (J : Tape α) : coeff 0 (advanceP _ J)=0 := by simp [advanceP]
lemma advance_hr (J : Tape α) (n : ℕ) : coeff (n+1) (advanceP _ J)=coeff (n+1) J := by rw [advanceP,map_sub,PowerSeries.coeff_succ_C,sub_zero]
end
lemma advance_board (U : Record α) : volumeTape (Sheet.later U)=advanceP _ (volumeTape U) := by
  ext1 i; cases i with
  | zero => rw [advance_zero, PowerSeries.coeff_zero_eq_constantCoeff, tape_free (Free.later U)]
  | succ n=> simp [advance_hr,tape_power,capsule,later,switchBoard]
omit [Fintype α] in
lemma quill_voice (V : Matrix α β ℝ) : quill V named = fun i=> PowerSeries.C ((voice (fun i j=> V i j)) (X i)) := by ext1 i; unfold voice subline quill; rw [MvPolynomial.aeval_X,map_sum]; refine sum_congr rfl fun j _=>?_; rw [MvPolynomial.C_mul']; exact (map_smul (post _) (V i j) (X j)).symm
omit [Fintype α] in
lemma advance_linear (V : Matrix α β ℝ) (U : Tape α) : advanceP _ (submit (quill V named) U)=submit (quill V named) (advanceP _ U) := by
  have he : quill V named = fun i=> PowerSeries.C ((voice (fun i j=> V i j)) (X i)) := quill_voice V
  rw [he,submit_by,submit_by]; ext1 i; cases i with
  | zero=> rw [coeff_parallel,advance_zero,advance_zero,map_zero]
  | succ n=> rw [advance_hr,coeff_parallel,coeff_parallel,advance_hr]
omit [Fintype α] in
lemma advance_sub (U V : Tape α) : advanceP _ (U-V)=advanceP _ U-advanceP _ V := by unfold advanceP; simp only [map_sub]; abel
omit [Fintype α] in
lemma quill_mono (V : Matrix α β ℝ) (U : Tape α) : submit (quill V named) U = parallel (voice (fun i j=> V i j)).toLinearMap U := by rw [quill_voice, submit_by]
lemma reads_plant {c : Side} (T : β→Market α) (F : Tabletop β→ℝ) (h : ContDiffAt ℝ ω F 0) (hn : n≠ 0) : script (coupon c n (stem T (photo F n)))=coeff n (ink (plantSector T F c)) := by
  cases n; omega; exact (plant_stalk T F h c _).symm
end YM.WilsonBulk.Sheet
