import YM.WilsonBulk.Slice.Eating

/-!
# Spectator equivariance & affine compatible cuts for Γ

Proof including arbitrary presentation of finite full Gaussian with zero
fields marginalized and output substitutions in polynomial parameters. Keeps
coarse quadratic and denominator operation in their own spaces. Materials
consume these identities before truncation, not approximating densities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Classical BigOperators
open Function Finset PowerSeries Matrix Sum
variable {A X : Type} {α β κ ι : Type} [CommRing A] [Algebra ℝ A]
variable [Fintype α] [Fintype β] [Fintype ι] [Fintype κ]
variable {G : Matrix α α ℝ} {V : Matrix β α ℝ} {H : Matrix β β ℝ}
-- underlies condition for transitions to affine in private only

omit [Fintype β] [Fintype ι] in
lemma inflow_quill (x : α) (i : β) : inflow (ι:=ι) x (quill V privateName i)= algebraMap ℝ (StageD α ι) (V i x) := by
  rw [Algebra.algebraMap_eq_smul_one]; simp [quill,inflow,privateName,smul_ite]
omit [Fintype α] in
lemma hat_still (x : α) (p : Tape ι) : inflow x (boast α ι p)=0 := by rw [boast,inflow, player_chain]; simp

-- V maps private inputs, I (φ) maps spectators. H=V G V^t (source with H, target with G)
def facade (V : Matrix β α ℝ) (u : κ→Tape ι) (e : Chamber β κ) : StageD α ι := Sum.elim (quill V privateName) (fun i=> boast α ι (u i)) e
omit [Fintype β] in
lemma lap_project (h : V*G*V.transpose=H) (i j : β) :
    ∑ x:α,∑ y:α,G x y * V i x * V j y= H i j := by
  rw [← h]; simp only [Matrix.mul_apply,sum_mul,transpose_apply]; rw [sum_comm]; apply sum_congr rfl fun _ _=>sum_congr rfl fun _ _=> ?_; ring
omit [Fintype β] [Fintype κ] in
lemma facade_reflect (u : κ→Tape ι) (h : V*G*V.transpose=H) : Reflects (facade V u) (forkM (ι:=κ) (κ:=ι) V) (house H) (house G) := by
  constructor
  · intro x y hx; cases x with
    | inr i=> exact absurd (house_front ..) hx
    | inl i=> cases y with
      | inr j=> exact absurd (house_out ..) hx
      | inl j=>
        have he (x : α) (i : Chamber β κ) : player (inl x) (facade V u i)= algebraMap ℝ (StageD α ι) (forkM (ι:=κ) (κ:=ι) V i (inl x)) := by
          cases i with
          | inl i=> exact inflow_quill ..
          | inr i=> change inflow x (boast α ι (u i)) = algebraMap ℝ _ 0; rw [hat_still, map_zero]
        exact ⟨he i,he j⟩
  intro i j
  simp_rw [Fintype.sum_sum_type,house_in, house_out]
  -- remaining nonzero house(out,left)
  simp_rw [house_front]; simp only [zero_mul,sum_const_zero,add_zero]; rcases i with i|i <;> rcases j with j|j
  · exact lap_project h ..
  all_goals simp [house,pair,forkM,two]
lemma lap_shadow (u : κ→Tape ι) (p : StageD β κ) (h : V*G*V.transpose=H) : bags ι G (submit (facade V u) p)=submit u (bags κ H p) := by
  rw [bags_script,bags_script,(facade_reflect u h).all]
  apply DFunLike.congr_fun (f:=(blankD α ι).comp (submit (facade V u))) (g:=(submit u).comp (blankD β κ))
  apply code_ext
  · rw [AlgHom.comp_apply,submit_X,blankD_X,constantCoeff_X]
  · simp only [AlgHom.comp_apply,submit_X,blankD_X]
  simp only [AlgHom.comp_apply,submit_named]; intro i; cases i with
  | inl i=>
    change blankD _ _ (quill _ _ i)=submit u (blankD β κ (privateName i))
    simp only [quill,map_smul,map_sum,blankD_name,smul_zero,sum_const_zero,map_zero]
  | inr j=> rw [blankD_reports,submit_named]; exact boast_home _
lemma linear_shadow (f : StageD α ι) (G H V : Matrix α α ℝ) (h : V*G*V.transpose=H) : bags ι G (switch (quill V privateName) f)=bags ι H f := by
  have hb : switch (quill V privateName : α→StageD α ι)=submit (facade V (fun i:ι=>named i)) := by
    apply byNames; exact switch_X ..; rintro (i|i)
    · exact switch_to ..
    exact Eq.trans (switch_side ..) (boast_calls _).symm
  rw [hb,lap_shadow _ f h, submit_id]
-- changing spectator parameters in nonlinear expressions

def consult (u : κ→ Tape ι) : StageD α κ→ₐ[ℝ]StageD α ι := submit (Sum.elim privateName (fun i=> boast α ι (u i)))
lemma consults (u : κ→ Tape ι) (f : StageD α κ) : bags ι G (consult u f)=submit u (bags κ G f) := by
  rw [consult,show Sum.elim _ _= facade (1:Matrix α α ℝ) u from funext (fun i=> by cases i with
     | inl i=> simp only [facade,quill_one,Sum.elim_inl]
     | inr i=>rfl)]
  exact lap_shadow u f (by simp)
omit [Fintype α] [Fintype ι] [Fintype κ] in
lemma consult_sat (u : κ→ Tape ι) (p : Tape κ) : consult u (boast α κ p)= boast α ι (submit u p) := by
  apply DFunLike.congr_fun (f:=(consult u).comp (boast α κ)) (g:=(boast α ι).comp (submit u))
  refine code_ext _ _ ?_ ?_ ?_
  · rw [AlgHom.comp_apply,boast_X,consult,submit_X,constantCoeff_X]
  · simp only [AlgHom.comp_apply,boast_X,consult,submit_X]
  · intro i; rw [AlgHom.comp_apply,AlgHom.comp_apply,submit_named,boast_calls,consult,submit_named]; rfl
section
omit [Fintype α] [Fintype ι]
lemma switch_sat (T : α→StageD α ι) (p : Tape ι) : switch T (boast α ι p)=boast α ι p := by
  apply DFunLike.congr_fun (f:=(switch T).comp (boast α ι)); refine code_ext _ _ ?_ ?_ ?_
  · simp only [AlgHom.comp_apply,boast_X,switch_X,constantCoeff_X]
  · simp only [AlgHom.comp_apply,boast_X,switch_X]
  intro i; rw [AlgHom.comp_apply,boast_calls,switch_side]
end
end YM.WilsonBulk.Sheet
