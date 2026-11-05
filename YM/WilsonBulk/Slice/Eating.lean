import YM.WilsonBulk.Slice.Quill

/-! # Full conditional Gaussian in held external variables -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Classical BigOperators
open Sum Function Filter Finset PowerSeries Matrix
open MvPolynomial (pderiv)
variable {α β κ ι : Type}
variable {D B U : Matrix α α ℝ} {u : Page α 2}
-- symmetric pair
lemma pair_two (V : α→α→ℝ) (i j : α) : pair V (two i j)= V i j := rfl
lemma pair_regular (h : U.IsSymm) : Regular (pair U) := by
  intro e; ext1 i
  change U (i (e 0)) (i (e 1)) = U (i 0) (i 1)
  have he : e 0≠ e 1 := e.injective.ne zero_ne_one
  generalize hx : e 0=a at *; generalize hz : e 1=b at *
  fin_cases a <;> fin_cases b <;> first| contradiction| exact h.apply .. | rfl

def forkM (G : Matrix α β ℝ) : Matrix (Chamber α ι) (Chamber β κ) ℝ := Matrix.fromBlocks G 0 0 0
lemma fork_regular (h : D.IsSymm) : Regular (pair (forkM (ι:=ι) (κ:=ι) D)) := pair_regular (by apply Matrix.IsSymm.ext; intro i j; cases i <;> cases j <;> first|exact h.apply ..| rfl)
abbrev house (D : Matrix α α ℝ) := (pair (forkM D) : Page (Chamber α ι) 2)
lemma house_in (i j : α) : house D (two (inl i) (inl j) : Legs (Chamber α ι) 2)=D i j:= rfl
lemma house_out (i : Chamber α ι) (j : ι) : house D (two i (inr j))=0 := by cases i <;> rfl
lemma house_front (i : Chamber α ι) (j : ι) : house D (two (inr j) i)=0 := by cases i <;> rfl
-- center eval

def blankC (α ι : Type) : Formula (Chamber α ι) →ₐ[ℝ]Formula ι := MvPolynomial.aeval (Sum.elim (fun _:α=>0) (MvPolynomial.X))
def blankD (α ι : Type) : StageD α ι→ₐ[ℝ] Tape ι := submit (Sum.elim (fun _:α=> (0:Tape ι)) (named))
def boast (α ι : Type) : Tape ι →ₐ[ℝ] StageD α ι := submit (fun i=>named (inr i))
lemma blankD_name (α ι : Type) (i : α) : blankD α ι (privateName i)=0 := submit_named ..
lemma blankD_reports (j : ι) : blankD α ι (named (Sum.inr j))=named j := submit_named ..
lemma boast_calls (j : ι) : boast α ι (named j)=named (inr j) := submit_named ..
lemma boast_home (p : Tape ι) : blankD α ι (boast α ι p)=p := by
  refine DFunLike.congr_fun (code_ext ((blankD α ι).comp (boast α ι)) (AlgHom.id ..) (by rw [AlgHom.comp_apply,blankD,boast,submit_X,submit_X,constantCoeff_X]) (by rw [AlgHom.comp_apply,boast,blankD,submit_X,submit_X]; rfl) (fun i=> by rw [AlgHom.comp_apply,boast_calls,blankD_reports]; rfl)) p
lemma blankD_X : blankD α ι X=X := submit_X _
lemma boast_X : boast α ι X=X := submit_X _
lemma blankD_full (p : StageD α ι) : blankD α ι p=parallel (blankC α ι).toLinearMap p := by
  rw [← submit_by]; unfold blankD; congr 2; ext1 i; cases i <;> simp [blankC,named]
lemma boast_full (p : Tape ι) : boast α ι p=parallel (MvPolynomial.rename inr).toLinearMap p := by rw [boast,← submit_by]; simp [named]
variable [Fintype α] [Fintype ι]
def lint (ι : Type) [Fintype ι] (D : Matrix α α ℝ) := (blankC α ι).toLinearMap.comp (wick (house D))
def bags (ι : Type) [Fintype ι] (D : Matrix α α ℝ) := parallel (lint ι D)
lemma lint_C (r : ℝ) : lint ι D (MvPolynomial.C r)=MvPolynomial.C r := by change blankC _ _ (wick _ _)=_; rw [wick_scalar]; exact (blankC α ι).commutes r
lemma bags_power (n : ℕ) (f : StageD α ι) : coeff n (bags ι D f)=lint ι D (coeff n f) := coeff_parallel ..
lemma bags_clock (f : StageD α ι) : clockD _ (bags ι D f)=bags ι D (clockD _ f) := clock_parallel ..
lemma bags_script (f : StageD α ι) : bags ι D f=blankD α ι (parallel (wick (house D)) f) := by rw [blankD_full]; ext1 i; simp only [bags_power,coeff_parallel]; rfl
lemma lint_wrap {G : Matrix α α ℝ} (h : G.IsSymm) (p : Formula (Chamber α ι)) (i : α) : lint ι G (MvPolynomial.X (.inl i)*p)=∑ j:α,G i j • lint ι G (pderiv (.inl j) p) := by
  change blankC _ _ (wick _ _)= ∑ j:α,G i j • blankC _ _ (wick _ _)
  rw [Wick_X (house _) (fork_regular h)]; simp only [map_add,map_mul,map_sum,map_smul]; rw [Fintype.sum_sum_type]; simp_rw [house_in,house_out]; simp [blankC]
lemma bags_wrap (h : D.IsSymm) (f : StageD α ι) (i : α) : bags ι D (privateName i*f)=∑ j:α,D i j • bags ι D (inflow j f) := by ext1 n; simp only [bags_power, privateName,named,coeff_C_mul,map_sum,coeff_smul,inflow,player,parallel_D,lint_wrap h]
lemma IBP [DecidableEq α] (D : Matrix α α ℝ) (h : D.IsSymm) (hb : B.IsSymm) (hv : B*D=1) (f : StageD α ι) (i : α) : bags ι D (inflow i f - inflow i (forceQ B privateName)*f)=0 := by
  have h₁ : bags ι D (quill B privateName i * f)= quill B (fun i=>bags ι D (privateName i*f)) i := by simp only [quill,sum_mul,map_sum,smul_mul_assoc,map_smul]
  rw [force_player hb,map_sub,h₁]; simp_rw [bags_wrap h, show ∀ i:α, (∑ j:α,D i j • bags ι D (inflow j f))=quill D (fun i=>bags ι D (inflow i f)) i from fun i=>rfl, quill_chain, hv, quill_one]; rw [sub_self]
-- external factor pulls out (denominator theorem normal)
lemma lint_display (h : D.IsSymm) (p : Formula (Chamber α ι)) (x : Formula ι) : lint ι D (MvPolynomial.rename (.inr) x*p)=x*lint ι D p := by
  induction x using MvPolynomial.induction_on generalizing p with
  | C a=> rw [MvPolynomial.rename_C, MvPolynomial.C_mul',MvPolynomial.C_mul',map_smul]
  | add a b ha hb=> rw [map_add, add_mul,add_mul,map_add,ha,hb]
  | mul_X q i hq=>
     simp only [map_mul,MvPolynomial.rename_X,mul_assoc]; rw [hq]; congr 1
     change blankC _ _ (wick _ _) = _*blankC _ _ (wick _ _); rw [Wick_X _ (fork_regular h)]; simp_rw [house_front]; simp [blankC]
lemma bags_display (h : D.IsSymm) (x : Tape ι) (f : StageD α ι) : bags ι D (boast α ι x*f)=x* bags ι D f := by
  ext1 n; rw [bags_power,coeff_mul,coeff_mul, map_sum]; refine sum_congr rfl fun i _=>?_; rw [bags_power, boast_full, coeff_parallel]; exact lint_display h ..
end YM.WilsonBulk.Sheet
