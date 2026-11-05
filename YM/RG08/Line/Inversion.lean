import YM.RG08.Line.Project

/-!
# Finite torus covariance. Whole-link representation of the rooted tree-slice inverse.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Line
open Stationary Function Matrix Lattice Exterior Precision RG Tree Wilson Laurent Bloch
open scoped Matrix BigOperators Topology Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {b : Bed} (F:Forest S.ratio)

lemma front_rear {p : Clip} {η D : ℝ}(h:Floor b p f η D) : (frontR G S b)ᵀ=frontR G S b:= by
  unfold frontR posting K
  rw [Matrix.transpose_add, Matrix.transpose_smul]; simp only [transpose_mul,transpose_transpose,← patron_star,h.symmetric.1,transpose_mul, Matrix.mul_assoc]

def linePrecision (G : Gauge)(S : StepData c f)(b : Bed) := patron G (K (b.metric.acts f) + S.kernel.penalty • ((probe S)ᵀ * probe S))

def onTree (x : Link G f) := ∀ a : G.ColorIndex, Precision.marked (S:=S) F (fun z=> x (z.1,z.2,a))

variable (S b) in
def knobs (G : Gauge) (t : S.Choices) : Matrix (Bodies G c f) (Bodies G c f) ℝ := frontR G S b + (postroom S t (inch S.patch.L))ᵀ * (postroom S t (inch S.patch.L))

theorem inverse_tree (Y : Matrix (Bodies G c f) (Bodies G c f) ℝ) (W : Matrix (Lines G f 0) (Bodies G c f) ℝ)
    (hY : Y*(frontR G S b+Wᵀ*W)=1) (hW:IsUnit (W*spreadM (G:=G) S).det){p : Clip} {η D : ℝ} (h:Floor b p f η D) :
    let P := project G S F
    let M := P*Y*Pᵀ
    (∀ x,onTree F (M *ᵥ x)) ∧ (∀ x, onTree F x → M *ᵥ (linePrecision G S b *ᵥ x)=x) ∧ Mᵀ=M := by
  classical
  let Q:= frontR G S b; let L:=embark G S; let A:=spreadM (G:=G) S
  intro P M
  have ht : Q*L*P=Q := by
    rw [Matrix.mul_assoc,show L*P=1+A*(correct G S F) from teamed .., Matrix.mul_add,←Matrix.mul_assoc,Matrix.mul_one,show Q*A=0 from front_mute ..,Matrix.zero_mul,add_zero]
  have h2 : Qᵀ=Q := front_rear h
  have hI (x : Link G f)(he:onTree F x) : (P*L)*ᵥ x=x := by
    rw [show P*L=patron G (gaugePin S F) from project_out ..]
    funext ⟨i,b,a⟩
    rw [painted G (gaugePin S F) x a ((i,b):Body 1 f),gaugePin_fix S F (fun z=>x (z.1,z.2,a)) (he a)]
  refine ⟨fun x=>?_,fun x hx=>jointProjection Q Y _ _ _ _ L hY (front_mute ..) (front_fee ..) h2 (project_root ..) hW ht x (hI x hx),?_⟩
  · unfold M P; simp only [Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
    intro a e he
    generalize (Y *ᵥ (project G S F)ᵀ *ᵥ x)=v
    dsimp only
    rw [project_range,Matrix.sub_mulVec];
    simp only [← Matrix.mulVec_mulVec,Pi.sub_apply] -- painted wrong dir
    rw [painted G (gaugePin S F) _ a ((e.1,coord e.2):Body 1 f),painted G (gaugeFrame S) _ a ((e.1,coord e.2):Body 1 f),tree_stop S F _ e he,tree_roots S F _ e he,sub_self]
  have hh := congr_arg transpose hY
  rw [transpose_mul,transpose_one] at hh
  change _= _
  have hSum : (Q+Wᵀ*W)ᵀ=Q+Wᵀ*W := by rw [Matrix.transpose_add,transpose_mul,transpose_transpose,h2]
  change (Q+Wᵀ*W)ᵀ*Yᵀ=1 at hh
  rw [hSum] at hh
  have hh : Yᵀ=Y := by
    conv_lhs => rw [← Matrix.one_mul Yᵀ,← hY, Matrix.mul_assoc]
    rw [hh,Matrix.mul_one]
  unfold M; rw [transpose_mul,transpose_mul,hh,transpose_transpose,Matrix.mul_assoc]
end YM.RG08.Line
