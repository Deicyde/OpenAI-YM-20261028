import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Assignment

/-!
# Completed Gram matrix on a sector

Here and later, no choosing another orientation of tag labels independently
when assembling the quadratic reference. Use all roots, coloring explicit,
in counting units. Identity at other positions/dummy; no Gaussian normalization
averaging over k/F within a matrix. All finite sizes including `Hot` empty.
`D` variation, not full curved-row tangent; `surcharge` subtracted accordingly.
No β factors yet (root charts: `a = mu+g*w` will convert this).
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Matrix Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows  Tags
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {ι κ : Type*}

/-- standard physical counting chart -/
def stand (x : ι → G.Color) (p : ι × G.ColorIndex) : ℝ := x p.1 p.2

def erect (G : Gauge) (x : ι × G.ColorIndex → ℝ) (p : ι) : G.Color := WithLp.toLp 2 (fun i => x (p,i))

lemma rises (x : ι → G.Color) : erect G (stand x)=x := rfl

section
variable (x : ι → G.Color) (e : ι × G.ColorIndex)

def dot (G : Gauge) (i : G.ColorIndex) := EuclideanSpace.basisFun (𝕜 := ℝ) G.ColorIndex i

def sing [DecidableEq ι] : ι → G.Color := Pi.single e.1 (dot G e.2)
lemma singled [DecidableEq ι] : stand (sing e)=Pi.single e 1 := by
  rcases e with ⟨i,j⟩; funext p
  rcases p with ⟨q,r⟩; dsimp only [stand,sing]
  by_cases h : q=i
  · subst q
    by_cases he : r=j
    · subst r; simp [dot]
    simp [he,dot,EuclideanSpace.basisFun_apply]
  have he : (q,r) ≠ (i,j) := by simp [h]
  rw [Pi.single_eq_of_ne h,Pi.single_eq_of_ne he]; rfl
lemma stand_spanned [Fintype ι] [DecidableEq ι] : (∑ i : ι × G.ColorIndex, stand x i • sing i)=x := by
  ext1 i; ext1 j
  let L : (ι → G.Color) →ₗ[ℝ] ℝ := (LinearMap.comp (LinearMap.proj j)
    (WithLp.linearEquiv 2 ℝ _).toLinearMap : G.Color →ₗ[ℝ] ℝ).comp (LinearMap.proj i)
  change L (∑ i : ι × G.ColorIndex, stand x i • sing i) = (x i) j
  rw [map_sum]; simp_rw [map_smul]
  have he (p : ι × G.ColorIndex) : L (sing p)=(Pi.single p 1 : _ → ℝ) (i,j) := congr_fun (singled p) (i,j)
  simp_rw [he]; rw [Finset.sum_eq_single (i,j)]
  · rw [Pi.single_eq_same, smul_eq_mul,mul_one]; rfl
  · intro p _ hp; rw [Pi.single_eq_of_ne hp.symm,smul_zero]
  simp

lemma stand_squared [Fintype ι] : (∑ i, ‖x i‖^2)=dotProduct (stand x) (stand x) := by
  simp_rw [EuclideanSpace.real_norm_sq_eq, dotProduct, Fintype.sum_prod_type, pow_two]; rfl
lemma stand_cap (i : G.ColorIndex) (x : G.Color) : |x i| ≤ ‖x‖ := by
  apply le_of_sq_le_sq _ (norm_nonneg _); rw [sq_abs,EuclideanSpace.real_norm_sq_eq]
  exact Finset.single_le_sum (fun j _ => sq_nonneg _) (mem_univ _)
end

namespace Coat
variable (X : Coat T F)
abbrev Mention (c f : Side) := Signed × Rod c f
abbrev Target (c f : Side) (G : Gauge) := Mention c f × G.ColorIndex
abbrev Tubular (f : Side) (G : Gauge) := Bond f × G.ColorIndex

def root (S : StepData c f) (p : Mention c f) := p.1.act (focus S p.2)

def scale := Real.sqrt ((Fintype.card Signed:ℝ)⁻¹)
lemma scale_pos : 0 < scale := by have : 0 < Fintype.card Signed := Fintype.card_pos; unfold scale; positivity

def motion (x : Directions G f) (p : Mention c f) : G.Color :=
    if X.selected p.1 (spot S p.2) then orientedRow T X.R p.1 p.2 X.V (X.lens x) else 0

def priced (x : Directions G f) (p : Mention c f) : G.Color :=
    if X.selected p.1 (spot S p.2) then scale • X.realPath p.1 p.2 x else 0

def form : Matrix (Target c f G) (Tubular f G) ℝ := Matrix.of (fun i j => scale * stand (X.motion (sing j)) i)

def sleepy : Matrix (Tubular f G) (Tubular f G) ℝ := diagonal fun i => if X.Hot i.1 then 0 else 1

def plate := X.form.transpose * X.form + X.sleepy

def linearBill := X.form.transpose *ᵥ stand (X.priced 0)

lemma motion_lin {C Ω Λ q} (h : T.up.Bounds q Ω C Λ) (p : Mention c f) : ∃ L : Directions G f →ₗ[ℝ] G.Color,
    ∀ x, X.motion x p=L x := by
  by_cases he : X.selected p.1 (spot S p.2)
  swap; · exact ⟨0,fun _ => by simp [motion,he]⟩
  obtain ⟨L,hL⟩ := SliceRows.linear T X.R h p.1 p.2 X.V
  let B : Directions G f →ₗ[ℝ] Directions G f :=
    { toFun := X.lens
      map_add' := fun x y => by funext i; by_cases hh : X.Hot i <;> simp [lens,hh]
      map_smul' := fun a i => by funext x; by_cases H : X.Hot x <;> simp [lens,H] }
  exact ⟨L.toLinearMap.comp B,fun _ => (if_pos he).trans (hL _).symm⟩

lemma charged_for {C Ω Λ q} (h : T.up.Bounds q Ω C Λ) (x : Directions G f) (p : Target c f G) :
    scale * stand (X.motion x) p = (X.form *ᵥ stand x) p := by
  obtain ⟨L,hL⟩ := X.motion_lin h p.1
  let Z : Directions G f →ₗ[ℝ] ℝ := (LinearMap.comp (LinearMap.proj p.2) (WithLp.linearEquiv 2 ℝ _).toLinearMap : G.Color →ₗ[ℝ] ℝ).comp L
  have hZ (i : Directions G f) : Z i=stand (X.motion i) p := by unfold stand; rw [hL]; rfl
  have he (i : Directions G f) : Z (∑ j : Tubular f G, stand i j • sing j)=Z i := congr_arg Z (stand_spanned i)
  rw [← hZ,← he,map_sum,Finset.mul_sum]; simp_rw [map_smul,hZ]
  exact Finset.sum_congr rfl fun j _ => by rw [smul_eq_mul,mul_comm (stand _ _),←mul_assoc]; rfl

lemma lens_zero : X.lens 0=0 := by funext i; by_cases he : X.Hot i <;> simp [lens,he]
lemma pricing {C Ω Λ q} (h : T.up.Bounds q Ω C Λ) (x : Directions G f) :
    stand (X.priced x)=stand (X.priced 0)+ X.form *ᵥ stand x := by
  funext p
  let i := p.1
  obtain ⟨L,hL⟩ := SliceRows.linear T X.R h p.1.1 p.1.2 X.V
  rw [Pi.add_apply, ← X.charged_for h x]; simp only [priced,stand,motion]
  split
  next he =>
    unfold realPath signal; rw [lens_zero,add_zero,← hL,← hL,← hL,map_add,← add_assoc,smul_add]
    rfl
  next he => change (0:ℝ) = 0+scale*0; ring

lemma in_count (x : Directions G f) : X.liftSq x = dotProduct (stand (X.priced x)) (stand (X.priced x))/2 := by
  rw [← stand_squared, Fintype.sum_prod_type]
  unfold liftSq Oriented.averaged extracted; simp_rw [spots_sum S,Finset.mul_sum]; simp_rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  unfold surcharge priced; dsimp only; split
  next he => rw [norm_smul, mul_pow,Real.norm_eq_abs, sq_abs,scale,Real.sq_sqrt (by positivity)]; ring
  next he => simp

lemma balance {q Ω C Λ} (h : T.up.Bounds q Ω C Λ) (x u : Directions G f) :
    X.liftSq (x+u) - X.liftSq x = dotProduct (stand u) (X.linearBill+ (X.form.transpose*X.form) *ᵥ stand x)+
      dotProduct (stand u) ((X.form.transpose*X.form) *ᵥ stand u)/2 := by
  let b := stand (X.priced 0)
  rw [X.in_count, X.in_count, X.pricing h (x+u), X.pricing h x, show stand (x+u)=stand x+stand u from rfl]
  unfold linearBill
  let M := X.form
  have he (v w) : dotProduct v (X.form.transpose *ᵥ w)=dotProduct (X.form *ᵥ v) w :=
    (Matrix.dotProduct_mulVec ..).trans <| congr_arg (dotProduct · w) (Matrix.vecMul_transpose ..)
  simp only [← Matrix.mulVec_mulVec, Matrix.mulVec_add, dotProduct_add, add_dotProduct, he]
  rw [dotProduct_comm (X.form *ᵥ stand u) b, dotProduct_comm (X.form *ᵥ stand u) (X.form *ᵥ stand x)]
  unfold b; ring

lemma cold (p : Tubular f G) (hp : ¬ X.Hot p.1) {q Ω C Λ} (h : T.up.Bounds q Ω C Λ) (i : Target c f G) : X.form i p=0 := by
  have he : X.lens (sing p)=0 := by
    funext j; unfold sing lens; split
    next hh =>
      rw [Pi.single_eq_of_ne]; rfl
      intro hc; apply hp; rwa [hc] at hh
    rfl
  unfold form; rw [of_apply]
  unfold stand motion; split
  next hg =>
    obtain ⟨L,hL⟩ := SliceRows.linear T X.R h i.1.1 i.1.2 X.V
    rw [he,← hL,map_zero]; change scale*(0:ℝ)=0; ring
  next hg => change scale*(0:ℝ)=0; ring

lemma asleep (p : Tubular f G) (hp : ¬ X.Hot p.1) {q Ω C Λ} (h : T.up.Bounds q Ω C Λ) (i : Tubular f G) : X.plate p i=(1:Matrix ..) p i := by
  rw [plate,Matrix.add_apply,Matrix.mul_apply]
  have hh := fun j => X.cold p hp h j
  simp only [Matrix.transpose_apply,hh,zero_mul,Finset.sum_const_zero,zero_add]
  by_cases he : p=i
  · subst i; simp [sleepy,hp]
  simp [sleepy,he]

lemma balanced : X.plate.IsHermitian := by
  ext i j
  simp_rw [plate,conjTranspose_add,conjTranspose_mul]
  rw [show X.formᴴ=X.form.transpose from by ext; simp,show X.form.transposeᴴ=X.form from by ext; simp]; simp [sleepy]

lemma toned : X.plate.transpose=X.plate := by
  rw [← show X.plateᴴ=X.plate.transpose from by ext; simp]; exact X.balanced
end Coat
end YM.ConnectedActivityE6
