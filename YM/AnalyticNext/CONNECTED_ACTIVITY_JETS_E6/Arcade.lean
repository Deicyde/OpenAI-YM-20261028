import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Terminal

/-!
# Price fields build and erase at internal tests (mass under local inverses)

Requires measures later, here estimate matrix jets at each ray. Helps β rotations. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c : Side} {E ι κ ν : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
open Brush
variable {v z f g r : ℝ} {k D M B : ℕ}
variable [Fintype ι] [Fintype κ] {x : E} {a : ι → Site c} {b : κ → Site c} {d : ν → Site c} {η γ : ℝ}
variable {A : E → Matrix ι κ ℝ}

private lemma tillage (P : ι→κ→Prop) (p : Matrix ι κ ℝ) (h : Price a b p η f) :
    Price a b (Matrix.of (fun i j=> if P i j then 0 else p i j)) η f := by
  constructor <;> intro i
  · apply le_trans _ (h.1 i); apply sum_le_sum; intro j _; simp only [Matrix.of_apply]; split
    next hj => rw [abs_zero,mul_zero]; exact mul_nonneg (wt_pos ..).le (abs_nonneg _)
    exact le_rfl
  apply le_trans _ (h.2 i); apply sum_le_sum; intro j _; simp only [Matrix.transpose_apply, Matrix.of_apply]; split
  next hj => rw [abs_zero,mul_zero]; exact mul_nonneg (wt_pos ..).le (abs_nonneg _)
  exact le_rfl

namespace Tablet
lemma faraway (p : Tablet k η f v A a b x) (X : ℕ)
    (h : ∀ i j,separation (a i) (b j) ≤ X → (fun y => A y i j) =ᶠ[𝓝 x] (fun _=>0)) (he : γ≤η) (hv : 0≤γ) :
      Tablet k γ (Real.exp ((γ-η)*X)*f) v A a b x := by
  obtain ⟨B,hB,hp⟩:=p.shape
  let C : Matrix ι κ ℝ := Matrix.of (fun i j=> if separation (a i) (b j) ≤ X then 0 else B i j)
  have hC : Price a b C η f := by convert tillage (fun i j=>separation (a i) (b j) ≤ X) B hp using 1; ext; simp [C]
  have hh i j (hi : separation (a i) (b j) ≤ X) : C i j=0 := if_pos hi
  refine ⟨hv,p.pos,mul_nonneg (Real.exp_pos _).le p.basis,C,fun i j=> ?_,
    neighbor_pay hC.1 X hh he, ?_⟩
  swap
  · refine neighbor_pay hC.2 X ?_ he; intro i j h
    rw [separation_comm] at h; exact hh _ _ h
  dsimp only [C,Matrix.of_apply]; split
  next he =>
    have hp := (Brush.certified (k:=k) (x:=x) p.pos (0:ℝ)).shimmy (h i j he); rwa [norm_zero] at hp
  exact hB ..
lemma across (ha : Census D a) (hb : Census M b) (hV : 0≤v) (h : ∀ i j, Brush k (f/wt η (a i) (b j)) v (fun y=> A y i j) x)
    (he : γ < η) (hg : 0≤γ) (hj : 0≤f) :
    Tablet k γ (max 0 (max (price0 (η-γ)*D*f) (price0 (η-γ)*M*f))) v A a b x := by
  let V : Matrix ι κ ℝ := Matrix.of (fun i j=> f/wt η (a i) (b j)); have he' i j : 0 ≤ V i j := (h i j).nonneg
  have hv i j : wt η (a i) (b j)*|V i j| ≤ f := by
    rw [abs_of_nonneg (he' _ _),mul_comm]
    unfold V; rw [Matrix.of_apply,div_mul_cancel₀ _ (wt_pos ..).ne']
  refine ⟨hg,hV,le_max_left ..,V,h, pricing (rows hb a V hj he hv) le_rfl (le_max_of_le_right (le_max_right ..)),
    pricing (rows ha b V.transpose hj he ?_) le_rfl (le_max_of_le_right (le_max_left ..))⟩
  intro i j; rw [wt_symm]; exact hv j i

variable {A : E → Matrix ι ι ℝ} [DecidableEq ι]

-- Ax(A) price recovered oni fixed X. Inverse and product estimates. Use
-- possibly smaller pref σ, not with any claim in wrong side of maximum.
def facePrice (k B m : ℕ) (f P : ℝ) : ℝ := ((ballCost (B+2):ℕ)*m:ℕ)*token k f P
lemma emboss (p : Tablet k η f v A a a x) (hc : Census M a)
    (W : Window a B) (hv : 0≤g) (h : ∀ i, let e:=Embedding.subtype (·∈W.take i)
      let C:=W.principal (A x) i; IsUnit C.det ∧ Price (a∘e) (a∘e) C⁻¹ η g) :
    Tablet k η (facePrice k B M f g) (driftP k v) (fun y=> W.pad (A y)) a a x := by
  let U:= token k f g; let b:= driftP k v; have hb : 0≤b := mul_nonneg (Nat.cast_nonneg _) p.pos
  let G := Matrix.of (fun i j=> if separation (a i) (a j)≤ B+2 then U/wt η (a i) (a j) else 0)
  have hu : 0≤U := by unfold U token; have := p.basis; positivity
  have he : 0≤facePrice k B M f g := mul_nonneg (Nat.cast_nonneg _) hu
  have hh : Rows a a G η (facePrice k B M f g) := by
    intro i; dsimp only [G,Matrix.of_apply]
    have hf (j): wt η (a i) (a j)*|if separation (a i) (a j)≤B+2 then U/wt η (a i) (a j) else 0|=
        (if separation (a i) (a j)≤B+2 then U else 0) := by
      split; next h => rw [abs_of_nonneg (div_nonneg hu (wt_pos ..).le), mul_comm,div_mul_cancel₀ _ (wt_pos ..).ne']
      next h' => rw [abs_zero,mul_zero]
    simp_rw [hf,← sum_filter,sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast count_near hc (a i) (B+2)) hu
  refine ⟨p.scale,hb,he,G,fun i j=> ?_,⟨hh,?_⟩⟩
  · by_cases hi : i∈W.take j
    · rw [show G i j=U/wt η (a i) (a j) from if_pos (W.high _ _ hi)]; simp_rw [show ∀ y:E, W.pad (A y) i j= _ from fun y=> W.inside _ j ⟨i,hi⟩]
      let V:=Embedding.subtype (·∈W.take j); exact ((p.trim_left V V).inverter (h j).1 (h j).2 hv).entry ⟨i,hi⟩ ⟨j,W.here j⟩
    simp_rw [W.outside _ i j hi]; apply (certified hb 0).climb _ le_rfl; rw [norm_zero]; dsimp only [G,Matrix.of_apply]; split
    next hj=> exact div_nonneg hu (wt_pos ..).le
    exact le_rfl
  have hx : G.transpose=G := by ext i j; dsimp only [G,transpose_apply,of_apply]; rw [wt_symm,separation_comm (a i)]
  rwa [hx]
end Tablet
end YM.ConnectedActivityE6.Blaze
