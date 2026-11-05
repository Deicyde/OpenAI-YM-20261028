import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import YM.Next.FREE_KERNELS.Glue
import YM.Work.F06.Stencil
import YM.Work.F08.Rows

/-!
# Width budgets for Laurent homotopies

Book transformations as replacing monomial x by a kernel even before testing
any closure condition. Coefficients on the full cover; no equations modulo n.
All exponents native. This policy will permit length seen under division again
on the second (same momentum) argument of a symbol.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08
open scoped Topology BigOperators ComplexConjugate

def envelopeW (η : ℝ) (z : Cover) := Real.exp (η*size z)
lemma envelope_pos (η : ℝ) (z : Cover) : 0 < envelopeW η z := Real.exp_pos _

/-- Prices may grow with the *input monomial*, book that into width. -/
def Tariff (R : Cover → Cover → ℝ) (η σ B : ℝ) := ∀ i,
    Width σ (B * envelopeW η i) (R i)

def payOut (R : Cover → Cover → ℝ) (f : Cover → ℝ) (z : Cover) := ∑' i, f i*R i z

variable {R : Cover → Cover → ℝ} {η σ B C : ℝ} {u : Cover → ℝ}
namespace Tariff
lemma estimate (h : Tariff R η σ B) (hb : 0 ≤ B) (hu : Width η C u) :
    SumBudget (fun z : Cover × Cover => envelopeW σ z.2*‖u z.1*R z.1 z.2‖) (B*C) := by
  let f := fun x y : Cover => envelopeW σ y*‖u x*R x y‖
  have hF : 0 ≤ Function.uncurry f := fun z => mul_nonneg (envelope_pos _ _).le (norm_nonneg _)
  let g := fun i => envelopeW η i*‖u i‖
  have hh i : SumBudget (f i) (B*g i) := by
    let w := fun z => envelopeW σ z * ‖R i z‖
    have he : SumBudget w _ := h i
    have hx : f i=fun z => ‖u i‖*w z := by unfold f w; simp_rw [norm_mul,mul_left_comm]
    rw [hx]; refine ⟨fun j => mul_nonneg (norm_nonneg _) (he.1 _),he.2.1.mul_left _,?_⟩
    rw [tsum_mul_left]
    exact (mul_le_mul_of_nonneg_left he.2.2 (norm_nonneg _)).trans_eq (by unfold g; ring)
  have hg : SumBudget g C := hu
  have ha : Summable fun i => ∑' j, f i j := (hg.2.1.mul_left B).of_nonneg_of_le (fun i => tsum_nonneg (hh i).1) fun i => (hh i).2.2
  have hx : Summable (Function.uncurry f) := (summable_prod_of_nonneg (by exact hF)).mpr ⟨fun i => (hh i).2.1,ha⟩
  refine ⟨hF,hx,?_⟩
  change ∑' z, uncurry f z ≤ _; rw [hx.tsum_prod]
  apply (ha.tsum_le_tsum (g:=fun i => B*g i) (fun i => (hh i).2.2) (hg.2.1.mul_left _)).trans
  rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hg.2.2 hb
lemma freedom (h : Tariff R η σ B) (hb : 0 ≤ B) (hu : Width η C u) (he : 0 ≤ σ) :
    Summable fun z : Cover × Cover => ‖u z.1*R z.1 z.2‖ := by
  have hh : Tariff R η 0 B := fun i => (h i).mono he le_rfl
  simpa [envelopeW] using (hh.estimate hb hu).2.1
lemma released (h : Tariff R η σ B) (hb : 0 ≤ B) (hu : Width η C u) (he : 0 ≤ σ) :
    Width σ (B*C) (payOut R u) := by
  let f := fun x y : Cover => envelopeW σ x*‖u y * R y x‖
  have h1 := h.estimate hb hu
  have hm : 0 ≤ uncurry f := fun ⟨i,j⟩ => h1.1 (j,i)
  have hs : Summable (uncurry f) := h1.2.1.prod_symm
  have hh : SumBudget (fun x => ∑' j, f x j) (B*C) := by
    refine ⟨fun i => tsum_nonneg (fun j => hm (i,j)),((summable_prod_of_nonneg hm).mp hs).2,?_⟩
    change ∑' x, ∑' j, (uncurry f) (x,j) ≤ _
    rw [← hs.tsum_prod]; unfold uncurry f
    exact ((Equiv.prodComm Cover Cover).tsum_eq (fun z => envelopeW σ z.2 * ‖u z.1 * R z.1 z.2‖)).trans_le h1.2.2
  unfold Width; refine budget_minor hh (fun _ => by positivity) fun i => ?_
  dsimp only [envelopeW,f,payOut]; rw [tsum_mul_left]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact norm_tsum_le_tsum_norm ((h.freedom hb hu he).prod_symm.prod_factor i)
lemma redeemed (h : Tariff R η σ B) (hb : 0 ≤ B) (hu : Width η C u) (he : 0 ≤ σ) {p : Momentum} (hp : physical p) :
    RRead (payOut R u) p = ∑' i, (u i:ℂ)*RRead (R i) p := by
  let f (x y : Cover) := mode p y * ((u x * R x y:ℝ):ℂ)
  have hs : Summable (Function.uncurry f) := by
    apply Summable.of_norm; simp_rw [uncurry, f]; simp only [norm_mul,mode_real p _ hp,one_mul,Complex.norm_real]
    simpa only [norm_mul] using h.freedom hb hu he
  calc
    _ = ∑' y, ∑' x, f x y := by unfold RRead Laurent.read payOut f; simp_rw [Complex.ofReal_tsum,smul_eq_mul,tsum_mul_left]
    _ = ∑' x, ∑' y, f x y := hs.tsum_comm
    _ = _ := by unfold RRead Laurent.read; refine tsum_congr fun i => ?_; rw [← tsum_mul_left]; exact tsum_congr fun j => by simp [f,mul_left_comm]
end Tariff

def token (x y : Cover) : ℝ := if y=x then 1 else 0
lemma token_rate (x : Cover) (η : ℝ) : Width η (envelopeW η x) (token x) := by
  let f z := envelopeW η z * ‖token x z‖
  have he (z) (h : z≠x) : f z=0 := by simp [f,h,token]
  change SumBudget f _
  refine ⟨fun z => mul_nonneg (envelope_pos _ _).le (norm_nonneg _),summable_of_ne_finset_zero (s:={x}) (fun i h => he i (by simpa using h)),?_⟩
  rw [tsum_eq_single x he]; simp [f,token]
lemma token_eval (x : Cover) (p : Momentum) : RRead (token x) p=mode p x := by
  unfold RRead Laurent.read; rw [tsum_eq_single x]; simp [token]
  exact fun i h => by simp [token,h]
lemma step_size (t : Cover) (x : Axis) (b : ℤ) (h : b.natAbs ≤ (t x).natAbs) : size (Function.update t x b) ≤ size t := by
  unfold size; apply Finset.sum_le_sum; intro i _; by_cases hx : i=x <;> simp [Function.update,h,hx]
lemma step_one (t : Cover) (x : Axis) (b : ℤ) : Function.update t x (b+1)=Function.update t x b+step x := by ext i; by_cases hx : i=x <;> simp [Function.update,hx]
lemma Width.scale_line (r : ℝ) (h : Width η C u) : Width η (‖r‖*C) (fun i => r*u i) := by
  let v : Row Unit Unit := fun _ _ => u
  exact strip_scale (show v.strip η C from fun _ _ => h) r () ()
lemma Width.add_line {v : Cover → ℝ} (h : Width η C u) (g : Width η B v) : Width η (C+B) fun i => u i+v i := by
  let P : Row Unit Unit := fun _ _ => u; let Q : Row Unit Unit := fun _ _ => v
  exact Work.F06.row_strip_add (show P.strip η C from fun _ _ => h) (show Q.strip η B from fun _ _ => g) () ()
lemma RRead_neg (u : Cover → ℝ) (p : Momentum) : RRead (fun x => -u x) p= - RRead u p := by unfold RRead Laurent.read; simp_rw [Complex.ofReal_neg,smul_neg,tsum_neg]
end YM.Next.Free
