import YM.Further.CURVED_GAUSSIAN_JETS.Horizon
import YM.Further.CURVED_GAUSSIAN_JETS.Rows

/-!
# Flat orientation channels, keeping path cut per channel

Noise in `tested` isn't computed by replacing one branch tag by
independent choices. The transformations here are on the channel-averaged
path part; `Dcut` in the next file still keeps the common-orientation probe
ONCE (not via a new average identity on different S's noise kernels).
Sworn is on the actual metric; prove its use on uncolored link components.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Rot
open Function Filter MeasureTheory Set Matrix Lattice SectorNext.Vacuum Wilson Tree RG Precision
open Progress.StationaryScenes Bid Exterior FlatTree Bloch Pressure Flat
open Green (wt)
open Rows (Bill)
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical
variable {G : Gauge} {n : Side}

def face (s : Signed) (x : OneForm n) := sendEdge s 0 ((wheel n).symm x)
def orbit (n : Side) (s : Signed) : OneForm n ≃ OneForm n := Equiv.ofBijective (wheel n ∘ face s) (by
  have h := (wheel n).injective.comp ((Wilson.sendEdge_injective s (0:Site n)).comp (wheel n).symm.injective)
  exact ⟨h,Finite.injective_iff_surjective.mp h⟩)
def sign (s : Signed) (x : OneForm n) : ℝ := if ((posDir (axisEquiv.symm x.2)).rotate s).neg then -1 else 1
def map (n : Side) (s : Signed) := Matrix.of fun (i j : OneForm n) => if orbit n s i = j then sign s i else 0
lemma swing_eq (s : Signed) (v : Vec (OneForm n)) : (map n s)*ᵥv=swing s v := by
  funext x; simp [map,mulVec,dotProduct,swing,beam,sign,orbit,face,ite_mul,Wilson.sendEdge, wheel,axisEquiv,Equiv.prodCongr]; rfl



def conjugate {I X : Type*} [Fintype I] (s : Matrix I X ℝ) (A : Table I) := s.transpose*A*s






variable {I : Type*} [Fintype I] (v : Signed → Table I)

def average : Table I := Matrix.of fun i j => (Fintype.card Signed:ℝ)⁻¹*∑ s, v s i j
lemma normal : 0 < (Fintype.card Signed : ℝ) := by exact_mod_cast (Fintype.card_pos (α:=Signed))
omit [Fintype I] in
lemma average_const (A : Table I) : average (fun _=> A)=A := by ext i j; simp [average, normal.ne']
omit [Fintype I] in
lemma average_sub (w : Signed → Table I) : average (fun i => v i-w i)=average v-average w := by
  ext i j; simp [average,Finset.sum_sub_distrib]; ring
omit [Fintype I] in
lemma average_symm (h : ∀ s, (v s).IsHermitian) : (average v).IsHermitian := by
  have he s i j : v s j i=v s i j := congr_fun (congr_fun (h s) i) j
  ext i j; simp only [conjTranspose_apply, average, of_apply, star_trivial]; simp_rw [he _ i j]

lemma average_bill {a : I → Site n} {w C : ℝ} (h : ∀ s, Bill a w (v s) C) : Bill a w (average v) C := by
  have he (v : Signed → Table I) (hv : ∀ s, Green.Rows a a (v s) w C) : Green.Rows a a (average v) w C := by
    intro i; unfold average; simp_rw [Matrix.of_apply,abs_mul,abs_of_pos (inv_pos.mpr normal), mul_left_comm (wt ..), ← Finset.mul_sum];
    calc
      _ ≤ (Fintype.card Signed:ℝ)⁻¹ * ∑ j, ∑ s, wt w (a i) (a j)*|v s i j| := by
        simp_rw [← Finset.mul_sum]; gcongr; exact (Green.wt_pos ..).le; exact Finset.abs_sum_le_sum_abs ..
      _ ≤ C := by rw [Finset.sum_comm]; apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _=> hv s i) (inv_pos.mpr normal).le).trans; simp [normal.ne']
  exact ⟨he v fun s => (h s).1,he (fun s=>(v s).transpose) fun s=>(h s).2⟩
end YM.Further.CurvedGaussianJets.Rot
