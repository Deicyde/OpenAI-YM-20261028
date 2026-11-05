import YM.Further.CURVED_GAUSSIAN_JETS.Rows
import YM.Further.CURVED_GAUSSIAN_JETS.Units
import YM.Next.FREE_KERNELS.Sell

/-!
# Principal-column selection and uniform exponential receipts (real, zero jet)

Compression of A itself (not omission of rows of D meeting its
boundary!). No symmetry or translational invariance of the set of chosen
columns necessary. Distance here separation on a native Site n; window
can be supplied from other conventions by giving the containment proof
at the displayed radius. Cost constants explicit, *after* the gap &
stencil quotes, even for empty key and bounded sides. No requiring
q or spectrum on the computed covariance as input.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets
open Function Filter Matrix Lattice Progress.StationaryScenes SectorNext.Vacuum Precision
open Green (wt Bottom wt_symm wt_pos)
open Rows (Bill)
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {n : Side} {I : Type*}
structure Prices where
  width : ℝ
  gap : ℝ
  mass : ℝ
  tags : ℕ
  width_pos : 0<width
  gap_pos : 0<gap
  mass_pos : 0<mass

namespace Prices
variable (p : Prices)
def ratio := min 1 ((p.gap/2)/p.mass)
def speed := p.ratio*p.width/4
def toll := (min 1 (p.gap/2))⁻¹
def reserve := 1+p.toll*(p.tags * Push.Uniform.countCost (2*p.speed))
lemma ratio_pos : 0<p.ratio := lt_min zero_lt_one (by have := p.gap_pos; have := p.mass_pos; positivity)
lemma slow : p.ratio≤1 ∧ p.ratio*p.mass≤p.gap/2 :=
    ⟨min_le_left ..,(le_div_iff₀ p.mass_pos).mp (min_le_right ..)⟩
lemma speed_pos : 0<p.speed := by unfold speed; have := p.ratio_pos; have := p.width_pos; positivity
lemma speed_le : 2*p.speed ≤ p.width := by
  have := mul_le_mul_of_nonneg_right p.slow.1 p.width_pos.le; unfold speed; linarith [p.width_pos]
lemma toll_pos : 0<p.toll := inv_pos.mpr (lt_min zero_lt_one (half_pos p.gap_pos))
lemma reserve_pos : 0<p.reserve := by unfold reserve; have := p.toll_pos; have := Push.Uniform.count_pos (mul_pos two_pos p.speed_pos); positivity
end Prices

variable [Fintype I]
structure Fits (a : I → Site n) (p : Prices) (A : Table I) : Prop where
  symm : A.IsHermitian
  entries : Bill a p.width A p.mass
  mult : Push.Uniform.Multiplicity a p.tags
  floor : Bottom A p.gap

namespace Fits
variable {a : I → Site n} {A : Table I} {p : Prices}
lemma restrict {J : Type*} [Fintype J] (h : Fits a p A) (e : J ↪ I) : Fits (a ∘ e) p (A.submatrix e e) :=
  ⟨h.symm.submatrix e,⟨h.entries.1.restrict e e,h.entries.2.restrict e e⟩, h.mult.comp e.injective,h.floor.restrict e⟩
lemma numeric (h : Fits a p A) : Numeric A p.gap p.mass := fun v=>⟨h.floor v, Rows.upper p.width_pos.le h.entries v⟩
lemma pos (h : Fits a p A) : A.PosDef := Matrix.PosDef.of_dotProduct_mulVec_pos h.symm fun v hv => by
    rw [star_trivial]; exact (mul_pos p.gap_pos (Joint.dot_pos hv)).trans_le (h.floor v)
end Fits

variable [DecidableEq I]

def shifted (A : Table I) (u : ℝ) := A + u • (1:Table I)
lemma Fits.shift_pos {a : I → Site n} {A : Table I} {p : Prices} (h : Fits a p A) {u : ℝ} (hu : 0≤u) :
    (shifted A u).PosDef := h.pos.add_posSemidef (Matrix.PosSemidef.one.smul hu)
lemma Fits.inverse {a : I → Site n} {A : Table I} {p : Prices} (h : Fits a p A) {u : ℝ} (hu : 0≤u) :
    ∀ i j, wt (4*p.speed) (a i) (a j) * |(shifted A u)⁻¹ i j| ≤ p.toll/(1+u) := by
  rw [show 4*p.speed=p.ratio*p.width by unfold Prices.speed; ring]
  have he := (Green.inverse p.width_pos.le p.gap_pos p.ratio_pos.le p.slow.1 p.slow.2 h.symm h.floor h.entries u hu).2.2
  intro i j
  exact (he i j).trans_eq (by unfold Prices.toll; field_simp)
omit [DecidableEq I] in
lemma Prices.of_point {a : I → Site n} {B : Table I} (p : Prices) (hm : Push.Uniform.Multiplicity a p.tags)
    {u : ℝ} (hu : 0≤u) (h : ∀ i j, wt (4*p.speed) (a i) (a j) * |B i j| ≤ p.toll/(1+u)) : Bill a (2*p.speed) B (p.reserve/(1+u)) := by
  have hf := Rows.weighed_budget hm h (by have := p.toll_pos; positivity) (by linarith [p.speed_pos])
  rw [show 4*p.speed/2=2*p.speed by ring] at hf
  apply Rows.bigger hf
  unfold Prices.reserve; have hx : 0<1+u := by positivity
  rw [div_mul_eq_mul_div]; gcongr; linarith

structure Windows (I : Type*) where
  box : I → Finset I
  within (i : I) : i∈box i

namespace Windows
variable (W : Windows I) (A : Table I)
def center (i : I) : W.box i := ⟨i,W.within i⟩
abbrev inside (i : I) : W.box i ↪ I := Function.Embedding.subtype _
def localGram (i : I) : Table (W.box i) := A.submatrix (W.inside i) (W.inside i)
def resolvent (i : I) (u : ℝ) := (shifted (W.localGram A i) u)⁻¹

def column (u : ℝ) := Matrix.of fun j i => if h : j ∈ W.box i then W.resolvent A i u ⟨j,h⟩ (W.center i) else 0

def defect (u : ℝ) := shifted A u * W.column A u - 1

def blend : Table I := (1/2:ℝ) • (W.column A 0 + (W.column A 0).transpose)
def mean (b : Vec I) := -((W.column A 0).transpose *ᵥ b)
omit [Fintype I] in
lemma blend_symm : (W.blend A).IsHermitian :=
    (show (W.column A 0 + (W.column A 0).transpose).IsHermitian from isHermitian_add_transpose_self _).smul (star_trivial _)

omit [DecidableEq I] in
lemma fitsGram {a : I → Site n} {p : Prices} (h : Fits a p A) (i : I) :
    Fits (a ∘ W.inside i) p (W.localGram A i) := h.restrict _
omit [Fintype I] in
lemma local_entry {i j k : I} {u : ℝ} (hj : j ∈ W.box i) (hk : k ∈ W.box i) :
    shifted (W.localGram A i) u ⟨j,hj⟩ ⟨k,hk⟩ = shifted A u j k := by simp [shifted,localGram,one_apply]

variable {A} {a : I → Site n} {p : Prices} (h : Fits a p A)

include h in
lemma column_left (u : ℝ) (hu : 0≤u) (i j : I) :
    wt (4*p.speed) (a i) (a j)*|W.column A u i j| ≤ p.toll/(1+u) := by
  unfold column; simp only [Matrix.of_apply]; split <;> rename_i H
  · exact ((W.fitsGram A h j).inverse hu ⟨i,H⟩ (W.center j))
  rw [abs_zero,mul_zero]; have := p.toll_pos; positivity
include h in
lemma column_both (u : ℝ) (hu : 0≤u) : Bill a (2*p.speed) (W.column A u) (p.reserve/(1+u)) :=
    Prices.of_point _ h.mult hu (W.column_left h u hu)

lemma restricted_mul (i j : I) (M : Table I) (u : ℝ) :
    (M * W.column A u) j i = ∑ k : W.box i, M j k * W.resolvent A i u k (W.center i) := by
  let v (k : I) := M j k * W.column A u k i
  rw [Matrix.mul_apply, show (∑ k, M j k * W.column A u k i) = ∑ k∈W.box i,v k from Eq.symm
      (Finset.sum_subset (Finset.subset_univ ..) fun k _ hk => by simp [v,column,hk]), ← Finset.sum_coe_sort]
  exact Finset.sum_congr rfl fun k _=> by simp [v,column,k.2]

include h in
lemma inside_defect (u : ℝ) (hu : 0≤u) (i j : I) (hj : j∈ W.box i) : W.defect A u j i = 0 := by
  have hh := (W.fitsGram A h i).shift_pos hu
  let E := shifted (W.localGram A i) u
  have he := Matrix.mul_nonsing_inv E (isUnit_iff_ne_zero.mpr hh.det_pos.ne')
  have hx := congr_arg (fun T : Table (W.box i)=> T ⟨j,hj⟩ (W.center i)) he
  rw [Matrix.mul_apply] at hx
  change (∑ k, shifted _ _ ⟨j,hj⟩ k * W.resolvent A i u k (W.center i)) = _ at hx
  conv at hx => lhs; arg 2; intro k; rw [show k=⟨k.val,k.property⟩ from rfl,W.local_entry A hj k.property]
  rw [defect,Matrix.sub_apply,restricted_mul, hx]; simp [Matrix.one_apply,center]
lemma outside_defect (u : ℝ) (i j : I) (hj : j∉ W.box i) : W.defect A u j i = (A*W.column A u) j i := by
  have hji : j≠i := by rintro rfl; exact hj (W.within _)
  simp [defect, shifted, Matrix.add_mul,column,hj,hji]

def Includes (a : I → Site n) (N : ℕ) : Prop := ∀ i j, separation (a i) (a j) ≤ N → i ∈ W.box j
variable {N : ℕ} (hW : W.Includes a N)

include h hW
private lemma entry_tail (u : ℝ) (hu : 0≤u) (i j : I) :
    wt p.speed (a i) (a j) * |W.defect A u i j| ≤ Real.exp (-p.speed*N)*(wt (2*p.speed) (a i) (a j) * |(A*W.column A u) i j|) := by
  by_cases hx : i∈W.box j
  · rw [W.inside_defect h u hu j i hx,abs_zero,mul_zero]; have := wt_pos (2*p.speed) (a i) (a j); positivity
  rw [outside_defect _ u j i hx, ←mul_assoc]; apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  unfold wt; rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
  have hh : (N:ℝ) < (separation (a i) (a j):ℝ) := by exact_mod_cast lt_of_not_ge (mt (hW i j) hx)
  nlinarith [p.speed_pos]

end Windows
namespace Prices
variable (p : Prices) (N : ℕ)
def deep := Real.exp (-p.speed*N) * (p.mass*p.reserve)
def halo := p.reserve * p.deep N
def error := p.mass * p.halo N
lemma deep_pos : 0<p.deep N := mul_pos (Real.exp_pos _) (mul_pos p.mass_pos p.reserve_pos)
lemma halo_pos : 0<p.halo N := mul_pos p.reserve_pos (p.deep_pos _)
lemma error_pos : 0<p.error N := mul_pos p.mass_pos (p.halo_pos _)
lemma delay : Tendsto p.error atTop (𝓝 0) := by
  unfold error halo deep
  have ht : Tendsto (fun N : ℕ => p.speed*(N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.const_mul_atTop p.speed_pos
  simpa only [neg_mul, Function.comp_apply, mul_zero, zero_mul] using (((Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).mul_const
    (p.mass*p.reserve)).const_mul p.reserve).const_mul p.mass
end Prices
namespace Windows
variable (W : Windows I) {A : Table I} {a : I → Site n} {p : Prices} (h : Fits a p A) {N : ℕ} (hW : W.Includes a N)
include h hW
lemma defect_price (u : ℝ) (hu : 0≤u) : Bill a p.speed (W.defect A u) (p.deep N/(1+u)) := by
  have hx := p.speed_pos
  have hr := W.column_both h u hu
  have he := Rows.product (by positivity) (Rows.slower h.entries p.speed_le) hr p.mass_pos.le (by have := p.reserve_pos; positivity)
  have H (M B : Table I) (H : ∀ i j,wt p.speed (a i) (a j)*|M i j| ≤ Real.exp (-p.speed*N) * (wt (2*p.speed) (a i) (a j) * |B i j|))
      (hB : Rows.Bill a (2*p.speed) B (p.mass*(p.reserve/(1+u)))) :
      Green.Rows a a M p.speed (p.deep N / (1+u)) := fun i => by
    apply (Finset.sum_le_sum (fun j _=>H i j)).trans; rw [← Finset.mul_sum]; apply
      (mul_le_mul_of_nonneg_left (hB.1 i) (Real.exp_pos _).le).trans_eq; unfold Prices.deep; ring
  exact ⟨H _ _ (entry_tail W h hW u hu) he,H _ _ (fun i j => by
    rw [wt_symm p.speed (a i), wt_symm (2*p.speed) (a i)]; exact entry_tail W h hW u hu j i) (Rows.tran he)⟩

lemma error_kernel (u : ℝ) (hu : 0≤u) : Bill a p.speed (W.column A u-(shifted A u)⁻¹) (p.halo N / (1+u)^2) := by
  let T := shifted A u
  have he : W.column A u-T⁻¹=T⁻¹*W.defect A u := by rw [defect, Matrix.mul_sub, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul T (isUnit_iff_ne_zero.mpr (h.shift_pos hu).det_pos.ne'),one_mul,mul_one]
  change Bill ..; rw [he]
  have hh : Bill a p.speed T⁻¹ (p.reserve/(1+u)) := Rows.slower (p.of_point h.mult hu (h.inverse hu)) (by linarith [p.speed_pos])
  rw [Prices.halo, pow_two,mul_div_mul_comm]; exact Rows.product p.speed_pos.le hh (W.defect_price h hW u hu)
    (by have := p.reserve_pos; positivity) (by have := p.deep_pos N; positivity)
lemma blend_error : Bill a p.speed (W.blend A - A⁻¹) (p.halo N) := by
  have hh : Bill a p.speed (W.column A 0-A⁻¹) (p.halo N) := by simpa only [shifted,zero_smul,add_zero,one_pow,div_one] using W.error_kernel h hW 0 le_rfl
  have ht := Rows.pay (Rows.plus hh (Rows.tran hh)) (1/2:ℝ)
  have hs : A⁻¹.transpose=A⁻¹ := h.symm.inv
  rw [transpose_sub,hs] at ht
  convert ht using 1
  · unfold blend; ext i j; simp; ring
  rw [abs_of_pos (by norm_num)]; ring
lemma correction_bill : Bill a p.speed (A*W.blend A-1) (p.error N) := by
  have he : A*W.blend A-1=A*(W.blend A-A⁻¹) := by rw [Matrix.mul_sub,A.mul_nonsing_inv (isUnit_iff_ne_zero.mpr h.pos.det_pos.ne')]
  rw [he]; exact Rows.product p.speed_pos.le (Rows.slower h.entries (by linarith [p.speed_le,p.speed_pos])) (W.blend_error h hW) p.mass_pos.le (p.halo_pos N).le




lemma correction_ratio (hN : p.error N < 1) : let C := W.blend A
    C.PosDef ∧ Rows.Bill a p.speed (C⁻¹-A) ((1-p.error N)⁻¹ * p.error N * p.mass) ∧
      ∀ i j, HasSum (fun k : ℕ => ((-(A*C-1))^(k+1)*A) i j) ((C⁻¹-A) i j) := by
  intro C
  have hh := W.correction_bill h hW
  have hz := (p.error_pos N).le
  have hc : C.PosDef := corrected_pos h.pos (W.blend_symm _) (Rows.unweighted hh p.speed_pos.le) hN
  have he : 1+(A*C-1)=A*C := by abel
  have hs := Rows.slower h.entries (r:=p.width) (h:=p.speed) (by linarith [p.speed_pos,p.speed_le])
  exact ⟨hc,Rows.inverse_error he hc hh hs p.mass_pos.le p.speed_pos.le hz hN,Rows.precision_series he hc hh p.speed_pos.le hz hN⟩

end Windows
end YM.Further.CurvedGaussianJets
