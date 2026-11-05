import YM.Further.CURVED_GAUSSIAN_JETS.LineLog
/-!
#  determinant & precision expansions with scalar local errors (zero jet)

Ordered matrix products, not spectral notation for non-normal S or E_u.
Price also on absolute chains in both orientations, for future labeling
(before paying any dependence-cover or derivative cost!). All at the common
positive prices of `Fits` and `Includes`. Empty-color (no key) cases ok.
Switch between Panel's genuine line and its window line with an absolutely
summable *integrated* receipt. Including comparison of two DIFFERENT tables
before multiplying or collecting any terms. No abstract infinite-volume
log or dropping small per-site tails in an exact identity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets
open Function Filter MeasureTheory Set Matrix Lattice SectorNext.Vacuum Precision Progress.StationaryScenes
open Green (wt wt_pos)
open Rows (Bill major)
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical
variable {n : Side} {I : Type*} [Fintype I] [DecidableEq I]
def Smooth (M : ℝ → Table I) := ∀ i j, ContinuousOn (fun u => M u i j) (Ioi 0)
omit [Fintype I] [DecidableEq I] in
lemma Smooth.const (A : Table I) : Smooth (fun _ => A) := fun _ _ => continuousOn_const
omit [DecidableEq I] in
lemma Smooth.mul {M N : ℝ → Table I} (hm : Smooth M) (hn : Smooth N) : Smooth (fun u => M u * N u) := by
  intro i j; simp only [Matrix.mul_apply]; exact continuousOn_finsetSum _ fun k _=> (hm i k).mul (hn k j)
lemma Smooth.pow {M : ℝ → Table I} (h : Smooth M) (k : ℕ) : Smooth (fun u=>M u ^ k) := by
  induction k with
  | zero => simp; exact Smooth.const _
  | succ j ih => simpa [pow_succ] using Smooth.mul ih h

namespace Windows
variable (W : Windows I) {A : Table I} {a : I → Site n} {p : Prices} (h : Fits a p A) {N : ℕ} (hW : W.Includes a N)
variable (A) in
def tollLine (L : ℝ) (i : I) := Panel.priceLine (W.localGram A i) L (W.center i)
variable (A) in
def chain (k : ℕ) (u : ℝ) := W.column A u * (-W.defect A u)^k
variable (A) in
def tail (k : ℕ) (i j : I) := ∫ u : ℝ in Ioi 0, W.chain A (k+1) u i j

include h
lemma column_cont : Smooth (W.column A) := by
  intro i j; unfold column; dsimp only [Matrix.of_apply]; split
  · exact Line.inv_cont (W.fitsGram A h j).pos _ _
  exact continuousOn_const
lemma chain_cont (k : ℕ) : Smooth (W.chain A k) := by
  have hm : Smooth (shifted A) := by
    intro i j; unfold shifted; simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]; fun_prop
  have hh := hm.mul (W.column_cont h)
  exact (W.column_cont h).mul (Smooth.pow (M:=fun u => -(W.defect A u)) (fun i j=> ((hh i j).sub continuousOn_const).neg) k)

include hW
lemma full_chain {u : ℝ} (hu : 0≤u) (hN : p.deep N<1) (i j : I) :
    HasSum (fun k => W.chain A (k+1) u i j) (((shifted A u)⁻¹ - W.column A u) i j) := by
  let E := W.defect A u
  have hs := Rows.neumann (W.defect_price h hW u hu) p.speed_pos.le (by have := p.deep_pos N; positivity)
    (by rw [div_lt_one (by positivity)]; linarith) -- entrywise
  have he : 1+E=shifted A u*W.column A u := by unfold E defect; abel
  have hh := hasSum_sum (s:=Finset.univ) (fun l _ => (hs l j).mul_left (W.column A u i l))
  change HasSum (fun k : ℕ => W.chain A k u i j) ((W.column A u * (1+E)⁻¹) i j) at hh
  have hi := (h.shift_pos hu).det_pos
  have hb : (shifted A u)⁻¹ * (1+E) = W.column A u := by rw [he, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hi.ne'),one_mul]
  have hz : ((1+E)⁻¹ * (1+E))=1 := by
    have hw (i j : I) := hasSum_sum (s:=Finset.univ) (fun l _=> (hs i l).mul_right ((-E) l j))
    ext i j
    rw [Matrix.mul_add, mul_one, Matrix.add_apply]
    specialize hw i j
    change HasSum (fun k : ℕ => ((-E)^k * (-E)) i j) (((1+E)⁻¹ * (-E)) i j) at hw
    simp_rw [←pow_succ,Matrix.mul_neg, Matrix.neg_apply] at hw
    have hm := (hasSum_nat_add_iff' 1).mpr (hs i j)
    simp only [Finset.sum_range_one, pow_zero] at hm
    change HasSum _ (((1+E)⁻¹) i j-(1:Table I) i j) at hm
    linarith only [hw.unique hm]
  rw [←hb, Matrix.mul_assoc, mul_eq_one_comm.mp hz,mul_one] at hh
  simpa only [Finset.sum_range_one,Matrix.sub_apply, chain,pow_zero,mul_one] using (hasSum_nat_add_iff' 1).mpr hh

lemma tail_fee (u : ℝ) (hu : 0 ≤ u) (k : ℕ) : Bill a p.speed (W.chain A (k+1) u)
    ((p.reserve * p.deep N ^(k+1))*Line.bell u) ∧ Bill a p.speed (major (W.column A u) * major (W.defect A u)^(k+1))
      ((p.reserve * p.deep N ^(k+1))*Line.bell u) := by
  have hp := Rows.slower (W.column_both h u hu) (h:=p.speed) (by linarith [p.speed_pos])
  have he := W.defect_price h hW u hu
  have hr : 0≤p.reserve/(1+u) := by have := p.reserve_pos; positivity
  have hx : 0≤p.deep N/(1+u) := by have := p.deep_pos N; positivity
  have hE (M E : Table I) (hM : Bill a p.speed M (p.reserve/(1+u))) (hE : Bill a p.speed E (p.deep N/(1+u))) :
      Bill a p.speed (M*E^(k+1)) ((p.reserve*p.deep N^(k+1))*Line.bell u) := by
    apply Rows.bigger (Rows.product p.speed_pos.le hM (Rows.power p.speed_pos.le hE hx (k+1)) hr (pow_nonneg hx _))
    calc
      _ = p.reserve/(1+u) * ((p.deep N/(1+u))^k*(p.deep N/(1+u))) := by rw [pow_succ]
      _ ≤ p.reserve/(1+u) * (p.deep N^k*(p.deep N/(1+u))) := by gcongr; exact div_le_self (p.deep_pos _).le (by linarith only [hu])
      _ = _ := by rw [pow_succ,Line.bell, pow_two, one_div, mul_inv]; ring
  exact ⟨hE _ _ hp (Rows.neg he),hE _ _ (Rows.absolute hp) (Rows.absolute he)⟩

lemma tail_price (hN : p.deep N<1) (i j : I) :
    let L := fun k u => p.reserve * (p.deep N * p.deep N^k) * Line.bell u
    (∀ k (u : ℝ), 0≤u → |W.chain A (k+1) u i j| ≤ L k u) ∧
      ∀ u, HasSum (fun k : ℕ => L k u) (p.reserve*(p.deep N * (1-p.deep N)⁻¹)*Line.bell u) := by
  intro f; exact ⟨fun k u hu => by simpa [pow_succ',f] using Rows.entry p.speed_pos.le (W.tail_fee h hW u hu k).1 i j,fun u =>
    ((((hasSum_geometric_of_lt_one (p.deep_pos _).le hN).mul_left (p.deep N)).mul_left _).mul_right _)⟩

lemma integrated_chain (hN : p.deep N<1) (i j : I) : HasSum (fun k => W.tail A k i j) (∫ u : ℝ in Ioi 0, ((shifted A u)⁻¹ - W.column A u) i j) := by
  obtain ⟨hs,ht⟩ := W.tail_price h hW hN i j
  have he := ae_restrict_mem (μ:=volume (α:=ℝ)) (measurableSet_Ioi (a:=(0:ℝ)))
  apply hasSum_integral_of_dominated_convergence (fun k u => p.reserve*(p.deep N*p.deep N^k) *Line.bell u)
      (fun k=> (W.chain_cont h (k+1) i j).aestronglyMeasurable measurableSet_Ioi)
      (fun k=>he.mono fun x hx=>hs k x (le_of_lt hx)) (he.mono fun u _ => (ht u).summable) _
      (he.mono fun u hu=> W.full_chain h hW (le_of_lt hu) hN i j)
  simp_rw [(ht _).tsum_eq]; exact Line.bell_int.1.const_mul _

lemma line_tables (hN : p.deep N<1) (i : I) : Panel.priceLine A p.mass i = W.tollLine A p.mass i - ∑' k : ℕ, W.tail A k i i := by
  have he : p.gap ≤ p.mass := (Panel.bill_quad h.symm h.numeric i).1.trans (Panel.bill_quad h.symm h.numeric i).2
  let M := W.localGram A i; let t := W.center i; have hm := W.fitsGram A h i
  rw [(W.integrated_chain h hW hN i i).tsum_eq]
  have hs (u : ℝ) : ((shifted A u)⁻¹-W.column A u) i i = Line.dose M t u - Line.dose A i u := by
    unfold Line.dose column resolvent; simp [W.within i, M, t, center]
  simp_rw [hs]; rw [integral_sub (Line.dose_int_aux hm.pos t).1 (Line.dose_int_aux h.pos i).1,
    Line.dose_price h.pos p.gap_pos he h.numeric, Line.dose_price hm.pos p.gap_pos he hm.numeric]; unfold tollLine; ring




end Windows
end YM.Further.CurvedGaussianJets
