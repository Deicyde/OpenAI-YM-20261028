import YM.Further.GAUSSIAN_SCALAR_LEDGER.Windows
import YM.SectorNext.VACUUM_NORMALIZATION.Panel

set_option warningAsError false

/-!
# **Earn** row rates on Πu, Eu and S; choose prices before period

Real windows.  value inequalities; quantitative fixed-L constants
as functions ONLY of this uniform input price, multiplicity and width,
on any Side, forest etc via center-point location. `field` is the
SYMMETRIC part of the parametrix at u=0; its correction and window
residual need not be symmetric.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Further.GaussianScalar

open Matrix Function Filter Precision SectorNext.Vacuum Lattice
open Round (rowRate)
open YM.Progress.StationaryScenes.Green
open YM.Push.Uniform (Multiplicity countCost count_pos)
open scoped Topology BigOperators Matrix.Norms.Frobenius

structure Expense where
  η : ℝ -- absolute row envelope exponent on A
  low : ℝ -- least eigen
  high : ℝ -- row/column bound on A
  counts : ℕ
  η_pos : 0 < η
  low_pos : 0 < low
  high_pos : 0 < high
namespace Expense
variable (p : Expense)

def slope := min 1 ((p.low/2)/p.high)
def sky := p.slope * p.η
def halfRate := p.sky / 2
def margin := p.halfRate / 2

def fare := min 1 (p.low/2)

lemma tilt_pos : 0 < p.slope* p.η := by
  have h := p.η_pos; have ht := p.low_pos; have hh := p.high_pos
  unfold slope; positivity
lemma sky_le : p.sky ≤ p.η := mul_le_of_le_one_left p.η_pos.le (min_le_left ..)
lemma margin_pos : 0 < p.margin := half_pos (half_pos p.tilt_pos)
lemma fare_pos : 0 < p.fare := lt_min zero_lt_one (half_pos p.low_pos)
lemma tilted : p.slope*p.high ≤ p.low/2 := (le_div_iff₀ p.high_pos).mp (min_le_right ..)

def payment : ℝ := 1+p.fare⁻¹*(p.counts*countCost (p.sky-p.halfRate))
def windowCost (r : ℝ) := Real.exp (-p.margin*r)*p.high*p.payment

def drift (r : ℝ) := p.payment*p.windowCost r
def correctionCost (r : ℝ) := p.high*p.drift r

lemma payment_pos : 0 < p.payment := by
  have hw := count_pos (sub_pos.mpr (half_lt_self (show 0<p.sky from p.tilt_pos)))
  have hh := p.fare_pos; unfold payment halfRate; positivity
lemma window_pos (r : ℝ) : 0 < p.windowCost r :=
  mul_pos (mul_pos (Real.exp_pos _) p.high_pos) p.payment_pos
lemma drift_pos (r : ℝ) : 0 < p.drift r := mul_pos p.payment_pos (p.window_pos _)
lemma correction_pos (r : ℝ) : 0 < p.correctionCost r := mul_pos p.high_pos (p.drift_pos _)
lemma pays : Tendsto p.windowCost atTop (nhds 0) := by
  have ht : Tendsto (fun x : ℝ => Real.exp (-p.margin*x)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr p.margin_pos))
  simpa only [zero_mul,windowCost] using! (ht.mul_const p.high).mul_const p.payment
lemma ages : Tendsto p.correctionCost atTop (nhds 0) := by
  simpa only [mul_zero,drift,correctionCost] using! ((p.pays.const_mul p.payment).const_mul p.high)
end Expense

variable {c : Side} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- No rows deleted at window boundaries. Locating fields/seed queries
needed by rows remains separate. -/
structure RawPrice (p : Expense) (y : ι → Site c) (A : Wall ι) : Prop where
  positive : Numeric A p.low p.high
  hermitian : A.IsHermitian
  weighted : Double y p.η p.high A
  crowded : Multiplicity y p.counts
namespace RawPrice

variable (Z : Lens ι) (p : Expense) {y : ι → Site c} {A : Wall ι} (h : RawPrice p y A)
include h

lemma paid : A.PosDef := h.hermitian.posDef_iff_eigenvalues_pos.mpr fun i =>
  p.low_pos.trans_le (Panel.bill_quad h.hermitian h.positive i).1

lemma ambient {u : ℝ} (hu : 0 ≤ u) :
    ∀ i j, wt p.sky (y i) (y j) * |(Lens.full A u) i j| ≤ (p.fare*(1+u))⁻¹ := by
  have hp := pos_of_mul_pos_left p.tilt_pos p.η_pos.le
  have hn : Bottom A p.low := fun v => (h.positive v).1
  exact (inverse p.η_pos.le p.low_pos hp.le (min_le_left ..) p.tilted h.hermitian hn h.weighted u hu).2.2

lemma ready {u : ℝ} (hu : 0 ≤ u) (i j : ι) :
    wt p.sky (y i) (y j) * |Z.visit A u i j| ≤ (p.fare*(1+u))⁻¹ := by
  by_cases hx : i∈ Z.eye j
  · let t : (Z.eye j) ↪ ι := Function.Embedding.subtype _
    have ht : Double (y ∘ t) p.η p.high (A.submatrix t t) :=
      ⟨h.weighted.1.restrict _ _,h.weighted.2.restrict _ _⟩
    have hl := pos_of_mul_pos_left p.tilt_pos p.η_pos.le
    have hn : Bottom A p.low := fun v => (h.positive v).1
    have ha := inverse p.η_pos.le p.low_pos hl.le (min_le_left ..) p.tilted (h.hermitian.submatrix t) (hn.restrict t) ht u hu
    unfold Lens.visit; rw [of_apply,dif_pos hx]
    exact ha.2.2 ⟨i,hx⟩ (Z.center j)
  unfold Lens.visit; rw [of_apply,dif_neg hx,abs_zero,mul_zero]; have ht := p.fare_pos; positivity

omit [DecidableEq ι] in
private lemma spends {u : ℝ} (hu : 0 ≤ u) (W : Wall ι)
    (hp : ∀ i j, wt p.sky (y i) (y j) * |W i j| ≤ (p.fare*(1+u))⁻¹) :
    Double y p.halfRate (p.payment/(1+u)) W := by
  apply Double.ease (Double.fromEntries (by have he := p.fare_pos; positivity)
    (half_lt_self p.tilt_pos) h.crowded hp)
  have he := p.fare_pos
  unfold Expense.payment Expense.halfRate
  field_simp; unfold Expense.sky; ring_nf; linarith

lemma lens {u : ℝ} (hu : 0 ≤ u) : Double y p.halfRate (p.payment/(1+u)) (Z.visit A u) :=
  h.spends _ hu _ (h.ready Z p hu)
lemma full {u : ℝ} (hu : 0 ≤ u) : Double y p.halfRate (p.payment/(1+u)) (Lens.full A u) :=
  h.spends _ hu _ (h.ambient p hu)

lemma ticket {u : ℝ} (hu : 0 ≤ u) {r : ℝ} (hr : Z.Outside y r) :
    Double y p.margin (p.windowCost r/(1+u)) (Z.missed A u) := by
  let T := A * Z.visit A u
  have hw : Double y p.halfRate (p.high*(p.payment/(1+u))) T :=
    Double.times (Double.loosen h.weighted (by apply le_trans _ p.sky_le; unfold Expense.halfRate; linarith [show 0<p.sky from p.tilt_pos]))
      (half_pos p.tilt_pos).le p.high_pos.le (by have ht := p.payment_pos; positivity) (h.lens Z p hu)
  let L := Real.exp (-p.margin*r)
  have hs (v : Wall ι) (K : Wall ι) (h : Rows y y K p.halfRate (p.high*(p.payment/(1+u))))
      (ht : ∀ i j, wt p.margin (y i) (y j)*|v i j| ≤ L*(wt p.halfRate (y i) (y j) * |K i j|)) :
      Rows y y v p.margin (p.windowCost r/(1+u)) := by
    intro i; calc
      _ ≤ L * ∑ j, wt p.halfRate (y i) (y j)* |K i j| := by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum fun j _ => ht i j
      _ ≤ L * (p.high*(p.payment/(1+u))) := mul_le_mul_of_nonneg_left (h _) (Real.exp_pos _).le
      _ = _ := by unfold L Expense.windowCost; ring
  let M := Z.missed A u
  have ht (i j : ι) : wt p.margin (y i) (y j)* |M i j| ≤ L*(wt p.halfRate (y i) (y j)*|T i j|) := by
    unfold M
    by_cases he : i∈Z.eye j
    · rw [Z.sight (h.paid p) hu i j he,abs_zero,mul_zero]; unfold L wt; positivity
    rw [Z.lost A u i j he, ←mul_assoc]; apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    unfold wt L; rw [← Real.exp_add]; apply Real.exp_monotone
    have he := mul_le_mul_of_nonneg_left (hr i j he) p.margin_pos.le
    rw [show p.halfRate=2*p.margin by unfold Expense.margin; ring]; linarith
  exact ⟨hs M T hw.1 ht, hs Mᵀ Tᵀ hw.2 fun i j => by
    rw [wt_symm p.margin, wt_symm p.halfRate]; exact ht j i⟩

omit h in
def field (Z : Lens ι) (A : Wall ι) := (1/2:ℝ) • (Z.visit A 0+(Z.visit A 0)ᵀ)
omit h in
def tear (Z : Lens ι) (A : Wall ι) := A * field Z A - 1

omit h [Fintype ι] in
lemma field_transpose (Z : Lens ι) (A : Wall ι) : (field Z A).IsHermitian := by
  unfold field Matrix.IsHermitian; simp [add_comm]

lemma centered_error {r : ℝ} (hr : Z.Outside y r) :
    Double y p.margin (p.drift r) (Z.visit A 0 - A⁻¹) := by
  have hh : Lens.full A 0=A⁻¹ := by simp [Lens.full,Lens.plus]
  have he : Double y p.margin p.payment A⁻¹ := by
    have hk := Double.loosen (h.full p (u:=0) le_rfl) (r:=p.margin) (half_le_self (show 0≤p.halfRate from (half_pos p.tilt_pos).le))
    rwa [hh,add_zero,div_one] at hk
  have hx := Z.rebuilds (h.paid p) (u:=0) le_rfl
  rw [hh] at hx
  have ht := h.ticket Z p (u:=0) le_rfl hr
  rw [add_zero,div_one] at ht
  rw [show Z.visit A 0-A⁻¹ = A⁻¹ * Z.missed A 0 by rw [←hx]; abel]
  exact Double.times he p.margin_pos.le p.payment_pos.le (p.window_pos _).le ht

lemma difference {r : ℝ} (hr : Z.Outside y r) :
    Double y p.margin (p.drift r) (field Z A - A⁻¹) := by
  have hx := h.centered_error Z p hr
  let Δ := Z.visit A 0-A⁻¹
  have hs : Δᵀ=(Z.visit A 0)ᵀ-A⁻¹ := by unfold Δ; rw [transpose_sub]; rw [show A⁻¹ᵀ=A⁻¹ by simpa [Matrix.IsHermitian] using (h.paid p).inv.1]
  have he : field Z A - A⁻¹=(1/2:ℝ) • (Δ+Δᵀ) := by
    unfold field; rw [hs]; unfold Δ; ext i j; simp; ring
  rw [he]
  have hh : Double y p.margin (|(1/2:ℝ)| * (p.drift r+p.drift r)) ((1/2:ℝ) • (Δ+Δᵀ)) :=
    Double.play (Double.add hx ( Double.mirror hx)) _
  rwa [show |(1/2:ℝ)| * (p.drift r+p.drift r) = p.drift r by rw [abs_of_nonneg (by norm_num : 0≤(1/2:ℝ))]; ring] at hh

lemma frays {r : ℝ} (hr : Z.Outside y r) :
    Double y p.margin (p.correctionCost r) (tear Z A) := by
  have hx : Double y p.margin p.high A := Double.loosen h.weighted (le_trans (by
    unfold Expense.margin Expense.halfRate; linarith [show 0<p.sky from p.tilt_pos]) p.sky_le)
  have hl : tear Z A=A*(field Z A-A⁻¹) := by unfold tear; rw [mul_sub, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (h.paid p).det_pos.ne')]
  rw [hl]; exact Double.times hx p.margin_pos.le p.high_pos.le (p.drift_pos _).le (h.difference Z p hr)

end RawPrice
end YM.Further.GaussianScalar
