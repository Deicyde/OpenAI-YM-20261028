import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Coercion
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.PressureC

/-!
# Apply windows in real sectors

No independent table choices. Pre-β θ, an actual room. Gap `CorePrice`
condition price for all Allocations at their posts. Delay positive uniform
for A, Pi, C. Rest of energy/determinant bills still to be requested prior
integ. We keep distance windows from both endpoints of the physical bond.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

namespace Coat
variable (X : Coat T F)
abbrev shutter := Coat.frames G S X.B

def kernelA := X.shutter.pad X.plate

def driftM := -(X.kernelA.transpose *ᵥ X.linearBill)

def μ := erect G X.driftM

def relating := X.shutter.frameMean X.plate

def shreds := X.shutter.flawed X.plate

lemma stays (v : Target c f G) (p : Tubular f G) (hp : ¬ X.Hot p.1)
    (hf : P.Funds S T) : X.form v p=0 := by
  obtain ⟨Y,W,H,-⟩ := hf.feeds; exact X.cold p hp H v

lemma no_b (p : Tubular f G) (hp : ¬ X.Hot p.1) (hf : P.Funds S T) : X.linearBill p=0 := by
  unfold linearBill; simp [Matrix.mulVec,dotProduct, X.stays _ p hp hf]

section cold
variable {m : ℕ} {η r Q : ℝ} (ha : Allow X.plate (along S) m η r Q) (hf : P.Funds S T)
include ha hf
lemma cold_pad (i j : Tubular f G) (h : (¬ X.Hot i.1) ∨ (¬X.Hot j.1)) :
    X.kernelA i j=(1:Matrix ..) i j := by
  obtain ⟨Y,W,H,-⟩ := hf.feeds
  by_cases he : i∈X.shutter.take j
  swap
  · have hi : i≠j := fun hi => he (hi.symm ▸ X.shutter.here i)
    rw [kernelA,X.shutter.outside X.plate i j he]; simp [hi]
  let e : ↥(X.shutter.take j) ↪ Tubular f G := Embedding.subtype _
  let A := X.shutter.principal X.plate j
  have hz : ∀ x : ↥(X.shutter.take j), ¬ X.Hot (e x).1 → ∀ u : ↥(X.shutter.take j), A⁻¹ x u=(1:Matrix ..) x u := by
    intro x hn u
    have he' : A x = (1:Matrix ..) x := funext fun y => by
      change X.plate (e x) (e y)=(1:Matrix ..) _ _; rw [X.asleep (e x) hn H _]
      simp [Matrix.one_apply,e.injective.eq_iff]
    have ht : A*A⁻¹=1 := (ha.sub e).initial.1
    have hg : (A*A⁻¹) x u=((1:Matrix (↥(X.shutter.take j)) (↥(X.shutter.take j)) ℝ)*A⁻¹) x u := by rw [Matrix.mul_apply,Matrix.mul_apply]; simp_rw [he']
    rw [ht,one_mul] at hg; exact hg.symm
  let u : ↥(X.shutter.take j) := ⟨i,he⟩; let v : ↥(X.shutter.take j) := ⟨j,X.shutter.here j⟩
  change X.shutter.pad X.plate u.val j=_
  rw [X.shutter.inside]; change A⁻¹ u v=(1:Matrix ..) (e u) (e v)
  rcases h with h|h
  · rw [hz u h]; simp [Matrix.one_apply,e.injective.eq_iff]
  have hv : IsHermitian A⁻¹ := (ha.sub e).symmetry.inv
  rw [show A⁻¹ u v=A⁻¹ v u from by conv_lhs => rw [← hv.eq]; rw [conjTranspose_apply,star_trivial], hz v h]
  by_cases h : u=v
  · rw [h]; simp
  simp [Ne.symm h,e.injective.ne h]
lemma uniform (i j : Tubular f G) (h : ¬ X.Hot i.1) : X.relating i j=(1:Matrix ..) i j := by
  unfold relating frameMean
  have hp := X.cold_pad ha hf i j (Or.inl h); have hh := X.cold_pad ha hf j i (Or.inr h)
  rw [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply]
  change _ • (X.kernelA i j+X.kernelA j i) = _
  rw [hp,hh, show (1:Matrix _ _ ℝ) j i=(1:Matrix ..) i j from by simp [Matrix.one_apply,eq_comm]]; simp only [smul_eq_mul]; ring
lemma not_e (i : Tubular f G) (h : ¬ X.Hot i.1) : X.driftM i=0 := by
  unfold driftM; rw [Pi.neg_apply,neg_eq_zero]
  simp [Matrix.mulVec,dotProduct,fun j => X.cold_pad ha hf j i (Or.inr h), Matrix.one_apply, X.no_b i h hf]
lemma μ_sleep (i : Bond f) (h : ¬ X.Hot i) : X.μ i=0 := by
  ext x; exact X.not_e ha hf (i,x) h
end cold
end Coat

open Coat

structure Torch (η r Q : ℝ) : Prop where
  hot : 0 < η
  spans : 0 < r
  hQ : 1 ≤ Q
  hv : r ≤ 1

namespace Torch
variable {η r Q : ℝ}
lemma prices (h : Torch η r Q) : 0 < retain η r Q :=
  div_pos (mul_pos (lt_min zero_lt_one (div_pos (half_pos h.spans) (zero_lt_one.trans_le h.hQ))) h.hot) (by norm_num)

/-- Any power for the gap. Post-L. -/
lemma physical (h : Torch η r Q) (G : Gauge) (L : Side) (k : ℝ) (m : ℕ) : Rate G L k (fun x => scraps η r Q m (radiusB x)) := by
  refine Rate.mul_right (show Rate G L k _ from ?_) _
  let e := retain η r Q
  refine (Rate.cutoff h.prices).compare (Eventually.of_forall ?_); intro x; simp only [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_monotone; apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr h.prices.le)
  exact_mod_cast (show Pressure.Stores.till x ≤ radiusB x by unfold Pressure.Stores.till; omega)
end Torch

/-- At one torus coat. No assumption of reassembly. Attach charges to all
real data. Remember sweeps/glides still need their footprints. -/
structure Rotator (P : Teller G) (L : Side) (η r Q Y : ℝ) (X : Coat T F) : Prop where
  full : Torch η r Q
  scale : Allow X.plate (Census.along S) (Census.tubularPrice G L) η r Q
  matrix : Control.Price (Census.aim S) (Census.along S) X.form η Y
  signs : 0<Y
  room : Room P S T X.x
  cap : Window.distPay η r Q (Census.tubularPrice G L) X.B ≤ Q⁻¹/2
  fullC : Matrix.PosDef X.relating

lemma shoots (P : Teller G) (L : Side) (D : Patch) (hd : D.Branches P.bind G) :
    ∃ η r Q Y, Torch η r Q ∧ ∀ᶠ x in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S)
      (F : Forest S.ratio) (X : Coat T F), X.x=x → S.patch=D → S.patch.L=L → Room P S T x → X.manifest →
        Rotator P L η r Q Y X := by
  obtain ⟨Y,hY,h⟩ := Coat.charges P L D hd
  obtain ⟨k,hk,H⟩ := Coat.energized P L D hd
  let r := min k 1; let η := P.top.width/2; let Q := Y*Y+1
  let m := Census.tubularPrice G L
  have ht : Torch η r Q := ⟨half_pos P.top.width_pos,lt_min hk zero_lt_one,by unfold Q; nlinarith, min_le_right ..⟩
  have hQ : 0 < Q⁻¹/2 := half_pos (inv_pos.mpr (zero_lt_one.trans_le ht.hQ))
  refine ⟨η,r,Q,Y,ht,?_⟩
  filter_upwards [H,((ht.physical G L (-1) m).mul_left (payE η r Q m)).below (by norm_num) _ hQ]
    with x he hp c f S T F X hX hS hL hR hM
  subst x
  obtain ⟨ha,hb⟩ := h c f S T F X hS hL hR η ht.hot.le le_rfl
  have hh : Allow X.plate (Census.along S) m η r Q :=
    { census := by unfold m; rw [← hL]; exact Census.entering S
      symmetry := X.balanced
      eta := ht.hot
      down := ht.spans
      fuel := zero_lt_one.trans_le ht.hQ
      price := hb
      ground := fun v => (mul_le_mul_of_nonneg_right (min_le_left ..) (nn v)).trans
        (he c f S T F X rfl hS hL hR hM v) }
  have hv := (le_abs_self _).trans hp
  exact ⟨ht,hh,ha,hY,hR,hv,Control.definite (Window.twin ..) (hh.ground_C X.shutter hv) hQ⟩
end YM.ConnectedActivityE6
