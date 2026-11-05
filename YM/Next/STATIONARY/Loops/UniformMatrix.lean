import YM.Next.STATIONARY.Loops.Fourier

set_option autoImplicit false
/-!
# Matrix analytic counting budgets. Plain-space versions (no `[Norm]` instance
on Matrix taken in use). Change of weights at either end via frames later.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate InnerProductSpace
variable {ι α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] {σ A C : ℝ}

def slug (v : Phase α) := ‖(WithLp.toLp 2 v : EuclideanSpace ℂ α)‖
open scoped Matrix.Norms.L2Operator in
def vflux (A : CompM α β) := ‖A‖

lemma slug_nonneg (v : Phase α) : 0≤slug v := norm_nonneg _
lemma slug_sq (v : Phase α) : slug v^2=∑ i,‖v i‖^2 := EuclideanSpace.norm_sq_eq _
lemma slug_star (v : Phase α) : slug (star v)=slug v := (sq_eq_sq₀ (slug_nonneg _) (slug_nonneg _)).1 (by rw [slug_sq,slug_sq]; simp)
lemma slug_zero : slug (0:Phase α)=0 := norm_zero
lemma slug_eq {p : Phase α} : slug p=0 ↔ p=0 := by unfold slug; simp
lemma slug_pos {v : Phase α} (h : v≠0) : 0<slug v := lt_of_le_of_ne (slug_nonneg _) (Ne.symm (slug_eq.not.mpr h))
lemma slug_scale (a : ℂ) (v : Phase α) : slug (a • v)=‖a‖*slug v := by
  unfold slug; rw [WithLp.toLp_smul,norm_smul]
lemma slug_plus (v w : Phase α) : slug (v+w) ≤ slug v+slug w := by unfold slug; rw [WithLp.toLp_add]; exact norm_add_le ..
lemma slug_neg (v : Phase α) : slug (-v)=slug v := by simpa using slug_scale (-1) v
lemma slug_inner (v w : Phase α) : @inner ℂ (EuclideanSpace ℂ α) _ (WithLp.toLp 2 v) (WithLp.toLp 2 w)=dotProduct (star v) w := by
  change ∑ i,@inner ℂ ℂ _ (v i) (w i)=_; unfold dotProduct; apply sum_congr rfl; intro i _; exact mul_comm ..
lemma slug_dot (x y : Phase α) : ‖dotProduct x y‖ ≤ slug x*slug y := by
  have h := norm_inner_le_norm (𝕜:=ℂ) (WithLp.toLp 2 (star x):EuclideanSpace ℂ α) (WithLp.toLp 2 y)
  rw [slug_inner,star_star] at h
  rw [← slug_star x]; exact h
lemma slug_self (x : Phase α) : dotProduct (star x) x=((slug x:ℝ)^2:ℝ) := by rw [← slug_inner,inner_self_eq_norm_sq_to_K]; push_cast; rfl
lemma slug_unit (a : α) : slug (Pi.single a (1:ℂ))=1 := by apply (sq_eq_sq₀ (slug_nonneg _) zero_le_one).1; rw [slug_sq,Finset.sum_eq_single a]; all_goals simp_all [Pi.single_apply]
lemma slug_atom (x : Phase α) (i) : ‖x i‖≤slug x := by
  simpa only [slug_unit,one_mul,single_one_dotProduct] using slug_dot (Pi.single i 1) x
open scoped Matrix.Norms.L2Operator

lemma flux_nonneg (X : CompM α β) : 0 ≤ vflux X := by unfold vflux; exact norm_nonneg _
lemma flux_plus (X Y : CompM α β) : vflux (X+Y)≤ vflux X+vflux Y := by unfold vflux; exact norm_add_le ..
lemma flux_neg (X : CompM α β) : vflux (-X)=vflux X := by unfold vflux; exact norm_neg _
lemma flux_sub (X Y : CompM α β) : vflux (X-Y)≤ vflux X+vflux Y := by rw [sub_eq_add_neg, ← flux_neg Y]; exact flux_plus ..
lemma flux_zero : vflux (0:CompM α β)=0 := by unfold vflux; exact norm_zero
lemma flux_cost (a : ℂ) (X : CompM α β) : vflux (a • X)=‖a‖*vflux X := by
  unfold vflux; exact norm_smul ..
lemma flux_power (X : CompM α β) (Y : CompM β γ) : vflux (X*Y) ≤ vflux X*vflux Y := l2_opNorm_mul ..
lemma flux_test (X : CompM α β) (v : Phase β) : slug (X *ᵥ v) ≤ vflux X * slug v := l2_opNorm_mulVec X (WithLp.toLp 2 v)

lemma flux_take (hp : 0≤A) (X : CompM α β) (h : ∀ i, slug (X *ᵥ i) ≤ A * slug i) : vflux X ≤ A := by
  let L := ((Matrix.toEuclideanLin (𝕜:=ℂ) (m:=α) (n:=β)).trans LinearMap.toContinuousLinearMap) X
  exact ContinuousLinearMap.opNorm_le_bound L hp (fun i => h i.ofLp)

lemma flux_price {X : CompM α β} (hp : 0 ≤ A) (h : ∀ u v, ‖dotProduct u (X *ᵥ v)‖ ≤ A*slug u*slug v) : vflux X≤A := by
  apply flux_take hp _
  intro v
  let u := X *ᵥ v
  rcases eq_or_ne u 0 with he|he
  · rw [show X *ᵥ v=0 from he,slug_zero]; exact mul_nonneg hp (slug_nonneg _)
  have hh := h (star u) v
  change ‖dotProduct (star u) u‖ ≤ _ at hh; rw [slug_self,slug_star] at hh
  simp only [Complex.norm_real,Real.norm_of_nonneg (sq_nonneg (slug u))] at hh
  have hu := slug_pos he; nlinarith

lemma flux_tester {X : CompM α β} (h : vflux X≤A) (v) : slug (X *ᵥ v) ≤ A*slug v := (flux_test ..).trans (mul_le_mul_of_nonneg_right h (slug_nonneg _))
lemma flux_pay (X : CompM α β) (u v) : ‖dotProduct u (X *ᵥ v)‖ ≤ vflux X * slug u * slug v := by
  rw [mul_comm (vflux X),mul_assoc]; exact (slug_dot ..).trans (mul_le_mul_of_nonneg_left (flux_test ..) (slug_nonneg _))
lemma flux_one : vflux (1:CompM α α)≤1 := flux_take zero_le_one _ fun i => by simp
lemma flux_diagonal (x : Phase α) : vflux (Matrix.diagonal x)=‖x‖ := Matrix.l2_opNorm_diagonal x
lemma flux_tilt (X : CompM α β) (i j) : ‖X i j‖ ≤ vflux X := by
  have he := flux_pay X (Pi.single i 1) (Pi.single j 1)
  simpa [slug_unit,single_one_dotProduct,mulVec_single] using he
lemma star_limit (X : CompM α β) : vflux Xᴴ=vflux X := l2_opNorm_conjTranspose X
private lemma flux_back (X : CompM α β) : vflux Xᵀ ≤ vflux X := by
  apply flux_price (flux_nonneg _); intro u v
  rw [dotProduct_mulVec, Matrix.vecMul_transpose,dotProduct_comm]; exact (flux_pay X v u).trans_eq (mul_right_comm ..)
lemma back_flux (X : CompM α β) : vflux Xᵀ=vflux X := le_antisymm (flux_back _) (by simpa using flux_back Xᵀ)
lemma flux_trace (X : CompM α α) : ‖X.trace‖ ≤ (Fintype.card α) * vflux X := by
  calc _ ≤ ∑ i, ‖X i i‖ := norm_sum_le ..
       _ ≤ ∑ _ : α,vflux X := sum_le_sum fun _ _ => flux_tilt ..
       _ = _ := by simp
end YM.Stationary
end

/-!
# Normalized directions in dual-periodic films. Pull the reference gauge
frames at ANY complex momentum. Frames encode one-point positive-quadratic
cost per mode, not necessarily holomorphic itself (alias gauge norms vary
with real part of p). -/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate InnerProductSpace
variable {ι α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] {σ A C : ℝ}

-- normalization works by v=chart(p)*w, charge w.
structure Slab (α : Type) [Fintype α] [DecidableEq α] where
  tile (p : Momentum) : CompM α α
  whole (p) : IsUnit (tile p).det

namespace Slab
def basic (α : Type) [Fintype α] [DecidableEq α] : Slab α where
  tile _ := 1
  whole _ := by simp
def dual (T : Slab α) : Slab α where
  tile p := ((T.tile (-p))ᵀ)⁻¹
  whole p := by rw [Matrix.det_nonsing_inv,det_transpose,Ring.inverse_eq_inv]; exact (T.whole _).inv
lemma tile_dual (P : Slab α) (p) : P.dual.tile (-p) = ((P.tile p)⁻¹)ᵀ := by rw [transpose_nonsing_inv]; simp [dual]
lemma inverse_dual (P : Slab α) (p) : (P.dual.tile p)⁻¹=(P.tile (-p))ᵀ := by simp [dual,nonsing_inv_nonsing_inv _ (show IsUnit ((tile P (-p))ᵀ).det by rw [det_transpose]; exact P.whole _)]
lemma retro (P : Slab α) : P.dual.dual=P := by
  cases P with | mk A B =>
  unfold dual; congr 1; funext p; dsimp; rw [transpose_nonsing_inv, transpose_transpose, neg_neg]; exact nonsing_inv_nonsing_inv _ (B p)
end Slab

variable (X : Slab α) (Y : Slab β) (Z : Slab γ)

def carryM (p q : Momentum) (V : CompM α β) := (X.tile p)⁻¹ *V * Y.tile q
def serial (p q : Momentum) (V : CompM α β) (C : ℝ) := vflux (carryM X Y p q V)≤C

variable {p q r : Momentum}
lemma carryM_join (U : CompM α β) (V : CompM β γ) : carryM X Z p q (U*V)=carryM X Y p r U * carryM Y Z r q V := by unfold carryM; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (Y.tile _),mul_nonsing_inv (Y.tile _) (Y.whole _),Matrix.one_mul]
lemma carryM_back (p q : Momentum) (V : CompM α β) : carryM Y.dual X.dual (-q) (-p) Vᵀ=(carryM X Y p q V)ᵀ := by
  unfold carryM; rw [transpose_mul,transpose_mul,X.tile_dual,Y.inverse_dual,neg_neg,Matrix.mul_assoc]
lemma carryM_back' (U : CompM α α) (p q) (Y : Slab α) : carryM Y X q p U⁻¹=(carryM X Y p q U)⁻¹ := by
  unfold carryM; rw [Matrix.mul_inv_rev _,Matrix.mul_inv_rev _, Matrix.nonsing_inv_nonsing_inv (X.tile _) (X.whole _), ← Matrix.mul_assoc]
lemma carryM_unit {p} : carryM X X p p 1=1 := by unfold carryM; rw [mul_one,nonsing_inv_mul _ (X.whole _)]
lemma carryM_solid {P Q : Slab α} (V : CompM α α) {p q} : IsUnit (carryM P Q p q V).det ↔ IsUnit V.det := by
  unfold carryM; rw [det_mul, det_mul]
  have h : IsUnit ((P.tile p)⁻¹).det := by rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv]; exact (P.whole _).inv
  simp only [IsUnit.mul_iff,Q.whole q, h, and_true,true_and]
lemma carryM_add (p q : Momentum) (U V : CompM α β) : carryM X Y p q (U+V) = carryM X Y p q U+carryM X Y p q V := by simp [carryM,Matrix.mul_add,Matrix.add_mul]
lemma carryM_sub (p q : Momentum) (U V : CompM α β) : carryM X Y p q (U-V) = carryM X Y p q U-carryM X Y p q V := by simp [carryM,Matrix.mul_sub,Matrix.sub_mul]
lemma carryM_neg (p q : Momentum) (V : CompM α β) : carryM X Y p q (-V) = - carryM X Y p q V := by simp [carryM,Matrix.mul_neg,Matrix.neg_mul]
lemma carryM_trace (p) (V : CompM α α) : V.trace=(carryM X X p p V).trace := by unfold carryM; rw [trace_mul_comm, ← mul_assoc, Matrix.mul_nonsing_inv _ (X.whole _),one_mul]

namespace serial
variable {X Y Z} {U V : CompM α β}
lemma fence (h : serial X Y p q U C) : 0≤C := (flux_nonneg _).trans h
lemma mono (h : serial X Y p q U A) (hp : A≤C) : serial X Y p q U C := LE.le.trans h hp
lemma bond {W : CompM β γ} (h : serial X Y p q U A) (hp : serial Y Z q r W C) : serial X Z p r (U*W) (A*C) := by
  unfold serial; rw [carryM_join _ Y (r:=q)]; exact (flux_power ..).trans (mul_le_mul h hp (flux_nonneg _) h.fence)
lemma plus (h : serial X Y p q U A) (hp : serial X Y p q V C) : serial X Y p q (U+V) (A+C) := by unfold serial; rw [carryM_add]; exact (flux_plus ..).trans (add_le_add h hp)
lemma sub (h : serial X Y p q U A) (hp : serial X Y p q V C) : serial X Y p q (U-V) (A+C) := by unfold serial; rw [carryM_sub]; exact (flux_sub ..).trans (add_le_add h hp)
lemma neg (h : serial X Y p q U C) : serial X Y p q (-U) C := by unfold serial; rw [carryM_neg,flux_neg]; exact h
lemma costs (h : serial X Y p q V C) (a : ℂ) : serial X Y p q (a • V) (‖a‖*C) := by
  unfold serial carryM; rw [Matrix.mul_smul,Matrix.smul_mul,flux_cost]; exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
lemma slide (h : serial X Y p q U C) : serial Y.dual X.dual (-q) (-p) Uᵀ C := by unfold serial; rw [carryM_back,back_flux]; exact h
lemma flat : serial X Y p q 0 0 := by simp [serial,carryM, Matrix.mul_zero,Matrix.zero_mul,flux_zero]
lemma free : serial X X p p 1 1 := by rw [serial,carryM_unit]; exact flux_one
lemma paid {U : CompM α α} (h : serial X X p p U C) : ‖U.trace‖ ≤ (Fintype.card α:ℝ)*C := by
  rw [carryM_trace X p U]; exact (flux_trace ..).trans (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))
end serial
end YM.Stationary
end

/-!
# Trace bills are not operator norm. Useful dual payer for `back` by difference & trip. -/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {ι α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] {σ A C : ℝ}

-- counting ideal
structure Doubly (U : CompM α β) (C : ℝ) : Prop where
  credit : 0 ≤ C
  cash (V : CompM β α) : ‖(U*V).trace‖ ≤ C*vflux V
namespace Doubly
variable {U V : CompM α β}
lemma credit2 (h : Doubly U A) (hk : A≤C) : Doubly U C := ⟨h.credit.trans hk,fun W => (h.cash W).trans (mul_le_mul_of_nonneg_right hk (flux_nonneg _))⟩
lemma duet (h : Doubly U A) (he : Doubly V C) : Doubly (U+V) (A+C) := by
  refine ⟨add_nonneg h.credit he.credit,fun W => ?_⟩
  rw [add_mul,Matrix.add_mul,trace_add]; exact (norm_add_le ..).trans (add_le_add (h.cash W) (he.cash W))
lemma duet_neg (h : Doubly U C) : Doubly (-U) C := ⟨h.credit, fun V => by rw [Matrix.neg_mul,trace_neg,norm_neg]; exact h.cash V⟩
lemma solo (x : ℂ) (h : Doubly U C) : Doubly (x • U) (‖x‖*C) := ⟨mul_nonneg (norm_nonneg _) h.credit,fun V => by rw [Matrix.smul_mul,trace_smul,norm_smul, mul_assoc]; exact mul_le_mul_of_nonneg_left (h.cash V) (norm_nonneg _)⟩
lemma zero (h : 0≤C) : Doubly (0:CompM α β) C := ⟨h,fun V => by simp [Matrix.zero_mul,mul_nonneg h (flux_nonneg V)]⟩
lemma duo (h : Doubly U A) {V : CompM β γ} (hp : vflux V≤C) : Doubly (U*V) (A*C) := by
  refine ⟨mul_nonneg h.credit ((flux_nonneg _).trans hp),fun W => ?_⟩
  rw [Matrix.mul_assoc,mul_assoc]; exact (h.cash _).trans (mul_le_mul_of_nonneg_left ((flux_power ..).trans (mul_le_mul_of_nonneg_right hp (flux_nonneg _))) h.credit)
lemma duet_top (h : Doubly U A) {V : CompM γ α} (hp : vflux V ≤ C) : Doubly (V*U) (C*A) := by
  refine ⟨mul_nonneg ((flux_nonneg _).trans hp) h.credit, fun W => ?_⟩
  rw [Matrix.mul_assoc,trace_mul_comm V, Matrix.mul_assoc, mul_comm C, mul_assoc, mul_comm C]; exact (h.cash _).trans (mul_le_mul_of_nonneg_left ((flux_power ..).trans (mul_le_mul_of_nonneg_left hp (flux_nonneg _))) h.credit)
lemma transpose (h : Doubly U C) : Doubly Uᵀ C := by
  refine ⟨h.credit,fun V => ?_⟩
  rw [← Matrix.trace_transpose, transpose_mul, transpose_transpose, trace_mul_comm, ← back_flux V]; exact h.cash _
lemma grouped (h : vflux U≤A) : Doubly U ((Fintype.card α:ℝ)*A) := by
  refine ⟨mul_nonneg (Nat.cast_nonneg _) ((flux_nonneg _).trans h),fun V => (flux_trace ..).trans ?_⟩
  rw [mul_assoc]; exact mul_le_mul_of_nonneg_left ((flux_power ..).trans (mul_le_mul_of_nonneg_right h (flux_nonneg _))) (Nat.cast_nonneg _)
lemma diagram (x : Phase α) : Doubly (diagonal x) (∑ i,‖x i‖) := by
  refine ⟨Finset.sum_nonneg (fun _ _ => norm_nonneg _),fun V => ?_⟩
  change ‖∑ i,(Matrix.diagonal x * V) i i‖≤_; rw [Finset.sum_mul]
  apply (norm_sum_le ..).trans; apply sum_le_sum; intro i _; rw [Matrix.diagonal_mul, norm_mul]; exact mul_le_mul_of_nonneg_left (flux_tilt ..) (norm_nonneg _)
lemma budget {U : CompM α α} (h : Doubly U A) : ‖U.trace‖≤A := by
  have hv := (h.cash 1).trans (mul_le_mul_of_nonneg_left flux_one h.credit)
  simpa only [Matrix.mul_one, mul_one] using hv
end Doubly

def bags (X : Slab α) (Y : Slab β) (p q : Momentum) (U : CompM α β) (C : ℝ) := Doubly (carryM X Y p q U) C
namespace bags
variable {p q r : Momentum} {X : Slab α} {Y : Slab β} {Z : Slab γ} {U V : CompM α β}
lemma credit (h : bags X Y p q U C) : 0≤C := Doubly.credit h
lemma mono (h : bags X Y p q U A) (hp : A ≤ C) : bags X Y p q U C := Doubly.credit2 h hp
lemma pay (h : bags X Y p q U A) {V : CompM β γ} (hp : serial Y Z q r V C) : bags X Z p r (U*V) (A*C) := by unfold bags; rw [carryM_join _ Y (r:=q)]; exact Doubly.duo h hp
lemma taken (h : bags X Y p q U A) {V : CompM γ α} (hp : serial Z X r p V C) : bags Z Y r q (V*U) (C*A) := by unfold bags; rw [carryM_join _ X (r:=p)]; exact Doubly.duet_top h hp
lemma plus (h : bags X Y p q U A) (he : bags X Y p q V C) : bags X Y p q (U+V) (A+C) := by unfold bags; rw [carryM_add]; exact Doubly.duet h he
lemma sale (h : bags X Y p q U A) : bags X Y p q (-U) A := by unfold bags; rw [carryM_neg]; exact Doubly.duet_neg h
lemma sub (h : bags X Y p q U A) (he : bags X Y p q V C) : bags X Y p q (U-V) (A+C) := by rw [sub_eq_add_neg]; exact h.plus he.sale
lemma billed (h : bags X Y p q U C) (a : ℂ) : bags X Y p q (a • U) (‖a‖*C) := by unfold bags carryM; rw [Matrix.mul_smul,Matrix.smul_mul]; exact Doubly.solo a h
lemma slide (h : bags X Y p q U C) : bags Y.dual X.dual (-q) (-p) Uᵀ C := by unfold bags; rw [carryM_back]; exact Doubly.transpose h
lemma envelope {U : CompM α α} (h : bags X X p p U C) : ‖U.trace‖≤C := by rw [carryM_trace X p U]; exact Doubly.budget h
lemma zero (h : 0≤C) : bags X Y p q 0 C := by unfold bags carryM; rw [Matrix.mul_zero, Matrix.zero_mul]; exact Doubly.zero h
lemma crew (h : serial X Y p q U C) : bags X Y p q U ((Fintype.card α:ℝ)*C) := Doubly.grouped h

end bags
end YM.Stationary
end

/-!
# Press uniform tilt / jet bills and their algebra
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset
open scoped Matrix Topology ContDiff BigOperators
variable {ι α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] {σ η A B C D : ℝ} {p q r : Momentum}

structure Charges (X : Slab α) (Y : Slab β) (F : Film ι α β) (σ C : ℝ) : Prop where
  covered : Play F σ
  base {p : Momentum} : p∈strip σ → serial X Y p p (F.tab p) C
  detail (i) {p q : Momentum} : Avenue σ p q → serial X Y (q+p) q (F.spot i p q) C
  stamp (i j) {p q r : Momentum} : Boulevard σ p q r → serial X Y (r+(p+q)) r (F.arch i j p q r) C
-- prove base credits via hσ. Composition accum.

namespace Charges
variable {X : Slab α} {Y : Slab β} {Z : Slab γ} {F G : Film ι α β}

lemma funds (h : Charges X Y F σ C) (hp : 0<σ) : 0≤C := (h.base (p:=0) (Work.F07.realStrip σ hp (by simp))).fence
lemma mono (h : Charges X Y F σ A) (hp : η≤σ) (he : A≤C) : Charges X Y F η C :=
    ⟨h.covered.mono hp, fun w => (h.base (fun j => (w j).trans_le hp)).mono he,
      fun i _ _ w => (h.detail i (w.part hp)).mono he, fun i j _ _ _ w => (h.stamp i j (w.costs hp)).mono he⟩
lemma current {K : Momentum → CompM α β} (hk : Poster σ K) (H : 0≤C) (h : ∀ p ∈ strip σ, serial X Y p p (K p) C) : Charges X Y (Film.cardF (ι:=ι) K) σ C :=
    ⟨Play.current hk, fun w => h _ w, fun i _ _ w => serial.flat.mono H, fun i j _ _ _ w => serial.flat.mono H⟩
lemma weight (h : Charges X Y F σ C) (c : ℂ) : Charges X Y (F.weight c) σ (‖c‖*C) :=
    ⟨h.covered.weight c,fun w => (h.base w).costs c, fun i _ _ w => (h.detail i w).costs c, fun i j _ _ _ w => (h.stamp i j w).costs c⟩
lemma plus (h : Charges X Y F σ A) (he : Charges X Y G σ C) : Charges X Y (F.plus G) σ (A+C) :=
    ⟨h.covered.plus he.covered, fun w => (h.base w).plus (he.base w), fun i _ _ w => (h.detail i w).plus (he.detail i w),fun i j _ _ _ w => (h.stamp i j w).plus (he.stamp i j w)⟩
lemma rear (h : Charges X Y F σ C) : Charges Y.dual X.dual F.rear σ C := by
  refine ⟨h.covered.rear, fun w => ?_,fun i p q w => ?_,fun i j p q r w => ?_⟩
  · simpa only [neg_neg,Film.rear] using (h.base (negResident w)).slide
  · have he := (h.detail i w.late).slide; rw [neg_neg,show -(-(q+p)+p)=q by abel] at he; exact he
  have hp := (h.stamp i j w.ebb).slide; rw [neg_neg,show -(-(r+(p+q))+(p+q))=r by abel] at hp; exact hp
lemma pay (h : Charges X Y F σ A) {G : Film ι β γ} (hp : Charges Y Z G σ C) (hσ : 0<σ) : Charges X Z (F.pay G) σ (4*A*C) := by
  have ha := h.funds hσ
  have he := hp.funds hσ
  refine ⟨h.covered.pay hp.covered,fun w => ((h.base w).bond (hp.base w)).mono (by nlinarith), fun i p q w => ?_,fun i j p q r w => ?_⟩
  · exact (((h.detail i w).bond (hp.base w.basic)).plus ((h.base w.added).bond (hp.detail i w))).mono (by nlinarith)
  have h1 := (h.detail j w.roads).bond (hp.detail i w.oneWay)
  have h2 := (h.detail i w.proceed).bond (hp.detail j w.second)
  rw [add_assoc] at h1; rw [add_right_comm,add_assoc] at h2
  exact (((((h.stamp i j w).bond (hp.base w.oneWay.basic)).plus h1).plus h2).plus ((h.base w.total).bond (hp.stamp i j w))).mono (by linarith)
end Charges

structure Freezer (X Y : Slab α) (K : Momentum → CompM α α) (σ C : ℝ) : Prop where
  period : ∀ p∈ strip σ, IsUnit (K p).det
  price : ∀ p∈ strip σ, serial Y X p p (K p)⁻¹ C

namespace Freezer
variable {X Y : Slab α} {F : Film ι α α}
lemma mono {K : Momentum→CompM α α} (h : Freezer X Y K σ A) (hp : η≤σ) (he : A≤C) : Freezer X Y K η C :=
    ⟨fun p w => h.period p (fun i => (w i).trans_le hp), fun p w => (h.price p (fun i => (w i).trans_le hp)).mono he⟩
lemma back (h : Charges X Y F σ A) (hp : Freezer X Y F.tab σ C) (hσ : 0<σ) :
    Charges Y X F.back σ (C+C*A*C+(C*A*C*A+C*A*C*A+C*A)*C) := by
  have he : ∀ p∈ strip σ, serial Y X p p (F.coupon p) C := hp.price
  have hu := h.funds hσ
  have hv := serial.fence (he (0:Momentum) (Work.F07.realStrip _ hσ (by simp)))
  have hx := mul_nonneg hv hu
  have hl := mul_nonneg hx hv; have hi := mul_nonneg hl hu
  have hw := mul_nonneg (add_nonneg (add_nonneg hi hi) hx) hv
  have hh i {p q} (w : Avenue σ p q) : serial Y X (q+p) q (F.vSpot i p q) (C*A*C) := (((he _ w.added).bond (h.detail i w)).bond (he _ w.basic)).neg
  refine ⟨h.covered.back hp.period,fun w => (hp.price _ w).mono (by linarith), fun i p q w => (hh i w).mono (by linarith),fun i j p q r w=> ?_⟩
  have h1 := (hh j w.roads).bond (h.detail i w.oneWay)
  have h2 := (hh i w.proceed).bond (h.detail j w.second)
  rw [add_assoc] at h1; rw [add_right_comm,add_assoc] at h2
  exact (serial.neg ((((h1.plus h2).plus ((he _ w.total).bond (h.stamp i j w))).bond (he _ w.oneWay.basic)))).mono (by linarith)

lemma figure (h : Charges X Y F σ A) (hp : Freezer X Y F.tab σ C) (hs : 0<σ) (i j) :
    Firm (σ/2) ((Fintype.card α:ℝ)*(C*A+C*A*C*A)) (starTrack (F.figure i j)) := by
  have he : ∀ p∈ strip σ, serial Y X p p (F.coupon p) C := hp.price
  refine highlights (h.covered.estate hs hp.period i j) (by positivity) fun p hx q hz => ?_
  have H {p q r : Momentum} (w : Boulevard σ p q r) : serial Y Y (r+(p+q)) r (F.framePay i j p q r) (C*A+C*A*C*A) := by
    have hu := h.detail i w.proceed; rw [add_right_comm,add_assoc] at hu
    exact ((he _ w.total).bond (h.stamp i j w)).sub ((((he _ w.total).bond hu).bond (he _ w.second.added)).bond (h.detail j w.second))
  have he := H (duo _ _ hs hx hz); rw [neg_add_cancel,add_zero] at he; exact he.paid
end Freezer
end YM.Stationary
end

/-!
# Two trace-log models. SUP right-charge on one inserted l1-column
factor; no trace leading in L^4 because a `bags` input is spent each time.
Endpoint weights arbitrary. Uses a finite number of insertions, tolerance
A,P pre-L usable with different F/G by taking max. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset
open scoped Matrix Topology ContDiff BigOperators
variable {ι α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] {σ η A B C D E : ℝ}

namespace bags
variable {X : Slab α} {Y : Slab β} {Z : Slab γ} {U U' : CompM α β} {V V' : CompM β γ}
lemma gap {p q r} (h : bags X Y p q (U-U') A) (hp : serial X Y p q U' B) (hv : serial Y Z q r V C) (he : bags Y Z q r (V-V') D) :
    bags X Z p r (U*V-U'*V') (A*C+B*D) := by
  have hz := (h.pay hv).plus (he.taken hp)
  simpa only [Matrix.sub_mul,Matrix.mul_sub, sub_add_sub_cancel] using hz
lemma wallet {X Z : Slab α} {U V : CompM α α} (hu : IsUnit U.det) (hv : IsUnit V.det) {p q}
    (hp : bags X Z p q (U-V) C) (he : serial Z X q p U⁻¹ B) (hr : serial Z X q p V⁻¹ D) : bags Z X q p (U⁻¹-V⁻¹) (B*C*D) := by
  rw [show U⁻¹-V⁻¹= -(U⁻¹*(U-V)*V⁻¹) by rw [Matrix.mul_sub,Matrix.nonsing_inv_mul U hu,Matrix.sub_mul,one_mul,Matrix.mul_assoc,Matrix.mul_nonsing_inv V hv,mul_one,neg_sub]]
  exact ((hp.taken he).pay hr).sale
lemma compose {p q} {U V M N : CompM α β} (h : bags X Y p q (U-V) C) (hp : bags X Y p q (M-N) D) :
    bags X Y p q ((U-M)-(V-N)) (C+D) := by rw [show U-M-(V-N)=U-V-(M-N) by abel]; exact h.sub hp
end bags

/-! `Small` ONLY DIFFERENCE. det/precision matrices also have Charges.
Full trace may need second budget ~L^4. -/
structure Ledger (X : Slab α) (Y : Slab β) (F : Film ι α β) (σ C : ℝ) : Prop where
  charge {p} (w : p∈strip σ) : bags X Y p p (F.tab p) C
  feat (i) {p q} (w : Avenue σ p q) : bags X Y (q+p) q (F.spot i p q) C
  dues (i j) {p q r} (w : Boulevard σ p q r) : bags X Y (r+(p+q)) r (F.arch i j p q r) C

def outstanding (F G : Film ι α β) := F.plus (G.weight (-1))
lemma ledger_cmp {X Y : Slab α} {F G : Film ι α α} (h : Charges X Y F σ A) (hp : Charges X Y G σ A) (he : Freezer X Y F.tab σ C) (hr : Freezer X Y G.tab σ C) (hs : 0<σ)
    (hv : Ledger X Y (outstanding F G) σ B) (i j) :
    let D := C*B*C
    let E := D*A+C*B
    Firm (σ/2) (E+((E*C+C*A*D)*A + C*A*C*B)) (starTrack fun p q => F.figure i j p q-G.figure i j p q) := by
  intro D E
  have hx := h.covered.estate hs he.period i j; have hy := hp.covered.estate hs hr.period i j
  refine highlights ⟨fun w v => (hx.eligible w v).sub (hy.eligible w v),fun ha hc w v => congr_arg₂ (·-·) (hx.rolls ha hc w v) (hy.rolls ha hc w v)⟩ (by positivity) fun p hw q hK => ?_
  have HM {p : Momentum} (w : p∈ strip σ) : bags Y X p p (F.coupon p-G.coupon p) D := by
    refine bags.wallet (he.period _ w) (hr.period _ w) ?_ (he.price _ w) (hr.price _ w)
    simpa [outstanding,Film.plus,Film.weight, sub_eq_add_neg] using hv.charge w
  have H {p q r : Momentum} (w : Boulevard σ p q r) : bags Y Y (r+(p+q)) r (F.framePay i j p q r - G.framePay i j p q r) (E+((E*C+C*A*D)*A + C*A*C*B)) := by
    have hs : serial Y X (r+(p+q)) (r+(p+q)) (G.coupon _) C := hr.price _ w.total
    have hx := hp.detail i w.proceed
    have hF := h.detail i w.proceed
    have hb : bags X Y (r+(p+q)) r (F.arch i j p q r-G.arch i j p q r) B := by simpa [outstanding,Film.plus,Film.weight,sub_eq_add_neg] using hv.dues i j w
    refine bags.compose (bags.gap (HM w.total) hs (h.stamp i j w) hb) ?_
    have hL : bags X Y (r+q+p) (r+q) (F.spot i p (r+q)-G.spot i p (r+q)) B := by simpa [outstanding,Film.plus,Film.weight,sub_eq_add_neg] using hv.feat i w.proceed
    have hb : bags X Y (r+q) r (F.spot j q r-G.spot j q r) B := by simpa [outstanding,Film.plus,Film.weight,sub_eq_add_neg] using hv.feat j w.second
    rw [add_right_comm,add_assoc] at hx hF hL
    have hR := hs.bond hx
    exact (((bags.gap (HM w.total) hs hF hL).gap hR (he.price _ w.second.added) (HM w.second.added)).gap (hR.bond (hr.price _ w.second.added)) (h.detail j w.second) hb)
  have ha := H (duo _ _ hs hw hK); rw [neg_add_cancel,add_zero] at ha
  unfold Film.figure; rw [← trace_sub]; exact ha.envelope
end YM.Stationary
end
