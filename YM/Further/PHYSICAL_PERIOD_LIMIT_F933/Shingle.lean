import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Polytrace
import YM.Next.FOUNDATIONS.SU2
import YM.Push.STATIONARY_UNIFORM.Paths

/-!
# Comparing periods by addressing cells, instead of an auxiliary gauge mass

This module: the intensive estimates which imply exponential period error
for the logarithmic scalar *differences* for actual unscaled inputs (c power
normalization). Works also with zero physical frequency, on real operators
(nonabelian components anyway) by counting. No contour continuation in volume
on external fields needed. All widths in this alternative are paid POST L.
More geometry below. -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Shingle
open Jacobi Polytrace    Push.Uniform
open Lattice Gauge RG Tree Function Matrix Finset Precision Filter
open scoped Topology ContDiff BigOperators Classical

variable {α : Type} {β : Type} [Fintype β] [Fintype α] (π : β→α)

def parcel (x : α) := (Finset.univ.filter (fun i : β=> π i=x))
omit [Fintype α] in
@[simp] lemma posted (x : α) (y : β) : y ∈ parcel π x ↔ π y=x := by simp [parcel]

def seam : Matrix β α ℝ := Matrix.of fun i j => if π i=j then 1 else 0
def Fold (m : ℕ) := ∀ i, (parcel π i).card=m
def Every (S : Matrix β β ℝ) (T : Matrix α α ℝ) := S*seam π=seam π*T

lemma multiplied {X : Type} [AddCommMonoid X] {m : ℕ} (h : Fold π m) (F : α → X) : ∑ i : β, F (π i)=m • ∑j:α, F j := by
  calc
    _ = ∑ j:α, ∑ i∈parcel π j,F j := by
      unfold parcel; simp_rw [Finset.sum_filter]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=> by simp
    _ = _ := by simp_rw [Finset.sum_const,show ∀ i, (parcel π i).card=m from h, Finset.smul_sum]

lemma received {m : ℕ} (h : Fold π m) : Fintype.card β=m*Fintype.card α := by simpa using multiplied π h (fun _ : α=>1 : α → ℕ)
omit [Fintype β] in
lemma left (U : Matrix α α ℝ) (i j) : (seam π*U) i j=U (π i) j := by simp [mul_apply,seam,ite_mul]
omit [Fintype α] in
lemma right (U : Matrix β β ℝ) (i j) : (U*seam π) i j=∑ b∈parcel π j,U i b := by simp [mul_apply,parcel,seam,mul_ite]; rw [Finset.sum_filter]
omit [Fintype β] in
lemma envelope (u : Positions α) (i) : (seam π *ᵥ u) i=u (π i) := by simp [seam,mulVec,dotProduct,ite_mul]
lemma intended (S : Matrix β β ℝ) (T : Matrix α α ℝ) :
    Every π S T ↔ ∀ i j, ∑ b∈parcel π j,S i b = T (π i) j := by simp_rw [← left π T, ← right π S]; exact ⟨fun h _ _=>by rw [show _*_=_*_ from h],fun h=> Matrix.ext h⟩
variable {π}
lemma square {R U : Matrix β β ℝ} {T Y : Matrix α α ℝ} (h : Every π R T) (he : Every π U Y) : Every π (R*U) (T*Y) := by unfold Every at *; rw [Matrix.mul_assoc,he,← Matrix.mul_assoc,h,Matrix.mul_assoc]
lemma flip [DecidableEq β] [DecidableEq α] {R : Matrix β β ℝ} {T : Matrix α α ℝ} (h : Every π R T) (he : R.det≠0) (ht : T.det≠0) : Every π R⁻¹ T⁻¹ := by
  have hs := Matrix.mul_nonsing_inv T (isUnit_iff_ne_zero.mpr ht)
  have hR := Matrix.nonsing_inv_mul R (isUnit_iff_ne_zero.mpr he)
  have h:= congr_arg (fun S : Matrix β α ℝ => R⁻¹*S*T⁻¹) (show R*seam π= seam π*T from h)
  change R⁻¹*(R*seam π)*T⁻¹ = R⁻¹*(seam π*T)*T⁻¹ at h
  rw [← Matrix.mul_assoc R⁻¹ R,hR,Matrix.one_mul,← Matrix.mul_assoc R⁻¹ _ T,Matrix.mul_assoc,hs,Matrix.mul_one] at h
  exact h.symm

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (v w : X)
lemma pay {f : X→Matrix β β ℝ} {g : X→Matrix α α ℝ} (he : ∀ᶠ y in 𝓝 0, Faces f y) (hy : ∀ᶠ y in 𝓝 0,Faces g y) (h : ∀ᶠ y in 𝓝 0,Every π (f y) (g y)) :
    ∀ᶠ y in 𝓝 0, Every π (delta v f y) (delta v g y) := by
  filter_upwards [he,hy,eventually_eventually_nhds.mpr h] with y hm hh hr
  apply (intended ..).mpr; intro i j
  simp only [delta,Matrix.of_apply, ← series v (fun k (_:k∈parcel π j) => hm i k)]
  exact congr_arg (fun L : X →L[ℝ] ℝ => L v) ((Filter.EventuallyEq.fderiv_eq ((hr.mono fun u hx => (intended ..).mp hx i j) : (fun u => ∑ k∈parcel π j,f u i k) =ᶠ[𝓝 y] fun u=>g u (π i) j)))
lemma spray {f : X→Matrix β β ℝ} {g : X→Matrix α α ℝ} (he : Faces f 0) (hy : Faces g 0) (h : ∀ᶠ y in 𝓝 0,Every π (f y) (g y)) :
    Every π (delta v (delta w f) 0) (delta v (delta w g) 0) := (pay v (faces_near (face_delta w he)) (faces_near (face_delta w hy)) (pay w (faces_near he) (faces_near hy) h)).self_of_nhds

variable {n : Side} {K N M : ℕ} {d t C A : ℝ} {l : β→Site n}
variable {P : Matrix β β ℝ} {s : Matrix α α ℝ}

omit [Fintype β] in
lemma discount (hh : Sealed l d P C) (hc : 0≤ C) (ht : t ≤ d) : Sealed l t P C := fun i j => (hh i j).trans (mul_le_mul_of_nonneg_left (fee ht ..) hc)

lemma premium {Q : Matrix β β ℝ} (hp : Sealed l d P A) (hq : Sealed l d Q C) (ha : 0 ≤ A) (hc : 0≤C) (hm : Multiplicity l K) (hy : t+t ≤ d) (h : 0<t) :
    Sealed l t (P*Q) (A*C*space K t) := by
  let f := Decay (n:=n) t
  have hf i j : 0≤ f i j := (decay_pos ..).le
  have he i j k : |P i k*Q k j| ≤ A*C*f (l i) (l j)*f (l i) (l k) := by
    let p := l i; let q := l k; let r := l j
    rw [abs_mul]
    have hx : t ≤ d := (le_add_of_nonneg_left h.le).trans hy
    apply (mul_le_mul ((hp _ _).trans (mul_le_mul_of_nonneg_left (separate hy ..) ha)) (discount hq hc hx _ _) (abs_nonneg _)
      (show 0≤ A*(f p q*f p q) from mul_nonneg ha (mul_nonneg (hf ..) (hf ..)))).trans
    have H : A*C*(f p q * f q r)*f p q ≤ A*C*f p r*f p q := by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (decay_step h.le ..) (mul_nonneg ha hc)) (hf ..)
    change A*(f p q * f p q)*(C*f q r) ≤ A*C*f p r*f p q; rw [show A*(f p q * f p q)*(C*f q r) = A*C*(f p q * f q r)*f p q by ring]; exact H
  intro i j; rw [Matrix.mul_apply]; apply ((Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun k _=>he i j k)).trans
  rw [← Finset.mul_sum]
  rw [mul_right_comm (A*C) (space K t)]
  exact mul_le_mul_of_nonneg_left (hm.count _ h _) (mul_nonneg (mul_nonneg ha hc) (hf ..))

structure Reserved (l : β→Site n) (π : β → α) (N : ℕ) : Prop where
  apart i k : π i=π k → i≠k → N ≤ separation (l i) (l k)

theorem deficit (hp : 0 < d) (hc : 0 ≤ C) (hL : Multiplicity l K) (hF : Fold π M) (he : Reserved l π N) (hs : Sealed l d P C) (h : Every π P s) :
    let t := d/2
    |(M:ℝ)*Matrix.trace s - Matrix.trace P| ≤ (Fintype.card β : ℝ)* (C * Real.exp (-t*N) * space K t) := by
  intro r
  have hr (i j) (hx : j∈(parcel π (π i)).erase i) :
      |P i j| ≤ (C*Real.exp (-r*(N:ℝ)))*Decay r (l i) (l j) := by
    obtain ⟨hy,hv⟩ := Finset.mem_erase.mp hx
    have hn : (N:ℝ) ≤ (separation (l i) (l j) : ℝ) := by exact_mod_cast he.apart _ _ ((posted ..).mp hv).symm (Ne.symm hy)
    have hR := half_pos hp
    have hh : Decay r (l i) (l j) ≤ Real.exp (-r*(N:ℝ)) := Real.exp_monotone (mul_le_mul_of_nonpos_left hn (neg_nonpos.mpr hR.le))
    apply (hs ..).trans (mul_le_mul_of_nonneg_left (separate (show r+r ≤ d from le_of_eq (add_halves d)) _ _) hc |>.trans ?_)
    rw [← mul_assoc C]
    gcongr
    exact (decay_pos ..).le
  have hx (i : β) : s (π i) (π i)- P i i=∑ j ∈ (parcel π (π i)).erase i,P i j := by
    have he := (intended ..).mp h i (π i)
    have hh : i∈parcel π (π i) := by simp
    rw [← he,← Finset.add_sum_erase (parcel π (π i)) (P i) hh,add_sub_cancel_left]
  unfold trace
  change |(M:ℝ)*(∑ i,s i i) - (∑ i,P i i)| ≤ _
  rw [show (M:ℝ)*_=(M:ℕ)•(∑ i,s i i) by rw [nsmul_eq_mul], ← multiplied (F:=fun i=>s i i) π hF, ← Finset.sum_sub_distrib]
  simp_rw [hx]
  apply (abs_sum_le_sum_abs ..).trans (le_trans (Finset.sum_le_sum (fun _ _=>Finset.abs_sum_le_sum_abs _ _)) _)
  let D := C*Real.exp (-r*N)
  rw [show (Fintype.card β:ℝ)*(_*_) = ∑ _i:β,D*space K r by simp [D]]
  refine Finset.sum_le_sum fun j _ => ?_
  apply le_trans (Finset.sum_le_sum fun i hi => hr j _ hi); rw [← Finset.mul_sum]
  have hm : (∑ i∈(parcel π (π j)).erase j,Decay r (l j) (l i)) ≤ space K r :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; exact (decay_pos ..).le)) (hL.count _ (half_pos hp) _)
  exact mul_le_mul_of_nonneg_left hm (mul_nonneg hc (Real.exp_pos _).le)
end YM.Further.PhysicalPeriodLimitF933.Shingle
