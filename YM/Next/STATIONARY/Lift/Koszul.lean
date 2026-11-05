import YM.Exterior.Initial
import YM.Laurent.Art
import YM.Next.STATIONARY.Infrastructure.Jets
import YM.Work.F06.Cartan


set_option autoImplicit false
/-! Quantitative single-coordinate division. Ordinary Fourier *entries*.
No removable-singularity convention on a mesh. Use interval telescopes on monomials,
so works also at the complex zeros. -/
noncomputable section
namespace YM.Stationary
open Filter Function Finset Laurent Asymptotics
open scoped Topology BigOperators ContDiff
set_option linter.unusedSectionVars false
variable {α : Type} [Fintype α] [DecidableEq α] {σ τ A : ℝ}

section one
variable (i : α) (p : Phase α) (x : Shift α)

def divZ (p : Phase α) := Complex.exp (Complex.I * p i)-1

def seriesLeg : Phase α → ℂ := fun p => if 0 ≤ x i then
    ∑ a ∈ Finset.range (x i).natAbs, mode p (update x i (a:ℤ)) else
    - ∑ a ∈ Finset.range (x i).natAbs, mode p (update x i (-(a+1:ℤ)))

private lemma eval_step (a : ℤ) : divZ i p * mode p (update x i a) =
    mode p (update x i (a+1))-mode p (update x i a) := by
  rw [show update x i (a+1)=update x i a+Pi.single i 1 by
    ext j; by_cases h : j=i <;> simp [*], mode_shift]; unfold divZ
  have he : mode p (Pi.single i 1)=Complex.exp (Complex.I * p i) := by simp [mode,Pi.single_apply,mul_ite]
  rw [he]; ring

private lemma evaluates : mode p (update x i 0)=mode (update p i 0) x := by
  unfold Laurent.mode
  congr 2
  exact sum_congr rfl fun j _ => by by_cases h : j=i <;> simp [*]

lemma seriesLeg_exact : divZ i p * seriesLeg i x p = mode p x-mode (update p i 0) x := by
  unfold seriesLeg
  split <;> rename_i H
  · have he (n : ℕ) :
        divZ i p * ∑ a ∈ Finset.range n, mode p (update x i (a:ℤ)) =
        mode p (update x i (n:ℤ))-mode p (update x i 0) := by
      induction n with
      | zero => simp
      | succ n ih => rw [sum_range_succ,mul_add,ih,eval_step,Nat.cast_add_one]; abel
    rw [he,show ((x i).natAbs:ℤ)=x i by omega,update_eq_self,evaluates]
  have he (n : ℕ) :
      divZ i p * (∑ a ∈ Finset.range n, mode p (update x i (-(a+1:ℤ)))) =
      mode p (update x i 0)-mode p (update x i (-(n:ℤ))) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ,mul_add,ih,eval_step,show -(n+1:ℤ)+1 = -(n:ℤ) by omega,Nat.cast_add_one]; abel
  rw [mul_neg,he,show -((x i).natAbs:ℤ)=x i by omega,update_eq_self,evaluates,neg_sub]

lemma seriesLeg_entire : Differentiable ℂ (seriesLeg i x) := by
  unfold seriesLeg
  split <;> unfold mode <;> fun_prop

lemma seriesLeg_fund (h : 0<σ) : Firm σ ((size x:ℝ)*Real.exp (σ*size x)) (seriesLeg i x) := by
  have he (q : ℤ) (hq : q.natAbs≤(x i).natAbs) : Firm σ (Real.exp (σ*size x)) (fun p => mode p (update x i q)) := by
    refine (Firm.mode _ h).mono h le_rfl (Real.exp_monotone (mul_le_mul_of_nonneg_left ?_ h.le))
    exact_mod_cast (sum_le_sum (s:=univ (α:=α)) (f:=fun j => ((update x i q) j).natAbs) fun j _ => by
      by_cases H : j=i; simpa only [H,update_self] using hq
      exact le_of_eq (congrArg Int.natAbs (update_of_ne H ..)))
  let s := Finset.range (x i).natAbs
  let g := fun _ : ℕ => Real.exp (σ*size x)
  have hv : ∑ a ∈ s,g a ≤ (size x:ℝ)*Real.exp (σ*size x) := by
    have hi : (x i).natAbs ≤ size x := single_le_sum (f:=fun j => (x j).natAbs) (fun _ _ => Nat.zero_le _) (mem_univ i)
    simp only [g,s,sum_const,card_range,nsmul_eq_mul]
    gcongr
  unfold seriesLeg
  split
  · exact ((Firm.sum s _ g h fun i hi => he _ (by rw [Int.natAbs_natCast]; exact (mem_range.mp hi).le))).mono h le_rfl hv
  refine Firm.neg (((Firm.sum s _ g h fun i hi => he (-((i:ℤ)+1)) (by have := mem_range.mp hi; omega))).mono h le_rfl hv)
end one

section divide
-- one width-independent choice on the strip. exact dependence on budget multiplicative
variable (i : α) {f : Phase α → ℂ}

def priceDivision (α : Type) [Fintype α] (σ : ℝ) := (σ/4)⁻¹ * (2*((1+σ/4)/(σ/4)))^(Fintype.card α)
lemma priceDivision_pos (σ : ℝ) (h : 0 < σ) (α : Type) [Fintype α] : 0 < priceDivision α σ := by
  unfold priceDivision; positivity

theorem div_var (hf : Firm σ A f) : ∃ g, Firm (σ/4) (A*priceDivision α σ) g ∧
    ∀ p ∈ Laurent.strip (σ/4), divZ i p * g p = f p - f (update p i 0) := by
  let τ := σ/4
  have he : 0 < σ := hf.width_pos
  have ht : 0 < τ := by unfold τ; positivity
  let H := market f 0
  let k := A * (2*((1+τ)/τ))^(Fintype.card α)
  have hH : Width (2*τ) k H := hf.1.issues hf.2 (2*τ) τ (by positivity) ht (by unfold τ; linarith)
  let T (x : Shift α) := Real.exp (2*τ*size x)*‖H x‖
  let v (x : Shift α) (p : Phase α) := seriesLeg i x p * H x
  have hc (x : Shift α) : Firm τ (τ⁻¹*T x) (v x) := by
    refine ((seriesLeg_fund i x ht).mul (Firm.const ht (H x))).mono ht le_rfl ?_
    change _ ≤ τ⁻¹ * (_ * _)
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [show 2*τ*(size x)=τ*(size x)+τ*(size x) by ring,Real.exp_add,← mul_assoc]
    have hy : (size x:ℝ) ≤ τ⁻¹*Real.exp (τ*size x) := by
      rw [inv_mul_eq_div, le_div_iff₀ ht]; linarith [Real.add_one_le_exp (τ*size x)]
    exact mul_le_mul_of_nonneg_right hy (Real.exp_pos _).le
  have hU : Summable (fun x => τ⁻¹*T x) := hH.2.1.mul_left _
  have hsum p (hp : p∈Laurent.strip τ) : Summable (fun x => ‖v x p‖) :=
    hU.of_nonneg_of_le (fun i => norm_nonneg _) fun i => (hc i).2 p hp
  refine ⟨fun p => ∑' x, v x p, ⟨⟨ht,fun p hp => ?_,fun p hp u => tsum_congr fun i => (hc i).1.reset p hp _⟩,fun p hp => ?_⟩,fun p hp => ?_⟩
  · obtain ⟨R,hR,H⟩ := Metric.mem_nhds_iff.mp ((Work.F07.stripOpen τ).mem_nhds hp)
    exact (Work.F02.analytic_series v hR (fun i => (seriesLeg_entire _ _).mul_const _) hU (fun i p hp => (hc i).2 p (H hp))).differentiableAt
  · apply (norm_tsum_le_tsum_norm (hsum p hp)).trans
    apply ((hsum p hp).tsum_le_tsum (fun i => (hc i).2 p hp) hU).trans
    rw [tsum_mul_left]
    exact (mul_le_mul_of_nonneg_left hH.2.2 (by positivity : 0 ≤ τ⁻¹)).trans_eq (by dsimp only [priceDivision,k,τ]; ring)
  have ha : 2*τ ≤ σ := by unfold τ; linarith
  have hm : ∀ p ∈ Laurent.strip τ, f p=∑' x, mode p x * H x := fun p hp =>
    (hf.1.paints hf.2 p (fun j => (hp j).trans_le (show τ ≤ σ by linarith))).symm
  have hg : update p i 0∈Laurent.strip τ := by
    intro j; by_cases h : j=i; simpa [h] using ht
    rw [update_of_ne h]; exact hp j
  have hx (p : Phase α) (hp : p∈Laurent.strip τ) : Summable (fun x => mode p x * H x) :=
    (hH.series p (fun i => (hp i).le.trans (by linarith))).2.1.of_norm
  rw [hm p hp,hm _ hg,← (hx _ hp).tsum_sub (hx _ hg), ← tsum_mul_left]
  refine tsum_congr fun x => ?_
  unfold v
  rw [← mul_assoc,seriesLeg_exact,sub_mul]

end divide
end YM.Stationary
end

/-!
Dense-direction cancellation for Bills on the real torus. `shadow` varies one
real coordinate only; hence e.g. preserves an auxiliary annihilator with no
assumption of continuity of that subspace versus the other coordinates.
-/
noncomputable section
namespace YM.Stationary
open Filter Function Finset Laurent Asymptotics
open scoped Topology BigOperators ContDiff
variable {α : Type} [Fintype α] [DecidableEq α] {σ τ A C : ℝ}

lemma divCost (i : α) {f : Phase α → ℂ} (h : Firm σ A f) :
    Firm σ A (fun p => f (update p i 0)) := by
  refine h.comp (fun p => update p i 0) ?_ h.width_pos ?_ ?_
  · rw [differentiable_pi]
    intro j; by_cases H : j=i
    · subst j; simp
    simp_rw [update_of_ne H]; fun_prop
  · intro p hp j; by_cases H : j=i; simpa [H] using h.width_pos
    rw [update_of_ne H]; exact hp j
  intro p x
  refine ⟨update x i 0,?_⟩
  funext j; by_cases H : j=i <;> simp [*,reciprocal]

lemma divMode (i : α) (hp : 0 < σ) : Firm σ (Real.exp σ + 1) (divZ i) := by
  have he : divZ i = (fun p => mode p (Pi.single i 1)-1) := by
    funext p; simp [divZ,mode,Pi.single_apply,mul_ite]
  rw [he]
  have hs : size (Pi.single i 1)=1 := by
    unfold Laurent.size
    rw [sum_eq_single i]
    · simp
    · intro a _ hi; simp [Pi.single_eq_of_ne hi]
    simp
  simpa only [hs, norm_one, Nat.cast_one, mul_one] using (Firm.mode (Pi.single i 1) hp).sub (Firm.const hp 1)



/-- In a linear ray with nonzero speed in slot i the divisor really has a
first-order zero (at the zeros along i). -/
theorem zero_div (r v : ℝ) (hv : v≠0) (he : Complex.exp (Complex.I*r)=1) :
    let z := fun t : ℝ => Complex.exp (Complex.I*↑(r+t*v))-1
    (fun t : ℝ => t) =O[cutRay] z := by
  intro z
  have hp : HasDerivAt z (Complex.I*v) 0 := by
    unfold z; simp_rw [Complex.ofReal_add,Complex.ofReal_mul]
    have ht := Complex.ofRealCLM.hasFDerivAt (x:=(0:ℝ))
    have hy : HasDerivAt (fun t : ℝ => (↑t:ℂ)) 1 0 := ht.hasDerivAt
    simpa [he, Complex.ofReal_mul] using (((hy.mul_const (v:ℂ)).const_add (r:ℂ) |>.const_mul Complex.I).cexp.sub_const 1)
  have hz : z 0=0 := by simp [z,he]
  have ht := (hasDerivAt_iff_tendsto_slope_zero.mp hp).norm
  simp only [hz,sub_zero,zero_add,norm_smul,norm_inv,Complex.norm_mul,Complex.norm_I,one_mul] at ht
  let K := ‖(v:ℂ)‖ / 2
  have hk : 0 < K := by unfold K; exact half_pos (norm_pos_iff.mpr (by exact_mod_cast hv))
  refine isBigO_iff.mpr ⟨K⁻¹,?_⟩
  filter_upwards [ht.eventually (le_mem_nhds (show K < ‖(v:ℂ)‖ by unfold K at *; linarith)),
    (self_mem_nhdsWithin : ∀ᶠ t : ℝ in cutRay, t ≠ 0)] with t ht hv
  rw [inv_mul_eq_div, le_div_iff₀ hk]
  rwa [inv_mul_eq_div, le_div_iff₀ (norm_pos_iff.mpr hv), mul_comm] at ht

lemma divisor_nonzero {r : ℝ} (v : ℝ) (hv : v≠0) :
    ∀ᶠ t : ℝ in cutRay, Complex.exp (Complex.I * ↑(r+t*v))-1 ≠ 0 := by
  let z := fun t : ℝ => Complex.exp (Complex.I*↑(r+t*v))-1
  by_cases he : z 0=0
  · have hu := zero_div r v hv (by unfold z at he; rw [zero_mul,add_zero] at he; exact sub_eq_zero.mp he)
    obtain ⟨M,hM⟩ := isBigO_iff.mp hu
    filter_upwards [hM,(self_mem_nhdsWithin : ∀ᶠ t : ℝ in cutRay, t ≠ 0)] with t ht hb hr
    rw [hr, norm_zero, mul_zero] at ht; exact hb (norm_eq_zero.mp (le_antisymm ht (norm_nonneg _)))
  have H : ∀ᶠ x in 𝓝 (0:ℝ), z x ≠ 0 := ((show Continuous z by unfold z; fun_prop).tendsto 0).eventually (eventually_ne_nhds he)
  exact H.filter_mono nhdsWithin_le_nhds

def shadow (x : Corn α) (i : α) (t : ℝ) : Corn α := update x i (x i+t)
omit [Fintype α] in
@[simp] lemma shadow_zero (x : Corn α) (i : α) : shadow x i 0=x := by simp [shadow]
omit [Fintype α] in
lemma shadows (x : Corn α) (i : α) : Tendsto (shadow x i) cutRay (𝓝 x) := by
  have he : Continuous (shadow x i) := continuous_pi fun j => by
    by_cases h : j=i
    · simp [*,shadow]
      fun_prop
    unfold shadow; simp_rw [update_of_ne h]; exact continuous_const
  have ht := he.tendsto 0; rw [shadow_zero] at ht; exact ht.mono_left nhdsWithin_le_nhds
omit [Fintype α] in
lemma shadow_fee (x : Corn α) (i : α) :
    ∀ᶠ t in cutRay, divZ i (axes (shadow x i t)) ≠ 0 := by
  simpa only [divZ, shadow, update_self, axes,mul_one] using divisor_nonzero (r:=x i) 1 one_ne_zero

theorem rays_div {f g : Phase α → ℂ} {s : ℕ} {i : α} (hg : Firm σ C g)
    (hp : Rays s (f ∘ axes))
    (h : ∀ p : Corn α, divZ i (axes p) * g (axes p) = f (axes p) - f (update (axes p) i 0)) :
    Rays (s-1) (g ∘ axes) := by
  cases s with
  | zero => exact rays_zero (hg.analytic_real 0)
  | succ n =>
    refine rays_from_dense (hg.analytic_real 0) {x : Corn α | x i ≠ 0} ?_ n ?_
    · intro x
      by_cases hi : x i=0
      · refine mem_closure_of_tendsto (shadows x i) ?_
        filter_upwards [(self_mem_nhdsWithin : ∀ᶠ t : ℝ in cutRay, t ≠ 0)] with t ht
        simpa [shadow, hi] using ht
      exact subset_closure hi
    intro p ht; change p i ≠ 0 at ht
    have hy : (fun t : ℝ => divZ i (axes (t • p)) * g (axes (t • p))) =O[cutRay] (fun t => t^(n+1)) := by
      apply ((hp p).sub (hp (update p i 0))).congr_left
      intro t
      dsimp only [comp_apply,Pi.sub_apply]
      rw [h]; congr 2
      funext j; by_cases H : j=i <;> simp [*,axes]
    have hv := zero_div 0 _ ht (by simp)
    change _ =O[cutRay] _ at hy
    have hv' : (fun t : ℝ => t)=O[cutRay] (fun t => divZ i (axes (t • p))) := by
      simpa only [divZ,axes,Pi.smul_apply,zero_add,smul_eq_mul] using hv
    obtain ⟨C,hC,hb⟩ := hv'.exists_pos
    obtain ⟨K,hK,hx⟩ := hy.exists_pos
    refine isBigO_iff.mpr ⟨C*K,?_⟩
    filter_upwards [hb.bound, hx.bound,(self_mem_nhdsWithin : ∀ᶠ t : ℝ in cutRay, t ≠ 0)] with t ht hc hi
    rw [norm_mul,norm_pow, pow_succ] at hc
    apply le_of_mul_le_mul_left _ (norm_pos_iff.mpr hi)
    dsimp only [comp_apply]
    calc
      _ ≤ C * ‖divZ i (axes (t • p))‖ * ‖g (axes (t • p))‖ := mul_le_mul_of_nonneg_right ht (norm_nonneg _)
      _ ≤ C * (K * (‖t‖^n * ‖t‖)) := by rw [mul_assoc]; gcongr
      _ = _ := by rw [norm_pow]; ring
end YM.Stationary
end

/-!
# Single-coordinate removal of a lattice curl

We don't divide by a norm squared. Koszul homotopy step replaces a
real-mesh cycle by one evaluating on this coordinate's face q_i=0 and
dropping any exterior component using i. We retain the path-width bill
(constant per finite type, paid pre-L). `wall` can remember previous legs,
so this primitive will also work with momentum coupling between arguments
when applied *after* the appropriate shear.
-/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Bloch Laurent Filter Finset Asymptotics
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators
set_option linter.unusedSectionVars false

variable {α ξ : Type} [Fintype α] [Fintype ξ]

abbrev SheetLeg (α ξ : Type) (r : ℕ) := Phase α → TypeFace r → ξ → ℂ

-- C along an indicated momentum
def cob (r : ℕ) (m : Phase α → Momentum) (f : SheetLeg α ξ (r+1)) : SheetLeg α ξ r :=
    fun p a x => ((symbol r (m p)).transpose *ᵥ (fun A => f p A x)) a

lemma cob_zero (r : ℕ) (m : Phase α → Momentum) (f : SheetLeg α ξ (r+2)) :
    cob r m (cob (r+1) m f)=0 := by
  funext p a x
  simp_rw [cob,Matrix.mulVec_mulVec, ← Matrix.transpose_mul,symbol, d_d,Matrix.transpose_zero,Matrix.zero_mulVec]
  rfl
lemma cob_add (r : ℕ) (m : Phase α → Momentum) (f g : SheetLeg α ξ (r+1)) : cob r m (f+g)=cob r m f+cob r m g := by
  funext p a x; exact congr_fun (Matrix.mulVec_add _ (fun A => f p A x) (fun A => g p A x)) a
lemma cob_sub (r : ℕ) (m : Phase α → Momentum) (f g : SheetLeg α ξ (r+1)) : cob r m (f-g)=cob r m f-cob r m g := by
  funext p a x; exact congr_fun (Matrix.mulVec_sub _ (fun A => f p A x) (fun A => g p A x)) a

variable {m : Phase α → Momentum} {r : ℕ}
/-- *Closure* only on real p (analyticity and periodization accounted for separately). -/
def Cycles (m : Phase α → Momentum) : (r : ℕ) → SheetLeg α ξ r → Prop
  | 0, _ => True
  | r+1,f => ∀ p : Corn α, cob r m f (axes p)=0

def projected (m : Axis ↪ α) : Phase α → Momentum := fun p => p ∘ m

def Uniforms (ξ α : Type) [Fintype ξ] (m : Axis ↪ α) (U : Corn α → Submodule ℂ (ξ → ℂ)) :=
    ∀ i j : Corn α, (∀ a ∉ Set.range m, i a=j a) → U i=U j

def wall (U : Corn α → Submodule ℂ (ξ → ℂ)) (f : SheetLeg α ξ r) := ∀ i a, f (axes i) a ∈ U i

def JetWall (s : ℕ) (f : SheetLeg α ξ r) := ∀ i x, Rays s (fun p => f (axes p) i x)
def CostWall (σ A : ℝ) (f : SheetLeg α ξ r) := ∀ i x, Firm σ A (fun p => f p i x)

lemma CostWall.mono {σ τ A B : ℝ} {f : SheetLeg α ξ r} (h : CostWall σ A f) (hp : 0<τ) (he : τ≤σ) (hb : A≤B) : CostWall τ B f := fun i x => (h i x).mono hp he hb

lemma CostWall.add {σ A B : ℝ} {f g : SheetLeg α ξ r} (h : CostWall σ A f) (hk : CostWall σ B g) : CostWall σ (A+B) (f+g) := fun i x => (h i x).add (hk i x)
lemma CostWall.sub {σ A B : ℝ} {f g : SheetLeg α ξ r} (h : CostWall σ A f) (hk : CostWall σ B g) : CostWall σ (A+B) (f-g) := fun i x => (h i x).sub (hk i x)

section creation
open Work.F06
-- Cartan with degree arbitrary; single-axis projection is literal zeroing.
lemma cartan_remove (v : TypeFace (r+1) → ℂ) (z : Momentum) (i : Axis) :
    (left ℂ r i) *ᵥ ((wedge r z).transpose *ᵥ v) +
      (wedge (r+1) z).transpose *ᵥ ((left ℂ (r+1) i) *ᵥ v) = z i • v := by
  unfold wedge
  simp_rw [Matrix.transpose_sum,Matrix.transpose_smul,Matrix.sum_mulVec, Matrix.smul_mulVec, Matrix.mulVec_sum,
    Matrix.mulVec_smul, ← Finset.sum_add_distrib, ← smul_add,
    cartan_axis v i]
  simp [smul_ite]
lemma cartan_0 (v : TypeFace 0 → ℂ) (z : Momentum) (i : Axis) :
    (wedge 0 z).transpose *ᵥ ((left ℂ 0 i) *ᵥ v) = z i • v := by
  unfold wedge
  simp_rw [Matrix.transpose_sum,Matrix.transpose_smul, Matrix.sum_mulVec,Matrix.smul_mulVec]
  have he (j : Axis) : (left ℂ 0 j).transpose *ᵥ ((left ℂ 0 i)*ᵥ v) = if i=j then v else 0 := by
    funext A
    rcases vac_only A
    have hnj : j ∉ vac.val := by simp [vac]
    rw [eliminate_transpose,dif_pos hnj,eliminate]
    split_ifs with h H
    · subst i; rw [remove_addAxis, ← mul_assoc,parity_square,one_mul]
    · exfalso; exact H (by simpa [addAxis,vac] using h)
    · subst i; exact False.elim (h (mem_addAxis j _ _))
    simp
  simp_rw [he, smul_ite, smul_zero]
  simp
lemma cartan_project (v : TypeFace (r+1) → ℂ) (i : Axis) (a : TypeFace (r+1)) :
    ((left ℂ r i) *ᵥ ((left ℂ r i).transpose *ᵥ v)) a= if i ∈ a.val then v a else 0 := by
  rw [eliminate]
  split_ifs with h
  · rw [eliminate_transpose, dif_pos (notMem_cut i a h), addAxis_remove, ← mul_assoc, parity_square, one_mul]
  rfl

end creation

variable [DecidableEq α]
section cut
variable (m' : Axis ↪ α) (i : Axis)

/-- Residual cycle after lifting at one ambient axis. -/
def comb (f : SheetLeg α ξ r) : SheetLeg α ξ r := fun p A x =>
    if i∈A.val then 0 else f (update p (m' i) 0) A x

private lemma cost_comb {σ A : ℝ} {f : SheetLeg α ξ r} (hp : CostWall σ A f) :
    CostWall σ A (comb m' i f) := by
  intro a x; unfold comb; split
  · have h := hp a x; exact (Firm.zero h.width_pos).mono h.width_pos le_rfl h.budget_nonneg
  exact divCost _ (hp a x)

lemma jet_comb {s : ℕ} {f : SheetLeg α ξ r} (hp : JetWall s f) : JetWall s (comb m' i f) := by
  intro a x; unfold comb; split
  · intro p; exact isBigO_zero ..
  intro p; apply (hp a x (update p (m' i) 0)).congr_left
  intro b; apply congr_arg (fun y => f y a x)
  ext1 j; by_cases h : j=m' i <;> simp [*,axes]

private lemma comb_wall {f : SheetLeg α ξ r} {U : Corn α → Submodule ℂ (ξ → ℂ)} (hU : Uniforms ξ α m' U) (h : wall U f) : wall U (comb m' i f) := by
  have hv (p) : U p = U (update p (m' i) 0) := hU p _ (by
    intro a hn; by_cases he : a=m' i
    · exact False.elim (hn (he.symm ▸ Set.mem_range_self _))
    simp [he])
  intro p a
  by_cases hi : i∈a.val
  · rw [show comb m' i f (axes p) a=0 from funext fun _ => if_pos hi]; exact (U p).zero_mem
  rw [show comb m' i f (axes p) a=f (update (axes p) (m' i) 0) a from funext fun _ => if_neg hi]
  rw [hv p, show update (axes p) (m' i) 0=axes (update p (m' i) 0) by ext1 j; by_cases h : j=m' i <;> simp [h,axes]]
  exact h _ _

private lemma symbol_update (p : Corn α) : q (projected m' (axes p)) =
    q (projected m' (axes (update p (m' i) 0))) + divZ (m' i) (axes p) • Pi.single i 1 := by
  ext1 j
  by_cases h : i=j
  · subst j; simp [q,projected,axes,divZ]
  simp [Ne.symm h,q,projected,axes]

private lemma cob_comb_core {f : SheetLeg α ξ r} (hc : Cycles (projected m') r f) (p : Corn α)
    (hp : divZ (m' i) (axes p) ≠ 0) (D : TypeFace r → ℂ) (x : ξ)
    (hd : divZ (m' i) (axes p) • D =
        (fun A => f (axes p) A x) - (fun A => f (axes (update p (m' i) 0)) A x)) :
    (symbol r (projected m' (axes p))).transpose *ᵥ ((left ℂ r i) *ᵥ D) =
      (fun A => f (axes p) A x)-(fun A => comb m' i f (axes p) A x) := by
  let z := projected m' (axes p)
  let p₀ := update p (m' i) 0
  let z₀ := projected m' (axes p₀)
  let d := divZ (m' i) (axes p)
  have he : update (axes p) (m' i) 0 = axes p₀ := by
    ext1 b; by_cases h : b=m' i <;> simp [p₀,h,axes]
  conv_rhs => arg 2; intro A; unfold comb; rw [he]
  cases r with
  | zero =>
    rw [symbol,cartan_0, show q (projected m' (axes p)) i=d from rfl]; apply hd.trans; congr 1
    ext1 a; simp [show i∉a.val by rw [vac_only a]; exact notMem_empty _]; rfl
  | succ r =>
    let v := fun A => f (axes p) A x
    let u := fun A => f (axes p₀) A x
    have h1 : (wedge r (q z)).transpose *ᵥ v=0 := by
      funext a; exact congr_fun (congr_fun (hc p) a) x
    have h0 : (wedge r (q z₀)).transpose *ᵥ u=0 := by
      funext a; exact congr_fun (congr_fun (hc p₀) a) x
    have hh : wedge r (q z)=wedge r (q z₀)+d • left ℂ r i := by
      rw [show q z=_ from symbol_update m' i p]
      simp only [wedge,Pi.add_apply, add_smul, sum_add_distrib, Pi.smul_apply,Pi.single_apply]
      simp [ite_smul,z₀,d,p₀]
    have hD : d • D=v-u := hd
    have hp' : (left ℂ r i)*ᵥ ((wedge r (q z)).transpose *ᵥ D) = -((left ℂ r i)*ᵥ ((left ℂ r i).transpose *ᵥ u)) := by
      apply smul_right_injective (r:=d) _ hp
      dsimp only
      rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul,hD,Matrix.mulVec_sub,h1,zero_sub,hh,
        Matrix.transpose_add,Matrix.add_mulVec,h0,zero_add,Matrix.mulVec_neg,Matrix.transpose_smul,Matrix.smul_mulVec,Matrix.mulVec_smul,smul_neg]
    have hy := cartan_remove D (q z) i; rw [hp',show q z i=d from rfl,hD] at hy
    have hV : _ = ((left ℂ r i)*ᵥ ((left ℂ r i).transpose *ᵥ u)) + (v-u) := eq_add_of_neg_add_eq hy
    apply hV.trans
    ext1 a
    rw [Pi.add_apply,cartan_project]
    by_cases H : i ∈ a.val <;> simp [p₀,u,v,H]



private lemma cob_step {σ A : ℝ} (hs : 0<σ) (ha : 0 ≤ A) (f : SheetLeg α ξ r)
    {s : ℕ} (hf : CostWall σ A f) (hv : Cycles (projected m') r f) (hk : JetWall s f)
    {U} (hU : Uniforms ξ α m' U) (hw : wall U f) :
    let g := comb m' i f
    CostWall σ A g ∧ Cycles (projected m') r g ∧ JetWall s g ∧ wall U g ∧
    ∃ B : SheetLeg α ξ (r+1), CostWall (σ/4) (A*priceDivision α σ) B ∧ JetWall (s-1) B ∧
      wall U B ∧ ∀ p : Corn α, f (axes p)= (cob r (projected m') B) (axes p)+g (axes p) := by
  intro g
  have ht : 0<σ/4 := by positivity
  have hg := cost_comb m' i hf
  choose D hD he using fun a x => div_var (m' i) (hf a x)
  let B : SheetLeg α ξ (r+1) := fun p a x => (left ℂ r i *ᵥ (fun b => D b x p)) a
  have hB : CostWall (σ/4) (A*priceDivision α σ) B := by
    intro a x
    unfold B; simp_rw [eliminate]
    split; next h => simpa only [parity, norm_pow, norm_neg,norm_one,one_pow,one_mul] using ((Firm.const ht (parity a.val i ℂ)).mul (hD (Exterior.remove i a h) x))
    exact (Firm.zero ht).mono ht le_rfl (mul_nonneg ha (priceDivision_pos σ hs _).le)
  have hh b x p : divZ (m' i) (axes p) * D b x (axes p)=f (axes p) b x - f (axes (update p (m' i) 0)) b x := by
    rw [he b x _ ((hD b x).in_range (axes_real p)), show axes (update p (m' i) 0)= update (axes p) (m' i) 0 by
      ext1 a; by_cases h : a=m' i <;> simp [h,axes]]
  have hj : JetWall (s-1) B := by
    have heD b x := rays_div (f:=fun p => f p b x) (i:=m' i) (hD b x) (hk b x)
      (fun p => he b x _ ((hD b x).in_range (axes_real p)))
    intro a x p
    unfold B; simp_rw [eliminate]; split
    next h => exact (heD (Exterior.remove i a h) x p).const_mul_left (parity a.val i ℂ)
    exact isBigO_zero ..
  have hy : ∀ p : Corn α, cob r (projected m') B (axes p)=f (axes p)-g (axes p) := by
    intro p; funext a x
    let l (p : Corn α) := cob r (projected m') B (axes p) a x
    have H : ContinuousAt l p := by
      suffices h : ∀ p, ContinuousAt l p from h p
      rw [← continuous_iff_continuousAt]
      unfold l cob Matrix.mulVec dotProduct
      refine continuous_finsetSum _ (fun j hj => ?_)
      refine Continuous.mul ?_ (continuous_iff_continuousAt.mpr fun v => ((hB j x).analytic_real v).continuousAt)
      simp only [symbol,q,wedge,projected,Function.comp_apply,Matrix.transpose_apply,Matrix.sum_apply, Matrix.smul_apply]
      apply continuous_finsetSum; intro i _; dsimp only [axes]; fun_prop
    have H' := ((hf a x).analytic_real p).continuousAt.sub ((hg a x).analytic_real p).continuousAt
    refine tendsto_nhds_unique_of_eventuallyEq (H.tendsto.comp (shadows p (m' i)))
      (H'.tendsto.comp (shadows p (m' i))) ?_
    filter_upwards [shadow_fee p (m' i)] with t ht
    let q := shadow p (m' i) t
    exact congr_fun (cob_comb_core m' i hv q ht (fun b => D b x (axes q)) _ (funext fun b => hh b x q)) a
  have hv' : Cycles (projected m') r g := by
    cases r with
    | zero => trivial
    | succ r =>
      intro p; funext a x
      let c := axes p
      have H := congr_fun (congr_fun (congr_fun (cob_zero r (projected m') B) c) a) x
      have z : cob r (projected m') (f-g) c a x=0 := by
        change ((symbol r _).transpose *ᵥ _) a=0
        rw [show (fun y => (f-g) c y x) = (fun y => cob (r+1) (projected m') B c y x) from
          funext fun b => (congr_fun (congr_fun (hy p) b) x).symm]; exact H
      rw [cob_sub] at z
      simp only [Pi.sub_apply] at z
      exact (sub_eq_zero.mp z).symm.trans (congr_fun (congr_fun (hv p) a) x)
  refine ⟨hg,hv',jet_comb m' i hk,comb_wall m' i hU hw,B,hB,hj,?_,fun p => by rw [hy]; abel⟩
  have hm (p : Corn α) (b) : (fun x => D b x (axes p))∈U p := by
    have hΔ a (k : ℝ) : U a = U (update a (m' i) k) := hU a _ (by
      intro v he; by_cases h : v=m' i
      · exact False.elim (he (h.symm ▸ Set.mem_range_self _))
      simp [h])
    have h (p : Corn α) : ContinuousAt (fun p => fun x => D b x (axes p)) p :=
      continuousAt_pi.mpr fun j => ((hD b j).analytic_real p).continuousAt
    apply (U p).closed_of_finiteDimensional.mem_of_tendsto ((h p).tendsto.comp (shadows p (m' i)))
    filter_upwards [shadow_fee p (m' i)] with t ht
    let q := shadow p (m' i) t
    rw [show U p=U q from hΔ p _]
    change (fun x => D b x (axes q)) ∈ _
    let R := divZ (m' i) (axes q) • (fun x => D b x (axes q))
    have hp : R∈U q := by rw [show R = _ - f (axes (update q (m' i) 0)) b from funext fun x => hh b x q]; apply (U q).sub_mem (hw q b); rw [hΔ q 0]; exact hw _ _
    exact ((U q).smul_mem_iff ht).mp hp
  intro p b
  by_cases H : i∈b.val
  · rw [show B (axes p) b=parity b.val i ℂ • fun x => D (Exterior.remove i b H) x (axes p) from funext fun x => by simp [B, eliminate,H]]
    exact (U p).smul_mem _ (hm ..)
  rw [show B (axes p) b=0 from funext fun x => by simp [B,eliminate,H]]
  exact (U p).zero_mem

private def purge (f : SheetLeg α ξ r) : List Axis → SheetLeg α ξ r
  | [] => f
  | i::l => purge (comb m' i f) l

private lemma allcombs {σ A : ℝ} (hs : 0<σ) (ha : 0 ≤ A) (l : List Axis) (f : SheetLeg α ξ r) {s : ℕ} (hf : CostWall σ A f)
    (hv : Cycles (projected m') r f) (hk : JetWall s f) {U} (hU : Uniforms ξ α m' U) (hw : wall U f) :
    ∃ B : SheetLeg α ξ (r+1), CostWall (σ/4) (A*(l.length*priceDivision α σ)) B ∧ JetWall (s-1) B ∧
      wall U B ∧ ∀ p : Corn α, f (axes p)=cob r (projected m') B (axes p)+purge m' f l (axes p) := by
  induction l generalizing f with
  | nil =>
    refine ⟨0,fun b x => ?_,fun b x p => isBigO_zero ..,fun p _ => (U p).zero_mem,fun p => ?_⟩
    · simpa only [List.length_nil,Nat.cast_zero,zero_mul,mul_zero,Pi.zero_apply] using Firm.zero (α:=α) (by positivity : 0<σ/4)
    funext i x; simp [cob,purge,Matrix.mulVec,dotProduct]
  | cons i l ih =>
    obtain ⟨ht,h1,h2,h3,X,hX,h4,h5,h6⟩ := cob_step m' i hs ha f hf hv hk hU hw
    obtain ⟨Y,hY,h7,h8,h9⟩ := ih _ ht h1 h2 h3
    refine ⟨X+Y, ?_,fun a x => Rays.add (h4 a x) (h7 a x),fun p i => (U p).add_mem (h5 p i) (h8 p i),fun p => ?_⟩
    · rw [List.length_cons,Nat.cast_add_one,show A*(((_ : ℝ)+1)*priceDivision α σ)=A*(priceDivision α σ)+A*(l.length*priceDivision α σ) by ring]
      exact hX.add hY
    rw [h6 p,h9 p, cob_add,purge]; simp [add_assoc]

private lemma purge_hit (f : SheetLeg α ξ r) (l : List Axis) (a : TypeFace r) (p : Corn α) :
    ∃ q : Corn α, (∀ j ∈ l, q (m' j) = 0) ∧
        (∀ j ∉ l.map m', q j=p j) ∧
        purge m' f l (axes p) a = if ∀ i ∈ a.val,i ∉ l then f (axes q) a else 0 := by
  classical
  induction l generalizing f p with
  | nil => exact ⟨p,by simp, by simp,by simp [purge]⟩
  | cons i l IH =>
    obtain ⟨q,H,K,ht⟩ := IH (comb m' i f) p
    refine ⟨update q (m' i) 0, ?_, ?_,?_⟩
    · intro j hj; by_cases h : j=i; simp [h]
      rw [update_of_ne (m'.injective.ne h)]; exact H _ (by simpa [h] using hj)
    · intro j hj; simp only [List.map_cons,List.mem_cons,not_or] at hj
      rw [update_of_ne hj.1]; exact K _ hj.2
    rw [purge,ht]; by_cases h : i∈a.val
    · split <;> rename_i u <;> rw [if_neg (fun H => H i h (by simp))]
      exact funext fun _ => if_pos h
    have he : (∀ j∈a.val,j∉i::l) ↔ ∀ j∈a.val,j∉l := by
      constructor
      · intro hf j hj hn; exact hf j hj (by simp [hn])
      intro hf j hj hx; simp only [List.mem_cons] at hx
      exact hx.elim (fun H => h (H ▸ hj)) (hf j hj)
    simp only [he]
    split <;> rename_i hu; swap; rfl
    funext x
    unfold comb
    rw [if_neg h, show update (axes q) (m' i) 0=axes (update q (m' i) 0) by
      ext1 j; by_cases h : j=m' i <;> simp [*,axes]]

def taxWall (α : Type) [Fintype α] (σ : ℝ) := 4*priceDivision α σ
lemma taxWall_pos {σ : ℝ} (h : 0 < σ) : 0 < taxWall α σ := mul_pos (by norm_num) (priceDivision_pos σ h _)

/-- The real analytic one-leg solve. Even degree zero, where its right
hypothesis is image-vanishing. Returns a width funded before any evaluation. -/
theorem wall_lift {σ A : ℝ} (hs : 0<σ) (ha : 0 ≤ A) (f : SheetLeg α ξ r) {s : ℕ} (hf : CostWall σ A f)
    (hv : Cycles (projected m') r f) (he : r≠0 ∨ ∀ p : Corn α, p ∘ m' = 0 → f (axes p)=0)
    (hk : JetWall s f) {U} (hU : Uniforms ξ α m' U) (hw : wall U f) :
    ∃ B : SheetLeg α ξ (r+1), CostWall (σ/4) (A*taxWall α σ) B ∧ JetWall (s-1) B ∧
      wall U B ∧ ∀ p : Corn α, f (axes p)=cob r (projected m') B (axes p) := by
  obtain ⟨B,H,h1,h2,h3⟩ := allcombs m' hs ha (List.finRange 4) f hf hv hk hU hw
  refine ⟨B, ?_, h1,h2,fun p => ?_⟩
  · simpa only [taxWall,List.length_finRange,Nat.cast_ofNat] using H
  rw [h3 p]; suffices hh : purge m' f (List.finRange 4) (axes p)=0 by rw [hh,add_zero]
  funext a
  obtain ⟨q,hq,-,hx⟩ := purge_hit m' f (List.finRange 4) a p
  apply hx.trans; split <;> rename_i hj; swap; rfl
  rcases he with he|he
  · have hv : a.val.Nonempty := card_pos.mp (a.property.symm ▸ Nat.pos_of_ne_zero he)
    obtain ⟨j,hj'⟩ := hv
    exact (hj j hj' (List.mem_finRange _)).elim
  exact congr_fun (he q (funext fun j => hq j (List.mem_finRange j))) a
end cut
end YM.Stationary
end
