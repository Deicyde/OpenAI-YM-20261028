import YM.Next.FOUNDATIONS.TestBounds
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Test
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Words


/-!
# Optional tighter readout gate: sum exchange

A Coefficient check will compare actual placed canonical functions, smooth
in the chart at flat, with sums of (infinitely many!) regular occurrences.
Before using jet test, need a proof that those germs can be tested through
the correct order even when the covariance is not asserted termwise. Use
B.Regular and B.supBounds at one **fixed** torus and order. No uniform
constant across periods claimed -- the theorem here is an exact identity,
not an approximate matrix estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Equivariance
open Function Filter Lattice Wilson RG Source Analysis Labels Next.Foundations
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff

section Layers
variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}

private def forms (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Submodule ℝ (Tensor.T E ℂ n) where
  carrier := { x | Tensor.Sym x }
  zero_mem' := fun _ _ => rfl
  add_mem' {A B} (ha : Tensor.Sym A) (hb : Tensor.Sym B) v w := by simp only [add_apply,ha _ _,hb _ _]
  smul_mem' r A (ha : Tensor.Sym A) v w := by simp only [smul_apply,ha _ _]

lemma polarization_sum {T : Tensor.T E ℂ n} {M : ι → Tensor.T E ℂ n} (hT : Tensor.Sym T)
    (hM : ∀ i, Tensor.Sym (M i)) (h : ∀ x : E, HasSum (fun i => Tensor.diagonal (M i) x) (Tensor.diagonal T x))
    (x : Fin n → E) : HasSum (fun i => M i x) (T x) := by
  let F := forms n E
  let A (x : Fin n → E) : F →ₗ[ℝ] ℂ :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) ℂ x).toLinearMap.comp F.subtype
  let p (b : Bool) : ℂ →L[ℝ] ℝ := if b then Complex.reCLM else Complex.imCLM
  let L (i : E × Bool) := (p i.2).toLinearMap.comp (A (fun _ => i.1))
  have ht (y : F) (ht : ∀ i, L i y = 0) : y = 0 := Subtype.ext (by
    apply Tensor.ext_diag _ _ y.2 (fun _ _ => rfl)
    exact funext fun v => Complex.ext (ht (v,true)) (ht (v,false)))
  let u : F := ⟨T,hT⟩; let v (i : ι) : F := ⟨M i,hM i⟩
  let P (B : F →ₗ[ℝ] ℝ) := HasSum (fun i => B (v i)) (B u)
  have hp (B : F →ₗ[ℝ] ℝ) : P B := by
    have he : B ∈ Submodule.span ℝ (Set.range L) := FiniteDimensional.mem_span_of_iInf_ker_le_ker (by
      intro y hy; rw [ht y (fun i => (Submodule.mem_iInf _).mp hy i)]; exact Submodule.zero_mem _)
    refine Submodule.span_induction (s:=Set.range L) (p:=fun B _ => P B) ?_ ?_ ?_ ?_ he
    · rintro B ⟨i,rfl⟩; exact (h i.1).mapL (p i.2)
    · exact hasSum_zero
    · exact fun b c _ _ hb hc => hb.add hc
    exact fun b c _ hc => hc.const_smul b
  have h1 : HasSum (fun i => (M i x).re) (T x).re := hp ((p true).toLinearMap.comp (A x))
  have h2 : HasSum (fun i => (M i x).im) (T x).im := hp ((p false).toLinearMap.comp (A x))
  have he := (h1.mapL Complex.ofRealCLM).add ((h2.mapL Complex.ofRealCLM).mul_right Complex.I)
  simpa only [Complex.ofRealCLM_apply,Complex.re_add_im] using he
end Layers

section Ray
variable {G : Gauge} {n : Side} {U : Config G n} {P : BudgetPoint}

private lemma lies (U : Config G n) (A : Directions G n) (s t : ℝ) :
    increment (increment U (t • A)) (s • A) = increment U ((s+t) • A) := by
  funext i; apply G.mat_injective
  simp only [increment, G.mat_mul, Pi.smul_apply, G.mat_lieExp,map_smul,add_smul,map_add,← mul_assoc]
  haveI : NormedAlgebra ℚ G.Mat := .restrictScalars ℚ ℝ _
  apply congr_arg (fun x => x * G.mat (U i))
  exact (NormedSpace.exp_add_of_commute (((Commute.refl (G.colorMat (A i))).smul_left s).smul_right t)).symm

private lemma scope_at {d : ℕ} {f : Config G n → ℂ} (U : Config G n) (A : Directions G n) (t : ℝ)
    (h : HasOrderAt f (increment U (t • A)) d) (j : ℕ) (hj : j < d) :
    HasDerivAt (iteratedDeriv j fun t : ℝ => f (increment U (t • A)))
      (iteratedDeriv (j+1) (fun t : ℝ => f (increment U (t • A))) t) t := by
  let L (s : ℝ) : ℂ := f (increment U (s • A)); let V := increment U (t • A)
  have he : L = (f ∘ increment V) ∘ (fun s => (s - t) • A) := by
    funext s; simp only [Function.comp_apply,V,lies,sub_add_cancel]; rfl
  have hd : ContDiffAt ℝ d L t := by
    rw [he]; refine ContDiffAt.comp t ?_ (by fun_prop)
    simp only [sub_self,zero_smul]; exact h
  have ht : DifferentiableAt ℝ (iteratedDeriv j L) t :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ℝ) ℂ (fun _ => 1)).differentiableAt.comp t
      (hd.differentiableAt_iteratedFDeriv (Nat.cast_lt.mpr hj))
  change HasDerivAt _ (iteratedDeriv (j+1) L t) t
  rw [iteratedDeriv_succ]; exact ht.hasDerivAt

/-- One ray at flat. Spell out the local summation step. Each cost may depend
on the budget and torus. No uniform control over the chosen ball claimed. -/
private lemma ray_sum {ι : Type*} {D : ι → Support n} {g : ι → Config G n → ℂ} {c : ι → ℝ} {o : Site n}
    (h : ∀ i, P.Regular (D i) (g i)) (hc : ∀ i, P.supBounds o (D i) (g i) (c i)) (hh : Summable c)
    {f : Config G n → ℂ} (hf : f =ᶠ[𝓝 (1:Config G n)] fun U => ∑' i, g i U) (A : Directions G n)
    (j : ℕ) (hj : j ≤ P.order) :
    HasSum (fun i => iteratedDeriv j (fun t : ℝ => g i (increment 1 (t • A))) 0)
      (iteratedDeriv j (fun t : ℝ => f (increment 1 (t • A))) 0) := by
  classical
  let B (t : ℝ) := increment (1:Config G n) (t • A)
  have he : Tendsto B (𝓝 0) (𝓝 1) := by
    have ht : Continuous B := by unfold B increment; fun_prop
    have he : B 0 = 1 := by rw [show B 0=increment (1:Config G n) ((0:ℝ) • A) from rfl,zero_smul,Work.G07.at_zero_increment]
    simpa only [he] using ht.tendsto 0
  obtain ⟨r,hr,hR⟩ := Metric.mem_nhds_iff.mp (he.eventually ((offFlags P.threshold P.threshold_pos).and hf))
  let V := Metric.ball (0 : ℝ) r
  have hV : IsOpen V := Metric.isOpen_ball
  have h0 : (0:ℝ)∈V := Metric.mem_ball_self hr
  let z := (1+‖A‖)/P.threshold
  have hz : 0 < z := div_pos (by positivity) P.threshold_pos
  have ht : P.dirBound o (z⁻¹ • A) := by
    intro e; rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hz).le]
    have h₁ : ‖A e‖ ≤ 1+‖A‖ := (norm_le_pi_norm A e).trans (by linarith)
    calc
      _ ≤ z⁻¹*(1+‖A‖) := mul_le_mul_of_nonneg_left h₁ (inv_pos.mpr hz).le
      _ = P.threshold := by unfold z; field_simp
      _ ≤ _ := le_mul_of_one_le_right P.threshold_pos.le (one_le_pow₀ (by simp))
  have hg i (t : ℝ) (ht : t∈V) : Healthy P.threshold (D i) (B t) := by unfold Healthy; rw [(hR ht).1]; simp
  let L (j : ℕ) (i : ι) := iteratedDeriv j ((g i) ∘ B)
  have hp (j) (hv : j≤P.order) (i) (t : ℝ) (h' : t∈V) : ‖L j i t‖ ≤ z^j*c i := by
    let l := List.replicate j (z⁻¹ • A)
    have hl : l.length = j := List.length_replicate
    change ‖iteratedDeriv j (fun t => g i (B t)) t‖ ≤ _
    rw [show (fun t => g i (B t)) = (fun t => g i (increment 1 (t • A))) from rfl, ← leftDerivs_diag]
    change ‖leftDerivs _ _ (B t)‖ ≤ _
    have hL : l.map (z • ·) = List.replicate j A := by simp only [l,List.map_replicate]; simp [hz.ne']
    have hB : HasOrderAt (g i) (B t) l.length := HasOrderAt.fewer (hl.symm ▸ hv) ((h i).smooth _ (hg i t h'))
    rw [← hL,slot_scale l z hB,hl, norm_smul, Real.norm_of_nonneg (pow_nonneg hz.le _)]
    exact mul_le_mul_of_nonneg_left ((hc i).2 _ (hg i t h') _ (hl.symm ▸ hv) fun A hA =>
      (List.mem_replicate.mp hA).2.symm ▸ ht) (by positivity)
  have hs (j) (hj : j ≤ P.order) (t) (ht : t∈V) : Summable fun i => L j i t :=
    Summable.of_norm_bounded (hh.mul_left (z^j)) fun i => hp j hj i t ht
  let y j := iteratedDeriv j (f ∘ B)
  have hh (j) (hj : j ≤ P.order) (t : ℝ) (ht : t∈V) : y j t = ∑' i, L j i t := by
    induction j generalizing t with
    | zero => exact (hR ht).2
    | succ j ih =>
      have he : ∀ i t, t∈V → HasDerivAt (L j i) (L (j+1) i t) t := fun i t hU =>
        scope_at 1 A t ((h i).smooth _ (hg i t hU)) j hj
      have hd := hasDerivAt_tsum_of_isPreconnected (hh.mul_left (z^(j+1))) hV Metric.isPreconnected_ball
        he (hp (j+1) hj) h0 (hs j (Nat.le_of_lt hj) 0 h0) ht
      change iteratedDeriv _ _ _ = _
      rw [iteratedDeriv_succ]
      exact (hd.congr_of_eventuallyEq (Filter.eventually_of_mem (hV.mem_nhds ht) (ih (Nat.le_of_lt hj)))).deriv
  exact (hs j hj _ h0).hasSum_iff.mpr (hh j hj 0 h0).symm
/-- Pass through the jet at flat (uses only finite-dimensionality of each
actual torus chart for polarization). Then transfer through `testLog`.
Do not exchange tests with masked sums blindly. -/
theorem jet_sum {ι : Type*} {D : ι → Support n} {g : ι → Config G n → ℂ} {c : ι → ℝ} {o : Site n}
    (h : ∀ i, P.Regular (D i) (g i)) (hc : ∀ i, P.supBounds o (D i) (g i) (c i)) (hh : Summable c)
    {f : Config G n → ℂ} (hf : f =ᶠ[𝓝 (1:Config G n)] fun U => ∑' i, g i U)
    (d : ℕ) (he : HasOrderAt f 1 d) (hd : d ≤ P.order) (A : Hol G) (J : Jet G) (k : ℕ) (hk : k≤d) :
    HasSum (fun i => iteratedDeriv k (fun t => g i (A.testLinks d o J t)) 0) (iteratedDeriv k (f ∘ A.testLinks d o J) 0) := by
  have hp (i : ι) : HasOrderAt (g i) 1 d := HasOrderAt.fewer hd
    ((h i).smooth _ (one_healthy (D i) _ P.threshold_pos.le))
  let K (F : Config G n → ℂ) j := iteratedFDeriv ℝ j (F ∘ increment 1) 0
  have hu (j : ℕ) (hJ : j ≤ d) (x) : HasSum (fun i => K (g i) j x) (K f j x) := by
    refine polarization_sum (sym_Jet (he.fewer hJ)) (fun i => sym_Jet ((hp i).fewer hJ)) ?_ x
    intro A
    have hw (u : Config G n → ℂ) (ht : HasOrderAt u 1 d) : Tensor.diagonal (K u j) A =
        iteratedDeriv j (fun t : ℝ => u (increment 1 (t • A))) 0 := (iteratedDeriv_on_line (ht.fewer hJ) A).symm
    change HasSum (fun i => Tensor.diagonal (K (g i) j) A) (Tensor.diagonal (K f j) A)
    rw [hw f he]; simp_rw [hw (g _) (hp _)]
    exact ray_sum h hc hh hf A _ (hJ.trans hd)
  let B := testLog A d o J
  let v (a : OrderedFinpartition k) (i : Fin a.length) := iteratedDeriv (a.partSize i) B 0
  have hx (u : Config G n → ℂ) (ht : HasOrderAt u 1 d) : iteratedDeriv k (u ∘ A.testLinks d o J) 0 =
      ∑ a : OrderedFinpartition k, K u a.length (v a) := by
    have hl : B 0=0 := testLog_zero ..
    have hy : u ∘ A.testLinks d o J =ᶠ[𝓝 0] (u ∘ increment 1) ∘ B := (increment_testLog ..).fun_comp u
    rw [hy.iteratedDeriv_eq, iteratedDeriv_vcomp_eq_sum_orderedFinpartition
      (show ContDiffAt ℝ d (u ∘ increment 1) (B 0) by rw [hl]; exact ht)
      ((testLog_diff A d o J).of_le le_top) (Nat.cast_le.mpr hk),hl]
  rw [hx f he]; change HasSum (fun i => iteratedDeriv k (g i ∘ _) 0) _
  simp_rw [hx (g _) (hp _)]
  exact hasSum_sum fun i _ => hu _ (i.length_le.trans hk) _
end Ray
end YM.ProjectorNext.Equivariance
