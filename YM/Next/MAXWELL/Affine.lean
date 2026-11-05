import YM.Next.MAXWELL.Force

/-!
# Tested affine weights and the translation/dilation generators

Chain signs on two-form indices and on all derivatives. Includes the
(supplementary, on the free system) actual dilation charge.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis
open WaveOn
open scoped ContDiff Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {G : Gauge} {j : ℕ}

/-- Cartan point formula. -/
lemma variation_value {v : Drive} (hv : Killing v) {f : Field F} {U : Set E4} (H : Bianchi U f) (hU : IsOpen U)
    {x} (hx : x ∈ U) (a b : Axis) :
    variation v f a b x = ∑ i : Axis, (v i x • grad i (f a b) x + grad a (v i) x • f i b x +
      grad b (v i) x • f a i x) := by
  have hh (a b : Axis) : grad a (tangent v f b) x = ∑ i : Axis,
      (v i x • grad a (f i b) x + grad a (v i) x • f i b x) := by
    have hp i : DifferentiableAt ℝ (v i) x := (hv.diff _).differentiable (by simp) _
    have hk i : DifferentiableAt ℝ (f i b) x := (H.smooth i b x hx).differentiableAt (by simp)
    change grad a (fun z => ∑ i : Axis, v i z • f i b z) x = _
    rw [grad_sum_f (fun i z => v i z • f i b z) (fun i _ => (hp i).smul (hk i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [grad,D,fderiv_fun_smul (hp i) (hk i)]
  rw [variation, exteriorD,Pi.sub_apply,hh,hh,← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have he : grad a (f i b) x - grad b (f i a) x = grad i (f a b) x := by
    rw [grad_skew H hU b i a hx]
    have ht := H.cycle a b i x hx
    nth_rw 1 [grad_skew H hU a b i hx] at ht
    nth_rw 1 [grad_skew H hU b i a hx] at ht
    -- ht : - ∂a f_i b -∂b f_a i + ...
    rw [sub_neg_eq_add]; rw [← neg_add] at ht
    exact neg_add_eq_zero.mp ht
  rw [← he,H.skew i a x hx,smul_neg,smul_sub]
  abel

lemma affine_wave {v : Drive} (hv : Killing v) (A : M4) (ha : ∀ a b x, grad a (v b) x = A b a)
    {f : Field F} {U} (hU : IsOpen U) (H : WaveOn U f) : WaveOn U (variation v f) := by
  have K := variation_closed v f hv (wave_closed H)
  refine ⟨K.smooth,K.skew,K.cycle,?_⟩
  intro b x hx
  have hf (i l) : DifferentiableAt ℝ (f i l) x := (H.smooth _ _ _ hx).differentiableAt (by simp)
  have hg (i a b) : DifferentiableAt ℝ (grad i (f a b)) x := (grad_smooth i (H.smooth _ _ _ hx) (m := ∞) (by simp)).differentiableAt (by simp)
  have ht (a : Axis) : grad a (variation v f a b) x =
      ∑ i : Axis, (v i x • grad a (grad i (f a b)) x + (A i a) • grad i (f a b) x +
        A i a • grad a (f i b) x + A i b • grad a (f a i) x) := by
    let F (i : Axis) (x : E4) := v i x • grad i (f a b) x
    let B (i : Axis) (x : E4) := F i x + A i a • f i b x + A i b • f a i x
    have hu i : DifferentiableAt ℝ (v i) x := (hv.diff i).differentiable (by simp) _
    have hh i : DifferentiableAt ℝ (F i) x := (hu i).smul (hg i a b)
    have hc i : DifferentiableAt ℝ (fun z => F i z + A i a • f i b z) x :=
      (hh i).add ((hf _ _).const_smul _)
    have he : variation v f a b =ᶠ[𝓝 x] fun z => ∑ i : Axis, B i z := by
      filter_upwards [hU.mem_nhds hx] with y hy; simp only [variation_value hv (wave_closed H) hU hy,ha]; rfl
    refine (GermD (basis a) he).trans ((grad_sum_f B (fun i _ => (hc i).add ((hf _ _).const_smul _)) _).trans ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    change fderiv ℝ (B i) x (basis a)=_
    unfold B
    rw [fderiv_fun_add (hc i) (show DifferentiableAt ℝ (fun z => A i b • f a i z) x from ((hf a i).const_smul _)),fderiv_fun_add (hh i) (show DifferentiableAt ℝ (fun z => A i a • f i b z) x from ((hf i b).const_smul _)),
      fderiv_fun_const_smul (hf a i),fderiv_fun_const_smul (hf i b)]
    unfold F; rw [fderiv_fun_smul (hu i) (hg i a b)]
    simp only [add_apply, smul_apply,ContinuousLinearMap.smulRight_apply]
    rw [show fderiv ℝ (v i) x (basis a) = _ from ha a i x]
    rfl
  let u := A timeAxis timeAxis
  simp_rw [ht, Finset.sum_add_distrib]
  have hd : ∑ a : Axis, ∑ i : Axis, v i x • grad a (grad i (f a b)) x = 0 := by
    rw [Finset.sum_comm]; apply Finset.sum_eq_zero; intro i _
    rw [← Finset.smul_sum];
    exact (congr_arg (fun q : F => v i x • q) ((wave_D H hU (basis i)).divergence b x hx)).trans (smul_zero _)
  have hj : ∑ a : Axis, ∑ i : Axis, A i b • grad a (f a i) x = 0 := by
    rw [Finset.sum_comm]; apply Finset.sum_eq_zero; intro i _; rw [← Finset.smul_sum,H.divergence _ _ hx,smul_zero]
  rw [hd,hj,zero_add,add_zero, Finset.sum_comm (f := fun a i => A i a • grad a (f i b) x)]
  simp_rw [← Finset.sum_add_distrib, ← add_smul]
  have he (a i : Axis) : A i a + A a i = if a=i then 2*u else 0 := by
    split_ifs with hx
    · subst i
      have hw : A a a = u := by unfold u; rw [← ha a a x,hv.diag a timeAxis,ha]
      rw [hw,two_mul]
    rw [← ha a i x,← ha i a x,hv.off a i hx]; exact neg_add_cancel _
  simp_rw [he]
  simp [ite_smul, ← Finset.smul_sum,H.divergence b x hx]

def drift (i : Axis) : Drive := fun a _ => kr a i

@[simp] lemma drift_grad (i a b : Axis) (x) : grad a (drift i b) x = 0 := by
  unfold grad D drift; simp

lemma drift_K (a : Axis) : Killing (drift a) := by
  refine ⟨fun _ => contDiff_const, ?_,?_⟩ <;> intros <;> simp

lemma variation_drift {U : Set E4} {f : Field F} (hU : IsOpen U) (H : WaveOn U f) (i a b : Axis) :
    EqOn (variation (drift i) f a b) (grad i (f a b)) U := by
  intro x hx; rw [variation_value (drift_K i) (wave_closed H) hU hx]; simp [drift,kr_eq,ite_smul]

lemma wave_drift {U : Set E4} {f : Field F} (hU : IsOpen U) (H : WaveOn U f) (i : Axis) :
    WaveOn U (variation (drift i) f) :=
  affine_wave (drift_K i) 0 (by simp) hU H

def fromCenter (A : M4) (x : E4) : Drive := fun b z => M4.move A (z-x) b

def row (A : M4) (b : Axis) : E4 →L[ℝ] ℝ := (EuclideanSpace.proj b : E4 →L[ℝ] ℝ).comp (Matrix.toEuclideanLin A).toContinuousLinearMap

lemma center_grad (A : M4) (x : E4) (a b : Axis) (z : E4) :
    grad a (fromCenter A x b) z = A b a := by
  let L := row A b
  change D (basis a) (L ∘ fun y => y-x) z = _
  have ht : HasFDerivAt ((·-x) : E4 → E4) (ContinuousLinearMap.id ℝ E4) z :=
    (hasFDerivAt_id z).sub_const _
  rw [D,fderiv_comp z L.differentiableAt ht.differentiableAt,ht.fderiv,L.fderiv]
  exact M4.move_basis A b a

lemma center_smooth (A : M4) (x : E4) (b : Axis) : ContDiff ℝ ∞ (fromCenter A x b) :=
  (row A b).contDiff.comp (contDiff_id.sub contDiff_const)

lemma radial_K (x : E4) : Killing (fromCenter 1 x) := by
  refine ⟨center_smooth 1 x,fun a b he z => ?_,?_⟩ <;> intros <;> simp_all [center_grad,eq_comm]

lemma skew_K (A : Ortho.Skew) (x : E4) : Killing (fromCenter A.val x) := by
  have he (i l : Axis) : A.val i l = -A.val l i := congr_arg (fun s : M4 => s l i)
    (show star A.val= -A.val from A.property)
  have ht (i : Axis) : A.val i i=0 := by have h := he i i; linarith
  refine ⟨center_smooth _ _,fun a b _ z => ?_,fun a b z => ?_⟩
  · rw [center_grad,center_grad]; exact he b a
  simp [center_grad,ht]

/-- Taylor multiplication by one centered linear function. Keep coefficients normalized. -/
lemma linear_times_series {f : E4 → F} (L : E4 →L[ℝ] ℝ) {x : E4} (h : ContDiffAt ℝ ∞ f x) (y : E4) :
    diagonal (coeff (fun z => L (z-x) • f z) (j+1) x) y = L y • diagonal (coeff f j x) y := by
  let g := fun z : E4 => L (z-x)
  have ht : ContDiff ℝ ∞ g := L.contDiff.comp (contDiff_id.sub contDiff_const)
  have hs : fderiv ℝ g x = L := by
    change fderiv ℝ (L ∘ fun y => y-x) x = _
    have hh : HasFDerivAt (fun z => z-x) (ContinuousLinearMap.id ℝ E4) x := (hasFDerivAt_id x).sub_const _
    rw [fderiv_comp x L.differentiableAt hh.differentiableAt, hh.fderiv,L.fderiv]; ext; rfl
  induction j generalizing f with
  | zero =>
    change coeff _ 1 x (fun _ => y) = L y • coeff f 0 x _
    rw [show (fun _ : Fin 1 => y) = Fin.cons y (fun _ => y) by funext i; fin_cases i; simp,
      coeff_apply_cons ((show ContDiffAt ℝ ∞ (fun z => g z • f z) x from (ht.contDiffAt.smul h)).of_le (WithTop.coe_le_coe.mpr le_top)),
      coeff_apply_zero,coeff_apply_zero]
    change ((↑(0+1 : ℕ):ℝ))⁻¹ • fderiv ℝ (fun z => g z • f z) x y = L y • f x
    rw [fderiv_fun_smul (ht.differentiable (by simp) x) (h.differentiableAt (by simp)),hs]
    simp [g]
  | succ j ih =>
    let A : Fin (j+1) → E4 := fun _ => y
    change coeff (fun z => g z • f z) (j+2) x (fun _ => y) = L y • coeff f (j+1) x A
    rw [show (fun _ : Fin (j+2) => y) = Fin.cons y A by funext i; exact Fin.cases rfl (fun _ => rfl) i,
      Tensor.coeff_apply_cons ((show ContDiffAt ℝ ∞ (fun z => g z • f z) x from ht.contDiffAt.smul h).of_le (WithTop.coe_le_coe.mpr le_top))]
    have w : D y (fun z => g z • f z) =ᶠ[𝓝 x] (g • D y f + L y • f) := by
      have h₂ := h.of_le (show (↑(2:ℕ) : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
      filter_upwards [h₂.eventually (by simp)] with z hz
      unfold D; rw [fderiv_fun_smul (ht.differentiable (by simp) z) (hz.differentiableAt (by simp))]
      have hg : fderiv ℝ g z = L := by
        rw [show g = fun z => L z - L x from funext fun z => L.map_sub ..]
        exact (L.hasFDerivAt.sub_const _).fderiv
      rw [hg]; simp
    have hd : ContDiffAt ℝ ∞ (D y f) x := dSmooth h _ (by simp)
    have hr : coeff (g • D y f) (j+1) x A = L y • diagonal (coeff (D y f) j x) y := ih hd
    let s : ℝ := (j+1 : ℕ)
    have heq : coeff f (j+1) x A = s⁻¹ • diagonal (coeff (D y f) j x) y := by
      rw [show A=Fin.cons y (fun _ => y) by funext i; exact Fin.cases rfl (fun _ => rfl) i]
      exact Tensor.coeff_apply_cons (h.of_le (WithTop.coe_le_coe.mpr le_top)) _ _
    have hp : ContDiffAt ℝ (↑(j+1 : ℕ)) f x := h.of_le (WithTop.coe_le_coe.mpr le_top)
    rw [GermCoeff (j+1) w, Tensor.coeff_add (show ContDiffAt ℝ (↑(j+1 : ℕ)) (g • D y f) x from
      (ht.contDiffAt.smul hd).of_le (WithTop.coe_le_coe.mpr le_top)) (show ContDiffAt ℝ (↑(j+1 : ℕ)) (L y • f) x from hp.const_smul _), add_apply,
      Tensor.coeff_smul _ hp, smul_apply,hr,heq, smul_smul, smul_add,smul_smul,smul_smul,← add_smul]
    · congr 1; dsimp [s]; field_simp; push_cast; ring

/-- Centered field weights hit just jet j (coefficient order) and act
by the transformation measured on the corresponding homogeneous solution. -/
lemma variation_center (A : M4) (x : E4) (hv : Killing (fromCenter A x)) (h₀ : Killing (fromCenter A 0))
    {f : Field F} {U : Set E4} (H : WaveOn U f) (hU : IsOpen U) (hx : x ∈ U) :
    let p : Solution F j := ⟨nth f j x,H.jets hU hx⟩
    nth (variation (fromCenter A x) f) j x = nth (variation (fromCenter A 0) (asWave p)) j 0 := by
  intro p
  let W := tangent (fromCenter A x) f
  let B := tangent (fromCenter A 0) (asWave p)
  have he (i : Axis) : Tensor.coeff (W i) (j+1) x = coeff (B i) (j+1) 0 := by
    -- diagonal equality, unfold via sums
    have hx' (b) := H.smooth b i x hx
    have ht (b) := (wavePoly p).smooth b i 0 (mem_univ 0)
    apply Tensor.ext_diag _ _ (coeff_symm ((tangent_diff _ _ _ hv fun i l => H.smooth i l x hx).of_le
      (WithTop.coe_le_coe.mpr le_top))) (coeff_symm ((tangent_diff _ _ _ h₀ fun i l => (wavePoly p).smooth i l 0 (mem_univ _)).of_le
      (WithTop.coe_le_coe.mpr le_top)))
    have hq {f' : Field F} (z : E4) (h : ∀ b, ContDiffAt ℝ ∞ (f' b i) z) (u : E4) :
        diagonal (coeff (tangent (fromCenter A z) f' i) (j+1) z) u =
        ∑ b : Axis, row A b u • diagonal (nth f' j z b i) u := by
      let J (b : Axis) (w : E4) := fromCenter A z b w • f' b i w
      have hk : tangent (fromCenter A z) f' i = ∑ b : Axis, J b := funext fun w => by rw [Finset.sum_apply]; rfl
      have hc (b) : ContDiffAt ℝ (↑(j+1 : ℕ)) (J b) z := ((center_smooth A z b).contDiffAt.smul (h b)).of_le (WithTop.coe_le_coe.mpr le_top)
      rw [hk,coeff_sum _ _ J _ fun b _ ↦ hc b,Tensor.diagonal, sum_apply]
      exact Finset.sum_congr rfl fun b _ => linear_times_series (row A b) (h b) _
    exact funext fun u => (hq x hx' u).trans (by rw [hq _ ht u, asWave_jet])
  ext1 a; ext1 b
  have hw (a) : ContDiffAt ℝ ∞ (W a) x := tangent_diff _ _ _ hv fun i l => H.smooth i l x hx
  have hz (a) : ContDiffAt ℝ ∞ (B a) 0 := tangent_diff _ _ _ h₀ fun i l => (wavePoly p).smooth i l 0 (mem_univ _)
  have hh a b : coeff (grad a (W b)) j x = coeff (grad a (B b)) j 0 := by
    apply Tensor.ext_diag _ _ (coeff_symm ((grad_smooth a (hw b) (m:=∞) (by simp)).of_le (WithTop.coe_le_coe.mpr le_top)))
      (coeff_symm ((grad_smooth a (hz b) (m:=∞) (by simp)).of_le (WithTop.coe_le_coe.mpr le_top)))
    funext u
    rw [show grad a (W b)=D (basis a) (W b) from rfl, ← slot_lower ((hw b).of_le
      (WithTop.coe_le_coe.mpr le_top)), he b]; exact slot_lower ((hz b).of_le (WithTop.coe_le_coe.mpr le_top)) ..
  change coeff (grad a (W b) - grad b (W a)) j x = coeff (grad a (B b)-grad b (B a)) j 0
  have hk {f g : E4 → F} (u) {z} (h₁ : ContDiffAt ℝ ∞ f z) (h₂ : ContDiffAt ℝ ∞ g z) :
      coeff (grad a f - grad u g) j z = coeff (grad a f) j z - coeff (grad u g) j z := by
    rw [sub_eq_add_neg, coeff_add, neg_coeff,sub_eq_add_neg]
    exacts [(grad_smooth _ h₁ (m:=∞) (by simp)).of_le (WithTop.coe_le_coe.mpr le_top),
      ((grad_smooth _ h₂ (m:=∞) (by simp)).neg).of_le (WithTop.coe_le_coe.mpr le_top)]
  rw [hk b (hw b) (hw a),hk b (hz b) (hz a),hh a b,hh b a]

lemma radial_flux {x : E4} {U} {f : Field G.Color} (hU : IsOpen U) (H : WaveOn U f) (p : Probe G j)
    {χ : E4 → ℝ} (hχ : ContDiff ℝ ∞ χ) (Hχ : HasCompactSupport χ)
    (hs : tsupport χ ⊆ U) (hx : χ =ᶠ[𝓝 x] fun _ => 1) :
    singleFlux (fromCenter 1 x) χ (pulse p x) f = -((j:ℝ)+2) * sample p f x := by
  let v := fromCenter 1 x
  have he := affine_wave (radial_K x) 1 (center_grad 1 x) hU H
  have hu := hs (enclosed _ hx)
  rw [jet_force hU H (radial_K x) hχ Hχ hs hx he p];
  let B : Shell G j := ⟨nth f j x,H.jets hU hu⟩
  have hh : variation (fromCenter 1 0) (asWave B) = ((j : ℝ)+2) • asWave B := by
    funext a b y
    rw [variation_value (radial_K 0) (wave_closed (wavePoly B)) isOpen_univ (mem_univ _)]
    simp only [center_grad,fromCenter,sub_zero, M4.move_one, Matrix.one_apply, ite_smul,zero_smul,
      one_smul, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    change (∑ i : Axis, y i • grad i (diagonal (B.val a b)) y) + _ + _ = _
    rw [grad_euler _ ((show ClosedJet _ from B.property.1).coeffSym a b)]
    change _ = ((j : ℝ)+2) • diagonal (B.val a b) y
    rw [add_smul,two_smul]
    simp [asWave,add_assoc]
  have hr := variation_center 1 x (radial_K x) (radial_K 0) H hU hu (j:=j)
  change _ = nth (variation (fromCenter 1 0) (asWave B)) j 0 at hr
  rw [sample,hr,hh]
  have hz : nth (((j:ℝ)+2) • asWave B) j 0 = ((j:ℝ)+2) • nth f j x := by
    rw [show nth f j x = B.val from rfl, ← asWave_jet];
    exact funext fun i => funext fun l => Tensor.coeff_smul _ (((wavePoly B).smooth i l 0 (mem_univ _)).of_le
      (WithTop.coe_le_coe.mpr le_top))
  rw [hz, map_smul]; simp only [smul_eq_mul,sample,neg_mul]

lemma drift_flux {x : E4} {U} {f : Field G.Color} (hU : IsOpen U) (H : WaveOn U f) (p : Probe G j)
    (a : Axis) {χ : E4 → ℝ} (hχ : ContDiff ℝ ∞ χ) (Hχ : HasCompactSupport χ)
    (hs : tsupport χ ⊆ U) (hx : χ =ᶠ[𝓝 x] fun _ => 1) :
    singleFlux (drift a) χ (pulse p x) f = -sample (raiseLeg (basis a) p) f x := by
  rw [jet_force hU H (drift_K a) hχ Hχ hs hx (wave_drift hU H a) p,← sample_deriv_label _ p H hU (hs (enclosed _ hx))]
  rw [sample_eq_of_germ (g := fun b c => D (basis a) (f b c)) fun b c =>
    (variation_drift hU H a b c).eventuallyEq_of_mem (hU.mem_nhds (hs (enclosed _ hx)))]

end YM.Maxwell.Free
