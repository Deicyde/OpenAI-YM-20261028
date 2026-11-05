import YM.Next.FOUNDATIONS.Readout
import YM.Source.ODE


/-!
# The local Π estimate: link part

's needed **bounds**. Alternative to tracking each polynomial
in the initial link position, fitting the RAuthors/Budgets. Rescale
parameter h to h/(1+native separation) for each link in the estimate. Uniformity in potentially
far-out test links then only requires a **compact set** of normalized
positions, and derivatives of one ODE endpoint on a fixed polynomial-in-time
profile space. Prove a cost in G.Color (physical normalization), relative
to the native separation from o (direction-test convention). Differentiating
the *real log-link map*, obtaining bounds at arbitrary Side but only
claiming the values **at 0** (analyticity radii may NOT be uniform).

This is about the actual test holonomies, not general off-shell
or complexified fields. No comparison of different mask policies. Here θ in [0,1] is amplitude of the readout test, next
consumer will take it equal to the threshold.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Foundations
open Lattice Wilson RG Source Labels Work
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff

variable {G : Gauge}

section Calculus

variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- For precomposing in log coords/scaling. Only assumes ContDiffAt. -/
theorem jets_linear (L : X →L[ℝ] E) {f : E → F} {k : ℕ} (hf : ContDiffAt ℝ k f 0) :
    iteratedFDeriv ℝ k (f ∘ L) 0 =
      (iteratedFDeriv ℝ k f 0).compContinuousLinearMap fun _ => L := by
  let p := G05.blockTaylor k f
  have hp : ContDiff ℝ k p := G05.blockTaylor_contDiff ..
  trans iteratedFDeriv ℝ k (p ∘ L) 0
  · refine G05.jets_comp (d:=k) L.contDiff.contDiffAt L.contDiff.contDiffAt ?_ hp.contDiffAt
      rfl (fun _ _ => rfl) ?_ k le_rfl
    · rw [map_zero]; exact hf
    rw [map_zero]; exact fun i hi => (G05.blockTaylor_jets hf i hi).symm
  rw [L.iteratedFDeriv_comp_right hp _ le_rfl, map_zero]; unfold p
  rw [G05.blockTaylor_jets hf k le_rfl]

lemma iteratedDeriv_on_line {f : E → F} {k : ℕ} (hf : ContDiffAt ℝ k f 0) (A : E) :
    iteratedDeriv k (fun t : ℝ => f (t • A)) 0 = Tensor.diagonal (iteratedFDeriv ℝ k f 0) A := by
  let L := (ContinuousLinearMap.id ℝ ℝ).smulRight A
  change iteratedFDeriv ℝ k (f ∘ L) 0 _ = _
  rw [jets_linear L hf, ContinuousMultilinearMap.compContinuousLinearMap_apply, Tensor.diagonal]
  congr! 1 with i
  simp [L]

private lemma iteratedDeriv_scale {f : ℝ → F} {k : ℕ} (hf : ContDiffAt ℝ k f 0) (r : ℝ) :
    iteratedDeriv k (fun t : ℝ => f (t * r)) 0 = r^k • iteratedDeriv k f 0 := by
  have he := iteratedDeriv_on_line hf r
  have hh := Tensor.homogeneous (iteratedFDeriv ℝ k f 0) 1 r
  rw [smul_eq_mul, mul_one] at hh
  exact he.trans hh

/-- Differentiate in the test parameter and then set it to the test center. -/
private lemma param_derivative {f : E × ℝ → F} {x : E × ℝ} (hf : ContDiffAt ℝ ω f x) (k : ℕ) :
    ContDiffAt ℝ ω (fun p : E × ℝ => iteratedDeriv k (fun t => f (p.1,t)) p.2) x := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ k ih =>
    let V (p : E × ℝ) (r : ℝ) := iteratedDeriv k (fun t => f (p.1,t)) r
    have ht : ContDiffAt ℝ ω (fun p : E × ℝ => fderiv ℝ (V p) p.2) x :=
      ContDiffAt.fderiv (f:=V) (g:=Prod.snd) (n:=ω)
        (ih.comp (f:=fun p : (E × ℝ) × ℝ => (p.1.1,p.2)) (x, x.2) (by fun_prop))
        contDiffAt_snd (by simp)
    simp_rw [iteratedDeriv_succ]
    exact ht.clm_apply (g:=fun _ => (1:ℝ)) contDiffAt_const

end Calculus

section Profile

variable {d : ℕ}

/-- Enlarge the input to a link ODE to arbitrary polynomial-in-time profiles
in color (degrees as in the test). -/
private abbrev TimeProfile (G : Gauge) (d : ℕ) :=
  (i : Fin (d-1)) → Tensor.T (ℝ × ℝ) G.Color (i.val+1)

private def field (X : TimeProfile G d) (s : ℝ) := ∑ i, Tensor.diagonal (X i) (1,s)

private lemma field_smooth (X : TimeProfile G d) : ContDiff ℝ 1 (field X) := by
  unfold field
  refine ContDiff.sum fun i _ => (Tensor.diag_smooth _ 1).comp (contDiff_const.prodMk contDiff_id)

/-- Use `exists_ode` machinery instead of assuming an ambient group ODE
for the extra profiles. The solution on the actual tested paths is unique. -/
private def path (X : TimeProfile G d) := (Hol.pipes (field_smooth X)).choose
private theorem path_leads (X : TimeProfile G d) : SolvesLink (path X) (field X) :=
  (Hol.pipes (field_smooth X)).choose_spec

private def localEndpoint (X : TimeProfile G d) : G.Color := G.plog (G.mat (path X 1))

private theorem endpoint_analytic (G : Gauge) (d : ℕ) :
    ContDiffAt ℝ ω localEndpoint (0 : TimeProfile G d) ∧ localEndpoint (0 : TimeProfile G d) = 0 := by
  let L : TimeProfile G d →ₗ[ℝ] ℝ → G.Mat := {
    toFun X s := G.colorMat (field X s)
    map_add' X Y := by
      funext s
      simp [field, Tensor.diagonal, Finset.sum_add_distrib]
    map_smul' t X := by
      funext s
      simp [field, Tensor.diagonal, Finset.smul_sum] }
  obtain ⟨h,h0,-⟩ := G02.endpointGerm L
    (fun X => G.colorMat.continuous_of_finiteDimensional.comp (field_smooth X).continuous)
    (fun X t => G.mat (path X t)) (fun X => by rw [(path_leads X).1]; rfl)
    (fun X t => (path_leads X).2 t)
  refine ⟨?_, by unfold localEndpoint; rw [h0,G.plog_one]⟩
  have ht : ContDiffAt ℝ ω G.plog (G.mat (path (0 : TimeProfile G d) 1)) := h0.symm ▸ G.plog_diff
  exact ht.comp (f:=fun X => G.mat (path X 1)) _ h.contDiffAt

private def coords (x : Cover) : E4 := WithLp.toLp 2 (fun i => ((x i):ℝ))

private def embedLine (y : E4) (r : ℝ) (i : Axis) : (ℝ × ℝ) →L[ℝ] E4 :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight y +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (r • basis i)

private def profile (d : ℕ) (J : Jet G) (i : Axis) (y : E4) (r a h : ℝ) : TimeProfile G d :=
  fun j => (a*h^(j.val+2)) • (((J j.val).1 i).compContinuousLinearMap fun _ => embedLine y r i)

private theorem field_profile (d : ℕ) (J : Jet G) (i : Axis) (x : Cover) (r θ h s : ℝ) :
    partConnection d (θ • J) (h*r) (x,i) s =
      field (profile d J i (r • coords x) r (θ*r) h) s := by
  have he (j : ℕ) : (h*r) • ((θ • J) j).value i ((h*r) • (coords x + s • basis i)) =
      (θ*r*h^(j+2)) • (J j).value i (embedLine (r • coords x) r i (1,s)) := by
    rw [show (h*r) • (coords x+s • basis i) = h • embedLine (r • coords x) r i (1,s) by
      simp [embedLine, smul_add, mul_smul, smul_comm s], Taylor.value_hom]
    change (h*r) • ((h^(j+1)) • (θ • ((J j).value i (embedLine (r • coords x) r i (1,s))))) = _
    rw [smul_smul, smul_smul]; ring_nf
  change (h*r) • ∑ j ∈ Finset.range (d-1), ((θ • J) j).value i ((h*r) • (coords x+s • basis i)) = _
  rw [Finset.smul_sum, ← Fin.sum_univ_eq_sum_range]; unfold field
  exact Finset.sum_congr rfl fun j _ => he j.val

private theorem profile_smooth (d : ℕ) (J : Jet G) (i : Axis) :
    ContDiff ℝ ω (fun p : (E4 × ℝ × ℝ) × ℝ => profile d J i p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  let P := (E4 × ℝ × ℝ) × ℝ
  have ht : ContDiff ℝ ω (fun p : P => embedLine p.1.1 p.1.2.1 i) := by
    unfold embedLine; dsimp only [P]; fun_prop
  apply contDiff_pi.mpr; intro j
  have hh : ContDiff ℝ ω (fun p : P => ((((J j.val).1 i).compContinuousLinearMap
      fun _ => embedLine p.1.1 p.1.2.1 i))) := by
    simp_rw [← ContinuousMultilinearMap.compContinuousLinearMapLRight_apply]
    exact ContinuousMultilinearMap.contDiff _ |>.comp (contDiff_pi.mpr fun _ => ht)
  refine ContDiff.smul (f:=fun p : P => p.1.2.2*p.2^(j.val+2)) ?_ hh
  dsimp only [P]; fun_prop

private theorem compact_price (d k : ℕ) (J : Jet G) (i : Axis) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : E4) (r a : ℝ), ‖y‖ ≤ 2 → r ∈ Set.Icc (0:ℝ) 1 → a ∈ Set.Icc (0:ℝ) 1 →
      ‖iteratedDeriv k (fun h => localEndpoint (profile d J i y r a h)) 0‖ ≤ C*a := by
  let F (p : (E4 × ℝ × ℝ) × ℝ) := localEndpoint (profile d J i p.1.1 p.1.2.1 p.1.2.2 p.2)
  let R (p : E4 × ℝ × ℝ) := iteratedDeriv k (fun h => F (p,h)) 0
  have he := endpoint_analytic G d
  have hf (p : E4 × ℝ × ℝ) : ContDiffAt ℝ ω F (p,0) := by
    have hp : profile d J i p.1 p.2.1 p.2.2 0 = 0 := by funext j; simp [profile]
    exact (hp.symm ▸ he.1).comp (f:=fun p : (E4 × ℝ × ℝ) × ℝ => profile d J i p.1.1 p.1.2.1 p.1.2.2 p.2) (p,0)
      (profile_smooth d J i).contDiffAt
  have hs : ContDiff ℝ ω R := contDiff_iff_contDiffAt.mpr fun p =>
    (param_derivative (hf p) k).comp p (f:=fun p => (p,0)) (contDiffAt_id.prodMk contDiffAt_const)
  let S := (Metric.closedBall (0:E4) 2) ×ˢ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1)
  obtain ⟨C,hC⟩ := (hs.contDiffOn (s:=S)).exists_lipschitzOnWith (by simp)
    ((convex_closedBall _ _).prod ((convex_Icc ..).prod (convex_Icc ..)))
    ((isCompact_closedBall ..).prod (isCompact_Icc.prod isCompact_Icc))
  have hz (y r) : R (y,r,0) = 0 := by
    have hp : (fun t : ℝ => F ((y,r,0),t)) = 0 := by
      funext t
      unfold F
      simp only
      rw [show profile d J i y r 0 t = 0 by funext l; simp [profile], he.2]
      rfl
    change iteratedDeriv k (fun t : ℝ => F ((y,r,0),t)) 0 = _
    rw [hp]; simp
  refine ⟨C,C.property,fun y r a hy hr ha => ?_⟩
  have hm : (y,r,0) ∈ S := ⟨by simpa using hy,hr,Set.left_mem_Icc.mpr zero_le_one⟩
  have hn : (y,r,a) ∈ S := ⟨hm.1,hr,ha⟩
  have ht := hC.dist_le_mul _ hn _ hm
  rw [hz] at ht
  change ‖R (y,r,a)‖ ≤ _
  simpa [Prod.dist_eq, Real.dist_eq, abs_of_nonneg ha.1, ha.1] using ht

end Profile
section Distance

private theorem position_norm {n : Side} (x : Site n) :
    ‖(1+(pdist x : ℝ))⁻¹ • coords (lift x)‖ ≤ 2 := by
  let R := 1+(pdist x : ℝ)
  have hr : 0 < R := by unfold R; positivity
  let y := R⁻¹ • coords (lift x)
  have ht (i : Axis) : ‖y i‖^2 ≤ 1 := by
    have he : ‖y i‖ ≤ 1 := calc
      ‖y i‖ = R⁻¹ * ((lift x i).natAbs : ℝ) := by
        change ‖R⁻¹ * ((lift x i) : ℝ)‖ = _
        rw [norm_mul, Real.norm_of_nonneg (inv_pos.mpr hr).le, ← norm_natAbs, Real.norm_natCast]
      _ ≤ R⁻¹ * (pdist x : ℝ) := by
        gcongr; exact component_le x i
      _ ≤ R⁻¹ * R := by gcongr; unfold R; linarith
      _ = 1 := inv_mul_cancel₀ hr.ne'
    nlinarith [norm_nonneg (y i)]
  change ‖y‖ ≤ 2
  have hb : ‖y‖^2 ≤ (4:ℝ) := by
    rw [PiLp.norm_sq_eq_of_L2]
    refine (Finset.sum_le_sum (fun i _ => ht i)).trans ?_
    simp [Axis]
  nlinarith

private lemma log_component (H : Hol G) (d k : ℕ) {n : Side} (J : Jet G) (o : Site n)
    (l : Edge (Site n)) :
    iteratedDeriv k (testLog H d o J) 0 l = iteratedDeriv k (fun t => testLog H d o J t l) 0 := by
  let L : Directions G n →L[ℝ] G.Color := ContinuousLinearMap.proj l
  change L (iteratedDeriv k _ _) = iteratedDeriv k (L ∘ testLog H d o J) 0
  unfold iteratedDeriv
  rw [L.iteratedFDeriv_comp_left (testLog_diff H d o J) le_top]; rfl

/-- The directions produced by logarithmic differentiation in the calculus
of the readout, measured against the **torus** distance. Constants independent
of side, θ, anchor and link. Includes order zero: in fact that log is 0.
`θ` acts on all jet amplitudes at once (slot scaling). The ODE identity
holds also at negative h. We are not claiming polynomial structure in the
positions (only the bound). -/
theorem testLog_bound (H : Hol G) (d k : ℕ) (J : Jet G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : Side) (o : Site n) (l : Edge (Site n)) (θ : ℝ),
      0 ≤ θ → θ ≤ 1 →
      ‖iteratedDeriv k (testLog H d o (θ • J)) 0 l‖ ≤ C*θ*(1+(separation l.1 o : ℝ))^(k-1) := by
  choose C hC hh using fun i : Axis => compact_price d k J i
  let K := 1 + ∑ i, C i
  have hK : 0 < K := add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ => hC i)
  refine ⟨K,hK,?_⟩
  rintro n o ⟨x,i⟩ θ ht ht'
  let R := 1+(separation x o : ℝ)
  have hR : 1 ≤ R := by unfold R; simp
  have hr : 0 < R := lt_of_lt_of_le one_pos hR
  let r := R⁻¹
  have hz : r ∈ Set.Icc (0:ℝ) 1 := ⟨(inv_pos.mpr hr).le, inv_le_one_of_one_le₀ hR⟩
  let y := r • coords (lift (x-o))
  have hy : θ*r ∈ Set.Icc (0:ℝ) 1 := ⟨mul_nonneg ht hz.1, mul_le_one₀ ht' hz.1 hz.2⟩
  rw [log_component]
  let B := testLog H d o (θ • J)
  let f (t : ℝ) := B t (x,i)
  have hd : ContDiffAt ℝ k f 0 :=
    ((contDiffAt_pi.mp (testLog_diff H d o (θ • J))) (x,i)).of_le le_top
  have he (h : ℝ) : localEndpoint (profile d J i y r (θ*r) h) = f (h*r) := by
    have h1 := path_leads (profile d J i y r (θ*r) h)
    have h2 := H.solves d (θ • J) (h*r) (lift (x-o),i)
    rw [funext (field_profile d J i (lift (x-o)) r θ h)] at h2
    unfold localEndpoint; rw [h1.unique h2]; rfl
  have hp := hh i y r (θ*r) (position_norm (x-o)) hz hy
  rw [funext he, iteratedDeriv_scale hd, norm_smul, Real.norm_of_nonneg (pow_nonneg hz.1 _)] at hp
  change ‖iteratedDeriv k f 0‖ ≤ _ * _ * R^(k-1)
  have hv : C i ≤ K := le_trans (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))
    (le_add_of_nonneg_left zero_le_one)
  calc
    _ = R^k * (r^k * ‖iteratedDeriv k f 0‖) := by simp [r, hr.ne']
    _ ≤ R^k * (C i*(θ*r)) := mul_le_mul_of_nonneg_left hp (pow_nonneg hr.le _)
    _ ≤ R^k * (K*(θ*r)) := by gcongr
    _ ≤ _ := by
      cases k with
      | zero =>
        simp only [pow_zero, one_mul, Nat.zero_sub, mul_one]
        rw [← mul_assoc]
        exact mul_le_of_le_one_right (mul_nonneg hK.le ht) hz.2
      | succ k =>
        rw [Nat.add_sub_cancel, pow_succ]; unfold r
        apply le_of_eq
        field_simp

end Distance
end YM.Next.Foundations
