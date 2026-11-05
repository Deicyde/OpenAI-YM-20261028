import YM.Extra.WEAK_SCALING_ACTLAW.Wick
import YM.Work.A01.Conserve

/-!
# Two stress-divergence tests on the normalized free comparator at four/five

Spectator is itself an invariant pair square at zero; first insertion at a
unit coordinate point. Work with the stipulated r-independent `normal*|x|⁻²`
scalar covariance before curls, and the no-internal-pairings moment. The
calculation is an upper bound on the exact H-real mean-zero conserved tensor
space. It does not say that the local shell identities in a Lighthouse.Goes
receipt must already pick a member with scalar part removed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.WeakScaling.Color
open Function Set Filter Analysis Labels Maxwell Tensor Cube Climb
open scoped Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {L : Register G}

private def δ (i j : Axis) : ℝ := basis i j
private lemma away_basis (i : Axis) : basis i ∈ away := norm_pos_iff.mp (by simp)

private def hess (i j : Axis) (y : E4) := -2*δ i j*(‖y‖^2)⁻¹^2 + 8*y i*y j*(‖y‖^2)⁻¹^3
private def H0 (i j : Axis) := -2*δ i j + 8*δ 0 i*δ 0 j
private def H1 (a i j : Axis) := 8*(δ 0 a * δ i j + δ 0 i * δ a j + δ 0 j * δ a i) - 48*δ 0 a*δ 0 i*δ 0 j

private lemma known (i j : Axis) : hess i j (basis 0) = H0 i j := by simp [hess,H0,δ]
private lemma hess_diff (i j : Axis) {y} (hy : y ∈ away) : DifferentiableAt ℝ (hess i j) y :=
  (((differentiableAt_const _).mul (((contDiff_norm_sq ℝ (n:=∞)).differentiable (by simp) y).inv (pow_ne_zero _ (norm_ne_zero_iff.mpr hy)) |>.pow 2)).add
    ((((differentiableAt_const _).mul (compAxis i).differentiableAt).mul (compAxis j).differentiableAt).mul
      (((contDiff_norm_sq ℝ (n:=∞)).differentiable (by simp) y).inv (pow_ne_zero _ (norm_ne_zero_iff.mpr hy)) |>.pow 3)))
private lemma gradient_hess (a i j : Axis) : D (basis a) (hess i j) (basis 0) = H1 a i j := by
  have hr := (hasFDerivAt_inv (show ‖basis 0‖^2 ≠ 0 by simp)).comp (basis 0) (hasStrictFDerivAt_norm_sq (basis 0)).hasFDerivAt
  have ht := ((hr.pow 2).const_mul (-2*δ i j)).add ((((compAxis i).hasFDerivAt.const_mul 8).mul (compAxis j).hasFDerivAt).mul (hr.pow 3))
  have hh := ht.fderiv; change fderiv ℝ (hess i j) (basis 0)=_ at hh
  rw [D,hh]; simp [compAxis,H1,δ, two_smul, -basis_eq]
  rw [show basis a 0=basis 0 a by simp [eq_comm]]; ring

private def curlOf (X : Axis → Axis → ℝ) (i j a b : Axis) :=
    X i b * δ a j - X i a * δ b j - (X j b * δ a i - X j a * δ b i)
private def curl (i j a b : Axis) (y : E4) := curlOf (fun i j => hess i j y) i j a b
private lemma is_curl (i j a b : Axis) {y : E4} (h : y∈away) : bareCurl i j a b y = Maxwell.normal * curl i j a b y := by
  simp only [bareCurl, Pi.sub_apply, Bare.opp_grad h,second_Green h,curl,curlOf,hess,δ]
  simp only [basis_eq,eq_comm (a:=j), eq_comm (a:=i)]
  split_ifs <;> ring

private lemma curl_at (i j a b : Axis) : curl i j a b (basis 0) = curlOf H0 i j a b := by simp only [curl,curlOf,known]
private lemma curl_diff {i j a b} : DifferentiableAt ℝ (curl i j a b) (basis 0) := by
  have hh i j (c : ℝ) := (hess_diff i j (away_basis 0)).mul_const c
  exact DifferentiableAt.sub ((hh i b (δ a j)).sub (hh i a (δ b j))) ((hh j b (δ a i)).sub (hh j a (δ b i)))
private lemma curl_step (k i j a b : Axis) : D (basis k) (curl i j a b) (basis 0) = curlOf (H1 k) i j a b := by
  have hh i j (c : ℝ) := (hess_diff i j (away_basis 0)).hasFDerivAt.mul_const c
  have h := (((hh i b (δ a j)).sub (hh i a (δ b j))).sub ((hh j b (δ a i)).sub (hh j a (δ b i))))
  have he : fderiv ℝ (curl i j a b) (basis 0)=_ := h.fderiv
  rw [D,he]; simp [curlOf, ← gradient_hess, D, mul_comm]

private def row (s i j a b p q : Axis) := 2*(curlOf (H1 s) i j p q * curlOf H0 a b p q + curlOf H0 i j p q * curlOf (H1 s) a b p q)
private def cost (G : Gauge) := G.lieDim * Maxwell.normal ^ 2
private lemma cost_pos (h : G.Simple) : 0 < cost G := by
  haveI := h.nontrivial_color
  have he : 0 < Module.finrank ℝ G.Color := Module.finrank_pos
  rw [finrank_euclideanSpace_fin] at he
  have hn := Maxwell.normal_pos; unfold cost; positivity

private abbrev w (L : Register G) (i j p q : Axis) := (⟨4,pinned L i j p q⟩ : (Bel L).Tag)
private abbrev other (L : Register G) (p q : Axis) (_ : Fin 1) := w L p q p q
private def kernel (L : Register G) (i j a b p q : Axis) (y : E4) := Ward.disc (Fin.cons (w L i j a b) (other L p q)) (Points.cons y 0)

private lemma clear {y : E4} (h : y ∈ away) : Points.cons (n:=1) y 0 ∈ conf _ := Work.A01.conf_cons (fun _ _ _ => Subsingleton.elim _ _) (fun _ => h)
private lemma agreement (i j a b p q : Axis) {y : E4} (hy : y∈away) : kernel L i j a b p q y =
    (↑((cost G * 2) * (curl i j p q y * curl a b p q y)) : ℂ) := by
  change Ward.disc _ _ = _; rw [show Fin.cons (w L i j a b) (other L p q) = ![w L i j a b,w L p q p q] by funext k; fin_cases k <;> rfl]
  rw [show Ward.disc .. = _ from paired_eval L _ (clear hy) i j a b p q p q]
  congr 1
  change (↑G.lieDim * (bareCurl _ _ _ _ (y-0)*bareCurl _ _ _ _ (y-0) + bareCurl _ _ _ _ (y-0)*bareCurl _ _ _ _ (y-0)) : ℝ) = _
  rw [sub_zero,is_curl i j p q hy,is_curl a b p q hy]; unfold cost; ring

private def tester (W : DiffPlan (Bel L)) (s p q : Axis) :=
  ((Work.A15.front (Points.cons (basis 0) 0) (other L p q) 5).comp (W.deriv 4 s)).restrictScalars ℝ
private lemma test_value (W : DiffPlan (Bel L)) (hW : W.Derivatives (Bel L)) (s i j a b p q : Axis) :
    tester W s p q (pinned L i j a b) = (↑(cost G * row s i j a b p q) : ℂ) := by
  simp only [tester,LinearMap.restrictScalars_apply,LinearMap.comp_apply,Work.A15.front_apply]
  rw [← Work.A01.D_cons (table_smooth _) W hW _ _ (clear (away_basis 0)) s]
  let F := fun y => (cost G*2) * (curl i j p q y * curl a b p q y)
  have he : kernel L i j a b p q =ᶠ[𝓝 (basis 0)] (Complex.ofRealCLM ∘ F) := by
    filter_upwards [open_away.mem_nhds (away_basis 0)] with z hz using agreement _ _ _ _ _ _ hz
  change D _ (kernel L i j a b p q) (basis 0) = _
  rw [GermD (basis s) he]
  have h := (DifferentiableAt.hasFDerivAt (curl_diff (i:=i) (j:=j) (a:=p) (b:=q))).mul (curl_diff (i:=a) (j:=b) (a:=p) (b:=q)).hasFDerivAt |>.const_mul (cost G*2)
  have hF : fderiv ℝ (Complex.ofRealCLM ∘ F) (basis 0) = _ := (Complex.ofRealCLM.hasFDerivAt.comp _ h).fderiv
  rw [D,hF]; dsimp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,smul_apply,add_apply, smul_eq_mul]
  congr 1
  change _ * (_ * (D (basis s) (_ : E4 → ℝ) (_ : E4)) + _ * (D (basis s) (_ : E4 → ℝ) (_ : E4))) = _
  simp only [curl_at,curl_step,row]; ring

private def observed (W : DiffPlan (Bel L)) (p q : Axis) : (Bel L).Stress →ₗ[ℝ] ℂ := ∑ i : Axis, (tester W i p q).comp
    ((LinearMap.proj (φ:=fun _ : Axis => (Bel L).Field 4) (0:Axis)).comp (LinearMap.proj i))
private lemma observed_apply (W : DiffPlan (Bel L)) (p q : Axis) (J : (Bel L).Stress) :
    observed W p q J = ∑ i : Axis, tester W i p q (J i 0) := by simp [observed]
private lemma vanishes (W : DiffPlan (Bel L)) {h : (Bel L).RealSpin} {J : (Bel L).Stress} (H : Table.Conserved W h J) (p q : Axis) :
    observed W p q J = 0 := by simp_rw [observed_apply,tester,LinearMap.restrictScalars_apply,LinearMap.comp_apply,← map_sum,H.divergence,map_zero]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private lemma calculations (W : DiffPlan (Bel L)) (hW : W.Derivatives (Bel L)) :
    let A := Types.A (pinned L); let B := Types.B (pinned L); let C := Types.C (pinned L); let F := observed W
    F 0 1 A = ↑(cost G * (-256)) ∧ F 1 2 A = 0 ∧ F 0 1 B = 0 ∧ F 1 2 B = ↑(cost G * (-256)) ∧
    F 0 1 C = ↑(cost G * 128) ∧ F 1 2 C = ↑(cost G * (-128)) := by
  dsimp only
  simp only [observed_apply,Fin.sum_univ_four,Types.A,Types.B,Types.C,Types.total,Types.contracted]; norm_num [Fin.ext_iff]
  simp only [test_value W hW]
  norm_num [row,curlOf, H0,H1,δ, Fin.ext_iff,Complex.real_smul]
  exact ⟨by ring,by ring,by ring,by ring⟩

theorem calibrated_line (h : G.Simple) (L : Register G) (T : Lighthouse L) (H : (Bel L).Hierarchy) (hW : T.W.Derivatives (Bel L))
    {τ : ℝ} (ht : τ ≠ 0) (hJ : T.J = τ • Types.stress (pinned L)) : Line T H.spin := by
  intro P ⟨hs,hr,hdiv⟩ hP hZ
  obtain ⟨x,y,z,rfl⟩ := (pairing_types L h H).spans H hP hr hZ
  let v := pinned L
  let t := x • Types.A v + y • Types.B v + z • Types.C v
  have hα : Table.Conserved T.W H.spin t := ⟨hs,hr,hdiv⟩
  obtain ⟨ha,ha',hb,hb',hc,hc'⟩ := calculations T.W hW
  have h₁ := vanishes _ hα 0 1
  have h₂ := vanishes _ hα 1 2
  dsimp only [t,v] at h₁ h₂
  rw [map_add,map_add,map_smul,map_smul,map_smul,ha,hb,hc] at h₁
  rw [map_add,map_add,map_smul,map_smul,map_smul,ha',hb',hc'] at h₂
  have h₁ := congrArg Complex.re h₁
  have h₂ := congrArg Complex.re h₂
  simp only [Complex.add_re, Complex.real_smul, Complex.re_ofReal_mul, Complex.ofReal_re, Complex.zero_re] at h₁ h₂
  have h₃ : cost G ≠ 0 := (cost_pos h).ne'
  have hx : z = 2*x := by apply mul_left_cancel₀ h₃; linarith
  have hy : y = -x := by apply mul_left_cancel₀ h₃; linarith
  refine ⟨(2*x)/τ,?_⟩
  rw [hx,hy,hJ,Types.stress_eq,smul_smul,smul_smul, div_mul_cancel₀ _ ht]; module
end YM.Extra.WeakScaling.Color

namespace YM.Extra.WeakScaling.Color
open Function Set Filter Analysis Labels Maxwell Tensor Cube Climb
open scoped Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge}

def viewing (L : Register G) (p q c d : Axis) := (Work.A15.front (Points.cons (basis 0) 0) (fun _ : Fin 1 => w L p q c d) 4).restrictScalars ℝ
private lemma amount (L : Register G) (p q c d a b i j : Axis) :
    viewing L p q c d (pinned L a b i j) = (↑(cost G *
      (curlOf H0 a b p q * curlOf H0 i j c d + curlOf H0 a b c d * curlOf H0 i j p q)) : ℂ) := by
  simp only [viewing, LinearMap.restrictScalars_apply, Work.A15.front_apply]; change Ward.disc _ _ = _
  rw [show Fin.cons (w L a b i j) (fun _ : Fin 1 => w L p q c d) = ![w L a b i j,w L p q c d] by funext k; fin_cases k <;> rfl]
  rw [show Ward.disc .. = _ from paired_eval L _ (clear (away_basis 0)) a b i j p q c d]
  congr 1
  unfold two cost
  change ↑G.lieDim * (bareCurl _ _ _ _ (basis 0-0)*bareCurl _ _ _ _ (basis 0-0) + bareCurl _ _ _ _ (basis 0-0)*bareCurl _ _ _ _ (basis 0-0)) = _
  simp only [sub_zero,is_curl _ _ _ _ (away_basis 0), curl_at]; ring

set_option maxHeartbeats 1000000 in
theorem tensor_detection (h : G.Simple) (L : Register G) (a b c : ℝ)
    (he : a • Types.A (pinned L) + b • Types.B (pinned L) + c • Types.C (pinned L) = 0) : a=0 ∧ b=0 ∧ c=0 := by
  have hd i j p q d e := congrArg (fun v : Table.Stress (Bel L) => viewing L p q d e (v i j)) he
  have ha := hd 0 0 0 1 0 1; have hb := hd 0 0 1 2 1 2; have hc := hd 0 1 0 2 1 2
  have ht : ∀ z : ℝ, cost G*z=0 → z=0 := fun _ e => (mul_eq_zero.mp e).resolve_left (cost_pos h).ne'
  simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply,Types.A,Types.B,Types.C,Types.total, Types.contracted,
    Fin.sum_univ_four, map_add, map_smul, map_zero] at ha hb hc
  norm_num [map_sub,map_smul, amount,curlOf,H0,δ,Fin.ext_iff] at ha hb hc
  replace ha := congrArg Complex.re ha
  norm_num at ha
  exact ⟨ht a (by linarith),hb.resolve_right (cost_pos h).ne',hc.resolve_right (cost_pos h).ne'⟩

lemma line_of_properties (h : G.Simple) {L : Register G} (T : Lighthouse L) (H : (Bel L).Hierarchy) (he : T.Goes L H.spin)
    (hJ : Table.Conserved T.W H.spin T.J) (hR : Table.RawTensor H.spin T.J) (h₀ : Centered T.J) : Line T H.spin := by
  let T' := { T with J := (1:ℝ) • Types.stress (pinned L) }
  have ht := calibrated_line h L T' H he.pales (τ:=1) one_ne_zero rfl
  obtain ⟨c,hc⟩ := ht T.J hJ hR h₀
  have hn : c≠0 := fun e => free_nonzero H he (hc.trans (by rw [e,zero_smul]))
  exact calibrated_line h L T H he.pales hn (hc.trans (by simp [T']))
end YM.Extra.WeakScaling.Color
