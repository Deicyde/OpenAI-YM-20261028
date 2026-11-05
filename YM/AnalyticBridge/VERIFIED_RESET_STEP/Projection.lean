import YM.AnalyticBridge.VERIFIED_RESET_STEP.Spin
import YM.Push.PRICE_COMPILER.Builders

/-! E:eq:FQaff--FDkin bilinear coefficients and prices on the actual germs.
Single-color charges normalized with a unit vector in the nonabelian Gauge.
No period-limit Fourier replacement. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset
open Function Filter Set Lattice Wilson RG StressFlux
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace Classical
variable {G : Gauge} {n : Side} {p : BudgetPoint} {X : Support n}

def spike (G : Gauge) : G.Color := if _h : Nontrivial G.Color then (exists_norm_eq G.Color zero_le_one).choose else 0
@[simp] lemma spike_norm (hG : G.Simple) : ‖spike G‖ = 1 := by
  haveI := hG.nontrivial_color; rw [spike,dif_pos hG.nontrivial_color]; exact (exists_norm_eq G.Color zero_le_one).choose_spec

private lemma wedge_add (o : Site n) (b : PlaqAxes) (x y : G.Color) :
    (wedge b (x+y)).field o = (wedge b x).field o + (wedge b y).field o := by funext e; simp [wedge_field,smul_add,ite_add_zero]
private lemma wedge_smul (o : Site n) (b : PlaqAxes) (r : ℝ) (x : G.Color) :
    (wedge b (r • x)).field o = r • (wedge b x).field o := by
  funext e; simp only [wedge_field,Pi.smul_apply]; split <;> first | exact smul_comm _ _ x | simp
private lemma wedge_adj (o : Site n) (b : PlaqAxes) (k : G.El) (x : G.Color) :
    (wedge b (G.adjoint k x)).field o = colorMove k ((wedge b x).field o) := by
  funext e; change _ = G.adjoint k _; simp [wedge_field,apply_ite (G.adjoint k)]

private def labelForm (f : Pot G n) (o : Site n) (b c : PlaqAxes) : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => logHessian f ((wedge b x).field o) ((wedge c y).field o))
    (by intros; simp only [hessian_eq,wedge_add,map_add,add_apply]) (by intros; simp only [hessian_eq,wedge_smul,map_smul,smul_apply])
    (by intros; simp only [hessian_eq,wedge_add,map_add]) (by intros; simp only [hessian_eq,wedge_smul,map_smul])

def coeff (f : Pot G n) (o : Site n) (b c : PlaqAxes) := labelForm f o b c (spike G) (spike G)

lemma label_color {f : Pot G n} (o : Site n) (hG : G.Simple) (hf : p.Regular X f) (b c : PlaqAxes) (x y : G.Color) :
    logHessian f ((wedge b x).field o) ((wedge c y).field o) = coeff f o b c * inner ℝ x y := by
  let M := labelForm f o b c
  have h (g : G.El) (x y : G.Color) : M (G.adjoint g x) (G.adjoint g y) = M x y := by
    change logHessian f _ _ = _; rw [wedge_adj,wedge_adj,hessian_color hG hf]; rfl
  obtain ⟨t,ht⟩ := bilinear_real hG M (bilinear_infinitesimal M h)
  change M x y = M (spike G) (spike G) * _; simp_rw [ht,real_inner_self_eq_norm_sq,spike_norm hG]; ring

lemma flux_formula (o : Site n) {f : Pot G n} (hG : G.Simple) (hf : p.Regular X f) (w z : Flux G) :
    logHessian f ((primitive w).field o) ((primitive z).field o) =
      ∑ i, ∑ j, coeff f o i j * inner ℝ (w i) (z j) := by
  rw [hessian_eq,primitive_field,map_sum,_root_.sum_apply]
  exact Finset.sum_congr rfl fun i _ => by
    rw [primitive_field,map_sum]; simp_rw [← hessian_eq]; exact Finset.sum_congr rfl fun j _ => label_color o hG hf i j ..


private lemma coeff_diag (hG : G.Simple) (o : Site n) {f : Pot G n} (hf : p.Regular X f) (b : PlaqAxes) :
    let u := p.threshold • (wedge b (spike G)).field o
    p.threshold^2 * coeff f o b b = leftDerivs f [u,u] 1 := by
  intro u; rw [← hessian_diag hG hf u]; simp only [u,hessian_eq,map_smul,smul_apply,smul_eq_mul]
  unfold coeff; change _ * logHessian _ _ _ = _; rw [hessian_eq]; ring
lemma coeff_diagonal (hG : G.Simple) {o : Site n} {f : Pot G n} (hf : p.Regular X f) {a : ℝ}
    (ha : p.supBounds o X f a) (b : PlaqAxes) : p.threshold^2 * |coeff f o b b| ≤ a := by
  have ho := p.order_ge
  let u := p.threshold • (wedge b (spike G)).field o
  rw [← abs_of_nonneg (sq_nonneg p.threshold),← abs_mul,coeff_diag hG o hf b]; apply ha.2 1 (flat_ok p X) [u,u] (by simp; omega)
  simp only [List.mem_cons,List.not_mem_nil,or_false,or_self,forall_eq]
  exact wedge_dir o p _ _ (spike_norm hG).le

private lemma coeff_avg (hG : G.Simple) (o : Site n) {f : Pot G n} (hf : p.Regular X f) (b c : PlaqAxes) :
    let w i := (wedge i (spike G)).field o
    let u := (p.threshold/2) • (w b + w c)
    4 * leftDerivs f [u,u] 1 = p.threshold^2 * (coeff f o b b + coeff f o c c + 2*coeff f o b c) := by
  intro w u
  rw [← hessian_diag hG hf u]
  simp only [u,hessian_eq,map_add,map_smul,add_apply,smul_apply,smul_eq_mul]
  change _ = _ * (logHessian f (w b) (w b) + logHessian f (w c) (w c) + 2*logHessian f (w b) (w c))
  simp_rw [← hessian_eq,hessian_symm hf (w c) (w b)]; ring

lemma coeff_bound (hG : G.Simple) {o : Site n} {f : Pot G n} (hf : p.Regular X f) {a : ℝ}
    (ha : p.supBounds o X f a) (b c : PlaqAxes) : p.threshold^2 * |coeff f o b c| ≤ 3*a := by
  have h := coeff_avg hG o hf b c
  dsimp only [] at h
  have ho := p.order_ge; let w i := (wedge i (spike G)).field o
  let u := (p.threshold/2) • (w b + w c)
  obtain ⟨hl,hr⟩ := abs_le.mp (ha.2 1 (flat_ok p X) [u,u] (by simp; omega) (by
    simp only [List.mem_cons,List.not_mem_nil,or_false,or_self,forall_eq]; exact wedge_avg o p b c _ (spike_norm hG).le))
  rw [← abs_of_nonneg (sq_nonneg p.threshold),← abs_mul]
  change 4*leftDerivs f [u,u] 1 = _ at h
  have hd (i) := abs_le.mp (show |p.threshold^2 * coeff f o i i| ≤ a by
    rw [abs_mul,abs_of_nonneg (sq_nonneg p.threshold)]; exact coeff_diagonal hG hf ha i)
  exact abs_le.mpr ⟨by linarith [(hd b).2,(hd c).2],by linarith [(hd b).1,(hd c).1]⟩

def expand (a : RegularAddress n) := a.support ∪ halo 2 {a.site}
def enlarges (a : RegularAddress n) : RegularAddress n := ⟨a.site,expand a,Finset.mem_union_left _ a.anchor⟩
def projection (a : RegularAddress n) (f : Pot G n) (i j : PlaqAxes) :=
    if Nonwrapping (expand a) a.site then coeff f a.site i j else 0

def quad (q : PlaqAxes → PlaqAxes → ℝ) (w z : Flux G) := ∑ i, ∑ j, q i j * inner ℝ (w i) (z j)
lemma projection_eq {a : RegularAddress n} {f : Pot G n} (hG : G.Simple) (hf : p.Regular a.support f)
    (ha : Nonwrapping (expand a) a.site) (w z : Flux G) :
    quad (projection a f) w z = logHessian f ((primitive w).field a.site) ((primitive z).field a.site) := by
  rw [flux_formula a.site hG hf]; simp only [quad, projection,if_pos ha]
lemma projection_bound (a : RegularAddress n) {f : Pot G n} (hG : G.Simple) (hf : p.Regular a.support f)
    {c : ℝ} (h : p.supBounds a.site a.support f c) (i j : PlaqAxes) :
    p.threshold^2 * |projection a f i j| ≤ 3*c := by
  unfold projection; split
  · exact coeff_bound hG hf h i j
  simp only [abs_zero,mul_zero]; linarith only [h.1]
lemma projection_diag (a : RegularAddress n) {f : Pot G n} (hG : G.Simple) (hf : p.Regular a.support f)
    {c : ℝ} (h : p.supBounds a.site a.support f c) (i : PlaqAxes) :
    p.threshold^2 * |projection a f i i| ≤ c := by
  unfold projection; split
  · exact coeff_diagonal hG hf h i
  simpa using h.1

private lemma halo_image (s : Signed) (b x : Site n) (j : ℕ) : halo j {affine s b x} = (halo j {x}).image (affine s b) := by
  ext y; obtain ⟨z,rfl⟩ := (Finite.injective_iff_surjective (f:=affine s b) |>.mp (fun q r (h : affine s b q = affine s b r) => s.act_injective (add_right_cancel h))) y
  simp only [Finset.mem_image,halo_spec,Finset.mem_singleton,exists_eq_left,affine,add_left_inj,s.act_injective.eq_iff]
  simp
lemma expand_moves (a d : RegularAddress n) (s : Signed) (b : Site n) (hd : d.support = a.support.image (affine s b))
    (h : d.site = affine s b a.site) : expand d = (expand a).image (affine s b) := by
  rw [expand, expand, Finset.image_union, hd,h,halo_image]
lemma quad_moves (s : Signed) (b : Site n) (hn : 4 ≤ n.val) {a d : RegularAddress n} (hd : d.support = a.support.image (affine s b))
    (h : d.site = affine s b a.site) {f g : Pot G n} (hG : G.Simple) (hf : p.Regular a.support f) (hg : p.Regular d.support g)
    (he : g = f ∘ pull s b) (w z : Flux G) : quad (projection d g) w z = quad (projection a f) (reframe w s) (reframe z s) := by
  have ha : Nonwrapping (expand d) d.site ↔ Nonwrapping (expand a) a.site := expand_moves a d s b hd h ▸ h ▸ spin_wrap ..
  by_cases hr : Nonwrapping (expand a) a.site
  · rw [projection_eq hG hf hr,projection_eq hG hg (ha.mpr hr), h, he]
    exact flux_hessian_pull s b _ hG hf (fun x hx => hr x (Finset.mem_union_left _ hx)) hn w z
  simp [quad,projection,hr, ha]
end YM.AnalyticBridge.VerifiedReset
