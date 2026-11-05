import YM.Extra.WILSON_STARTUP.Curvature

/-!
# Uniform normalized derivatives of the one-face Wilson matching residual

Estimate in through-order Left increment derivatives, on genuine group fields,
by plaquette smallness. In particular no bound on log of individual links and
no gauge fixing of a torus; all estimates here work with wrapping and at
threshold equality. Constants before coupling and torus choice.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup
open Function Filter Work Tensor Next.Fluctuations Lattice Wilson RG
open scoped ContDiff Topology Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge}

namespace Quad
abbrev Space (G : Gauge) := Fin 4 → G.Mat
abbrev Dir (G : Gauge) := Fin 4 → G.Color
abbrev Group (G : Gauge) := Fin 4 → G.El
abbrev mat (u : Group G) : Space G := fun i => G.mat (u i)

def readMat (X : Space G) := X 0 * X 1 * star (X 2) * star (X 3)

def read (X : Group G) := X 0 * X 1 * (X 2)⁻¹ * (X 3)⁻¹

def kMat (X : G.Mat) := G.projectColor ((1/2 : ℝ) • (X - star X))

def distMat (X : G.Mat) := ‖X-1‖^2/G.colorScale^2/2

def surplusMat (X : G.Mat) := distMat X - ‖kMat X‖^2/2 - diagonal (fourth G) (kMat X)

def spin (a : Dir G) (X : Space G) : Space G := fun i => G.mat (G.lieExp (a i)) * X i

def jet : List (Dir G) → Space G → ℝ
  | [] => surplusMat ∘ readMat
  | a :: l => fun X => deriv (fun t : ℝ => jet l (spin (t • a) X)) 0

theorem k_actual (u : G.El) : kMat (G.mat u) = G.curvature u := by
  rw [Gauge.curvature,G.mat_inv]; rfl

theorem surplus_actual (u : G.El) : surplusMat (G.mat u) = surplus u := by
  rw [surplusMat,k_actual,surplus,distMat,← div_pow]
  change G.chord u ^ 2 / 2 - _ - _ = _
  rw [G.chord_price]; ring

theorem read_actual (U : Group G) : readMat (mat U) = G.mat (read U) := by
  simp only [read,G.mat_mul,G.mat_inv]; rfl

@[fun_prop] theorem kMat_diff : ContDiff ℝ ω (kMat (G:=G)) := by
  refine ContDiff.comp (g:=G.projectColor.toContinuousLinearMap) (f:=fun x => _ • (x - star x)) (by fun_prop) ?_
  exact (contDiff_id.sub ((starL ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff)).const_smul _

@[fun_prop] theorem surplusMat_diff : ContDiff ℝ ω (surplusMat (G:=G)) := by
  have he : ContDiff ℝ ω (distMat (G:=G)) := (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).div_const _).div_const _
  exact (he.sub (((contDiff_norm_sq ℝ).comp kMat_diff).div_const _)).sub ((diag_smooth _ _).comp kMat_diff)

@[fun_prop] theorem readMat_diff : ContDiff ℝ ω (readMat (G:=G)) := by
  unfold readMat
  have hs (i : Fin 4) : ContDiff ℝ ω fun U : Space G => star (U i) :=
    (starL ℝ (A:=G.Mat)).contDiff.comp (contDiff_apply ..)
  exact (((contDiff_apply ..).mul (contDiff_apply ..)).mul (hs 2)).mul (hs 3)

@[fun_prop] theorem spin_diff : ContDiff ℝ ω (uncurry (spin (G:=G))) := by
  refine contDiff_pi.mpr fun i => ?_
  exact ((G.exp_jet.comp (contDiff_apply ..)).comp contDiff_fst).mul ((contDiff_apply ..).comp contDiff_snd)

theorem jet_diff (k : ℕ) : ContDiff ℝ ω fun p : (Fin k → Dir G) × Space G => jet (List.ofFn p.1) p.2 := by
  induction k with
  | zero =>
    simp only [List.ofFn_zero, jet]
    exact (surplusMat_diff.comp readMat_diff).comp contDiff_snd
  | succ k ih =>
    let V (p : (Fin (k+1) → Dir G) × Space G) (s : ℝ) := jet (List.ofFn (Fin.tail p.1)) (spin (s • p.1 0) p.2)
    have ht : ContDiff ℝ ω (uncurry V) := by
      exact ih.comp ((contDiff_pi.mpr fun i => (contDiff_apply ..).comp contDiff_fst.fst).prodMk
        (spin_diff.comp ((contDiff_snd.smul ((contDiff_apply ..).comp contDiff_fst.fst)).prodMk contDiff_fst.snd)))
    simp only [List.ofFn_succ,jet, deriv]
    exact (ht.fderiv (g:=fun _ => 0) contDiff_const le_top).clm_apply (g:=fun _ => (1:ℝ)) contDiff_const

theorem jet_smul (r : ℝ) (l : List (Dir G)) (X : Space G) :
    jet (l.map (fun a => r • a)) X = r^l.length * jet l X := by
  induction l generalizing X with
  | nil => simp [jet]
  | cons a l ih =>
    simp only [List.map_cons, jet, List.length_cons, ih, smul_smul, mul_comm _ r,
      deriv_const_mul_field, deriv_comp_mul_left r (fun t => jet l (spin (t • a) X)),mul_zero,smul_eq_mul,pow_succ,mul_assoc]
    ring

/-- Each differentiation can reduce the vanishing order by at most one along any
smooth family of actual links with base curvature element identity (not merely k=0). -/
theorem jet_flat (l : List (Dir G)) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : E → Group G) (h : ContDiff ℝ ω (mat ∘ U)) (hz : read (U 0) = 1) :
    FlatAt (5-l.length) (jet l ∘ mat ∘ U) 0 := by
  induction l generalizing E with
  | nil =>
    rw [show jet ([]:List (Dir G)) ∘ mat ∘ U = surplus ∘ read ∘ U from funext fun x => by simp only [jet,comp_apply,read_actual,surplus_actual]]
    exact surplus_jet _ hz (by
      simp only [comp_apply, ← read_actual]
      exact (readMat_diff.comp h).contDiffAt)
  | cons a l ih =>
    let Q (v : E × ℝ) (i : Fin 4) := G.lieExp (v.2 • a i) * U v.1 i
    have hm : mat ∘ Q = uncurry spin ∘ fun x => (x.2 • a, mat (U x.1)) := by funext x i; exact G.mat_mul ..
    have hQ : ContDiff ℝ ω (mat ∘ Q) := by
      rw [hm]; exact spin_diff.comp ((contDiff_snd.smul contDiff_const).prodMk (h.comp contDiff_fst))
    have hf := ih Q hQ (by simpa [Q] using hz)
    rw [List.length_cons, ← Nat.sub_sub]; change FlatAt _ (fun x => deriv _ 0) _
    refine hf.partial_zero ?_
    rw [← List.ofFn_get l]
    exact (jet_diff l.length).comp (contDiff_const.prodMk hQ)

/-- Parametrize link 0 by the remaining three and the face log (near small
chord), to get a single compact-parameter estimate. -/
def reconstruct (W : Space G) (x : G.Color) : Space G := fun i => if i=0 then
    G.mat (G.lieExp x) * W 3 * W 2 * star (W 1) else W i

theorem reconstruct_diff : ContDiff ℝ ω (uncurry (reconstruct (G:=G))) := by
  have hs (i : Fin 4) : ContDiff ℝ ω fun p : Space G × G.Color => p.1 i := (contDiff_apply ..).comp contDiff_fst
  refine contDiff_pi.mpr fun i => ?_
  dsimp [uncurry,reconstruct]
  split
  · exact (((G.exp_jet.comp contDiff_snd).mul (hs _)).mul (hs _)).mul ((starL ℝ (A:=G.Mat)).contDiff.comp (hs _))
  exact hs _

theorem reconstruct_flat (U : Group G) (l : List (Dir G)) : FlatAt (5-l.length) (jet l ∘ reconstruct (mat U)) 0 := by
  let V (x : G.Color) (i : Fin 4) := if i=0 then G.lieExp x * U 3 * U 2 * (U 1)⁻¹ else U i
  have he : reconstruct (mat U) = mat ∘ V := by
    ext1 x; ext1 i
    dsimp only [reconstruct,comp_apply,mat,V]; split <;> simp [*,G.mat_mul,G.mat_inv]
  rw [he]
  refine jet_flat l V (he ▸ reconstruct_diff.comp (contDiff_const.prodMk contDiff_id)) ?_
  simp [V,read,mul_assoc]

theorem reconstructed (U : Group G) {x : G.Color} (h : G.lieExp x = read U) :
    reconstruct (mat U) x = mat U := by
  ext1 i
  simp only [reconstruct,h,mat,← G.mat_inv,← G.mat_mul]
  split
  · simp [*, read, mul_assoc]
  rfl

lemma unscaled_bound (G : Gauge) (k : ℕ) (r : ℝ) : ∃ c : ℝ, 0 < c ∧
    ∀ (a : Fin k → Dir G), ‖a‖ ≤ r → ∀ (U : Group G) (x : G.Color), ‖x‖ ≤ 1 → G.lieExp x = read U →
      ‖jet (List.ofFn a) (mat U)‖ ≤ c*‖x‖^(5-k) := by
  let L (p : (Fin k → Dir G) × Space G) (x : G.Color) := jet (List.ofFn p.1) (reconstruct p.2 x)
  have hd : ContDiff ℝ ω (uncurry L) := (jet_diff k).comp (contDiff_fst.fst.prodMk (reconstruct_diff.comp
    (contDiff_fst.snd.prodMk contDiff_snd)))
  let K : Set ((Fin k → Dir G) × Space G) := Metric.closedBall 0 r ×ˢ Set.range mat
  obtain ⟨C,hC,he⟩ := uniform_flat_price K ((isCompact_closedBall _ _).prod (isCompact_range (f:=mat) (by unfold mat; fun_prop)))
    1 L hd (fun _ => True) (5-k) (by
      rintro ⟨a,W⟩ ⟨-,u,hu⟩ -
      change mat u = W at hu
      subst W
      simpa only [L,List.length_ofFn,Function.comp_def] using reconstruct_flat u (List.ofFn a))
  refine ⟨C,hC, fun a ha U x hx hz => ?_⟩
  have h := he (a,mat U) ⟨by simpa using ha,Set.mem_range_self U⟩ trivial x hx
  simpa only [L,reconstructed U hz] using! h

lemma small_jet (G : Gauge) (k : ℕ) (r : ℝ) : ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ δ ≤ 1 ∧
    ∀ (U : Group G) (a : Fin k → Dir G) (t : ℝ), 0 < t → t ≤ δ → ‖a‖ ≤ t*r → G.chord (read U) ≤ t →
      ‖jet (List.ofFn a) (mat U)‖ ≤ C*t^5 := by
  obtain ⟨c,b,hc,hb,h⟩ := log_chart_cost G
  obtain ⟨p,hp,h'⟩ := unscaled_bound G k r
  let δ := min (min b c⁻¹) 1
  refine ⟨p*c^(5-k),δ, by positivity, lt_min (lt_min hb (inv_pos.mpr hc)) one_pos, min_le_right ..,?_⟩
  intro U a t ht ht' ha hu
  have hs := le_min_iff.mp ht'
  obtain ⟨h₁,h₂⟩ := le_min_iff.mp hs.1
  have hl := h (read U) (hu.trans h₁)
  have hx := hl.2.trans (mul_le_mul_of_nonneg_left hu hc.le)
  have hy : ‖t⁻¹ • a‖ ≤ r := by
    rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr ht).le]
    exact (mul_le_mul_of_nonneg_left ha (inv_pos.mpr ht).le).trans_eq (inv_mul_cancel_left₀ ht.ne' _)
  have hp' := h' (t⁻¹ • a) hy U _ (hx.trans ((mul_le_mul_of_nonneg_left h₂ hc.le).trans_eq (mul_inv_cancel₀ hc.ne'))) hl.1
  have he := jet_smul t (List.ofFn (t⁻¹ • a)) (mat U)
  simp only [List.length_ofFn,List.map_ofFn,comp_def,Pi.smul_apply,smul_smul,mul_inv_cancel₀ ht.ne',one_smul] at he
  rw [he,norm_mul,Real.norm_of_nonneg (pow_pos ht _).le]
  refine (mul_le_mul_of_nonneg_left (hp'.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx _) hp.le))
    (pow_nonneg ht.le _)).trans ?_
  rw [mul_pow, show t^k * (p*(c^(5-k)*t^(5-k))) = p*c^(5-k)*t^(k+(5-k)) by rw [pow_add]; ring]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht.le hs.2 (by omega)) (by positivity)
end Quad
end YM.WilsonStartup
