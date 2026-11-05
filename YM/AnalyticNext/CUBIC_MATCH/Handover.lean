import YM.AnalyticNext.CUBIC_MATCH.Lift.Atoms
import YM.Progress.JOINT_CALENDAR.Germs


set_option warningAsError false

/-!
# Cubic handover from the estimate on the link-space residual

Requirements here include actual funded estimates (not proved HERE). But no
needed hypotheses on cubic curvature correction existence, gauge completion,
or exterior lift. Caller owes the real kernel price on actual third derivative
BEFORE such construction, attaining positive width indep of unknown input
path caps. This applies to the genuine top Wilson too. `SameJet 3` after
these costed data: *no cancellation* with particular choice of quartic or
loop required at order three. Keep them free for subsequent invoices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch
open Function Filter RG Precision Tree Progress.StationaryScenes Bid Lift Lattice Wilson Exterior Work.F03
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
variable {G : Gauge}

abbrev baseline (q : Clip) (T : PathData G) {n : Side} (x : Dir G n) := secondTerm q T (represent x)

section local_jet
variable {n : Side} {σ C Λ : ℝ} {q : Clip} {T : PathData G} {V : ℕ → Atom G 3}

lemma aware (h : T.Bounds q σ C Λ) : Checks n (baseline q T) := by
  apply checksRead _ _ (quadratic_invariant h) quadratic_rotated
  unfold secondTerm Patch.average; apply contDiffAt_const.mul
  refine ContDiffAt.sum fun i _ => Work.F02.quadratic_contDiffAt (A:=fun x : Dir G n => pull i 0 (represent x)) h
    (Progress.Joint.pulled_smooth _ (fun i => (represent_smooth i).contDiffAt) _)

lemma along_baseline {P : PathData G} (h : P.row=T.row) : baseline (n:=n) q P = baseline q T := by
  funext i; simp_rw [baseline,secondTerm,quadratic,PathData.ell,PathData.ellTerms,h]

lemma first_coeff (h : T.Bounds q σ C Λ) (x : Dir G n) :
    term 3 (fun t : ℝ => mainTerm q T (represent (t • x))) =
      term 3 (fun t : ℝ => baseline q T (t • x)) +
        Patch.average (fun s : Signed => term 3 (fun t : ℝ => uncut T.cubic (represent (t • rotate s x)))) := by
  unfold mainTerm baseline secondTerm Patch.average; simp_rw [represent_pulled]
  have hh (f : Signed → ℝ → ℝ) (hf : ∀ i, ContDiffAt ℝ ω (f i) 0) :
      term 3 (fun t : ℝ => (Fintype.card Signed:ℝ)⁻¹ * ∑ i,f i t)=(Fintype.card Signed:ℝ)⁻¹*∑ i,term 3 (f i) := by
    rw [show term 3 (fun t : ℝ => (Fintype.card Signed:ℝ)⁻¹ * ∑ i,f i t)=(Fintype.card Signed:ℝ)⁻¹*term 3 (fun t => ∑ i,f i t) from
      term_scaled (g:=fun t => ∑ i,f i t) _ (ContDiffAt.sum (fun i _ => hf i)),term_sum (g:=f) (s:=Finset.univ) (fun i _ => (hf i).of_le le_top)]
  have hM (i) : ContDiffAt ℝ ω (fun t : ℝ => quadratic q T (represent (t • pulled x i))) 0 :=
    Work.F02.quadratic_contDiffAt (A:=fun t : ℝ => represent (t • pulled x i)) h (test_ray _)
  have ht (i) : ContDiffAt ℝ ω (fun t : ℝ => uncut T.cubic (represent (t • pulled x i))) 0 :=
    Work.F02.uncut_contDiffAt (A:=fun t : ℝ => represent (t • pulled x i)) h.width h.three (test_ray _)
  have hq (i) : ContDiffAt ℝ ω (fun t : ℝ => uncut T.quartic (represent (t • pulled x i))) 0 :=
    Work.F02.uncut_contDiffAt (A:=fun t : ℝ => represent (t • pulled x i)) h.width h.four (test_ray _)
  rw [hh _ (fun i => ((hM i).add (ht i)).add (hq i)), hh _ hM,← mul_add,← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have he := (preamble h.width h.four (pulled x i)).2 3 (by omega)
  change _ = term 3 (fun t => _) + term 3 (fun t : ℝ => uncut T.cubic (represent (t • pulled x i)))
  have hj := term_add (k:=3) (((hM i).add (ht i)).of_le le_top) ((hq i).of_le le_top)
  simp only [he,add_zero] at hj
  exact hj.trans (congr_arg id (term_add ((hM i).of_le le_top) ((ht i).of_le le_top)))

/-- The price part of the cubic invoice (true path, invariant color). Not a
comparison of the purely direct branch, nor of the quadratic data. -/
def Flies (θ A : ℝ) (V : ℕ → Atom G 3) : Prop :=
    SumBudget (fun i => (V i).budget θ) A ∧ ∀ i, (V i).Invariant

lemma same_three {K : Stored G} {θ B} (hθ : 0<θ) (hB : 0≤B) (p : Pace θ B K) (h : T.Bounds q σ C Λ)
    {F : Dir G n → ℝ} (hf : Checks n F) {P : PathData G} {a v z} (hP : P.Bounds q a v z)
    (g : P.row=T.row) (w : P.cubic=plant3 K)
    (e : ∀ x : Dir G n, pair3 (completely K) x x x=Tensor.diagonal (Tensor.coeff (F-baseline q T) 3 0) x) :
    SameJet 3 F fun x => mainTerm q P (represent x) := by
  let K₀ : Dir G n → ℝ := baseline q T
  let L : Dir G n → ℝ := fun x => mainTerm q P (represent x)
  have hr : Checks n K₀ := aware h
  have hs : ContDiffAt ℝ ω L 0 := Work.F02.mainTerm_contDiffAt (A:=fun x : Dir G n => represent x) hP fun i =>
    (represent_smooth (G:=G) _).contDiffAt
  have he : ∀ i x, term 3 (fun t : ℝ => uncut P.cubic (represent (t • rotate (G:=G) (n:=n) i x))) =
      term 3 (fun t : ℝ => F (t • x))-term 3 (fun t : ℝ => K₀ (t • x)) := by
    intro i x
    rw [w,plant3_third p hθ hB, e,← term_ray ((hf.inherited hr).analytic.of_le le_top)]
    simp_rw [← map_smul]
    rw [(hf.inherited hr).rotated]
    have hx : ContDiffAt ℝ ω (fun t : ℝ => t • x) 0 := by fun_prop
    have h1 : ContDiffAt ℝ ω F ((0:ℝ) • x) := by rw [zero_smul]; exact hf.analytic
    have h2 : ContDiffAt ℝ ω K₀ ((0:ℝ) • x) := by rw [zero_smul]; exact hr.analytic
    exact term_sub ((h1.comp 0 hx).of_le le_top) ((h2.comp 0 hx).of_le le_top)
  have hm (x : Dir G n) : Tensor.diagonal (Tensor.coeff F 3 0) x=Tensor.diagonal (Tensor.coeff L 3 0) x := by
    rw [← term_ray (hf.analytic.of_le le_top), ← term_ray (f:=L) (hs.of_le le_top)]; unfold L
    rw [first_coeff hP, along_baseline g]
    simp_rw [he]; rw [Patch.average,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      inv_mul_cancel_left₀ (by exact_mod_cast (Fintype.card_pos (α:=Signed)).ne')]; unfold K₀; abel
  refine ⟨hf.analytic,hs,?_⟩
  apply smul_right_injective (Tensor.T (Dir G n) ℝ 3) (inv_ne_zero (show ((3:ℕ).factorial:ℝ)≠0 from by positivity))
  exact Tensor.ext_diag (Tensor.coeff F 3 0) (Tensor.coeff L 3 0) (Tensor.coeff_symm (hf.analytic.of_le le_top))
    (Tensor.coeff_symm (hs.of_le le_top)) (funext hm)


end local_jet

/-- Interface useful even with `q` already fixed. `F` the actual StationValue
(or top Wilson). Quantitative estimate REQUIRED on its whole-cover scalar
LINK kernel. This port doesn't postulate basis rearrangements or any identity
with candidate output curvature data. Needs the 0/1/2 matches from RScene.
Hands over actual CURVATURE-kernel PathData.cubic entries with true cost.
Widths determined before volume or size of input cap.
-/
theorem earn (G : Gauge) {η : ℝ} (he : 0<η) : ∃ θ D : ℝ, 0<θ ∧ 0<D ∧
    ∀ (n : ℕ → Side) (_ : Tendsto (fun i => (n i).val) atTop atTop) (q : Clip) (P : PathData G) (b v z : ℝ),
    P.Bounds q b v z → ∀ F : ∀ i, Dir G (n i) → ℝ, (∀ i,Checks (n i) (F i)) →
    (∀ i, SameJet 1 (F i) (baseline q P)) → (∀ i, SameJet 2 (F i) (baseline q P)) →
    ∀ C : ℝ, 0≤C → ∀ K : Three (Shades G) 1 1 1, Pace η C K →
    (∀ p, ∀ x y t,pair3 (n:=n p) K x y t=Tensor.coeff (F p-baseline q P) 3 0 ![x,y,t]) →
      ∃ R : ℕ → Atom G 3, Flies θ (D*C) R ∧ ∀ σ B Λ (T : PathData G), T.Bounds q σ B Λ → T.row=P.row → T.cubic=R →
        ∀ i, SameJet 3 (F i) fun x => mainTerm q T (represent x) := by
  obtain ⟨θ,D,hθ,hD,H⟩ := paid_lift G he
  let M := bookFee G θ *D+1; have hp : 0<M := add_pos_of_nonneg_of_pos (mul_nonneg (bookFee_nonneg ..) hD.le) one_pos
  refine ⟨θ/2,M,half_pos hθ,hp,fun n hn q P b v z hP F hf h₁ h₂ C hC K hK hx => ?_⟩
  let L i := F i-baseline q P
  have hh i : Checks _ (L i) := Checks.inherited (hf i) (aware hP)
  have hz i : iteratedFDeriv ℝ 2 (L i) 0=0 := by
    unfold L
    obtain ⟨ha,hb,hq⟩ := h₂ i; rw [iteratedFDeriv_sub_apply (ha.of_le le_top) (hb.of_le le_top),hq,sub_self]
  have hL i : fderiv ℝ (L i) 0=0 := by
    obtain ⟨ha,hb,hq⟩ := h₁ i
    unfold L; rw [fderiv_sub (ha.differentiableAt (by simp)) (hb.differentiableAt (by simp))]; apply sub_eq_zero.mpr
    apply ContinuousLinearMap.ext; intro v
    have he := DFunLike.congr_fun hq (fun _ => v); simp only [iteratedFDeriv_one_apply] at he; exact he
  obtain ⟨ha,hα,hβ,hγ⟩ := shadows hK he hn hh hL hz hx
  obtain ⟨X,hx',hp',hX⟩ := H _ hC K hK ha hα hβ hγ
  have hv : 0 ≤ D*C := mul_nonneg hD.le hC
  have hg := plant3_quote hx' hθ hv
  refine ⟨plant3 X,⟨⟨hg.1,hg.2.1,hg.2.2.trans ?_⟩,plant3_valid hp'⟩, fun σ B Λ T hT ht hj i =>
      same_three hθ hv hx' hP (hf i) hT ht hj (fun a => ?_)⟩
  · unfold M; rw [add_mul,one_mul,mul_assoc]; linarith
  rw [hX,hx]
  unfold Tensor.diagonal; congr 1; ext1 i; fin_cases i <;> rfl
end YM.CubicMatch
