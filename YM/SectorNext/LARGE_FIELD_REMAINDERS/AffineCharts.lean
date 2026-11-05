import YM.Next.FLUCTUATIONS.Charts
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Delay
import YM.Shift.Breath
import YM.Work.A09
import YM.Work.B04


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Response analytic lemma for actual affine subtraction

Relative displacement increments and base logs both small; read true Q (or
all-choices local function), compare its curvature error with a directional
derivative of *relative Q* at the specified base. In particular can use at
nonflat V, and with opposite sign tangent for noise: no identifying Q- and
V- adjoints on inversions. Here no period estimates or hypotheses presumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder.Affine
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial  Next.Fluctuations Scales Metric   Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical  ContDiff

section jets
variable {E F C : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup C] [NormedSpace ℝ C] (f g : E × F → C)

/-- a × b variable, t along a at current small b. -/
def response (a : E) (b : F) := deriv (fun t : ℝ => g (t • a,b)) 0

private lemma stem (a : E) (b : F) : HasDerivAt (fun s : ℝ => (s • a,b)) (a,(0:F)) 0 := by
  simpa using! (((hasDerivAt_id' 0).smul_const a).prodMk (hasDerivAt_const (0:ℝ) b))

private lemma comes (a : E) (b : F) (h : DifferentiableAt ℝ f (0,b)) :
    HasDerivAt (fun s : ℝ => f (s • a,b)) (response f a b) 0 ∧ response f a b=fderiv ℝ f (0,b) (a,0) := by
  have he : HasDerivAt (fun s : ℝ => f (s • a,b)) (fderiv ℝ f (0,b) (a,0)) 0 := by
    have h' : DifferentiableAt ℝ f ((0:ℝ) • a,b) := by simpa
    convert! h'.hasFDerivAt.comp_hasDerivAt 0 (stem a b) using 1; simp
  exact ⟨he.differentiableAt.hasDerivAt,he.deriv⟩

/-- Compare f to the indicated tangent g. Treating both a and b as
small, okay to lose an h² even when a=0. For K-germs involving logs
this only asserts in the common neighborhoods of the standardized
identity chart. -/
lemma charts (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0)
    (s : ℝ) (h : f 0=0) (ha : ∀ (v : E), f (v,0)=s • g (v,0)) :
    ∃ C r : ℝ, 0<C ∧ 0<r ∧ ∀ (u : ℝ), 0 ≤ u → u ≤ r → ∀ (v : E) (w : F),
      ‖v‖ ≤ u → ‖w‖ ≤ u →
      DifferentiableAt ℝ (fun t : ℝ => g (t • v,w)) 0 ∧
      ‖f (v,w) - (f (0,w)+s • response g v w)‖ ≤ C*u^2 ∧
        ‖f (v,w)‖ ≤ C*u ∧ ‖f (0,w)‖ ≤ C*u ∧ ‖response g v w‖ ≤ C*u := by
  let A := fderiv ℝ f 0
  let D := fderiv ℝ g
  have h1 a : HasDerivAt (fun v : ℝ => f (v • a)) (A a) 0 := by
    have he : HasFDerivAt f A ((0:ℝ) • a) := by rw [zero_smul]; exact (hf.differentiableAt (by simp)).hasFDerivAt
    simpa only [one_smul,Function.comp_def] using! he.comp_hasDerivAt 0 (by simpa using (hasDerivAt_id' (0:ℝ)).smul_const a : HasDerivAt (fun v : ℝ => v • a) a 0)
  have he : ContDiffAt ℝ ω D 0 := hg.fderiv_right (by simp)
  obtain ⟨C',r₁,hC,hr,h₁⟩ := chart_quadratic_cost f A hf.analyticAt h1
  obtain ⟨B,r₂,hB,hr',H⟩ := chart_linear_cost D 0 he.analyticAt
  obtain ⟨r₃,hr₃,h3⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp (hg.eventually (by simp))
  let r := min r₁ (min r₂ (min r₃ 1))
  have hR : 0<r := lt_min hr (lt_min hr' (lt_min hr₃ zero_lt_one))
  let C₀ := 2*C'+(|s|+1)*B+‖D 0‖
  have hsC : 2*C' ≤ C₀ := by
    unfold C₀
    have h : 0≤(|s|+1)*B := by positivity
    have hz := norm_nonneg (D 0); linarith
  refine ⟨C₀,r,hC.trans_le (by linarith),hR,?_⟩
  intro u hu hw v w hv hw'
  have hV : ‖(v,w)‖ ≤ u := max_le hv hw'
  have hW : ‖((0:E),w)‖ ≤ u := max_le (by rwa [norm_zero]) hw'
  have hk : DifferentiableAt ℝ g (0,w) := (h3 (x:=((0:E),w)) (by rw [Metric.mem_closedBall,dist_zero_right]; exact hW.trans (hw.trans ((min_le_right ..).trans ((min_le_right ..).trans (min_le_left ..)))))).differentiableAt (by simp)
  have h0 := comes g v w hk
  have hi : ‖D (0,w)-D 0‖ ≤ B*u := by
    apply (H (0,w) (by rw [sub_zero]; exact hW.trans (hw.trans ((min_le_right ..).trans (min_le_left ..))))).trans
    rw [sub_zero]; gcongr
  have hx : u≤1 := hw.trans ((min_le_right ..).trans ((min_le_right ..).trans (min_le_right ..)))
  let J (v : E × F) := D 0 v
  have hJ : ‖(v,(0:F))‖ ≤ u := max_le hv (by rwa [norm_zero])
  have hf0 : response f v 0=A (v,(0:F)) := (comes f v 0 (hf.differentiableAt (by simp))).2
  have hg0 := (comes g v (0:F) (hg.differentiableAt (by simp))).1
  have hβ : A (v,(0:F))=s • J (v,0) := by
    rw [← hf0]; unfold response; simp only [ha]
    have hx : response g v (0:F)=D 0 (v,(0:F)) := (comes g v (0:F) (hg.differentiableAt (by simp))).2
    exact ((hg0.const_smul s).deriv).trans (congr_arg (s • ·) hx)
  have hJ' : ‖J (v,0)‖ ≤ ‖D 0‖ * u := ((D 0).le_opNorm _).trans (mul_le_mul_of_nonneg_left hJ (norm_nonneg _))
  have hn : ‖response g v w - J (v,0)‖ ≤ B*u^2 := by
    rw [h0.2]; change ‖((D (0,w) - D 0) (v, (0:F)))‖ ≤ _
    exact ((D (0,w)-D 0).le_opNorm _).trans ((mul_le_mul hi hJ (norm_nonneg _)
      (mul_nonneg hB.le hu)).trans_eq (by ring))
  have hl (z : E × F) (hy : ‖z‖ ≤ u) : ‖f z-A z‖ ≤ C'*u^2 := by
    have he := ((h₁ z).2 (hy.trans (hw.trans (min_le_left ..)))).trans (show C'*‖z‖^2 ≤ C'*u^2 by gcongr)
    simpa only [h, zero_add] using! he
  have hw (z : E × F) (hy : ‖z‖ ≤ u) : ‖f z‖ ≤ C₀*u := by
    have hc := hl z hy
    have hw := ((h₁ z).1).trans (mul_le_mul_of_nonneg_left hy hC.le)
    calc
      _ = ‖(f z-A z)+A z‖ := by rw [sub_add_cancel]
      _ ≤ _ := (norm_add_le ..).trans ((add_le_add hc hw).trans (by nlinarith [mul_le_mul_of_nonneg_left (mul_self_le_mul_self hu hx) hC.le, mul_le_mul_of_nonneg_right hsC hu, mul_le_mul_of_nonneg_left hx (mul_nonneg hC.le hu)]))
  refine ⟨h0.1.differentiableAt,?_,hw _ hV,hw _ hW,?_⟩
  · have HE : (v,w)=(v,0)+(0,w) := by simp [Prod.mk_add_mk]
    have hh : A (v,w)=s • J (v,0)+A (0,w) := by rw [HE,map_add,hβ]
    rw [show f (v,w) - (f ((0:E),w)+s • response g v w)=
      ((f (v,w)-A (v,w))-(f (0,w)-A (0,w)))-s • (response g v w-J (v,0)) by rw [hh,smul_sub]; abel]
    apply (norm_sub_le ..).trans ((add_le_add_left (norm_sub_le ..) _).trans ?_); rw [norm_smul,Real.norm_eq_abs]
    have h1 := hl (v,w) hV; have h2 := hl (0,w) hW
    unfold C₀
    nlinarith only [h1,h2,mul_le_mul_of_nonneg_left hn (abs_nonneg s),
      mul_nonneg hB.le (sq_nonneg u),mul_nonneg (norm_nonneg (D 0)) (sq_nonneg u)]
  · calc
      _ = ‖(response g v w-J (v,0))+J (v,0)‖ := by rw [sub_add_cancel]
      _ ≤ _ := (norm_add_le ..).trans ((add_le_add hn hJ').trans ?_)
    unfold C₀
    nlinarith only [mul_le_mul_of_nonneg_left hx (mul_nonneg hB.le hu),
      mul_nonneg (abs_nonneg s) (mul_nonneg hB.le hu),mul_nonneg hC.le hu]
end jets

section relative
variable {G : Gauge} {n : Side}

/-- Use wherever differentiating affine displacement even without branch identities beyond real gauge. -/
lemma exp_ad (u : G.El) (v : G.Color) : G.lieExp (G.adjoint u v)= u * G.lieExp v * u⁻¹ := by
  apply G.mat_injective
  rw [G.mat_lieExp,G.mat_adjoint,G.exp_conjugate]
  simp only [G.mat_mul,G.mat_inv,G.mat_lieExp,Gauge.conjugate]

lemma increment_gauge (W : Config G n) (a : Directions G n) (z : Site n → G.El) :
    gauge z (increment W a) = increment (gauge z W) (fun i => G.adjoint (z i.1) (a i)) := by
  funext i
  unfold Lattice.gauge increment; rw [exp_ad]; group

lemma travel_bound (s : ℝ) (w : Walk) (i : Site n) (P Q : Config G n)
    (h : ∀ x : Bond n, x.1∈(visits i w).toFinset → G.chord (P x*(Q x)⁻¹) ≤ s) :
    G.chord (travel P i w * (travel Q i w)⁻¹) ≤ w.length*s := by
  induction w generalizing i with
  | nil => simp [travel]
  | cons d w ih =>
    have he : G.chord (d.read P i*(d.read Q i)⁻¹) ≤ s := by
      unfold Step.read; split
      next hd =>
        have hv : d.vec (R:=Per n) = -Lattice.step d.dir := by simp only [Step.vec, hd,↓reduceIte]
        specialize h (i-step d.dir,d.dir) (by rw [visits]; simp only [Prod.fst,sub_eq_add_neg,hv,List.mem_toFinset,List.mem_cons_self,List.mem_cons]; right; cases w <;> simp [visits])
        let p := P (d.used i); let q := Q (d.used i)
        change G.chord (p⁻¹*q⁻¹⁻¹) ≤ s
        have ht : G.chord (p⁻¹*q⁻¹⁻¹) = G.chord (p*q⁻¹) := by rw [← G.chord_inv (p*q⁻¹),show (p*q⁻¹)⁻¹=p*(p⁻¹*q⁻¹⁻¹)*p⁻¹ by group,G.chord_conj]
        rw [ht]
        · unfold p q Step.used; rw [if_pos hd]; exact h
      next hd =>
        unfold Step.used; rw [if_neg hd]; apply h; simp [visits]
    have ht := ih (i+d.vec) (fun x hx => h x (by simpa only [visits, List.mem_toFinset,List.mem_cons] using Or.inr (b:=x.1∈visits (i+d.vec) w) (List.mem_toFinset.mp hx)))
    rw [travel,travel,show d.read P i * travel P (i+d.vec) w * (d.read Q i * travel Q (i+d.vec) w)⁻¹ =
      d.read P i*(d.read Q i)⁻¹ * (d.read Q i*(travel P (i+d.vec) w*(travel Q (i+d.vec) w)⁻¹)*(d.read Q i)⁻¹) by group]
    apply (G.chord_triangle ..).trans
    rw [G.chord_conj]; exact (add_le_add he ht).trans_eq (by simp [add_mul]; ring)

lemma ad_change (w : G.Color) (u v : G.El) : ‖G.adjoint u w-G.adjoint v w‖ ≤
    2 * G.colorScale * G.chord (u*v⁻¹)* ‖w‖ := by
  have h : G.adjoint u w = G.adjoint (u*v⁻¹) (G.adjoint v w) := by rw [← G.adjoint_mul,inv_mul_cancel_right]
  rw [h]; exact (adjoint_norm_sub _ _).trans (by rw [G.norm_adjoint])
end relative
end YM.SectorNext.Remainder.Affine
