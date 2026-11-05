import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Arcade

/-!
# Gliding estimates for probes (principal inverse), scraps scalar

Also discrepancy under kth direction on radius d attenuated. No χ. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Foramen
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c : Side} {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
open Brush Tablet
variable {v z f g r Q : ℝ} {k D M B : ℕ} {A : E→Matrix ι ι ℝ}
variable [Fintype ι] {x : E} {a : ι → Site c} {η γ : ℝ}
variable [DecidableEq ι] (T : Window a B)

lemma thunder (p : Tablet k η f v A a a x) (u : ℝ) (h : u∈Set.Icc 0 1) :
    Tablet k η (1+(f+1)) v (fun z=> glide (A z) u) a a x := by
  have hv:= Tablet.fixed (x:=x) (k:=k) (1:Matrix ι ι ℝ) (one_pay a _) p.scale zero_le_one p.pos
  change Tablet k η (1+(f+1)) v (((1:E→ Matrix ..)) + u • (A+ -1)) a a x
  apply hv.joined
    (((p.joined hv.mirror).scalar u).tilt (mul_le_of_le_one_left (add_nonneg p.basis zero_le_one)
      ((Real.norm_of_nonneg h.1).trans_le h.2)) le_rfl p.scale le_rfl)

lemma puncture (h : ∀ i, IsUnit (T.principal (A x) i).det) (p : ∀ i j, ContDiffAt ℝ (↑k) (fun x=>A x i j) x) :
    ∀ᶠ z in 𝓝 x, ∀ i, IsUnit (T.principal (A z) i).det := by
  apply eventually_all.mpr; intro i
  exact ((determinant (A:=fun z=> T.principal (A z) i) (fun u v=>p u.val v.val)).continuousAt.eventually_ne
    (h i).ne_zero).mono fun _ he=> IsUnit.mk0 _ he

lemma padjets (h : Tablet k γ f v A a a x) (he : Allow (A x) a M η r Q) (hv : γ ≤ retain η r Q) :
    Tablet k γ (facePrice k B M f (payE η r Q M)) (driftP k v) (fun z=> T.pad (A z)) a a x :=
  h.emboss he.census T he.disc (fun i=>by
    let p:= (he.sub (Embedding.subtype (·∈T.take i)))
    exact ⟨isUnit_det_of_right_inverse p.initial.1,increase p.flatup hv le_rfl⟩)

def tidal (γ f F : ℝ) (B : ℕ) := Real.exp ((γ/2-γ)*B)*(f*F+1)
lemma wavesP (h : Tablet k γ f v A a a x) (he : Allow (A x) a M η r Q) (hv : γ ≤ retain η r Q) :
    Tablet k (γ/2) (tidal γ f (facePrice k B M f (payE η r Q M)) B) (v+driftP k v)
      (fun z=> T.error (A z)) a a x := by
  have hc := padjets T h he hv
  have hh := h.enjoin hc; let g := tidal γ f (facePrice k B M f (payE η r Q M)) B
  have hp := hh.joined (Tablet.fixed (1:Matrix ..) (one_pay a _) h.scale zero_le_one hh.pos).mirror
  refine hp.faraway B (fun i j hi=>?_) (half_le_self h.scale) (by have := h.scale; positivity)
  have hF := puncture (k:=k) T (fun i=> isUnit_det_of_right_inverse (he.sub (Embedding.subtype (·∈T.take i))).initial.1)
    (fun i j=> (h.singular i j).smooth)
  filter_upwards [hF] with y hy
  exact T.mileage (A y) i j (T.low _ _ hi) (mul_nonsing_inv _ (hy j))

lemma treasure (h : Tablet k γ f v A a a x) (he : Allow (A x) a M η r Q) (hv : γ ≤ retain η r Q) :
    let s:= token k f (payE η r Q M); let F := facePrice k B M f (payE η r Q M)
    Tablet k (γ/2) (s*tidal γ f F B) (driftP k v + (v+driftP k v))
      (fun t => T.pad (A t) - (A t)⁻¹) a a x := by
  intro s F; have hf := wavesP T h he hv; have hh := isUnit_det_of_right_inverse he.initial.1; have hQ := hf.scale
  have hP := h.inverter hh (increase he.flatup hv le_rfl) he.disc
  refine ((hP.tilt (le_refl _) (le_refl _) hQ (half_le_self h.scale)).enjoin hf).merges ?_
  filter_upwards [(determinant (fun i j=> (h.singular i j).smooth)).continuousAt.eventually_ne hh.ne_zero] with z hz
  unfold Window.error; rw [mul_sub,← mul_assoc,nonsing_inv_mul _ (IsUnit.mk0 _ hz), one_mul,mul_one]

lemma debris (h : Tablet k γ f v A a a x) (he : Allow (A x) a M η r Q) (hv : γ ≤ retain η r Q)
    (hh : ∀ i,(A i).IsHermitian) : let s:= token k f (payE η r Q M); let F := facePrice k B M f (payE η r Q M)
    Tablet k (γ/2) (f*(s*tidal γ f F B)) (v+(driftP k v+(v+driftP k v)))
      (fun z=> T.flawed (A z)) a a x := by
  intro s F
  let S z := T.pad (A z)-(A z)⁻¹
  let e := s*tidal γ f F B
  let V:=driftP k v+(v+driftP k v)
  have hv := treasure T h he hv
  have hg : Tablet k (γ/2) e V (fun z=>T.frameMean (A z)-(A z)⁻¹) a a x := by
    have hx := (hv.joined hv.reverse).scalar (1/2:ℝ)
    refine hx.tilt (le_of_eq ?_) (le_refl _) hx.scale le_rfl |>.merges (Eventually.of_forall (fun i=>?_))
    · change ‖(1/2:ℝ)‖*(e+e)=e; rw [Real.norm_of_nonneg (by norm_num : (0:ℝ)≤1/2)]; ring
    change (1/2:ℝ) • (S i + (S i).transpose)= _
    have hq : ((A i)⁻¹).transpose=(A i)⁻¹ := (by
      have hp:= (hh i).inv; ext j k; simpa only [IsHermitian, conjTranspose_apply, star_trivial, transpose_apply] using! hp.apply j k)
    unfold S Window.frameMean; rw [transpose_sub,hq]; module
  apply ((h.tilt le_rfl le_rfl hg.scale (half_le_self h.scale)).enjoin hg).merges
  have hh := isUnit_det_of_right_inverse he.initial.1
  filter_upwards [(determinant (fun i j=> (h.singular i j).smooth)).continuousAt.eventually_ne hh.ne_zero] with z hz
  rw [mul_sub,mul_nonsing_inv _ (IsUnit.mk0 _ hz)]; rfl
end YM.ConnectedActivityE6.Blaze.Foramen
