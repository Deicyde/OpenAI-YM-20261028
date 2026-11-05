import YM.EveryPhase.Vitali
import YM.EveryPhase.Pack
/-!
Strict waves as continuous scalar functions on the character space.
A common polynomial margin bound. Analytic continuation also commutes
with the ground-algebra barycenter here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase
open Function Set Filter MeasureTheory Spec Boundary Probe Complex Next.BOUNDARY
open scoped Topology NNReal ContDiff InnerProductSpace

section power
open Org OS
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
    {F : Final C f S} (L : Almanac F)

theorem power (n : ℕ) (v : Fin n → S.Union) : ∃ m : ℕ, ∃ C₀ : ℝ, 0≤C₀ ∧
    ∀ i, ∀ (y : Heights n) (k : ℝ), k∈Ioc 0 1 → broad y k → ∀ x,
    ‖(L.contours i).waves.restricted v y x‖ ≤ C₀*k⁻¹^m := by
  obtain ⟨B,hB,-⟩ := (onFinal F).1.reveals
  choose Q d hQ h using (fun i => B.price (v i))
  let P (i : Fin n) := Q i * 8^d i
  have hP i : 0 ≤ P i := by have := hQ i; unfold P; positivity
  have hn := Finset.prod_nonneg (s:=Finset.univ) (fun i _ => hP i)
  refine ⟨∑ i, d i, ∏ i, P i, hn, fun i y k hk hb x => ?_⟩
  obtain ⟨Y,hY,-⟩ := (L.cards i).reveals
  let p := Small.logD k
  have hp : Small.enough y p := Work.C03.enough_logD hk hb
  have he : Small.lit (shift x y) p := by simpa [Small.lit,shift] using hp
  have hX (a : S.Union) : ‖Y.bits.bar p a‖ ≤ ‖B.bits.bar p a‖ := by
    obtain ⟨r,t,rfl⟩ := F.sector.derivatives.covered F.room.kernel.laws.toSymmetric F.phase.transport.injection a
    rw [B.linked r t p hp.1,Y.linked r t p hp.1]
    exact L.priced i _ _ (Work.C01.centeredSlab _ _ hp.1)
  have hi j : ‖Y.bits.bar p (v j)‖ ≤ P j * k⁻¹^d j := by
    apply le_trans (hX _) ((h j p ⟨hp.1,hp.2.1⟩).trans_eq ?_)
    unfold p P; rw [Work.C03.coe_logD hk, inv_div,div_eq_mul_inv,mul_pow,mul_assoc]
  rw [← hY, Waves.restricted,Y.yields n _ (Work.C03.lit_strict he) p he]
  calc
    _ ≤ ∏ j, ‖Y.bits.bar p (v j)‖ := by
      have ht : ‖(L.chambers i).omega‖=1 := OS.nil_norm _ (F.phase.phase.states i).laws
      convert Work.C03.norm_matrix Y.bits p v (shift x y) (trace x) he using 1
      rw [ht]; ring
    _ ≤ ∏ j, (P j * k⁻¹^d j) := Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => hi j)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
end power

section path
variable {n : ℕ} (y : Heights n) (x : Points n)

def scalePath (c : ℂ) : Times n := fun i => ↑(y i)*I + c*↑(YM.time (x i))

def scaleIm (t : ℝ) : Heights n := fun i => y i+t*YM.time (x i)

lemma path_im (c : ℂ) : (fun i => (scalePath y x c i).im) = scaleIm y x c.im := by
  funext; simp [scalePath,scaleIm]

lemma path_one : scalePath y x 1=shift x y := by funext; simp [scalePath,shift,add_comm]

lemma path_I (t : ℝ) : scalePath y x (↑t*I)= fun i => ↑(scaleIm y x t i)*I := by
  funext; dsimp only [scalePath,scaleIm]; push_cast; ring

lemma path_open (hy : y ∈ east n) : ∃ (k : ℝ), k ∈ Ioc 0 1 ∧
    ∃ (δ : ℝ), 0<δ ∧ ∀ t∈Ioo (-δ) δ, broad (scaleIm y x t) k := by
  obtain ⟨j,hj,hb⟩ := Work.C15.east_broad hy
  refine ⟨j/2, ⟨by linarith [hj.1],by linarith [hj.2]⟩,?_⟩
  let U : Set ℝ := {s | broad (scaleIm y x s) (j/2)}
  have hT : ∀ᶠ s in 𝓝 (0:ℝ), broad (scaleIm y x s) (j/2) := by
    simp only [broad,eventually_all]
    intro a b hij
    have hp : Continuous fun t => scaleIm y x t b-scaleIm y x t a := by unfold scaleIm; fun_prop
    have hg : j / 2 < scaleIm y x 0 b-scaleIm y x 0 a := by
      simp [scaleIm]; linarith [hb a b hij,hj.1]
    exact ((hp.tendsto 0).eventually (lt_mem_nhds hg)).mono fun _ h => h.le
  obtain ⟨δ,hδ,hx⟩ := Metric.mem_nhds_iff.mp (show U∈ 𝓝 0 from hT)
  exact ⟨δ,hδ,fun t ht => hx (Metric.mem_ball.mpr (by simpa [abs_lt,Real.dist_eq] using ht))⟩

variable {δ k : ℝ}
def ribbon (δ : ℝ) : Set ℂ := im ⁻¹' Ioo (-δ) δ
lemma ribbon_zero (h : 0<δ) : (0:ℂ) ∈ ribbon δ := ⟨neg_lt_zero.mpr h,h⟩
lemma ribbon_one (h : 0<δ) : (1:ℂ) ∈ ribbon δ := ⟨neg_lt_zero.mpr h,h⟩
lemma open_ribbon (δ : ℝ) : IsOpen (ribbon δ) := isOpen_Ioo.preimage continuous_im
lemma pre_ribbon (δ : ℝ) : IsPreconnected (ribbon δ) :=
  Convex.isPreconnected ((convex_Ioo (-δ) δ).linear_preimage imCLM.toLinearMap)
lemma path_strict {c : ℂ} (h : c∈ribbon δ)
    (hk : k∈Ioc (0:ℝ) 1) (hb : ∀ t∈Ioo (-δ) δ, broad (scaleIm y x t) k) :
    scalePath y x c ∈ strict n := fun a b hp => by
  simpa [scaleIm,scalePath] using
    (sub_pos.mp (hk.1.trans_le (hb c.im h a b hp)))

lemma path_shift (c : ℂ) : scalePath y x c=shift (place (trace x) (fun i => c.re*YM.time (x i)))
    (scaleIm y x c.im) := by
  funext i; apply Complex.ext <;> simp [scalePath,place,scaleIm,shift]

lemma from_imaginary {P : ℂ → Prop} {U : Set ℂ} (h : U ∈ 𝓝 0)
    (he : ∀ t : ℝ, (↑t*I)∈U → P (↑t*I)) : ∃ᶠ q in 𝓝[≠] (0:ℂ), q∈U ∧ P q := by
  intro hn
  let f (t : ℝ) := ↑t*I
  have hh : Tendsto f (𝓝[>] (0:ℝ)) (𝓝[≠] (0:ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hi : Continuous f := continuous_ofReal.mul continuous_const
      simpa [f] using ((hi.tendsto 0).mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with i hi
    change f i ≠ 0; simp [f,(mem_Ioi.mp hi).ne']
  obtain ⟨c,hc,h⟩ := ((hh.eventually hn).and ((hh.mono_right nhdsWithin_le_nhds).eventually h)).exists
  exact hc ⟨h, he c h⟩
end path

section
open Metric
/-- An integrable locally uniform bound suffices here too; only need the
constant-bound finite-measure version. -/
theorem integral_holomorphic {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {F : α → ℂ → ℂ} {U : Set ℂ} {C : ℝ} (h : IsOpen U) (he : ∀ i, DifferentiableOn ℂ (F i) U)
    (ha : ∀ x∈U, Integrable (fun i => F i x) μ) (hb : ∀ i x, x∈U → ‖F i x‖ ≤ C) :
    DifferentiableOn ℂ (fun x => ∫ i, F i x ∂μ) U := by
  intro x hx
  obtain ⟨r,hr,hU⟩ := Metric.mem_nhds_iff.mp (h.mem_nhds hx)
  have ht : 0<r/2 := by linarith
  let B := ball x (r/2)
  have hB : B ⊆ U := (ball_subset_ball (by linarith : r/2 ≤ r)).trans hU
  let D (z : ℂ) (i : α) := deriv (F i) z
  have hv i y (hy : y∈B) : HasDerivAt (F i) (D y i) y :=
    ((he i).differentiableAt (h.mem_nhds (hB hy))).hasDerivAt
  have hp i y (hy : y∈B) : ‖D y i‖ ≤ C/(r/2) := by
    have hw : closedBall y (r/2) ⊆ U := by
      intro w hw; exact hU (mem_ball.mpr ((dist_triangle w y x).trans_lt (by linarith [mem_closedBall.mp hw, mem_ball.mp hy])))
    dsimp only [D]; rw [← Complex.cderiv_eq_deriv h (he i) ht hw]; exact Complex.norm_cderiv_le ht
      fun w hw' => hb i w (hw (sphere_subset_closedBall hw'))
  classical
  have hm : AEStronglyMeasurable (D x) μ := by
    let G y (i : α) := if y∈U then slope (F i) x y else 0
    have hG (y) : AEStronglyMeasurable (G y) μ := by
      by_cases H : y∈U
      · simp only [G,H,if_true,slope_def_module]; exact ((ha y H).aestronglyMeasurable.sub
          (ha x hx).aestronglyMeasurable).const_smul (y-x)⁻¹
      simp only [G,H,if_false]; exact aestronglyMeasurable_const
    apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] x) hG
    refine ae_of_all _ fun i => ((hv i x (mem_ball_self ht)).tendsto_slope).congr'
      (Eventually.mono (show ∀ᶠ z in 𝓝[≠] x, z∈U from nhdsWithin_le_nhds (h.mem_nhds hx)) (fun z hz => by simp only [G,hz,if_true]))
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=fun z i => F i z)
    (s:=B) (F':=D) (bound:=fun _ : α => C/(r/2)) (ball_mem_nhds x ht)
    (Eventually.mono (h.mem_nhds hx) (fun y hy => (ha y hy).aestronglyMeasurable))
    (ha x hx) hm (ae_of_all μ hp) (integrable_const _) (ae_of_all μ hv)
  exact hh.2.differentiableAt.differentiableWithinAt
end

variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
    {F : Final C f S} (L : Almanac F) {n : ℕ}

lemma imaginary_evaluation (x : SpacePoints n) (v : Fin n → S.Union)
    {y : Heights n} (hy : y∈east n) :
    let z : Times n := fun j => ↑(y j)*I
    Continuous (fun i => (L.contours i).waves.F n z x v) ∧
     (∫ i, (L.contours i).waves.F n z x v ∂F.α.space.μ)=F.B.waves.F n z x v := by
  dsimp only
  choose d t h using (fun i => F.sector.derivatives.covered F.room.kernel.laws.toSymmetric
    F.phase.transport.injection (v i))
  let u : Fin n → S.Tag := fun i => ⟨d i,t i⟩
  rw [show v=(fun i => S.pin (u i).1 (u i).2) from (funext h).symm]
  simp_rw [fun i => (L.cards i).fromPhase.heat.roots n u x y hy, F.realization.allWorld.heat.roots n u x y hy]
  let q := Word.realize (fun i => (⟨d i,S.representative _ (t i)⟩ : C.book.Token)) (place x y)
  have hp : Word.distinct q := (Word.realized ..).mpr (clear hy _)
  have hh (T : Table C.book) : S.useAt T (place x y) u=T.expect q := (T.readAt (fun i => ⟨d i,S.representative _ (t i)⟩) (place x y)).symm
  simp_rw [hh]
  refine ⟨?_, F.α.space.barycenter _ F.phase.phase.decomposition F.phase.phase.chosen
    F.room.kernel.translations q hp⟩
  simp_rw [fun i => OS.Cluster.track F.α.unselected q hp i (F.phase.phase.chosen i)]
  exact F.phase.phase.decomposition.weak _

private lemma path_price (x : Points n) (v : Fin n → S.Union) (y : Heights n) {k δ : ℝ}
    (hk : k∈Ioc 0 1) (hp : ∀ t∈Ioo (-δ) δ, broad (scaleIm y x t) k) : ∃ C₀ : ℝ, ∀ i z, z∈ribbon δ →
    ‖(L.contours i).waves.F n (scalePath y x z) (trace x) v‖ ≤ C₀ := by
  obtain ⟨m,A,hA,h⟩ := power L n v
  refine ⟨A*k⁻¹^m, fun i z hz => ?_⟩
  rw [path_shift y x z]
  let X := place (trace x) (fun i => z.re * YM.time (x i))
  have hh : trace X=trace x := by ext1; simp [trace,X,place]
  have he := h i (scaleIm y x z.im) k hk (hp _ hz) X
  unfold Waves.restricted at he
  rwa [hh] at he

private lemma path_diff {T : Table C.book} {A : Contour S} (h : A.From T) (x : Points n)
    (v : Fin n → S.Union) (y : Heights n) {k δ : ℝ} (hk : k∈Ioc 0 1)
    (hp : ∀ t∈Ioo (-δ) δ, broad (scaleIm y x t) k) :
    DifferentiableOn ℂ (fun z => A.waves.F n (scalePath y x z) (trace x) v) (ribbon δ) := by
  apply (h.heat.hol n v (trace x)).comp (f:=scalePath y x)
    (show Differentiable ℂ (scalePath y x) from by unfold scalePath; fun_prop).differentiableOn
  intro z hz; exact path_strict y x hz hk hp

/-- At strict heights -- includes ALL points, not just tested limits. -/
lemma strict_evaluation (x : Points n) (v : Fin n → S.Union) {y : Heights n} (hy : y∈east n) :
    Continuous (fun i => (L.contours i).waves.restricted v y x) ∧
     (∫ i, (L.contours i).waves.restricted v y x ∂F.α.space.μ)=F.B.waves.restricted v y x := by
  obtain ⟨k,hk,δ,hδ,H⟩ := path_open y x hy
  let g i (z : ℂ) := (L.contours i).waves.F n (scalePath y x z) (trace x) v
  let U := ribbon δ
  have hp i : DifferentiableOn ℂ (g i) U := path_diff (L.cards i).fromPhase x v y hk H
  obtain ⟨D,hD⟩ := path_price L x v y hk H
  have hb i (z : ℂ) (h : z∈U) : ‖g i z‖ ≤ D := hD i z h
  have hu : U∈𝓝 (0:ℂ) := (open_ribbon δ).mem_nhds (ribbon_zero hδ)
  have he (t : ℝ) (ht : ↑t*I∈U) : scaleIm y x t∈east n := by
    have hz := path_strict y x ht hk H
    change (fun i => (scalePath y x (↑t*I) i).im)∈east n at hz
    simpa only [path_im,mul_I_im,ofReal_re] using hz
  have hf (z : ℂ) (hz : z∈U) : Continuous fun i => g i z := by
    apply continuous_iff_continuousAt.mpr; intro i
    apply propagate_limit (F:=g) (f:=g i) (open_ribbon _) (pre_ribbon _) (Eventually.of_forall hp) (hp i)
      _ (ribbon_zero hδ) _ hz
    · intro x hx
      obtain ⟨r,hr,hT⟩ := Metric.mem_nhds_iff.mp ((open_ribbon δ).mem_nhds hx)
      exact ⟨r,hr,D,Eventually.of_forall fun i z hz => hb i z (hT hz)⟩
    refine from_imaginary hu fun t ht => ?_
    dsimp only [g]; rw [path_I]
    exact (imaginary_evaluation L (trace x) v (he t ht)).1.tendsto _
  haveI := F.phase.phase.decomposition.normalized
  let G₀ z := F.B.waves.F n (scalePath y x z) (trace x) v
  have hg : EqOn (fun z => ∫ i, g i z ∂F.α.space.μ) G₀ U := by
    have ha := integral_holomorphic (μ:=F.α.space.μ) (open_ribbon _) hp (fun z hz => (hf z hz).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) hb
    apply (ha.analyticOnNhd (open_ribbon _)).eqOn_of_preconnected_of_frequently_eq
      ((path_diff F.realization.allWorld x v y hk H).analyticOnNhd (open_ribbon _)) (pre_ribbon δ) (ribbon_zero hδ)
    refine (from_imaginary (P:=fun z => (∫ i, g i z ∂F.α.space.μ)=G₀ z) hu (fun t ht => ?_)).mono (fun _ h => h.2)
    dsimp only [g,G₀]; rw [path_I]; exact (imaginary_evaluation L (trace x) v (he t ht)).2
  unfold Waves.restricted
  rw [← path_one y x]
  exact ⟨hf 1 (ribbon_one hδ),hg (ribbon_one hδ)⟩

end YM.EveryPhase
