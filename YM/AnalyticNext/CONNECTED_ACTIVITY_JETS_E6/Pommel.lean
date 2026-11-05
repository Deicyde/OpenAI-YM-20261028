import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Eider
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Impasto
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Osmote
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Suites
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Terminal

/-!
# One-dimensional chart cost (one EDGE variable)

 Includes Jacobian score derivative; not paying a product shape^{card}
 for one mass. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical NNReal ENNReal
variable {G : Gauge} {E F Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
open Brush
variable {d A : ℝ} {j : ℕ} {x : E}
-- Compact fibers including charts with product instance diamonds.
omit [NormedSpace ℝ E] [NormedSpace ℝ Y] in
private lemma hanging {T : E→ Y → ℝ} {S : Set Y} (h : IsCompact S) (he : ∀ v∈S, ContinuousAt (uncurry T) (x,v))
    (hp : ∀ v∈S, 0<T x v) : ∀ᶠ y in 𝓝 x, ∀ v∈S, 0<T y v := by
  let V := {z:E×Y | 0<(uncurry T z)}
  obtain ⟨A,B,hA,-,hX,hS,H⟩:= generalized_tube_lemma (isCompact_singleton (x:=x)) h (isOpen_interior (s:=V)) (by
    rintro ⟨a,b⟩ ⟨hx,hb⟩; have hx:a=x:=hx; subst a
    exact mem_interior_iff_mem_nhds.mpr ((he b hb).eventually (lt_mem_nhds (hp b hb))))
  filter_upwards [hA.mem_nhds (hX (Set.mem_singleton _))] with z hz i hi using interior_subset (s:=V)
    (H (show (z,i)∈ A×ˢ B from ⟨hz,hS hi⟩))
-- Slice one of the parameters
private lemma sitting (i:Y) (x:E) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E→ Y → F}
    (V : ℝ) (he : Brush j V 1 (uncurry g) (x,i)) : Brush j V 1 (fun y=>g y i) x := by
    have hk : ContDiffAt ℝ (↑j) (fun y=> g y i) x := he.smooth.comp x (f:=fun m=> (m,i)) (contDiffAt_id.prodMk contDiffAt_const)
    refine ⟨hk,zero_le_one,fun k hp=>?_⟩
    let L:= ContinuousLinearMap.inl ℝ E Y
    have hs := sprains (U:=g) (he.smaller hp).smooth
    have hh : ‖L‖≤1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by intro v; simp [L,Prod.norm_def])
    change ‖JetF g k x i‖ ≤ _; dsimp only at hs; rw [hs]; refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) ?_
    exact (mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one (fun _ _=> norm_nonneg _) (fun _ _=> hh))).trans (he.order k hp)
namespace Eider

omit [NormedSpace ℝ E] in
private lemma elastic {g : E→E} (K : ℝ≥0) (h : LipschitzWith K g) (hp : K < 1) [CompleteSpace E] :
    Bijective (fun x=>x+g x) := by
  refine ⟨?_,?_⟩
  · intro x y he; change x+g x=y+g y at he
    suffices he : x-y=g y-g x by
      apply dist_eq_zero.mp; rw [dist_eq_norm, he, ← dist_eq_norm]; have h' := h.dist_le_mul x y
      rw [dist_eq_norm x y, he, ← dist_eq_norm,dist_comm (g x)] at h'
      have hp : (K:ℝ) < 1 := hp
      nlinarith [dist_nonneg (x:=g y) (y:=g x)]
    rw [sub_eq_iff_eq_add]; calc
      _ = x+g x-g x := by abel
      _ = _ := by rw [he]; abel
  intro x; let f v := x-g v
  have hx : ContractingWith K f := by
    refine ⟨hp,LipschitzWith.of_dist_le_mul fun i j=>?_⟩
    rw [show dist (f i) (f j)=dist (g i) (g j) by rw [dist_eq_norm,show f i-f j=g j-g i from (by unfold f; abel), ← dist_eq_norm,dist_comm]]
    exact h.dist_le_mul i j
  obtain ⟨y,hy,-⟩:= hx.exists_fixedPoint x (edist_ne_top x (f x))
  exact ⟨y,((sub_eq_iff_eq_add).1 (show x-g y=y from hy)).symm⟩

lemma clmDetB [FiniteDimensional ℝ E] (B : Y→ E→L[ℝ] E) (x:Y) {j : WithTop ℕ∞} (hp : ContDiffAt ℝ j B x) :
    ContDiffAt ℝ j (fun i=> (B i).det) x := by
  let l:= Module.finBasis ℝ E
  simp_rw [ContinuousLinearMap.det,← LinearMap.det_toMatrix l]; apply determinant
  intro i k
  simp_rw [LinearMap.toMatrix_apply]
  exact (l.coord i).toContinuousLinearMap.contDiff.contDiffAt.comp x (hp.clm_apply (g:=fun _=>l k) contDiffAt_const)

def pax (G : Gauge) (χ : Chi) (d : ℝ) (M : G.Mat) (x : G.Color) :=
    ContinuousLinearMap.id ℝ G.Color+ fderiv ℝ (plume G χ d M) x

def palm (G : Gauge) (χ : Chi) (d : ℝ) (M : G.Mat) (x : G.Color) := (pax G χ d M x).det

variable (p : Canary G d A) (χ : Chi)
include p
lemma plum (x : G.Color) (M : G.Mat) (he : ‖M-1‖ ≤ A) : HasFDerivAt (fleece G χ d M) (pax G χ d M x) x := by
  apply (hasFDerivAt_id _).add
  have hp : ContDiffAt ℝ ∞ (fun v=> plume G χ d M v) x := (sheen p χ x M he).comp x (f:=fun a=> (M,a))
    (contDiffAt_const.prodMk contDiffAt_id)
  exact (hp.differentiableAt (by simp)).hasFDerivAt
lemma leaves (x:G.Color) : palm G χ d 1 x=1 := by
  unfold palm; rw [← (plum p χ x 1 (by simp [p.side.le])).fderiv, nothing_f p χ,fderiv_id]; exact LinearMap.det_id
lemma duckling {x:G.Color} (h : 2*d<‖x‖) (M:G.Mat) : palm G χ d M x=1 := by unfold palm pax; rw [retreats p χ M x h,add_zero]; exact LinearMap.det_id
lemma lift (M : G.Mat) (b : G.Color) (he : ‖M-1‖ ≤ A) : ContDiffAt ℝ (↑j) (uncurry (palm G χ d)) (M,b) :=
    clmDetB (uncurry (pax G χ d)) _ (contDiffAt_const.add (lamina p χ b M he))
set_option maxHeartbeats 350000 in
lemma above : ∀ᶠ M:G.Mat in 𝓝 1, ∀ x:G.Color, 0<palm G χ d M x := by
  let S := Metric.closedBall (0:G.Color) (2*d)
  have hs : IsCompact S := isCompact_closedBall _ _
  have he (i:G.Color) : ContinuousAt (uncurry (palm G χ d)) (1,i) := (lift p χ 1 i (j:=0) (by simp [p.side.le])).continuousAt
  have hv (i:G.Color):0<palm G χ d 1 i := by rw [leaves p]; norm_num
  filter_upwards [hanging (T:=palm G χ d) hs (fun i _=>he i) (fun i _=>hv i)] with M hm i
  by_cases ht:i∈S
  · exact hm i ht
  rw [duckling p χ (by simpa [S,not_le] using ht)]; exact zero_lt_one
lemma vies : ∀ᶠ M:G.Mat in 𝓝 1, ‖M-1‖ < A ∧ Bijective (fleece G χ d M) ∧
    ∀ i:G.Color, ‖plume G χ d M i‖ < d/2 ∧ 0 < palm G χ d M i := by
  filter_upwards [above p χ,limn p χ, Metric.ball_mem_nhds (1:G.Mat) p.side] with M hM hp he
  rw [Metric.mem_ball,dist_eq_norm] at he; refine ⟨he,elastic (1/2) ?_ (by norm_num), fun i=> ⟨(hp i).1,hM i⟩⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (𝕜:=ℝ)
  · intro x; have h := (sheen p χ x M he.le).comp x (f:=fun a=> (M,a)) (contDiffAt_const.prodMk contDiffAt_id)
    exact h.differentiableAt (by simp)
  intro x; apply NNReal.coe_le_coe.mp; simpa only [coe_nnnorm,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] using! (hp x).2.le

lemma thorax (j : ℕ) : ∃ v z : ℝ, 0<v ∧ 0<z ∧ ∀ i:G.Color,
    Brush j v 1 (fun M=> plume G χ d M i) 1 ∧ Brush j z 1 (fun M=> palm G χ d M i) 1 := by
  let S : Set (G.Mat × G.Color) := {1}×ˢMetric.closedBall 0 (2*d); have hs : IsCompact S := isCompact_singleton.prod (isCompact_closedBall _ _)
  obtain ⟨v,hv,hA⟩ := Brush.compact (k:=j) (f:=uncurry (plume G χ d)) hs (by
    rintro ⟨x,y⟩ hx; have he:x=1 := hx.1; subst x; exact (sheen p χ _ _ (by simp [p.side.le])).of_le (WithTop.coe_le_coe.mpr le_top))
  obtain ⟨z,hz,hX⟩ := Brush.compact (k:=j) (f:=uncurry (palm G χ d)) hs (by
    rintro ⟨x,y⟩ hx; have he:x=1 := hx.1; subst x; exact lift p χ _ _ (by simp [p.side.le]))
  have hh (x:G.Color) (hx: ‖x‖≤2*d) : (1,x)∈S := ⟨Set.mem_singleton _,by simpa using hx⟩
  refine ⟨v,z,hv,hz,fun i=> ?_⟩
  by_cases he : ‖i‖ ≤ 2*d
  · exact ⟨sitting (g:=plume G χ d) i 1 _ (hA _ (hh i he)),sitting (g:=palm G χ d) i 1 _ (hX _ (hh i he))⟩
  have hy : 1≤ z := by
    have hx:= (hX (1,0) (hh _ (by rw [norm_zero]; linarith [p.warm]))).bound; simpa only [uncurry_apply_pair,leaves p,norm_one] using hx
  simp_rw [cooler p χ (le_of_lt (lt_of_not_ge he)),duckling p χ (lt_of_not_ge he)]
  exact ⟨(Brush.certified zero_le_one _).climb (by rw [norm_zero]; exact hv.le) le_rfl,(Brush.certified zero_le_one _).climb (by rw [norm_one]; exact hy) le_rfl⟩
lemma cozies (j : ℕ) (L : Side) {V : ℝ→ℝ} (h : Rate G L (-(1/2)) V) : ∃ S Z : ℝ→ℝ, Rate G L (-(1/2)) S ∧ Rate G L 0 Z ∧
    ∀ᶠ s in atTop, ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (M:E→G.Mat) (x:E), M x=1 → Brush j (royalty G) (V s) M x →
    ∀ y:G.Color, Brush j (S s) 1 (fun i=> plume G χ d (M i) y) x ∧ Brush j 1 (Z s) (fun i=> palm G χ d (M i) y) x := by
  obtain ⟨u,z,hU,hZ,hp⟩:= thorax p χ j; let D s:=(1+royalty G)*V s
  let B:=1+(j.factorial:ℝ)*z
  have hb : 1≤ B := le_add_of_nonneg_right (by positivity)
  refine ⟨fun s=>(j.factorial:ℝ)*u*D s,fun s=> B*D s,(h.mul_left _).mul_left _, ((h.mul_left _).mul_left B).weaken (by norm_num),?_⟩
  filter_upwards [(h.mul_left (1+royalty G)).below (by norm_num) 1 zero_lt_one] with s hS E _ _ M x hm hM y
  obtain ⟨hv,hh⟩:=hp y; rw [← hm] at hv hh
  have hp : 0≤ D s := by unfold D; have he:= royalty_ge G; have := hM.pos; positivity
  constructor
  · have hf := hM.pine hv
    refine Brush.offer.mpr ⟨hf.smooth,fun i hi=>?_⟩
    match i with
    | 0 => unfold normJ; rw [norm_iteratedFDeriv_zero,hm,nothing p χ,norm_zero]; positivity
    | i+1 =>
      apply (hf.order _ hi).trans; exact mul_le_mul_of_nonneg_left ((pow_le_pow_of_le_one hp ((le_abs_self _).trans hS) (by omega : 1 ≤ i+1)).trans_eq (pow_one _)) (by positivity)
  have hx:= hM.pine hh
  refine ⟨hx.smooth,mul_nonneg (zero_le_one.trans hb) hp,fun i hi=>?_⟩; match i with
  | 0=> unfold normJ; rw [norm_iteratedFDeriv_zero,hm, leaves p,norm_one,pow_zero,mul_one]
  | i+1=> apply (hx.order _ hi).trans; rw [one_mul,mul_pow B]; exact mul_le_mul_of_nonneg_right
            ((le_add_of_nonneg_left zero_le_one).trans (le_self_pow₀ (n:=i+1) hb (by omega))) (pow_nonneg hp _)
end Eider
end YM.ConnectedActivityE6.Blaze
