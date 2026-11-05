import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Melody
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Quaver

/-! # Real common-domain table at the predicted mean plus noise

The AND of two gauges at the same data (held tree or actual phi of A0);
tested initially on bareStores' channel. All torus sizes, only one survey;
Neumann cancellations NOT needed for the passage across the analytic
logarithms. Noise here is in *link* log units, before scaling or restriction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Metric Set Lattice Wilson Pressure Precision RG Tree Next Next.Fluctuations Next.SectorChange
    Exterior Laurent Bloch Bid AnalyticBridge.LocalGaussianLaws Lift AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {x : ℝ} {k : S.Choices} {n : ℕ}
    {t C D r : ℝ}

abbrev π₁ (G : Gauge) (c f : Side) := ContinuousLinearMap.fst ℝ (Directions G c) (Directions G f)
abbrev π₂ (G : Gauge) (c f : Side) := ContinuousLinearMap.snd ℝ (Directions G c) (Directions G f)
section build

variable (sw : Bool) (hC : ‖φ T F sw‖ ≤ C) {p : Deck G c f} (hr : ‖p‖ ≤ 1) (hf : Through n (forecast T x F k) p.1 D) (he : ‖expandBare F x (G:=G)‖ ≤ t)
include hC hr hf he
private lemma sounded (i : Bond f) : Through n (fun p => chord T F x k sw p i) p (1+C+(1+t*D)+1) := by
  have hl := (norm_nonneg _).trans hC
  have ht := (norm_nonneg _).trans he; have hd := mul_nonneg ht hf.nonneg
  have h₁ : ‖π₁ G c f‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ..
  have h₂ : ‖π₂ G c f‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ..
  have hz {I : Type} [Fintype I] (j : I) : ‖ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : I => G.Color) j‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun w => (norm_le_pi_norm w j).trans_eq (one_mul ..).symm)
  let M := 1+C+(1+t*D)+1
  have hP (j : Site f) : Through n (fun p : Deck G c f => φ T F sw p.1 j) p M := by
    exact (linear_through (pre_through _ h₁ p (upright _ n hC ((norm_fst_le p).trans hr))) (hz j) (L:=ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ => G.Color) j) (f:=(⇑(φ T F sw)) ∘ π₁ G c f)).mono (by dsimp [M]; linarith)
  have hA : Through n (fun p : Deck G c f => expandBare F x (forecast T x F k p.1)) p (t*D) := linear_through _ (pre_through _ h₁ p hf) he
  have hB := sum_through hA (upright _ n h₂ hr)
  have hy : Through n (fun p : Deck G c f => carriedCopy S (G:=G) p.1) p 1 := pre_through _ h₁ p (upright _ n (carriedCopy_norm S G) ((norm_fst_le p).trans hr))
  exact pair_through (pair_through (hP i.1) (hP _)) (pair_through ((linear_through _ hB (hz i)).mono (by linarith)) ((linear_through _ hy (hz i)).mono (by linarith)))
end build

lemma chart_home (hv : forecast T x F k 0=0) (sw : Bool) (i : Bond f) : chord T F x k sw 0 i=0 := by
  simp only [chord,Prod.fst_zero,Prod.snd_zero, map_zero,hv,Pi.zero_apply,zero_add,show linearCopy (G:=G) S.ratio 0 i = 0 from congr_fun (carriedCopy S (G:=G) |>.map_zero) i]; rfl

private lemma audition {sw : Bool} (h : DifferentiableAt ℝ (forecast T x F k) 0) (i : Bond f) (u : Deck G c f) :
    fderiv ℝ (fun p => chord T F x k sw p i) 0 u =
      ((φ T F sw u.1 i.1, φ T F sw u.1 (i.1+step i.2)), (expandBare F x (fderiv ℝ (forecast T x F k) 0 u.1) i+u.2 i,linearCopy S.ratio u.1 i)) := by
  let a j := ((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Site f => G.Color) j).comp (φ T F sw)).comp (π₁ G c f)
  let c₀ := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Bond f => G.Color) i
  let b₀ := c₀.comp (expandBare F x)
  have he := ((b₀.hasFDerivAt (x:=forecast T x F k 0)).comp 0 h.hasFDerivAt).comp (f:=π₁ G c f) (0:Deck G c f)
    (π₁ G c f).hasFDerivAt
  have h := ((a i.1).hasFDerivAt (x:=(0:Deck G c f))).prodMk (a (i.1+step i.2)).hasFDerivAt
  have h := h.prodMk ((he.add (c₀.comp (π₂ G c f)).hasFDerivAt).prodMk ((c₀.comp (carriedCopy S)).comp (π₁ G c f)).hasFDerivAt)
  exact DFunLike.congr_fun h.fderiv u

lemma display_deriv (h : DifferentiableAt ℝ (forecast T x F k) 0) (h₀ : forecast T x F k 0=0) (sw : Bool) (hg : DifferentiableAt ℝ (display T F x k sw) 0) :
    fderiv ℝ (display T F x k sw) 0 = mainStroke T F sw +
      ((expandBare F x).comp (fderiv ℝ (difference T F x k) 0)).comp (π₁ G c f) := by
  apply ContinuousLinearMap.ext; intro u; funext i; let L := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Bond f => G.Color) i
  have he : DifferentiableAt ℝ (fun p => chord T F x k sw p i) 0 := by
    unfold chord
    apply DifferentiableAt.prodMk
    · fun_prop
    exact DifferentiableAt.prodMk ((L.differentiableAt.comp _ ((expandBare F x).differentiableAt.comp _ (h.comp (f:=Prod.fst (β:=Directions G f)) 0 differentiableAt_fst))).add (L.differentiableAt.comp _ differentiableAt_snd))
      (L.differentiableAt.comp _ ((carriedCopy S (G:=G)).differentiableAt.comp _ differentiableAt_fst))
  change (L.comp (fderiv ℝ (display T F x k sw) 0)) u = _
  rw [← (L.hasFDerivAt.comp (f:=display T F x k sw) 0 hg.hasFDerivAt).fderiv]; rw [show L ∘ display T F x k sw=decode ∘ (fun p => chord T F x k sw p i) from rfl]
  rw [fderiv_comp 0 (f:=fun p => chord T F x k sw p i) (g:=decode) ?_ he,ContinuousLinearMap.comp_apply,audition h i u]
  swap; · rw [chart_home h₀]; exact (decode_analytic G).1.differentiableAt (by simp)
  let U := π₁ G c f u; let B := fderiv ℝ (difference T F x k) 0 U
  have ht : fderiv ℝ (forecast T x F k) 0 U = B+first T F x U := by unfold B difference; rw [fderiv_sub h (first T F x).differentiableAt,(first T F x).fderiv,sub_apply]; abel
  rw [chart_home h₀,decode_first,show u.1=U from rfl,ht,map_add,Pi.add_apply,expandBare_pick,show linearCopy S.ratio U i=carriedCopy S U i from rfl]
  cases sw
  · change 0 + (_ + treeMap T F U i + u.2 i) + carriedCopy S U i - 0 = (woody T F U i+u.2 i)+_; rw [woody_eq]; change _=(treeMap T F U i+carriedCopy S U i + u.2 i)+ expandBare F x B i; abel
  change _ = (route T U i+u.2 i)+_; rw [← harvest T F U i,woody_eq]; change _=( (_+(treeMap T F U i+carriedCopy S U i)-_)+u.2 i)+ expandBare F x B i; dsimp [φ]; abel

variable (T) (F) (x) (k)
structure Tour (n : ℕ) (r Q : ℝ) : Prop where
  represents (sw : Bool) (p : Deck G c f) : ‖p‖ ≤ r → increment 1 (display T F x k sw p)=sounds T F x k sw p
  costs sw : Portrait (display T F x k sw) (mainStroke T F sw) n (temp x) r Q
variable {T F x k}

private lemma concert {r₀ r₁ t D C K : ℝ} (h₀ : 0<r₀) (h₁ : 0<r₁) (_hK : 0<K) (hD : 0<D) (ht : 0≤t) (hn : 1 ≤ n)
    (hs : ∀ p : Directions G c, ‖p‖ ≤ r₀ → Through n (forecast T x F k) p D) (hA : ‖pegs F (main T) (G:=G)‖≤C) (he : ‖expandBare F x (G:=G)‖ ≤ t)
    (hf : difference T F x k 0=0 ∧ ‖fderiv ℝ (difference T F x k) 0‖ ≤ temp x)
    (hd : ∀ p : Chord G, ‖p‖ ≤ r₁ → Through n (decode (G:=G)) p K ∧ G.lieExp (decode p) = touch p) :
    let A := 1+C+(1+t*D)+1
    Tour T F x k n (min (r₁/A) (min r₀ 1)) (1+t+|Push.Uniform.composeCost n K A|) := by
  intro A
  have hC : 0≤C := (norm_nonneg _).trans hA
  have ha : 0<A := by unfold A; positivity
  let r := min (r₁/A) (min r₀ 1); have hr : 0<r := lt_min (div_pos h₁ ha) (lt_min h₀ zero_lt_one)
  let Q := 1+t+|Push.Uniform.composeCost n K A|
  have h : forecast T x F k 0=0 := sub_eq_zero.mp hf.1 |>.trans (first T F x).map_zero
  have hp (sw : Bool) (p : Deck G c f) (i : Bond f) (hp : ‖p‖ ≤ r) : G.lieExp (display T F x k sw p i)=sounds T F x k sw p i ∧
      Through n (fun p => display T F x k sw p i) p Q := by
    have hT (p : Deck G c f) (hp' : ‖p‖ ≤ r) : Through n (fun p => chord T F x k sw p i) p A := sounded sw (by cases sw; exact norm_zero.le.trans hC; exact hA)
      (hp'.trans ((min_le_right ..).trans (min_le_right ..))) (hs _ ((norm_fst_le ..).trans (hp'.trans ((min_le_right ..).trans (min_le_left ..))))) he i
    have hl := (locate hT hn (chart_home h sw i) hp).trans (mul_le_mul_of_nonneg_left (hp.trans (min_le_left ..)) ha.le) |>.trans_eq (mul_div_cancel₀ _ ha.ne')
    obtain ⟨hD,hw⟩ := hd _ hl
    exact ⟨hw,(Through.comp (f:=fun p => chord T F x k sw p i) hD (hT p hp)).mono ((le_abs_self _).trans (le_add_of_nonneg_left (by positivity)))⟩
  have he (sw p ht) := pi_through (f:=display T F x k sw) (show 0≤Q by unfold Q; positivity) (fun i => (hp sw p i ht).2)
  refine ⟨(fun sw p ht => funext fun i => by change _ * 1 = _; rw [mul_one]; exact (hp sw p i ht).1), fun sw => ⟨he sw,by unfold display; simp_rw [chart_home h,decode_zero]; rfl,?_⟩⟩
  have hj : (n:ℕ∞ω)≠0 := by exact_mod_cast (by omega : n≠0)
  rw [display_deriv ((hs 0 (by simpa using h₀.le)).smooth.differentiableAt hj) h sw ((he sw 0 (by simpa using hr.le)).smooth.differentiableAt hj),add_sub_cancel_left]
  exact ((ContinuousLinearMap.opNorm_comp_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ..)).trans ((ContinuousLinearMap.opNorm_comp_le ..).trans
    (mul_le_mul ‹‖expandBare F x‖ ≤ t› hf.2 (norm_nonneg _) ht))) : _ ≤ t*temp x) |>.trans (mul_le_mul_of_nonneg_right (show t ≤ Q by unfold Q; linarith [abs_nonneg (Push.Uniform.composeCost n K A)]) (Work.E04.temp_nonneg _))

-- post-L purchase on same Booths. Pre-L license of Matins to keep SEPARATELY (user of mainStroke).
theorem orchestra (G : Gauge) (P : Patch) (Pt : Teller G) (hp : P.Branches Pt.bind G) (n : ℕ) (hn : 2 ≤ n) :
    ∃ r Q : ℝ, 0<r ∧ 1≤Q ∧ ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Booth Pt S T → 100*(1+radiusB x) ≤ c.val →
      ∀ (F : Forest S.ratio) (k : S.Choices), Tour T F x k n r Q := by
  obtain ⟨r₀,D,h₀,hD,hs⟩ := survey G P Pt hp n
  obtain ⟨C,hc,hA⟩ := coaches Pt Pt.top.power 1 Pt.top.power_ge zero_lt_one
  obtain ⟨t,ht,H⟩ := budget_expandBare G
  obtain ⟨K,r₁,hK,h₁,he⟩ := decode_cert G n
  let A := 1+C+(1+t*D)+1
  refine ⟨min (r₁/A) (min r₀ 1),1+t+|Push.Uniform.composeCost n K A|,lt_min (by unfold A; positivity) (lt_min h₀ zero_lt_one), by linarith [abs_nonneg (Push.Uniform.composeCost n K A)],?_⟩
  filter_upwards [hs,dissent G P Pt hp] with x hs hF c f S T hP hT hp F k
  exact concert h₀ h₁ hK hD ht (by omega) (hs S T hP hT.1 hp F k) ((hA S T hT.1 F).norm_phi) (H S F x) (hF S T hP hT hp F k) he
end YM.PhysicalNext.JointLoad.Heir
