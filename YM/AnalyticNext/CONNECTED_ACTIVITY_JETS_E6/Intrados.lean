import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Inc

/-!
# Pointwise projector jets

 Polar at ANY X.χ applied consistently; quantities post-χ. Windows price can
 enter. Unit costs for repeated masks achieved by raising only derivative
 growth. Not assuming global small Gaussian w.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open Pulse Itinerary Scroll Vine Polar Frond Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {X : Coat T F} {z : Air f G} {E Y : Type}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] {x : E}
variable {a α β γ d η σ w s b : ℝ} {j : ℕ}
open Brush
lemma plateauChi (χ : Chi) {f : E→Y} (ht : Brush j d 1 f x) (hp : ∀ i∈ Set.Icc (0:ℝ) 4, Brush j w 1 χ.read i)
    (h : 0<s) (he : ‖f x‖≤2*s) :
    let K:=s⁻¹*d
    Brush j 1 ((1+j.factorial*w)*((1+K*K)*(1+1))) (fun i=> χ.innerShare s ‖f i‖) x := by
  intro K; let g (i:E):=s⁻¹ • f i
  have hv : Brush j K 1 g x := by
    have he:= ht.smul s⁻¹; rw [Real.norm_of_nonneg (by positivity : 0 ≤ s⁻¹)] at he; exact he
  have hh i : χ.innerShare s ‖f i‖=χ.read (‖g i‖^2) := by unfold Chi.innerShare g; rw [norm_smul,Real.norm_of_nonneg (by positivity : 0 ≤ s⁻¹),div_eq_mul_inv, mul_comm ‖f i‖]
  have hy : ‖g x‖≤2 := by
    unfold g; rw [norm_smul,Real.norm_of_nonneg (by positivity : 0 ≤ s⁻¹)]
    apply (inv_mul_le_iff₀ h).mpr; simpa only [mul_comm s] using he
  simp_rw [hh]; apply ((squared hv).pine (hp _ ⟨sq_nonneg _,by nlinarith [norm_nonneg (g x)]⟩)).exalt
  rw [Real.norm_of_nonneg ((χ.range _).1)]
  exact (χ.range _).2
namespace Silica.Clutch

lemma kernels (G : Gauge) (L : Side) (χ : Chi) {V : ℝ→ℝ} (h : Rate G L (-(1/2)) V) (j : ℕ) (b : ℝ) :
    ∃ X : ℝ→ℝ, Rate G L 0 X ∧ ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio)
    (Q : Coat T F), Q.x=x → S.patch.L=L → Q.χ=χ → 0<b*Q.t → ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : Air f G) (a β : ℝ) (y:E) (U : E → Config G c) (f':E → Directions G f) (W:E → Air f G),
    Clutch Q z a β (V x) y j U f' W → ∀ i, Brush j 1 (|X x|) (fun y=> Q.cone b (f' y) i) y := by
  obtain ⟨w,hp,hX⟩ := Brush.compact (k:=j) (f:=χ.read) (s:=Set.Icc 0 4) isCompact_Icc (fun _ _=>
    (χ.smooth.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)))
  let t:= (Pressure.fiery G · L); let K x:= (b*t x)⁻¹*(V x +2*b*t x)
  have hk:Rate G L 0 K := by
    have hh: Rate G L (1/2) (fun x=> (b*t x)⁻¹) := by simpa only [_root_.mul_inv_rev] using! (inverse_mist G L).mul_right b⁻¹
    convert hh.mul (h.add (Rate.mul_left (Rate.flame (G:=G) (L:=L)) (2*b))) using 1; norm_num
  refine ⟨fun x=>(1+(j.factorial:ℝ)*w)*((1+K x*K x)*(1+1)),
    ((((Rate.const 1).add ((hk.mul hk).weaken (by simp))).mul_right (1+1)).mul_left _),?_⟩
  refine Eventually.of_forall fun x c f S T F Q hQ he hχ hw E _ _ z a β y U f' W H i=> ?_
  by_cases hp:(fun y=> Q.cone b (f' y) i)=ᶠ[𝓝 y] fun _=>0
  · exact Brush.zi hp zero_le_one (abs_nonneg _)
  obtain ⟨hd,hA⟩:= H.fostered i hw hp
  unfold cone; rw [hχ]
  apply (plateauChi χ hA hX hw (by rw [← mul_assoc]; exact hd)).climb le_rfl
  change _ ≤ |(1+j.factorial*w)*((1+K x*K x)*(1+1))|
  simp_rw [Coat.t,hQ,he]; exact le_abs_self _

lemma puffs (G : Gauge) (L : Side) (χ : Chi) (a : ℝ) {Ñ : ChartRatio G} (hÑ : LocalRatio Ñ) {V : ℝ→ℝ} (h : Rate G L (-(1/2)) V)
    (j : ℕ) : ∃ X, Rate G L (-(1/2)) X ∧ ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio)
      (Q : Coat T F), Q.x=x → S.patch.L=L → Q.χ=χ → ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      (z : Air f G) (β : ℝ) (y:E) (U : E→ Config G c) (f':E → Directions G f) (W:E→ Air f G), Clutch Q z a β (V x) y j U f' W →
      ∀ i, Brush j (|X x|) 1 (fun y=> Q.gentry Ñ a (f' y) i) y := by
  obtain ⟨A,hA,hp⟩:= kernels G L χ h j (2*a)
  let v (t:G.Color) := Real.log (Ñ.J t)
  have he: ContDiffAt ℝ ω v 0 := ((hÑ.germ 0 (Metric.mem_ball_self hÑ.patch)).log (by rw [hÑ.anchored]; norm_num))
  obtain ⟨b,hb,hg⟩:= Brush.neighborhood (k:=j) 0 (he.of_le le_top)
  obtain ⟨u,hu,hh⟩:=Metric.nhds_basis_closedBall.eventually_iff.mp hg
  obtain ⟨B,r,hB,hr,ht⟩:= Next.Fluctuations.chart_linear_cost _ _ he.analyticAt
  have hv := hA.compare (v:=fun x=>|A x|) (Eventually.of_forall fun i=> (abs_abs _).le)
  let X x:= V x+2*(2*a)*Pressure.fiery G x L; have hx:Rate G L (-(1/2)) X := h.add (Rate.flame.mul_left _)
  have hz := Rate.const (G:=G) (L:=L) 1
  let D x := 1+(|A x|+1)
  have hF : Rate G L 0 (fun x=> (D x)^j) := by simpa only [zero_mul] using! ((hz.add (hv.add hz)).pow j)
  refine ⟨fun x=> ((1:ℝ)*((B+j.factorial*b)*X x))*(D x)^j,(by simpa only [add_zero] using!
    (((hx.mul_left (B+j.factorial*b)).mul_left 1).mul hF)),?_⟩
  filter_upwards [hp,hx.below (by norm_num) (min 1 (min u r)) (by positivity)] with x hX hy c f S T F Q hQ hL he E _ _ z β y U f' W H i
  by_cases hp : (fun y=> Q.cone (2*a) (f' y) i)=ᶠ[𝓝 y] fun _=>0
  · refine Brush.zi (hp.mono ?_) (abs_nonneg _) zero_le_one; intro i' hi; change Q.cone _ _ _*_=_; rw [show Q.cone _ _ _=0 from hi,zero_mul]
  have hm : 0<2*a*Q.t := by rw [mul_assoc]; exact mul_pos (by norm_num) H.pulse
  have ht' := hX _ _ S T F Q hQ hL he hm E z a β y U f' W H i
  have hh' : Brush j (X x) 1 (fun y=>f' y i) y := by
    have h:= (H.fostered _ hm hp).2; unfold Coat.t at h; rw [hQ,hL] at h; exact h
  obtain ⟨hK,hY⟩:= le_min_iff.mp ((le_abs_self _).trans hy); let f:= f' y i
  have hf : ‖f‖ ≤ X x := hh'.bound; obtain ⟨hw,hM⟩ := le_min_iff.mp hY
  have h' : Brush j b 1 v f := hh (Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hf.trans hw))
  have hv : ‖v f‖≤B* X x := by
    have hv:= ht f (by simpa using hf.trans hM); simp only [sub_zero,v,hÑ.anchored,Real.log_one] at hv
    exact hv.trans (mul_le_mul_of_nonneg_left hf hB.le)
  exact ((ht'.paints (hh'.even h' hK hB.le hv)).trim).climb (le_abs_self _) le_rfl
end Silica.Clutch
end YM.ConnectedActivityE6.Blaze
