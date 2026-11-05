import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Cupola

/-! # Concentration angular h cost.

Use `|catastrophe|` and Coupler powered budgets. Logs later add Epoch sales
 and exact velocity markup across shapes. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open Pulse Itinerary Scroll Vine Polar Frond Corona Footprint
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {X : Coat T F} {z : Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {a α β γ d η σ W s b μ : ℝ} {j : ℕ}
open Brush
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
namespace Silica.Clutch

-- A convenient mask price (foot cover includes enlargement CUT). Later v*shapeW.
lemma central (G : Gauge) (L : Side) (χ : Chi) (j : ℕ) {V : ℝ→ℝ} (h : Rate G L (-(1/2)) V) (b : ℝ) :
    ∃ B, Rate G L 0 B ∧ (∀ x,0≤B x) ∧ ∀ᶠ x in atTop, ∀ (c f:Side) (S:StepData c f) (T: Tube G S) (F : Forest S.ratio)
      (X : Coat T F), X.x=x → X.χ=χ → S.patch.L=L → 0 < b*X.t → ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      (z : Air f G) (a β : ℝ) (y:E) (U : E→ Config G c) (f':E → Directions G f) (w:E → Air f G), Clutch X z a β (V x) y j U f' w →
        ∀ Y (M:Support c),Y⊆ M → Brush j 1 (B x*coverNumber X.B M) (fun y=> X.enforce b (f' y) (X.plaza Y)) y := by
  obtain ⟨C,hC,hp⟩:= kernels G L χ h j b
  let B x:= (ballCost (radiusB x):ℝ)*ballCost 1*Itinerary.density L*|C x|
  have hb := width_rate G L 1 0; simp only [one_mul,add_zero] at hb
  refine ⟨B,by unfold B; simpa only [add_zero] using!
    (((hb.mul_right (ballCost 1)).mul_right (Itinerary.density L)).mul (hC.compare (v:=fun x=> |C x|) (Eventually.of_forall fun x=> (abs_abs _).le))),
    fun x=> by unfold B; positivity,hp.mono ?_⟩
  intro x hx c f S T F X he hχ hL ht E _ _ z a β y U f' w H Y M hm; apply (Blaze.canopy (a:=b) (X:=X) f' M (|C x|) (M:=X.plaza Y)
    (fun i _=> hx _ _ S T F X he hL hχ ht E z a β y U f' w H i) (worn X hm) (abs_nonneg _)).climb le_rfl
  apply le_of_eq; unfold B; rw [← he,hL]; change _= (ballCost X.B:ℝ)* _ * _ * _ * _
  ring

private lemma curtain {U : Config G f} (Y:E→ Config G c) (hp : ∀ i A, Brush j 1 d (fun y=> Mask.noise A X.χ i X.t W U X.k (Y y)) x) (hd : 0≤d)
    (R : Rep G f) (k : Finset ℕ) (i : Panic c f) : Brush j (topStorm S.patch) d (fun v=> veil (vary X (Y v)) R W U k i) x := by
  have hv (a : ℝ) (h : 0≤a) (hp : a≤topStorm S.patch) : Brush j (topStorm S.patch) d (fun _ : E=> a) x :=
    (Brush.certified hd a).climb (by rw [Real.norm_of_nonneg h]; exact hp) le_rfl
  rcases i with i|i|i|i|i
  · exact hv (Mask.fine X.seeds X.χ i X.t U) (Mask.fine_range ..).1 ((Mask.fine_range ..).2.trans (topStorm_one _))
  · exact (hp i X.seeds).climb (topStorm_one _) le_rfl
  · exact hv (pinMass U X.k i) (pin_nn ..) ((pin_cap ..).trans (le_add_of_nonneg_left (by positivity)))
  · exact hv (siteMass U X.k i) (site_nn ..) ((site_cap ..).trans ((le_add_of_nonneg_left zero_le_one).trans (le_add_of_nonneg_right (Nat.cast_nonneg _))))
  change Brush j (topStorm S.patch) d (fun _:E=> Contract.charges R k U i) x
  rcases Contract.ordinary R k U i with hh|hh <;> simp_rw [hh]
  · exact hv _ le_rfl (zero_le_one.trans (topStorm_one _))
  exact hv _ zero_le_one (topStorm_one _)

lemma ash (G : Gauge) (L : Side) (χ : Chi) (j : ℕ) {V v : ℝ→ℝ} (h : Rate G L (-(1/2)) V) (he : Rate G L (-(1/2)) v) (W a : ℝ)
    (l : ℕ) (hl : 1 ≤ l) : ∃ B, Rate G L 0 B ∧ (∀ x, 0≤ B x) ∧ ∀ᶠ x in atTop, ∀ (c f:Side) (S:StepData c f) (T: Tube G S)
      (F : Forest S.ratio) (X : Coat T F) (R : Rep G f), X.x=x → X.χ=χ → S.patch.L=L → 0<W*X.t →
      ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      (z : Air f G) (y:E) (U : E→ Config G c) (f':E → Directions G f) (w:E → Air f G), Clutch X z a R.beta (V x) y j U f' w →
      Mode U y j (v x) → ∀ (i : WarningAt c f) (k : Finset ℕ) (Y : Config G f),
        Brush j (topStorm S.patch+1) (B x*(1+coverNumber X.B (field_support S X.B l i))) (fun v=> sprinkle (vary X (U v)) a R W (f' v) Y k i) y := by
  obtain ⟨B,hB,h₁,hp⟩:= central G L χ j h (2*a)
  obtain ⟨A,hA,h₂⟩:= kernels G L χ h j a
  obtain ⟨C,hC,h₃⟩:= notches G L χ j he W
  let Q x:= B x+|C x|+ |A x|
  have hh x:0 ≤ Q x := add_nonneg (add_nonneg (h₁ _) (abs_nonneg _)) (abs_nonneg _)
  refine ⟨Q,(hB.add (hC.compare (v:=fun x=> |C x|) (Eventually.of_forall fun y=> (abs_abs _).le))).add
    (hA.compare (Eventually.of_forall fun x=> (abs_abs _).le)), hh,?_⟩
  filter_upwards [hp,h₂,h₃] with x hx hz hA c f S T F X R hX hχ hL ht E _ _ z y U f' w H m i k Y
  have hT := topStorm_one S.patch
  have hu:0 < 2*a*X.t := by rw [mul_assoc]; exact mul_pos (by norm_num) H.pulse
  subst χ; let A' i:=coverNumber X.B (field_support S X.B l i); let f i := Q x * (1+(A' i:ℝ))
  have hF i: Q x ≤ f i := le_mul_of_one_le_right (hh x) (le_add_of_nonneg_right (Nat.cast_nonneg _))
  let Z i:= (vary X (U i))
  rcases i with i|i
  · let T' := halo X.B (districts S i); change Brush j _ (f (.inl i)) (fun y=> if mandatory X.seeds X.B i then 0 else
      X.enforce (2*a) (f' y) (X.plaza T')*(veil (Z y) R W Y k i-1)) y
    split_ifs
    · exact Brush.zi EventuallyEq.rfl (by linarith only [hT]) ((hh x).trans (hF _))
    let I := field_support S X.B l (.inl i)
    have hΛ:= hx _ _ S T F X hX rfl hL hu E z a R.beta y U f' w H T' I (show T'⊆I from Corona.halo_mono
      (le_mul_of_one_le_left (Nat.zero_le _) hl) (Subset.refl _))
    have hm : Brush j (topStorm S.patch) (|C x|) (fun v=> veil (Z v) R W Y k i) y := curtain U
      (hA _ _ S T F X hX rfl hL ht Y E U y m) (abs_nonneg _) R k i
    refine (hΛ.paints (hm.separating (Brush.certified hm.pos (1:ℝ)))).climb (by rw [norm_one,one_mul]) ?_
    let O:ℝ:= A' (.inl i)
    change B x*O+|C x| ≤ Q x*(1+O)
    have ho:0≤O := Nat.cast_nonneg _
    nlinarith only [ho,h₁ x,abs_nonneg (C x),abs_nonneg (A x), show Q x=B x+|C x|+|A x| from rfl]
  change Brush j _ (f (.inr i)) (fun y=> if X.Hot i ∧ i∉ X.plaza (X.seeds.dome (304*X.B)) then X.cone a (f' y) i-1 else 0) _
  split_ifs
  · refine ((hz c _ S T F X hX hL rfl H.pulse E z a R.beta y U f' w H i).separating (Brush.certified (abs_nonneg (A x)) (1:ℝ))).climb
      (by rw [norm_one]; linarith only [hT]) ((le_add_of_nonneg_left (add_nonneg (h₁ x) (abs_nonneg _))).trans (hF _))
  exact Brush.zi EventuallyEq.rfl (by linarith only [hT]) ((hh _).trans (hF _))
end Silica.Clutch
end YM.ConnectedActivityE6.Blaze
