import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Pommel
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Cupola
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Aria
import YM.RemainderComparison.Gear.Class

/-!
 # New vouchers for angular motion

 Share each parameter with the *same* oboe, Lamp. Meant for
 roots projected by activation of opaque lamps. Only
 demand on actual copy (availability post stamp). No smooth masks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat RemainderComparison
open Eider Silica
open Brush
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical NNReal ENNReal
variable {G : Gauge} {d A x : ℝ}
lemma stripped (p : Canary G d A) (P : Teller G) (L : Side) (j : ℕ) (χ : Chi) {V : ℝ→ℝ} (h : Gear G L (-(1/2)) V) :
    ∃ B D, Gear G L (-(1/2)) B ∧ Reserve G L D ∧ ∀ᶠ x in atTop,
      ∀ (c f:Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio) (X : Coat T F), X.x=x → Works P L x S T → X.χ=χ → ∀ β>0,
      ∀ z : Air f G, ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (U:E→ Config G c) (y:E), U y=X.V → Mode U y j (V x) →
        let u:=Vine.worldZ X β z
        (∀ i,Brush j 1 (D x) (fun v=>steerJ X d u (U v) i) y) ∧ (∀ a : ℝ, 0<a*X.t → 8*a*X.t ≤ d/2 →
          Clutch X z a β (|B x|) y j U (fun v=> steer X d u (U v)) (fun v=>course X d β z (U v))) := by
  obtain ⟨v,z,hv,hz,hβ'⟩:= Eider.thorax p χ j; let D s:=(1+royalty G)*V s
  let B s:= (j.factorial:ℝ)*v* D s; let K:=(j.factorial:ℝ)*z
  have hk:= h.mul_left (1+royalty G)
  refine ⟨B,fun s=>(1+K)*D s,hk.mul_left _,Gear.zero.mp ((hk.mul_left _).weaken (by norm_num)),?_⟩
  filter_upwards [hk.rate.below (by norm_num) 1 zero_lt_one] with x hX c f S T F X h hr hχ β hβ s E _ _ U y ht hh u
  subst χ
  let M (j: Bond f) (t:E):=G.mat (action X (U t) j)
  have hM (i:Bond f): M i y=1:=by unfold M; rw [ht]; simp only [Silica.action,mul_inv_cancel,G.mat_one]
  have hp i: Brush _ (royalty G) (V x) (M i) y:= chargeMode X (V x) hh i
  have hm i : Brush j (B x) 1 (fun z' => plume G X.χ d (M i z') (u i)) y := by
    have hv:= (hp i).pine (show Brush j v 1 (fun M=> plume G X.χ d M (u i)) (M i y) from hM i |>.symm ▸ (hβ' (u i)).1)
    have hL : ‖plume G X.χ d (M i y) (u i)‖≤0 :=by rw [hM,nothing p, norm_zero]
    simpa only [zero_add] using! shrinker hv hL (show D x≤1 from (le_abs_self _).trans hX)
  refine ⟨fun i=>?_,fun a ha hF=> ⟨ht,hβ,?_,ha,fun v=> proceeds _ _ hβ _ _,abs_nonneg _,?_,?_⟩⟩
  · unfold steerJ
    have hz:= (hp i).pine (show Brush j z 1 (fun M=> palm G X.χ d M (u i)) (M i y) from hM i |>.symm ▸ (hβ' (u i)).2)
    have hL : ‖palm G X.χ d (M i y) (u i)‖≤1:=by rw [hM,leaves p,norm_one]
    exact Brush.exalt hz hL
  · rw [ht,home X p s hβ]
  · intro i; unfold steer fleece; change Brush _ _ _ (fun v=> u i+_ -u i) _; simp_rw [add_sub_cancel_left]; exact
      (hm i).climb (le_abs_self _) le_rfl
  filter_upwards [nearby X p ht hh] with y hh; exact conquered X p (U y) u hh ha hF
lemma canopyG (G : Gauge) (L : Side) (χ : Chi) {V : ℝ→ℝ} (h : Gear G L (-(1/2)) V) (j : ℕ) (b : ℝ) :
    ∃ B, Reserve G L B ∧ (∀ x,0≤B x) ∧ ∀ x : ℝ, ∀ (c f:Side) (S:StepData c f) (T:Tube G S) (F : Forest S.ratio)
      (X : Coat T F), X.x=x → X.χ=χ → S.patch.L=L → 0 < b*X.t → ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      (z : Air f G) (a β : ℝ) (y:E) (U : E→ Config G c) (f':E → Directions G f) (w:E → Air f G), Clutch X z a β (V x) y j U f' w →
        ∀ Y (M:Support c),Y⊆ M → Brush j 1 (B x*coverNumber X.B M) (fun y=> X.enforce b (f' y) (X.plaza Y)) y := by
  obtain ⟨w,hp,hX⟩ := Brush.compact (k:=j) (f:=χ.read) (s:=Set.Icc 0 4) isCompact_Icc (fun _ _=>
    (χ.smooth.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)))
  let t:= (Pressure.fiery G · L); let K x:= (b*t x)⁻¹*(V x +2*b*t x)
  have hk:Reserve G L K := by
    have hh: Gear G L (1/2) (fun x=> (b*t x)⁻¹) := by simpa only [_root_.mul_inv_rev] using! ((Gear.inverse (G:=G) (L:=L)).mul_right b⁻¹)
    apply Gear.zero.mp; convert hh.mul (h.add (Gear.mul_left (Gear.flame (G:=G) (L:=L)) (2*b))) using 1; norm_num
  let C x:=(1+(j.factorial:ℝ)*w)*((1+K x*K x)*(1+1))
  have hh:Reserve G L C:= (Reserve.const _).mul (((Reserve.const _).add (hk.mul hk)).mul (Reserve.const _))
  let B x:=(ballCost (radiusB x):ℝ)*ballCost 1*Pulse.Itinerary.density L*|C x|
  refine ⟨B,(((Reserve.ball _ Reserve.field).mul (Reserve.const _)).mul (Reserve.const _)).mul hh.absolute,fun x=>by unfold B; positivity,?_⟩
  intro x c f S T F X he hχ hL hw E _ _ z a β y U f' W H Y M hm
  have hC i : Brush j 1 (|C x|) (fun y=> X.cone b (f' y) i) y:=by
    by_cases hp:(fun y=> X.cone b (f' y) i)=ᶠ[𝓝 y] fun _=>0
    · exact Brush.zi hp zero_le_one (abs_nonneg _)
    obtain ⟨hd,hA⟩:= H.fostered i hw hp
    unfold cone; rw [hχ]; apply (plateauChi χ hA hX hw (by rw [← mul_assoc]; exact hd)).climb le_rfl
    unfold C Coat.t; simp_rw [he,hL]; exact le_abs_self _
  apply (Blaze.canopy (a:=b) (X:=X) f' M (|C x|) (M:=X.plaza Y) (fun i _=> hC i) (worn X hm) (abs_nonneg _)).climb le_rfl
  apply le_of_eq; unfold B; rw [← he,hL]; change _= (ballCost X.B:ℝ)* _ * _ * _ * _
  ring
end YM.ConnectedActivityE6.Blaze
