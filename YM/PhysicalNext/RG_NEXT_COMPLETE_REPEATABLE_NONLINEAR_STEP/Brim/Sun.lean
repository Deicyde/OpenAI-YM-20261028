import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Brim.Heights
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Brim.Lugs
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Brim.Weld

/-!
# Budget-compatible sales, simultaneous for all sectors and tickets

Of course a lower `t` cannot be asserted as if Active P already earned;
use Grants_S for BOTH on same angular covers. `x→excursion` monitors,
price release on unmodified H space even with wrap. Ink manifests outside
active patch not consumed. Recombination up to `p.order`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Brim
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet Quill Baffle Prism
open WardBin.Lies Push.PriceCompiler Foramen Gate
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {B B' : BudgetPoint} {Y : Support c} {K : Support f} {U : Config G c} {p j n : ℕ} {L : Side}
variable {d A t C' w M N z β W k ε J' L₀ X' : ℝ}

lemma widening {ι E:Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E] {B : E→Matrix ι ι ℝ} {x:E} (hb : Prism.Holds B x M n) (hM : M ≤ N): Prism.Holds B x N n := ⟨fun i j=> (hb.liable i j).climb hM le_rfl,fun i j=> (hb.back i j).trans hM,hb.sane⟩
set_option linter.unusedVariables false in
lemma kite {ι E:Type} [Fintype ι] {A B : E→ι→ℝ} [NormedAddCommGroup E] [NormedSpace ℝ E] {x:E} (hA : Moves x n A M)
    (hv : Moves x n (A-B) N) : Moves x n B (M+N) := fun i=> ((hA i).separating (hv i)).shimmy (Eventually.of_forall (fun x=> (sub_sub_cancel ..).symm))

section trunks
variable (G : Gauge) (P : Teller G) (L : Side) (n : ℕ) (Q : Anthem n) (D : Record) (χ κ : Chi) (W : ℝ) (o : ConnectedActivityE6.Target.Order G W)
    (d A : ℝ) (hp : Canary G d A) {M C J v u s : ℝ→ℝ}
    (hM : Rate G L (-(1/2)) M) (hT : Rate G L 0 C) (hJ : Rate G L (-1) J) (hv : Rate G L (-(1/2)) v) (hu : Rate G L (-(1/2)) u) (hs : Rate G L 0 s)
include hM hT hJ hv hu hs hp
-- release labels K untouched by O.P.
lemma sweaters : ∃ N δ V : ℝ→ℝ, Rate G L 0 N ∧ Rate G L (-(1/2)) δ ∧ Rate G L 0 V ∧
    ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio) (Y:Coat T F), Y.x=x → Works P L x S T →
    Y.χ=χ → 8*o.a*Y.t≤ d/2 → ∀ (i : ℕ) (R : Rep G f) (_:Intake P T Y.x R) (I:Type) [Fintype I] [DecidableEq I] (H : Support c)
      (a : Museum F Y.x (bareStores S) (R.activities.reg i).support H I) (q : Chi) (b : ℝ), ∀ y∈H, coverNumber (radiusB Y.x) H ≤ radiusB Y.x →
      ∀ t j (U : Slab G c j), Tentacle (M x) (|C x|) (|J x|) (|v x|) t (|u x|) Y a q b U n →
      ∀ z:Prices G I, ‖z‖ ≤ s x → Score Y i R a q κ b D z (incomingE G L x) d o.a (δ x) (N x) (V x) Q (journey Y.V j U) 0 := by
  obtain ⟨B,B',hB,hb,hX⟩:= Silica.clips hp P L n χ hM
  obtain ⟨Z,hz,hk⟩:= Silica.Clutch.kernels G L χ (absolut hB) n (2*o.a)
  let m:= grade G L; let K x:= (colony L x:ℝ); let H x:= (1+K x*|B' x|)^n; let f x:= (1+K x*|Z x|)^n
  obtain ⟨t,ht,hg⟩:= Brush.compact isCompact_Icc (s:=Set.Icc (0:ℝ) 4) (fun _ _=> (κ.smooth.contDiffAt).of_le (show (↑n:WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))
  let L' := burst G L
  let D₀ x:= L' x*|J x|; let δ x:= |v x|+|D₀ x|
  have hJ': Rate G L (-(1/2)) D₀ := by convert (burst_rate G L).mul (absolut hJ) using 1; ring
  have hδ: Rate G L (-(1/2)) δ:= (absolut hv).add (absolut hJ')
  let F₀ x:=L' x*(|B x|+(|u x|+|u x|))+s x; let F' x:=F₀ x+D₀ x
  let w₀ x:= 1*((Fintype.card G.ColorIndex:ℝ)*F' x); let w x:= (1+K x*((1+(n.factorial:ℝ)*t)*((1+w₀ x*w₀ x)*(1+1))))^n
  let V x:= |C x|+|H x|+|w x|+|f x|+|F₀ x|+|F' x|
  have hx:= Rate.const (G:=G) (L:=L) 1
  have hm : Rate G L 0 m := graded G L
  have hK : Rate G L 0 K:= colonies G L
  have hi : Rate G L 0 F₀ := by refine Rate.add ?_ hs; simpa only [add_neg_cancel] using! ((burst_rate G L).mul ((absolut hB).add ((absolut hu).add (absolut hu))))
  have hf' : Rate G L 0 F':= hi.add (hJ'.weaken (by norm_num))
  have h₀ := (hf'.mul_left (Fintype.card G.ColorIndex:ℝ)).mul_left 1
  have hw : Rate G L 0 w:= prep (hx.add (bell hK (((hx.add (bell h₀ h₀)).mul_right _).mul_left _))) _
  have he : Rate G L 0 V:= (((((absolut hT).add (absolut (prep (hx.add (bell hK (absolut hb))) n))).add (absolut hw)).add (absolut (prep (hx.add (bell hK (absolut hz))) n))).add (absolut hi)).add (absolut hf')
  obtain ⟨_,h₁,h₂,-⟩:= flecks n hm he hδ
  have hF:= projectionX n Q hm he hδ
  refine ⟨m,δ,V,hm,hδ,he,?_⟩
  filter_upwards [hX,hk,snip G L P D hδ,ConnectedActivityE6.room G P L,h₁.below (by norm_num) 1 zero_lt_one,h₂.below (by norm_num) (1/2) (by norm_num),
      hF.below (by norm_num) 1 zero_lt_one, ((incomingE_rate G L).mul he).below (by norm_num) 1 zero_lt_one] with x HH HJ HM hr hK hq hw ht c f' S T h hY hx Hχ hx' hL i R hP I _ _ H' a q b y hy hu t' j U he z hz  -- edit
  subst x; let x:=hY.x
  have hf := hr c f' S T Hχ
  let A' := journey hY.V j U
  have hX₀ : A' 0=hY.V:= Planned.AtomRegular.Sample.journey_origin ..
  let u':= spied hY a z
  have he' := he
  have hp := HH c f' S T h hY rfl Hχ hx' R.beta hP.positive u' (Panels j) A' 0 hX₀ he.sunny
  have hR : hY.t= fiery G x L := by unfold Coat.t x; rw [Hχ.length_eq]
  have hQ : 0<o.a*hY.t := mul_pos o.large hf.fiery
  have hl := hp.2 o.a hQ hL
  have h₀ := HJ _ _ S T h hY rfl Hχ.length_eq hx' (show 0<2*o.a*hY.t by rw [mul_assoc]; positivity)
    (Panels j) u' _ R.beta 0 A' _ _ hl
  have hN : (Fintype.card I:ℝ) ≤ K x := by unfold K; rw [← Hχ.length_eq]; exact_mod_cast settlers a hy hu
  have hv : (Fintype.card (I × G.ColorIndex):ℝ) ≤ m x := by unfold m grade; rw [← Hχ.length_eq]; exact_mod_cast thrives a hy hu
  have hβ: (gStep R.beta)⁻¹ ≤ L' x := burst_h (by rw [← Hχ.length_eq]; exact hP.window.2)
  have hS : Moves 0 n (fun x=> reading6 hY (A' x) a z d R.beta) (F₀ x) := geared hY a z hl he.out hβ hz
  let X6 x:=reading6 hY (A' x) a z d R.beta; let X9 x:= reading9 hY (A' x) a z q b d R.beta
  have hT : Moves 0 n (X6-X9) (D₀ x):= pitch9 hY i R a z q b he.offset hβ hP.positive
  have hb : Moves 0 n X9 (F' x) := kite hS hT
  have hC : 0≤F' x:= by unfold F' F₀ D₀; have ht := (norm_nonneg z).trans hz; have hQ:=le_trans (inv_nonneg.mpr (show 0 ≤ gStep R.beta from by unfold gStep; positivity)) hβ; positivity
  have Hα (X Y Z W U V : ℝ) : let v:=|X|+|Y|+|Z|+|W|+|U|+|V|
                            |X|≤ v ∧ Y≤v ∧ Z≤v ∧ W≤v ∧ V≤ v ∧ U ≤ v := by simp only; refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith only [abs_nonneg X,abs_nonneg Y,abs_nonneg Z,abs_nonneg W,abs_nonneg U,abs_nonneg V,le_abs_self Y,le_abs_self Z,le_abs_self W,le_abs_self U,le_abs_self V]
  have Hα := Hα (C x) (H x) (w x) (f x) (F₀ x) (F' x)
  have hB := hp.1; have hZ (i':Bond f') := (hp.1 i').climb le_rfl (le_abs_self _)
  have hx' : ∀ᶠ y in 𝓝 0,(lamp6 hY a (A' y)).PosDef ∧ (lamp9 hY a (A' y)).PosDef:= he.toward.mono fun y hy=> ⟨hy.1.submatrix (scoop hY a).injective,hy.2⟩
  exact ⟨hX₀,hv,(abs_nonneg _).trans Hα.1,add_nonneg (abs_nonneg _) (abs_nonneg _),(le_abs_self _).trans ht,widening he.area Hα.1,widening he.skies Hα.1,hx',
    fun i j=> (he.trends i j).climb (le_add_of_nonneg_right (abs_nonneg _)) le_rfl,(le_abs_self _).trans hK,(le_abs_self _).trans hq,(le_abs_self _).trans hw,
    (beep hY a z (abs_nonneg _) hN hZ).climb Hα.2.1 le_rfl, fun i=> (hS i).climb Hα.2.2.2.2.2 le_rfl,fun i=> (hb i).climb Hα.2.2.2.2.1 le_rfl,
    fun i=> (hT i).climb ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))) le_rfl,(pane6 hY i R a z hN (abs_nonneg _) h₀).climb Hα.2.2.2.1 le_rfl,
    (pane9 hY i R a z κ q hg D b hP.positive hb hC hN (HM _ _ S T R Hχ.length_eq hP).2.2).climb Hα.2.2.1 le_rfl⟩
end trunks
end YM.PhysicalNext.Repeat.Brim
