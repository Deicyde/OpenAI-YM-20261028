import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Jac
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Levan
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Par

/-!
# Real unmasked probes on reference sales with likelihood & Jacobian

 Uses old F, plot, tag choir and stencil. Identity nested even prior
 estimating neighborhood and drawing a Motion. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Flux
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical ENNReal
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {z : Air f G} {E : Type*} [MeasurableSpace E]
variable {a A α β γ d η σ W s b μ r p q C C' v : ℝ} {j n l : ℕ} {Ñ : ChartRatio G}
variable (I : Finset (Bond f)) (X : Coat T F)

/-- Physical sub-density. Use even when new branch is near state not obtained
 from Paint Bud; lens all graph colors. Jacob θ β counted in same score. -/
def scalp (B : Finset (Bond f)) (X : Coat T F) (C : Config G c) (β d : ℝ) (w : Air f G) :=
    let S:= lensS B G; let x := Pond.swim S w
    let g:= Pond.swim S (course X d β w C)
    jacL B X d β C w * (lens₀ (circuit S (vary X C).relating) g / lens₀ (circuit S X.relating) x)

def recoil (B : Finset (Bond f)) (X : Coat T F) (C : Config G c) (d : ℝ) (Ñ : ChartRatio G) (p : Molecule S) (R : Rep G f)
    (W a : ℝ) (l : ℕ) (y : Air f G) :=
    scalp B X C R.beta d y * Polar.floating (vary X C) a R W Ñ (course X d R.beta y C) (own p) l p

def rhythm (B : Finset (Bond f)) (X : Coat T F) (C : Config G c) (d : ℝ) (Ñ : ChartRatio G) (p : Molecule S) (R : Rep G f)
    (W a : ℝ) (l : ℕ) (t : F.Slice G × Air f G) := recoil B (X.wrapY t.1) C d Ñ p R W a l t.2

variable {Y : E→ F.Slice G} {z : E→ Air f G} (h : Canary G d A) (V : Config G c) (hV : Drivable X d A V)
include h hV
lemma steering (he : Measurable Y) (hp : Measurable z) (ht : P.Funds S T) (hF : ShellAccess S G X.x W X.width γ) (β : ℝ) :
    let Z p:=X.wrapY (Y p); Measurable (fun x=> jacL I (Z x) d β V (z x)) ∧ Measurable (fun i=> course (Z i) d β (z i) V) := by
  intro Z; let S' p:= worldZ (Z p) β (z p)
  have hS : Measurable S' := (compassBro (V:=fun _=>X.V) ht measurable_const X he hF β).2.2 z hp
  have hΨ i : Continuous fun v=> fleece G X.χ d (G.mat (action X V i)) v := continuous_iff_continuousAt.mpr fun x=>
    continuousAt_id.add (((Eider.sheen h X.χ x (G.mat (action X V i)) (hV.good i).1.le).continuousAt).comp (f:=fun x=> ((_ : G.Mat),x)) (continuousAt_const.prodMk continuousAt_id))
  have hQ i : Continuous fun v=> palm G X.χ d (G.mat (action X V i)) v := continuous_iff_continuousAt.mpr fun x=>
    ((Eider.lift h X.χ _ x (j:=0) (hV.good i).1.le).continuousAt).comp (f:=fun v=> ((_ : G.Mat),v)) (continuousAt_const.prodMk continuousAt_id)
  have ht' : Measurable fun x i=> steer (Z x) d (S' x) V i := measurable_pi_lambda _ fun i=> (hΨ i).measurable.comp ((measurable_pi_apply i).comp hS)
  have hh := (compassBro (V:=fun x:E=> V) ht measurable_const X he hF β).1
  let M i:=(gStep β)⁻¹ • (steer (Z i) d (S' i) V-voltage (vary (Z i) V)); have hc:Measurable M:= (measurable_const (a:=(gStep β)⁻¹)).smul (ht'.sub hh)
  refine ⟨Finset.measurable_fun_prod _ fun i _=> ?_, (WithLp.measurable_toLp _ _).comp ?_⟩
  · exact (hQ i).measurable.comp ((measurable_pi_apply i).comp hS)
  apply measurable_pi_lambda; intro i; exact (EuclideanSpace.proj (𝕜:=ℝ) (ι:=G.ColorIndex) i.2).measurable.comp
    ((measurable_pi_apply i.1).comp hc)
lemma inshore (he : Measurable Y) (hp : Measurable z) (ht : Intake P T X.x R) (hΞ : ShellAccess S G X.x W X.width γ)
    (hh : LocalRatio Ñ) (p : Molecule S) : Measurable (fun i=> recoil I (X.wrapY (Y i)) V d Ñ p R W a l (z i)) := by
  let P' i:=X.wrapY (Y i); let f x:=course (P' x) d R.beta (z x) V
  obtain ⟨hJ,hZ⟩:= steering I X h V hV he hp ht.ready hΞ R.beta
  have hm (S : Coat T F) {_V : E→ Body (↥ (lensS I G))} (he:Measurable _V):=bulbB (fun _ _=> measurable_const : Borel fun i:E=> circuit (lensS I G) S.relating) he
  have hF : Measurable (fun x=> scalp I (P' x) V R.beta d (z x)) := hJ.mul ((show Measurable fun x=> lens₀ (circuit (lensS I G) (vary X V).relating)
      (Pond.swim _ (f x)) from hm (vary X V) ((swim_m (lensS I G)).comp (show Measurable f from hZ))).div (hm X ((swim_m (lensS I G)).comp hp)))
  apply Measurable.mul (f:=fun x=> scalp I _ _ _ _ _) hF
  exact collectionB X hΞ ht hh (V:=fun x:E=>V) measurable_const he hZ (own p) a l p

omit h hV in
lemma slab (z z' : Air f G) (hp : Pond.swim (lensS I G) z=Pond.swim (lensS I G) z') (d β : ℝ) : scalp I X V β d z=scalp I X V β d z' := by
  unfold scalp jacL; dsimp only; rw [hp,← pitch_alt,← pitch_alt,hp]; refine congrArg₂ (· * ·) ?_ rfl
  apply prod_congr rfl; intro i hi
  have he : X.atmos z i=X.atmos z' i := congrArg (fun t=>stereo I G t ⟨i,hi⟩) hp
  unfold steerJ worldZ; rw [Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,he]

lemma transition (p : Molecule S) (hp : X.relating.PosDef) (he : 500≤l) (Y : Support c) (hS : ground R T l X.B p⊆ Y)
    (q : Room P S T X.x) (ht : Intake P T X.x R) (hh : ShellAccess S G X.x W X.width γ) (hÑ : LocalRatio Ñ) (hv : I=edgesM S Y X.B) :
    bars (lensS I G) (vary X V) p R Ñ W a l=∫ x, (∫ z,recoil I (X.wrapY x) V d Ñ p R W a l z ∂X.dice) ∂ F.order G := by
  unfold bars; apply integral_congr_ae; filter_upwards with x
  let B:= lensS I G; let Z:= X.wrapY x; let A':= circuit B X.relating
  let J:= sweep A'; have hP : MeasurePreserving (swim B) X.dice J := Pond.orbit hp.posSemidef B
  let f : Air f G → ℝ:= recoil I Z V d Ñ p R W a l
  have hF : Measurable f := inshore (Y:=fun (_:Air _ G)=> x) (z:=id) I X h V hV measurable_const measurable_id ht hh hÑ p
  have hB : B=podium S G Y X.B := by unfold B; rw [hv]; exact chargedU ..
  have hf : confined (swim B) f := by
    intro u v hh; unfold f recoil; rw [Flux.slab I Z V u v hh d]; apply congrArg
    have hp := congr_arg (pitch I Z d R.beta V) hh; rw [pitch_alt,pitch_alt] at hp
    apply (Borough.flops (X:=vary Z V) (X':=vary Z V) (l:=l) (Z:=Y) ?_ q he (show Intake P T (vary Z V).x R from ht) _ _ _ hS)
    refine ⟨Village.refl ..,fun i hi=> (Pond.observe B).mp hp i (hB.symm ▸ hi), fun _ _=>Iff.rfl⟩
  have he: Drivable Z d A V := ⟨fun i=> hV.good i⟩
  let F' z:=lens₀ (circuit B (vary Z V).relating) z * Polar.floating (vary Z V) a R W Ñ (Pond.spill B z) (own p) l p
  change (∫ z,F' z) = ∫ z,f z ∂X.dice
  rw [Pond.gathered (Pond.spill B) (spill_m B) hP (settled _) hf hF]
  change _ = ∫ z, f (Pond.spill B z) ∂ sweep A'
  rw [gyre I Z h ht.positive V he F', Shield.recommends A' (show A'.PosDef from hp.submatrix Subtype.val_injective) _]
  apply integral_congr_ae; filter_upwards with y
  let z:= spill B y; let w:= course Z d R.beta z V; let b:=pitch I Z d R.beta V y; let E v:=Polar.floating (vary Z V) a R W Ñ v (own p) l p
  have hG : E (Pond.spill B b)=E w := by
    refine Borough.flops (X:=vary Z V) (X':=vary Z V) (Z:=Y) ?_ q (by assumption) (show Intake P T (vary Z V).x R from ht) _ _ _ hS
    exact ⟨Village.refl ..,fun i hi=> (observe B).1 (settled B b) i (hB.symm ▸ hi),fun _ _=> Iff.rfl⟩
  change jacL _ Z d R.beta V z*(lens₀ _ b*E _)=lens₀ A' y*(scalp I Z V R.beta d z* E w)
  have hp : scalp I Z V R.beta d z=jacL I Z d R.beta V z*(lens₀ (circuit B (vary Z V).relating) b/lens₀ A' y) := by
    unfold scalp; dsimp only; rw [show swim B z=y from settled ..]; rfl
  change jacL _ Z d R.beta V z*(lens₀ (circuit B (vary Z V).relating) b*E _)=_
  rw [hG,hp]; field_simp [ne_of_gt (fullFuel A' y)]
end YM.ConnectedActivityE6.Blaze.Flux
