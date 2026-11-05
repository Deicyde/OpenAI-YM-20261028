import YM.UVExtension.Wick.Kilt

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wick
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a p q : ℝ} {z : Air f G} {Y : Config G c}

-- Angular frame scaling on tested lanes. No complex variation in hard coordinates.
variable (d : ℝ)
lemma unity_heat : gStep 1=1:= by norm_num [gStep]
lemma freeze (z : Air f G): scaled 1 z=z:=by rw [scaled,unity_heat,inv_one,one_smul]
def sailplane (z : Air f G) (V:Config G c) := course X d 1 z V
def loom (z : Air f G) := voltage X + X.atmos z
lemma flown (h:0<u) (z : Air f G) (V : Config G c) : course X d u (scaled u z) V= scaled u (sailplane X d z V):= by
  unfold sailplane course; rw [fanned _ _ h]; rw [worldZ,unity_heat,one_smul,inv_one,one_smul]; rfl
lemma embers (h:0<u) (z : Air f G) (V:Config G c) : worldZ (vary X V) u (scaled u (sailplane X d z V))=steer X d (loom X z) V := by
  rw [← flown X d h, Silica.proceeds X d h, fanned X z h]; rfl
lemma stitch (I : Finset (Bond f)) (h:0<u) (z : Air f G) (V:Config G c): jacL I X d u V (scaled u z)=jacL I X d 1 V z:= by unfold jacL; rw [fanned _ _ h,worldZ,unity_heat,one_smul]

def rosined (I : Finset (Bond f)) (y : Config G c) (w : Air f G):=
    let L:= lensS I G; cloud (circuit L X.relating) 1 (Pond.swim L w)-cloud (circuit L (vary X y).relating) 1 (Pond.swim L (sailplane X d w y))
def scorched (I : Finset (Bond f)) (y : Config G c) (v : ℂ) (w : Air f G):ℂ:=
    (Flux.scalp I X y 1 d w:ℂ)*Complex.exp ((v-1)*(rosined X d I y w:ℂ))
lemma real_ears (I : Finset (Bond f)) (h:0<v) (V:Config G c)(z : Air f G):
    (scalp I X V v d (scaled v z))=scalp I X V 1 d z *Real.exp ((v-1)*rosined X d I V z):= by
  unfold scalp rosined; rw [stitch X d I h,flown X d h]; let L:= lensS I G
  let A:=circuit L (vary X V).relating; let S:=circuit L X.relating; let w:= sailplane X d z V
  change jacL _ _ _ 1 _ _*(lens₀ A ((gStep v)⁻¹ • Pond.swim L w)/lens₀ S ((gStep v)⁻¹ • Pond.swim L z))=jacL _ _ _ 1 _ _*(lens₀ A (Pond.swim L w)/lens₀ S (Pond.swim L z))*Real.exp ((v-1)*(cloud S 1 (Pond.swim L z)-cloud A 1 (Pond.swim L w)))
  rw [crispyV _ h,crispyV _ h, mul_div_mul_comm, ← Real.exp_sub]; ring_nf
lemma coal (I : Finset (Bond f)) (hv:0<v) (V:Config G c) (z : Air f G) (u : ℂ) : scorched X d I V u z=
    (scalp I X V v d (scaled v z):ℂ)*Complex.exp ((u-(v:ℂ))*(rosined X d I V z:ℂ)):= by
  rw [real_ears X d I hv]; push_cast; rw [mul_assoc,← Complex.exp_add]; unfold scorched; apply congr_arg; apply congr_arg; ring
lemma censored (I : Finset (Bond f)) (hv:0<v) (V:Config G c) (z : Air f G):
    (scalp I X V v d (scaled v z):ℂ)=scorched X d I V v z:= by rw [coal X d I hv]; simp
variable {ι : Type} [Fintype ι] (V : ι → Juice G f)

def cockpit (X : Coat T F) (d a W : ℝ) (p : Molecule S) (R : Rep G f) (Ñ:ChartRatio G) (l : ℕ) (V:ι → Juice G f)
    (z : Vines ι) (I : Finset (Bond f)) (U : Config G c) (y:F.Slice G × Air f G):ℂ:=
    let Y:=X.wrapY y.1; let u:=steer Y d (loom Y y.2) U; let t:=vary Y U
    scorched Y d I U (z none) y.2 * ∏ i∈p, amberP t R Ñ W a (Matter.own p) l V (z none) (z ∘ some) (sailplane Y d y.2 U) u (t.input u) i

def held (X : Coat T F) (d a W : ℝ) (p : Molecule S) (R : Rep G f) (Ñ:ChartRatio G) (l : ℕ) (V:ι → Juice G f)
    (z : Vines ι) (I : Finset (Bond f)) (U : Config G c) (y:F.Slice G × Air f G):ℂ:=
    let Y:=X.wrapY y.1; let u:=steer Y d (loom Y y.2) U; let t:=vary Y U
    scorched Y d I U (z none) y.2 * ∏ i∈p, amberP t R Ñ W a (Matter.own p) l V (z none) (z ∘ some) (sailplane Y d y.2 U) u (Y.input (loom Y y.2)) i
lemma jetcoin (y:F.Slice G) (U:Config G c) (u : ℝ) (R:Rep G f) (W:ℝ) (Ñ:ChartRatio G) (h:LocalRatio Ñ) (z:Air f G)
    (σ : Drums ι) (a:ℝ) (p:Molecule S) (I:Finset (Bond f)) (hv:σ none=u) (ht:0<u) (l:ℕ) :
    (Flux.rhythm I X U d Ñ p (chunk R (blend V (σ ∘ some)) u) W a l (y,scaled u z):ℂ)=
      cockpit X d a W p R Ñ l V (hoist σ) I U (y,z):= by
  subst u; let u:=σ none; unfold cockpit rhythm Flux.recoil; dsimp only [chunk]; push_cast
  refine congr_arg₂ (·*·) (censored _ _ _ ht U z) ?_
  unfold floating; dsimp only [flight]; rw [Complex.ofReal_prod]; refine prod_congr rfl fun i hi=> ?_
  rw [flown _ _ ht,embers _ _ ht]; exact (originalP _ V (σ ∘ some) h ht i).symm
lemma amp_hol (Ñ : ChartRatio G) (i : Head S) (v : ℝ) (hp:0<v) (x: Finset ℕ) (l:ℕ) (W B:ℝ) (z:Air f G) (U:Directions G f) (w : Config G f) :
    Bumps (parade v B) (fun t:Vines ι=> amberP X R Ñ W a x l V (t none) (t ∘ some) z U w i) := by
  intro s f hs hf hZ; have he i:DifferentiableOn ℂ (fun t=> f t i) s:= (ContinuousLinearMap.proj (R:=ℂ) (φ:=fun _:Option ι=>ℂ) i).differentiable.comp_differentiableOn hZ
  rcases i with i|i|i|i; all_goals unfold amberP; dsimp only [Sum.elim]
  · split_ifs; exacts [((warmth_diff X (he none) (fun z hz=> breath hp (marching (f z)|>.1 (hf hz)).1) 1 i _).mul_const _), (differentiableOn_const _)]
  · exact DifferentiableOn.fun_sum (fun i _=> (he _).mul_const _)
  · unfold valRay; split_ifs; exacts [((DifferentiableOn.fun_sum fun i _=> (he _).mul_const _).cexp.sub_const _),(((he _).mul_const _).cexp.sub_const _),(differentiableOn_const _)]
  exact differentiableOn_const _
end YM.UVExtension.Wick
