import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Das


/-!
# Same chart map on any receptive lens: tiling Euclidean spaces

 All colors per receptive coordinate. Doesn't change normalization choosing
 the sup vs 2 norm coordinates; compute derivative in Euclid, evaluate by
 blocks for exact determinant. Includes empty plots.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Flux
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets  Silica Poll Pond  Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical ENNReal
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {z : Air f G} {E : Type*}
variable {a A α β γ d η σ W s b μ r p q C C' v : ℝ} {j n l : ℕ} {Ñ : ChartRatio G}

-- General footprint lens; instantiate with `podium`. P empty even y dim=0.
def lensS (P : Finset (Bond f)) (G : Gauge) := P×ˢ (univ:Finset G.ColorIndex)

def edgesM (S : StepData c f) (H : Support c) (b : ℕ) := univ.filter (fun p: Bond f=> Cleanroom H (25*b) (atEdge S p))
lemma chargedU (H : Support c) (b : ℕ) : lensS (edgesM S H b) G=podium S G H b := by
  ext i; simp only [lensS,edgesM,mem_product,mem_filter,mem_univ,true_and,and_true,podium,along]
variable (P : Finset (Bond f))
def tongs : Body (↥(lensS P G)) →ₗ[ℝ] (P→G.Color) :=
    { toFun z p:= WithLp.toLp 2 fun i : G.ColorIndex=> z ⟨(p.1,i),mem_product.mpr ⟨p.2, mem_univ _⟩⟩
      map_add' _ _:=rfl
      map_smul' _ _:=rfl }
def spikes (G : Gauge) (p : ↥(lensS P G)) : ↥ P:= ⟨p.1.1,(mem_product.mp p.2).1⟩
def hinges : (P→ G.Color) →ₗ[ℝ] Body (↥(lensS P G)) :=
    { toFun t:= WithLp.toLp 2 fun i=> t (spikes P G i) i.val.2
      map_add' _ _:=rfl
      map_smul' _ _:= rfl }

def stereo (G : Gauge) : Body (↥(lensS P G)) ≃L[ℝ] (P→G.Color) := (LinearEquiv.ofLinear (tongs P) (hinges P) (by
    ext i j k; rfl) (by ext i j; rfl)).toContinuousLinearEquiv

lemma serves (X : Coat T F) (z : Air f G) (i:P) : stereo P G (swim (lensS P G) z) i=X.atmos z i.val := rfl
lemma arid (X : Coat T F) (z : Body (↥(lensS P G))) (i:P) : stereo P G z i=X.atmos (spill (lensS P G) z) i.val := by
  nth_rw 1 [← Pond.settled (lensS P G) z]; rw [serves]

def pitch (X : Coat T F) (d β : ℝ) (V : Config G c) (z : Body (↥(lensS P G))) := Pond.swim (lensS P G) (course X d β (Pond.spill (lensS P G) z) V)

def chore (X : Coat T F) (d β : ℝ) (V : Config G c) (i : Bond f) (a : G.Color) :=
    let g:= gStep β; g⁻¹ • (Eider.fleece G X.χ d (G.mat (action X V i)) (voltage X i+g • a) - voltage (vary X V) i)

lemma marquee (X : Coat T F) (d β : ℝ) (V : Config G c) (z : Air f G) (i : Bond f) :
    X.atmos (course X d β z V) i=chore X d β V i (X.atmos z i) := rfl
lemma quirk (X : Coat T F) (d β : ℝ) (V : Config G c) (z : Body (↥(lensS P G))) :
    pitch P X d β V z=(stereo P G).symm (fun i=> chore X d β V i.val (stereo P G z i)) := by
  apply (stereo P G).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]; funext i; unfold pitch; rw [serves P X,arid P X,marquee]

lemma pitch_alt (X : Coat T F) (d β : ℝ) (V : Config G c) (z : Air f G) :
    pitch P X d β V (Pond.swim (lensS P G) z)= Pond.swim (lensS P G) (course X d β z V) := by
  apply (stereo P G).injective
  rw [quirk,ContinuousLinearEquiv.apply_symm_apply]; funext i; rw [serves P X]; rfl

lemma has_chore (X : Coat T F) (p : Eider.Canary G d A) (h : 0<β) (V : Config G c) (hv : Drivable X d A V)
    (i : Bond f) (a : G.Color) : let M := G.mat (action X V i); let z:= voltage X i+gStep β • a
    HasFDerivAt (chore X d β V i) (pax G X.χ d M z) a := by
  intro M z; let g:= gStep β; have he : 0<g := inv_pos.mpr (Real.sqrt_pos.mpr h)
  let Z x:= voltage X i+g • x; let P:= pax G X.χ d M z
  have hZ : HasFDerivAt Z (g • ContinuousLinearMap.id ℝ G.Color) a := (hasFDerivAt_id a).const_smul g|>.const_add _
  have hh:= (((Eider.plum p X.χ z M ((hv.good i).1.le)).comp a hZ).sub_const (voltage (vary X V) i)).const_smul (g⁻¹)
  convert! hh using 1; ext x; simp [z,g, he.ne', inv_smul_smul₀]

lemma across (X : Coat T F) (_p : Canary G d A) (h : 0<β) (V : Config G c) (hv : Drivable X d A V) : Bijective (pitch P X d β V) := by
  let g:=gStep β; have hh:g≠0 := (inv_pos.mpr (Real.sqrt_pos.mpr h)).ne'
  let f:= fun s:P→ G.Color=> fun i:P=> chore X d β V i.val (s i)
  have hp i : Bijective (chore X d β V i) := by
    let f:= Eider.fleece G X.χ d (G.mat (action X V i)); let U:= voltage (vary X V) i
    have he: Bijective f:= (hv.good i).2.1; constructor
    · intro x y h; change g⁻¹ • _ = g⁻¹ • _ at h; apply_fun (fun y:G.Color=>g • y) at h 
      rw [smul_inv_smul₀ hh,smul_inv_smul₀ hh] at h
      have hp : g • x=g • y:= add_left_cancel (he.1 (sub_left_inj.mp h)); exact (smul_right_injective _ hh) hp
    intro i'; obtain ⟨a,ha⟩:= he.2 (g • i'+U)
    refine ⟨g⁻¹ • (a-voltage X i),?_⟩; change g⁻¹ • (f _-U)=_; rw [smul_inv_smul₀ hh,add_sub_cancel,ha,add_sub_cancel_right,inv_smul_smul₀ hh]
  have hF: Bijective f := by
    constructor
    · intro x y he; exact funext fun i=> (hp _).1 (congr_fun he i)
    intro x; choose u hu using fun i:P=> (hp i.val).2 (x i)
    exact ⟨u,funext hu⟩
  rw [show pitch P X d β V=(stereo P G).symm ∘ f ∘ (stereo P G) from funext fun z=> quirk P X _ _ _ z]
  exact (stereo P G).symm.bijective.comp (hF.comp (stereo P G).bijective)
end YM.ConnectedActivityE6.Blaze.Flux
