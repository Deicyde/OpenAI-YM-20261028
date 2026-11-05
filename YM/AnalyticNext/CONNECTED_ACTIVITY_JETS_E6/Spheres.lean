import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Brushhold
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Mesoglea
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Tropolis

/-! # Budget for recoil wrt Rand clock.

 No Port claim on inactive characters. Spectral invoice uniform γ. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Flux
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x:E}
variable {j n : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {X : Coat T F} (I : Finset (Bond f)) {η r Q q Y A a β b p v d t σ : ℝ} {C : E→ Config G c} {w : Air f G}

def cenote (i:ℕ) (c g s t : ℝ) := ((↑(i+1:ℕ):ℝ)*(1+c)^i)*(i.factorial*(1+(s*g+1)*(1+t)^i)^i)
def seismic (i:ℕ) (u h f z b w y : ℝ) :=
    let d := cenote i y z f b; let s:= driftP i b
    let t:= (y*(w*(token i f z*w)))*(1+(1+(s+1)))^i
    (1+i.factorial*h)*(1+((i.factorial*u)*(1+(1+d)*i)^i+(t+t)))
lemma elevates {F B : ℝ} (hF : Brush j F 1 Real.log 1) (hB : Brush j B 1 Real.exp 0) (hp : Rotator P L η r Q Y (vary X (C x)))
    (he : Tablet j 0 v d (fun i=> (vary X (C i)).plate) (along S) (along S) x) (hL : ∀ i, Brush j A 1 (fun y=>voltage (vary X (C y)) i) x) (hA : 0≤A)
    (hq : Clutch X w a β t x j C (fun v=> steer X p (worldZ X β w) (C v)) (fun v=>course X p β w (C v))) (h : ∀ i,Brush j 1 q
    (fun v=>steerJ X p (worldZ X β w) (C v) i) x) (hh : 0≤q) (hw : (gStep β)⁻¹*(t+(A+A))+facescale I w≤b):
    let m:=tubularPrice G L; let z:=payE η r Q m; let f:=facePrice j X.B m v z; let t:= facescale I w
    let D:= seismic j F B f (payE (retain η r Q) (Q⁻¹/2) (1+z) m) (driftP j d) b t
    Brush j 1 (t*q+D) (fun y=> scalp I X (C y) β p w) x := by
  intro m z f' t' D
  let s v:=course X p β w (C v); let i:=lensS I G; let n(v):= Pond.swim i (s v); let Y(v):= Pond.circuit i (vary X (C v)).relating
  have he:= feast X I C hp he
  have hh' : 0≤b := by
    have ht:= hq.price; have hg:0 < (gStep β)⁻¹ := inv_pos.mpr (inv_pos.mpr (Real.sqrt_pos.mpr hq.beta))
    have hh := (expenses I w).1; exact le_trans (by positivity) hw
  have hz := oriflamme (Ω:=n) hF hB he (own_mat hp I) (hp.fullC.submatrix Subtype.val_injective) (fun i=> (meager hq I hL hA i).climb hw le_rfl) hh'
  let F' := payE (retain η r Q) (Q⁻¹/2) (1+z) m
  have hy : 0≤F' := (own_mat hp I).disc
  let M:ℝ:= (lensS I G).card; let K:=seismic j F B f' F' (driftP j d) b M
  have hu : Brush j 1 K (fun y=> lens₀ (circuit i (vary X (C y)).relating) (n y)/lens₀ (circuit i X.relating) (Pond.swim i w)) x := by
    have hf:n x= Pond.swim i w := congr_arg (Pond.swim i) hq.birth
    dsimp only at hz; rw [hq.tipped,hf,Fintype.card_coe] at hz; exact hz
  have hX : 0≤driftP j d:= he.pos; have hY:= he.basis
  have h : Brush j 1 ((I.card:ℝ)*q) (fun y=> jacL I X p β (C y) w) x := by
    simpa only [sum_const,nsmul_eq_mul, prod_const_one] using! Brush.all_prod I _ _ _ (fun i (_:i∈I)=> h i)
  refine (h.paints hu).climb (one_mul _).le (add_le_add (mul_le_mul_of_nonneg_right (expenses I w).2.1 hh) ?_)
  unfold D K seismic; dsimp only
  let H := driftP j d; have he:=hF.nonneg; have hx:=hB.nonneg; have hn := (expenses I w).2.2.1
  have hg : 0≤token j f' F' := by unfold token; exact sum_nonneg fun _ _=> by change 0≤ (f'*F'+1)^_*F'; positivity
  have hm:0≤M := Nat.cast_nonneg _
  have hp : 0≤ f':=hY
  change M ≤ t' at hn
  have hh : cenote j M F' f' H≤cenote j t' F' f' H := by unfold cenote; gcongr
  have hy : 0≤cenote j M F' f' H := by unfold cenote; positivity
  have hΘ:0≤driftP j (driftP j d):= mul_nonneg (Nat.cast_nonneg _) hX
  gcongr
end YM.ConnectedActivityE6.Blaze.Flux
