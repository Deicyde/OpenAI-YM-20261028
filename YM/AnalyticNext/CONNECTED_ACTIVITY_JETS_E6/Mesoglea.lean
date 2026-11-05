import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Levan
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Pendant

/-!
# Scalp PDF curvature with ratio derivatives (complete C on projection)

 Use stamped Both at projected root. Unit polynomial-in-RUN budget: want
 BurstBall and RGeom. d,T.Color positivity only when using. 
 -/
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
variable {k : Finset ℕ} {R : Rep G f} {z : Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x:E}
variable {a A α β γ d η σ W s b μ r p q C C' v : ℝ} {j m n l : ℕ} {Ñ : ChartRatio G}

section sends
variable {ι : Type} [Fintype ι] [DecidableEq ι] {g : ι→Site c} {A : E→ Matrix ι ι ℝ} {Ω : E → Body ι}

private lemma crystalLog (F : ℝ) (hF : Brush j F 1 Real.log 1) (hp : Tablet j 0 d v A g g x) (hA : (A x).PosDef)
    (hr : Control.Price g g (A x)⁻¹ 0 C) (hC : 0≤C) :
    let p t := Real.log (A t).det - Real.log (A x).det
    let b := d*C+1
    let k := ((↑(j+1:ℕ):ℝ)*(1+Fintype.card ι)^j)*(j.factorial*(1+b*(1+v)^j)^j)
    Brush j (j.factorial*F) ((1+k)*j) p x := by
  intro p b k; let S t:= A t*(A x)⁻¹; let T t:= S t+ -1
  have hs : S x=1:= Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
  have hJ: T x=0:= by unfold T; rw [hs,add_neg_cancel]
  have hF' := hp.enjoin (Tablet.fixed (A x)⁻¹ hr hp.scale hC (le_refl (0:ℝ)))
  simp only [add_zero] at hF'
  have hk : Tablet j 0 b v T g g x := hF'.joined (Tablet.fixed (1:Matrix ..) (one_pay ..) hp.scale zero_le_one hp.pos).mirror
  have he (t:E) : S t=T t+1 := by unfold T; abel
  have hD : Brush j k j (fun t=> (S t).det) x := by
    simp_rw [he]; exact jewels (fun i p=> (hk.singular i p).trim) hJ
      (mul_nonneg hk.basis (pow_nonneg (add_nonneg zero_le_one hp.pos) _))
  have hX : (A x)⁻¹.det=(A x).det⁻¹ := by rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
  apply (hD.pine (by rw [hs,det_one]; exact hF)).shimmy
  filter_upwards [(determinant (fun i j=> (hp.singular i j).smooth)).continuousAt.eventually_ne hA.det_pos.ne'] with t ht
  unfold p; rw [show (S t).det=(A t).det / (A x).det by unfold S; rw [det_mul,hX]; ring,Real.log_div ht hA.det_pos.ne']

lemma oriflamme {F B : ℝ} (hF : Brush j F 1 Real.log 1) (hB : Brush j B 1 Real.exp 0) (hp : Tablet j 0 d v A g g x) (he : Allow (A x) g m η r p)
    (hA : (A x).PosDef) (hw : ∀ i, Brush j W 1 (fun x=> WithLp.ofLp (Ω x) i) x) (hW : 0 ≤ W) :
    let q:= payE η r p m; let b:= token j d q
    let c := (Fintype.card ι:ℝ); let D:= driftP j v
    let k := ((↑(j+1:ℕ):ℝ)*(1+c)^j)*(j.factorial*(1+(d*q+1)*(1+v)^j)^j)
    let z := (j.factorial*F)*(1+(1+k)*j)^j
    let r := (c*(W*(b*W)))*(1+(1+(D+1)))^j
    Brush j 1 ((1+j.factorial*B)*(1+(z+(r+r)))) (fun y=> lens₀ (A y) (Ω y)/lens₀ (A x) (Ω x)) x := by
  intro q b c D k z r
  have hv:= increase he.flatup he.weather.1.le le_rfl
  let α y := WithLp.ofLp (Ω y); let g (y) := -(dotProduct (α y) ((A y)⁻¹ *ᵥ α y)/2)
  have hx := hp.inverter (isUnit_iff_ne_zero.mpr hA.det_pos.ne') hv he.disc
  have ht := driftP j v
  have hg : Brush j r 1 g x := by
    have hg :0 ≤ D:=hx.pos
    have hF := ((((Brush.spree (x:=x) univ _ (fun (_:ι)=> W * (b*W)) (add_nonneg (zero_le_one (α:=ℝ)) (add_nonneg hg zero_le_one)) (fun i _=>
      (hw i).paints (beam_vec hx hW zero_le_one (u:=α) hw i))).trim)) )
    simp only [sum_const, nsmul_eq_mul,card_univ] at hF
    exact (semi hF).opposite
  let L y:=Real.log (A y).det - Real.log (A x).det; let P y := - (L y /2)+(g y-g x)
  have hP : Brush j (z+(r+r)) 1 P x := by
    have hv:Brush j z 1 L x:= (crystalLog F hF hp hA hv he.disc).trim
    exact (semi hv).opposite.gathering (hg.separating ((Brush.certified zero_le_one (g x)).climb hg.bound le_rfl))
  have h₀ : P x=0 := by unfold P L; ring_nf
  apply (((hP.pine (h₀.symm ▸ hB)).exalt (show ‖Real.exp (P x)‖ ≤ 1 by simp [h₀])).climb le_rfl
    (by rw [mul_one])).shimmy
  refine Eventually.of_forall fun t=>?_ ; unfold lens₀ P
  have he : Real.sqrt (2*Real.pi)^Fintype.card ι≠0 := ne_of_gt (by positivity)
  dsimp only; rw [mul_div_mul_left _ _ (inv_ne_zero he), ← Real.exp_sub]
  apply congrArg; unfold L g α; ring
end sends
end YM.ConnectedActivityE6.Blaze.Flux
