import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Plise

/-! # Monomial bookkeeping for M ranks, height scored symbol.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Flux
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets  Silica Poll Pond  Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x:E}
variable {j n : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {X : Coat T F} {I : Finset (Bond f)} {η r Q q Y A a β b p v d : ℝ} {C : E→ Config G c} {w : Air f G}

structure Polyprice (G : Gauge) (L : Side) (f : ℝ → ℝ→ℝ) : Prop where
  fees : ∃ k : ℕ,∃ p, Rate G L 0 p ∧ ∀ x y:ℝ, 1 ≤ y → |f x y| ≤ |p x| * y^k
namespace Polyprice
variable {f g : ℝ→ℝ→ℝ}
lemma fixed {p : ℝ → ℝ} (h : Rate G L 0 p) : Polyprice G L (fun x _=> p x) := ⟨0,p,h, by simp⟩
lemma uniform (G : Gauge) (L : Side) (a : ℝ) : Polyprice G L (fun _ _=> a) := fixed (Rate.const _)
lemma variableP (G : Gauge) (L : Side) : Polyprice G L (fun _ y=> y) := ⟨1,fun _=>1,Rate.const 1, fun x y hy=> by rw [pow_one,abs_of_nonneg (zero_le_one.trans hy),abs_one,one_mul]⟩
lemma together (h : Polyprice G L f) (p : Polyprice G L g) : Polyprice G L (fun x y=> f x y*g x y) := by
  obtain ⟨k,v,hv,hP⟩:=h.fees; obtain ⟨m,w,hW,hx⟩:=p.fees
  refine ⟨k+m,_,(hv.mul hW).weaken (by simp),fun x y hy=>?_⟩; rw [abs_mul,abs_mul]
  refine (mul_le_mul (hP x y hy) (hx x y hy) (abs_nonneg _) (by positivity)).trans_eq ?_
  rw [pow_add]; ring
lemma combine (h : Polyprice G L f) (p : Polyprice G L g) : Polyprice G L (fun x y=> f x y+g x y) := by
  obtain ⟨k,v,hv,hP⟩:=h.fees; obtain ⟨m,w,hW,hx⟩:=p.fees
  refine ⟨k+m,fun x=> |v x| + |w x|, (hv.compare (v:=fun x=> |v x|) (Eventually.of_forall (fun i=> (abs_abs _).le))).add
    (hW.compare (Eventually.of_forall fun i=> (abs_abs _).le)),fun x y hy =>?_⟩
  rw [abs_of_nonneg (show 0 ≤ |v x|+|w x| from add_nonneg (abs_nonneg _) (abs_nonneg _)),add_mul]
  exact ((abs_add_le ..).trans (add_le_add (hP x y hy) (hx x y hy))).trans (by gcongr <;> omega)
lemma powP (h : Polyprice G L f) (j : ℕ) : Polyprice G L (fun x y=> (f x y)^j) := by
  induction j with
  | zero => simp only [pow_zero]; exact uniform ..
  | succ j ih => simp only [pow_succ]; exact ih.together h
end Polyprice

-- total M test on Gaussian margin; rho obejcts relax.
def facescale (I : Finset (Bond f)) (w : Air f G) := 1+(I.card:ℝ)+(lensS I G).card + ∑ i∈ lensS I G,|w i|
lemma expenses (I : Finset (Bond f)) (w : Air f G) : 1 ≤ facescale I w ∧ (I.card:ℝ)≤facescale I w ∧
    ((lensS I G).card:ℝ)≤facescale I w ∧ ∀ i∈lensS I G,|w i| ≤ facescale I w := by
  unfold facescale
  let z := ∑ i∈lensS I G,|w i|; have hz: 0 ≤ z := sum_nonneg fun _ _ => abs_nonneg _
  have hg:0≤(I.card:ℝ):=by positivity
  have hx:0≤((lensS I G).card:ℝ):=by positivity
  refine ⟨by linarith,by linarith,by linarith,fun i hi=> ?_⟩
  exact (Finset.single_le_sum (fun i _=> abs_nonneg (w i)) hi).trans (le_add_of_nonneg_left (by positivity))

lemma own_mat (p : Rotator P L η r Q Y X) (I : Finset (Bond f)) :
    let i:=lensS I G; let m:=tubularPrice G L; Allow (Pond.circuit i X.relating) (along S ∘ (fun v:↥i=>v.val)) m
      (retain η r Q) (Q⁻¹/2) (1+payE η r Q m) := by
  intro i m; have h := p.scale
  have hx:Allow X.relating (along S) m (retain η r Q) (Q⁻¹/2) (1+payE η r Q m) := ⟨h.census,Window.twin ..,h.weather.1,
    half_pos (inv_pos.mpr h.fuel),add_pos_of_pos_of_nonneg zero_lt_one h.disc,
    ((Control.increase (h.mate X.shutter) le_rfl (le_add_of_nonneg_left zero_le_one))).1,h.ground_C X.shutter p.cap⟩
  exact hx.sub (Embedding.subtype (fun z=> z∈i))

-- jets at Φ(TATE)
lemma feast (X : Coat T F) (I : Finset (Bond f)) (V : E → Config G c) (h : Rotator P L η r Q Y (vary X (V x)))
    (hp : Tablet j 0 q v (fun i=> (vary X (V i)).plate) (along S) (along S) x) :
    let i:=lensS I G; let a:=along S ∘ (fun v:↥i=>v.val)
    Tablet j 0 (facePrice j X.B (tubularPrice G L) q (payE η r Q (tubularPrice G L))) (driftP j v)
      (fun u=> Pond.circuit i (vary X (V u)).relating) a a x := by
  intro i a; have he:= Foramen.padjets X.shutter hp h.scale h.full.prices.le
  let p:= (Embedding.subtype (fun z:Tubular f G=> z∈i))
  have hh := (((he.joined he.reverse).scalar (1/2:ℝ)).trim_left (K:=p) (X:=p))
  apply hh.tilt _ le_rfl le_rfl le_rfl
  rw [Real.norm_eq_abs,abs_of_nonneg (by norm_num : 0 ≤ (1/2:ℝ))]; apply le_of_eq; ring

lemma meager {u : E→ Directions G f} {z' : E→ Air f G} (h : Clutch X w a β p x j C u z') (I : Finset (Bond f))
    (hv : ∀ i : Bond f, Brush j b 1 (fun v=> voltage (vary X (C v)) i) x) (_hb : 0≤b)
    (i : ↥(lensS I G)) : let t y:= swim (lensS I G) (z' y)
    Brush j (((gStep β)⁻¹*(p+(b+b)))+facescale I w) 1 (fun i'=> WithLp.ofLp (t i') i) x := by
  intro t; let e:= i.val.1; let q:= i.val.2; let G' y:=vary X (C y)
  have hg : Brush j (b+b) 1 (fun y=> voltage (G' y) e - voltage X e) x := (hv e).separating
    ((Brush.certified zero_le_one _).climb (by have he:= (hv e).bound; rwa [h.tipped] at he) le_rfl)
  let m y:= X.atmos (z' y) e; let g:= gStep β; have hx : 0<g := inv_pos.mpr (Real.sqrt_pos.mpr h.beta)
  have he : Brush j (g⁻¹*(p+(b+b))) 1 (fun y=> m y-X.atmos w e) x := by
    have hh:= ((h.bud e).separating hg).smul g⁻¹; rw [Real.norm_of_nonneg (inv_nonneg.mpr hx.le)] at hh
    refine hh.shimmy (Eventually.of_forall fun y=> ?_); dsimp only; rw [← h.moving y]; symm; apply (inv_smul_eq_iff₀ (show g≠0 from hx.ne')).2
    rw [show worldZ (vary X (C y)) β _ e=voltage (G' y) e + g • m y from rfl, show worldZ X β w e= voltage X e + g • X.atmos w e from rfl,smul_sub]; abel
  have hh := (colorEvaluated q he).gathering ((Brush.certified (show 0≤(1:ℝ) from zero_le_one) (w i.val)).climb ((expenses ..).2.2.2 i.val i.2) le_rfl)
  refine hh.shimmy (Eventually.of_forall (fun y=> ?_)); exact (sub_add_cancel _ _).symm
end YM.ConnectedActivityE6.Blaze.Flux
