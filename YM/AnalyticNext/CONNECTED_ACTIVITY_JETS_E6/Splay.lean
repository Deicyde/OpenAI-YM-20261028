import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Brushhold

/-!
# Rug of payments over full integral expressions at Soma

 L² tilt choreography exact to stamp. Count auxiliaries on shape only.
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
variable {G : Gauge} {j n : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {R : Rep G f}
variable {X : Coat T F} (I : Finset (Bond f)) {η r q Y W A a β b p v d t γ C s C' μ : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi} {H : Cash W s μ L Q o C T R}

lemma spaces (H : Cash W s μ L Q o C T R) (X : Molecule S) : (H.unionP X).card ≤ H.shapeW X *(Animals.ballCost (radiusB s):ℝ) := by
  have hh : ((H.unionP X).card:ℝ) ≤ (∑ i ∈ X, (H.supportP i).card:ℕ) := Nat.cast_le.mpr Finset.card_biUnion_le
  apply hh.trans
  unfold Cash.shapeW Mixed.charges Reserves.setPrice; rw [sum_mul]; push_cast; refine sum_le_sum fun i hi=>?_
  let b:=H.supportP i; let B:=radiusB s
  have hF : (b.card:ℝ) ≤ coverNumber B b*(Animals.ballCost B:ℝ) := by exact_mod_cast brood b B
  apply hF.trans
  have hx : 0≤ Mixed.lengths S H.faresP (lengths T R) i := by rcases i with i|i; exact mul_nonneg H.laws.acquired.extra (Nat.cast_nonneg _); exact Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hx) (Nat.cast_nonneg _)
lemma crewsC (H : Cash W s μ L Q o C T R) (X : Molecule S) : (edgesM S (H.unionP X) (radiusB s)).card ≤
    H.shapeW X * Animals.ballCost (radiusB s)* (Itinerary.density S.patch.L:ℝ) := by
  let p:= H.unionP X; let Y:= univ.filter fun i:Bond f=> atEdge S i∈p
  have he: edgesM S p (radiusB s)⊆ Y := fun i hi=> mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2 (atEdge S i) (by simp)⟩
  have hv: ((edgesM S p (radiusB s)).card:ℝ) ≤ p.card*(Itinerary.density S.patch.L:ℝ) := by
    exact_mod_cast (card_le_card he).trans (perch S p)
  exact hv.trans (mul_le_mul_of_nonneg_right (spaces H X) (Nat.cast_nonneg _))

lemma walksW (G : Gauge) (L : Side) (p : ℝ) (j : ℕ) : ∃ (A : ℝ→ℝ) (n : ℕ), Rate G L 0 A ∧ ∀ S : ℝ, ∀ (ι κ e:ℝ),
    1≤e → 0≤ι → ι≤e*ballCost (radiusB S)*(Itinerary.density L:ℝ) → κ=ι*Fintype.card G.ColorIndex →
    (1+ι+κ+κ)^j*(1+κ*(2*Real.exp (p*(j:ℝ)^2/2))) ≤ |A S| * e^n := by
  let v (x:ℝ) (e:ℝ):= e*ballCost (radiusB x)*(Itinerary.density L:ℝ); let k (x e:ℝ):= v x e*Fintype.card G.ColorIndex
  have he:= width_rate G L 1 0; simp only [one_mul,add_zero] at he
  have hc:= Polyprice.uniform G L 1; have hh := Polyprice.variableP G L
  have hv : Polyprice G L v := (hh.together (Polyprice.fixed he)).together (Polyprice.uniform _ _ _)
  have hp: Polyprice G L k:= hv.together (Polyprice.uniform _ _ _)
  obtain ⟨l,A,h,F⟩:= ((((hc.combine hv).combine hp).combine hp).powP j|>.together (hc.combine
    (hp.together (Polyprice.uniform G L (2*Real.exp (p*(j:ℝ)^2/2)))))).fees
  refine ⟨A,l,h,?_⟩; intro S i K e hr hi hK hV
  apply ((le_abs_self _).trans (F S e hr)) |> le_trans ?_
  change _ ≤ (1+v S e+k S e+k S e)^j*(1+k S e* _)
  rw [hV]; unfold k; replace hK: i ≤ v S e:= hK; gcongr

lemma divideC {κ : Type*} [MeasurableSpace κ] (μ : Measure κ) [IsProbabilityMeasure μ] (f : κ→ℝ)
    (h : Integrable f μ) (b : ℝ) (hb : 0 ≤ b) (S : Set κ) (hS : MeasurableSet S) {v:ℝ}
    (hp : μ.real S ≤ v^2) (hv : 0≤v) (hz : Integrable (fun i=> (f i)^2) μ) (he : ∫ i,(f i)^2 ∂μ ≤ b^2) :
    ∫ x,S.indicator f x ∂μ ≤ b*v := by
  rw [integral_indicator hS]
  let g := μ.real S; let p:= μ.restrict S
  by_cases hg : g=0
  · have hr:μ S=0:= (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hg
    rw [Measure.restrict_eq_zero.mpr hr, integral_zero_measure]; positivity
  have ht:0<g:=lt_of_le_of_ne (by unfold g; positivity) (Ne.symm hg)
  let a := ∫ x, f x ∂p
  have hC : (∫ x,(f x)^2 ∂p)≤ b^2 := le_trans (setIntegral_le_integral hz (ae_of_all _ (fun _=> sq_nonneg _))) he
  have hy: 0 ≤ ∫ x,(f x)^2-2*(a/g)*f x+(a/g)^2 ∂p := integral_nonneg (fun i=> by change (0:ℝ) ≤ (f i)^2-2*(a/g)*f i+(a/g)^2; nlinarith [sq_nonneg (f i-(a/g))])
  have hY i: Integrable (fun x=> i*f x) p := h.restrict.const_mul i
  have hF: Integrable (fun i=> f i^2) p := hz.restrict
  rw [integral_add (show Integrable (fun x=> (f x)^2-2*(a/g)*f x) p from hF.sub (hY _)) (integrable_const _),integral_sub hF (hY _),integral_const_mul, integral_const] at hy
  rw [show p.real Set.univ=g from by unfold p g; simp only [Measure.real,Measure.restrict_apply_univ], smul_eq_mul] at hy
  have he:a^2 ≤ g*b^2 := by
    change 0 ≤ (_ : ℝ) -2*(a/g)*a + g*(a/g)^2 at hy
    have hh := mul_nonneg ht.le hy
    field_simp at hy
    nlinarith
  apply le_of_sq_le_sq _ (mul_nonneg hb hv); rw [mul_pow]; exact he.trans ((mul_le_mul_of_nonneg_right hp (sq_nonneg b)).trans_eq (mul_comm _ _))
end YM.ConnectedActivityE6.Blaze.Flux
