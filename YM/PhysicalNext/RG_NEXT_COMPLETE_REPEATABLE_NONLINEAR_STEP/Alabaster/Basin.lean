import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Courage
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Molt
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Trinket
/-! # Core contribution fringe's value AND jets, exact same posting per X
     including fresh seats. ∑ budget real at neighboring repr.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Alabaster
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze March Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ} {u : Chi}
variable {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W} {R I : RG.Rep G f}
    {x μ C v : ℝ} {i : ℕ} {H : Cash W x μ L Q o C T R}

variable (Θ : Rig H i v u)
include Θ
lemma rimfire : ∃ M : ℝ,0 ≤ M ∧ ∃ η:ℝ,0<η∧∀ (I:RG.Rep G f) (a b : ℕ → ℝ) (t:ℝ),Equalized Q.table R I a b t→ 0 < t→t ≤ η→ ∀ (d:ℝ) (H' : Cash W x μ L Q o d T I), Rig H' i v u → ∃ f:Molecule S→ℝ, SumBudget f M ∧∀ (F:Forest S.ratio) (X:Coat T F), X.x=x→X.width=o.K→ X.χ=u→∀ (p:Molecule S), (roster p).flags=∅ → Healthy (Pressure.temp x) (H.unionP p) X.V →
     let v₁ Y:= fringe (vary X Y) W o.a p R Q.table Q.halo; let v₂ Y:= fringe (vary X Y) W o.a p I Q.table Q.halo
     Ore X.V (v₂-v₁) v (t*f p) i := by
  obtain ⟨K,hK,s,hs,h⟩:= meritBar Θ.veins
  refine ⟨K,hK,s,hs,?_⟩; intro I a b t hp he ht d H' V; obtain ⟨f',hf,hP⟩:= h I H' a b t hp ht he
  refine ⟨f',hf,?_⟩; intro F X hx hV hχ p hy hh v₁ v₂ E _ _ _ U y hU hψ
  have hz:= acc (H:=H) (H':=H') hp.toFacing p; have hh':= show Healthy _ (H'.unionP p) _ from hz ▸ hh
  have h₁ : v₁ ∘ U=ᶠ[𝓝 y] fun y=>shelter (vary X (U y)) W o.a p R Q.table Q.halo:= rainbow p Θ.plate hx hV hχ hy hh hψ hU
  have h₂ : v₂ ∘ U=ᶠ[𝓝 y] fun y=>shelter (vary X (U y)) W o.a p I Q.table Q.halo:= rainbow p V.plate hx hV hχ hy hh' hψ hU
  have hM := h₂.sub h₁
  refine Brush.shimmy ?_ hM; let B:=radiusB x
  let r' := t*f' p
  have ht':∀ q,(vary X q).B=B:=fun q=>congr_arg _ hx
  change Brush i r' 1 ((fun y=> shelter (vary X (U y)) W o.a p I Q.table Q.halo)-(fun y=>shelter (vary X (U y)) W o.a p R Q.table Q.halo)) y
  unfold shelter; simp_rw [ht',accused hp.toFacing,accusedS hp.toFacing]; split_ifs with heq
  · let s r X k:= bars (podium S G k B) (F:=F) (T:=T) X p r Q.table W o.a Q.halo
    let K₀ r t k i:= s r ((preps (vary X (U i)) (roster p)).taggedL t) k
    let D (t:S.Choices):=K₀ I t (H'.unionP p)-K₀ R t (H.unionP p); let k:ℝ:=Fintype.card S.Choices; have hk:0<k:=by unfold k; positivity
    have hD k: Brush i r' 1 (D k) y := by
      let Y:=((planted X p).taggedL k); have hX:Y.B=B:= ht' X.V
      have hE := hP F Y hx hV hχ (planted_valid X p) E U y hU hψ p (show Healthy (Pressure.temp Y.x) (H.unionP p) Y.V from (by rw [show Y.x=_ from hx]; exact hh)); dsimp only at hE; rw [hX] at hE
      refine hE.shimmy (Eventually.of_forall fun y=>?_); exact congr_arg₂ (fun p q:ℝ=>p-q) (spices p H' X hx (U y) (U y) (fun _ _ _=>rfl) hh' hy k).symm (spices p H X hx (U y) (U y) (fun _ _ _=>rfl) hh hy k).symm
    apply (((Brush.spree _ D _ zero_le_one (fun t (_:t∈univ)=> hD t)).smul k⁻¹).climb ?_ le_rfl).shimmy (Eventually.of_forall fun i=>?_)
    · rw [sum_const,nsmul_eq_mul,card_univ,Real.norm_of_nonneg (inv_nonneg.mpr hk.le),inv_mul_cancel_left₀ hk.ne' _]
    change k⁻¹*(∑ t,K₀ I t (H'.unionP p) i)-k⁻¹*(∑ t,K₀ R t (H.unionP p) i)= k⁻¹*(∑ t,(K₀ I t _ i-K₀ R t _ i))
    rw [← mul_sub, sum_sub_distrib] -- ground rewrite changed??
  exact Brush.zi (Eventually.of_forall fun _=> sub_self _) (mul_nonneg he.le (hf.1 _)) zero_le_one
end YM.PhysicalNext.Repeat.Alabaster
