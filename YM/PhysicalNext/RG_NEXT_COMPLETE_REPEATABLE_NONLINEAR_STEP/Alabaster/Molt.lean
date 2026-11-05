import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Loom
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Satin
/-!
# Uniform consummation of orbit at unforced Molecule. Genuine warp.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Alabaster
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W} {R I : RG.Rep G f}
    {p μ C v D' d r D K' : ℝ} {i j n m : ℕ} {χ : Chi} {H : Cash W p μ L Q o C T R} {η εK θ β a h g l b Y A q e r' u : ℝ}
local notation "F₀" => (facescale (univ:Finset (Bond f)))
local notation "L₁" => low R I
lemma acc {μ X : ℝ} {H' : Cash W p X L Q o μ T I} (P : Facing R I) (n:Molecule S) : H.unionP n=H'.unionP n := by unfold Cash.unionP; change n.biUnion (Matter.areas R T _ _)=n.biUnion (Matter.areas I T _ _); unfold Matter.areas; rw [show footprints T R Q.halo (radiusB p)=footprints T I Q.halo (radiusB p) from ?_]; unfold footprints; rw [show Raw.forcedFoot S.ratio Q.halo (radiusB p) R=forcedFoot S.ratio Q.halo (radiusB p) I from funext (pointed P _ _),roadway,roadway, location P]

variable (V : Loom H a b v χ j)
include V
theorem meritBar : ∃ K : ℝ,0 ≤ K ∧ ∃ s:ℝ,0 < s∧∀ {C':ℝ} (I:RG.Rep G f) (H':Cash W p μ L Q o C' T I) (g g₀:ℕ→ℝ) (t:ℝ),Equalized Q.table R I g g₀ t→t ≤ s →0<t →
    ∃ f:Molecule S→ℝ, SumBudget f K ∧ ∀ (F:Forest S.ratio) (X:Coat T F), X.x=p→ X.width=o.K→ X.χ=χ→X.manifest→ ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (U:E→ Config G c) (x:E), U x=X.V→ Mode U x j v → ∀ p':Molecule S,
       Healthy (Pressure.temp X.x) (H.unionP p') X.V →
       let u₀ y:= bars (podium S G (H.unionP p') X.B) (vary X (U y)) p' R Q.table W o.a Q.halo
       let u' y:= bars (podium S G (H'.unionP p') X.B) (vary X (U y)) p' I Q.table W o.a Q.halo
       Brush j (t*f p') 1 (u'-u₀) x := by
  obtain ⟨K,hK,s,hs,h',h⟩:= spectra V
  let n:= V.order+2*j; let C i:= cargo G L f o.eta o.gap o.ample i; let z:=massQ G f L o.eta o.gap o.ample; let A := (2^n*C n + z * (C (n+2)+2^(n+2)*C (n+2))) + C n
  refine ⟨|A| *K,mul_nonneg (abs_nonneg _) hK,s,hs,?_⟩; intro C' I H' g k t hp hs ht; obtain ⟨f',hF,n,hn,Hp⟩:=h I H' g k t hp hs ht
  subst n; refine ⟨fun i=> |A| *f' i,budget_scale (abs_nonneg _) hF,?_⟩
  intro F X hx hv hχ hm E _ _ _ U x ht' hU q hQ u u'
  let A' := X.relating; let w:= H.unionP q; let L':= low R I; let J:= edgesM S w (radiusB p); let μ:=(F.order G).prod X.dice; let P R y (x:F.Slice G × Air f G):= rhythm J X (U y) a Q.table q R W o.a Q.halo x
  have hd : H'.unionP q=w:=(acc (H:=H) hp.toFacing _).symm; have hb : Rotator _ _ _ _ _ _ X:= (H.laws.data.localP F X hx hv hm).sails; have hc := V.mask F X hx hv hχ hm E U x ht' hU|>.1
  have he := chutes (V:=U) H hx hm hv hc V.body V.grants q; have he' := chutes H' hx hm hv hc V.body V.grants q; have hY := boosts H hx hm hv hc V.body V.grants q J; have hY' := boosts H' hx hm hv hc V.body V.grants q J
  have hB : X.B=radiusB p:= congr_arg _ hx
  let u₁ y:=∫ z,P R y z ∂μ; let u₂ y:=∫ z,P I y z ∂μ
  have hg : u=ᶠ[𝓝 x] u₁:= by unfold u; rw [hB]; exact he
  have hg' : u'=ᶠ[𝓝 x] u₂:= by unfold u'; rw [hB,hd]; dsimp only at he'; rw [hd] at he'; exact he'
  have hL := hY.1.calls; have hL' := hY'.1.calls
  have hp' : 0<L':= (uplift hp.toFacing).2.2.1; let T x:=walk A' L' x; let g(z:F.Slice G × Air f G):= (T z.2+ |T z.2-1|/t +1)*growF n z
  have hm' := ht.ne'
  obtain ⟨hr,hθ⟩:= hearth X hb n hp' (hs.trans h') hp.heat; obtain ⟨hγ,hξ⟩:= amplitude X hb n hp' (hs.trans h') hp.heat; obtain ⟨hy,hz⟩:= ingot X hb n
  let v(z:F.Slice G× Air f G):= T z.2*growF n z
  let y(z:F.Slice G× Air f G):= |T z.2-1| *growF n z
  have hG : g=(v+ t⁻¹ • y)+growF n:= funext fun i=> by change (_+_/t+1)*_= v i+t⁻¹*y i+growF n i; unfold v y; ring
  have hI : Integrable g μ:= hG.symm ▸ ((hr.add (show Integrable (t⁻¹ • y) μ from hγ.smul _)).add hy)
  have hp₁ : ∫ x,g x ∂μ ≤ |A|:= by
    rw [hG,integral_add' (show Integrable (v+t⁻¹ • y) μ from (hr.add (show Integrable (t⁻¹ • y) μ from (hγ.smul t⁻¹)))) (show Integrable (growF n) μ from hy), integral_add' (show Integrable v μ from hr) (show Integrable (t⁻¹ • y) μ from (hγ.smul t⁻¹))]; simp_rw [Pi.smul_apply,integral_smul]
    apply le_trans (b:=A) ?_ (le_abs_self _); apply add_le_add (add_le_add hθ ?_) hz; change t⁻¹*_≤_; exact (mul_le_mul_of_nonneg_left hξ (inv_pos.mpr ht).le).trans_eq (by field_simp; rfl)
  apply Brush.shimmy _ (hg'.sub hg)
  refine Brush.offer.2 ⟨hL'.1.sub hL.1,fun i hi=>?_⟩; unfold normJ; rw [iteratedFDeriv_sub_apply (show ContDiffAt ℝ i u₂ x from hL'.1.of_le (Nat.cast_le.mpr hi)) (show ContDiffAt ℝ i u₁ x from hL.1.of_le (Nat.cast_le.mpr hi))]
  let Z:=P R; let V':=P I; have hL' := hL'.2 i hi; have hL:=hL.2 i hi
  let F₁ (i:F.Slice G× Air f G):= (i.1,L' • i.2) -- shadow edit
  let D i':= T i'.2 • JetF V' i x (F₁ i')
  have he' := earningsK (μ:=F.order G) _ hb.fullC hp' (JetF V' i x)
  have hd : Integrable D μ:= he'.2.1 hL'.1
  let V₁:=t * f' q; have hvQ : 0 ≤ V₁:= mul_nonneg ht.le (hF.1 _)
  rw [(show iteratedFDeriv ℝ i u₂ x=∫ x,D x ∂μ from hL'.2.trans he'.1),(show iteratedFDeriv ℝ i u₁ x=∫ v,JetF Z i x v ∂μ from hL.2),← integral_sub hd hL.1]
  refine (norm_integral_le_integral_norm _).trans ((integral_mono_ae ((hd.sub hL.1).norm) (hI.const_mul V₁) ?_).trans ?_)
  · obtain ⟨s',hxS,hS,hxQ⟩:= hY.1.haveSmooth
    filter_upwards [hS] with t ht
    obtain ⟨y,z'⟩:=t; let X':= X.wrapY y
    let O x':= P R x' (y,z'); let O' x':= P I x' (F₁ (y,z'))
    have ht : ContDiffAt ℝ i O x:= (ht x (mem_of_mem_nhds hxS)).of_le (Nat.cast_le.mpr hi)
    have he := Hp F X' hx hv hχ hm E U x ht' hU z' q J hQ
    let c:= T z'; let f t:= c • O' t
    have hC: c≠0:= (bristle _ _ hp' _).ne'
    have hx : Brush i (g (y,z') *V₁) 1 (f-O) x:= he.smaller hi
    have hf : ContDiffAt ℝ i O' x:= by
      apply ((hx.smooth.add ht).const_smul c⁻¹).congr_of_eventuallyEq; exact Eventually.of_forall (fun i=> by change O' i=c⁻¹ • (f i-O i+O i); rw [sub_add_cancel]; exact (inv_smul_smul₀ hC _).symm)
    have hp := (Brush.offer.1 hx).2 i le_rfl; unfold normJ at hp; rw [iteratedFDeriv_sub_apply (show ContDiffAt ℝ i f x from hf.const_smul _) ht, show f=c • O' from rfl,iteratedFDeriv_const_smul_apply hf] at hp
    rw [mul_comm V₁]; exact hp
  rw [integral_const_mul]; refine (mul_le_mul_of_nonneg_left hp₁ hvQ).trans_eq ?_; unfold V₁; ring
end YM.PhysicalNext.Repeat.Alabaster
