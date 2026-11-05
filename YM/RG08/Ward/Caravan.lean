import YM.RG08.Arc.Ball
/-!
# Haar walkers. Tree dropoffs do not bias even arbitrarily small open
windows; symmetry contingent on gauge consent, supplied later on collars.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Reflect
open Filter MeasureTheory Set
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent
open PertExtension.Series.Tested Profiles
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f m : Side} (G : Gauge) {g : Ratio c f} (T : Forest g)
local notation "C" => Config G f
local notation "P" => T.Slice G
local notation "μΦ" => prior G f
local notation "Λ" => T.order G
lemma illuminated : MeasurePreserving (Profiles.wick T) μΦ Λ := by
  have hc:=continuous_wick (G:=G) T
  refine ⟨hc.measurable,?_⟩; ext a ha
  let u := a.indicator (fun _=> (1:ℝ)) ∘ (Profiles.wick T (G:=G))
  have hm : MeasurableSet ((Profiles.wick T) ⁻¹' a) := hc.measurable ha
  have hS : Integrable u μΦ := by simpa only [u,indicator_comp_right] using! ((integrable_const (μ:=μΦ) (1:ℝ)).indicator hm)
  have hi:= T.pack u hS fun k ht x=> congr_arg (a.indicator _) (wick_gauge T x k ht)
  have hw (x:T.Slice G) : u (T.drape x)=a.indicator (fun _=>(1:ℝ)) x := by unfold u; simp only [Function.comp_apply,wick_root]
  simp_rw [hw,show u=(Profiles.wick T ⁻¹' a).indicator (fun _=>(1:ℝ)) from funext fun x=> by by_cases h : wick T x ∈ a <;> simp [h,u]] at hi
  rw [integral_indicator hm,integral_indicator ha, setIntegral_const,setIntegral_const] at hi
  rw [Measure.map_apply hc.measurable ha]; apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  simpa only [smul_eq_mul,mul_one] using! hi
-- parameter transport condition; works on all sets, not asserting arbitrary contour local under arbitrary gauge amplitude.
def Cart (e : C ≃ₜ C) := ∀ k: Site f→G.El,(∀ i: Site c,k (g.embed i)=1) → ∀ x, Profiles.wick T (e (Lattice.gauge k x))= Profiles.wick T (e x)
variable (e : Config G f ≃ₜ Config G f)


lemma cargo (h : Cart G T e) (x : C) : Profiles.wick T (e (T.drape (Profiles.wick T x)))= Profiles.wick T (e x) := by
  rw [wears]; exact h _ (fun i=> T.fold_root ..) _
def carriage (h : Cart G T e) (hp : Cart G T e.symm) : (P) ≃ₜ (P) where
  toFun u:= Profiles.wick T (e (T.drape u))
  invFun u:= Profiles.wick T (e.symm (T.drape u))
  left_inv u:= by dsimp only; rw [cargo G T _ hp, Homeomorph.symm_apply_apply, wick_root]
  right_inv u:= by dsimp only; rw [cargo G T _ h, Homeomorph.apply_symm_apply, wick_root]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop
lemma preserving (h : MeasurePreserving e μΦ μΦ) (hp : Cart G T e) (hh : Cart G T e.symm) : MeasurePreserving (carriage G T e hp hh) Λ Λ := by
  refine ⟨(carriage ..).continuous.measurable,?_⟩
  have he:= (illuminated G T).comp h; have hc:= he.map_eq
  let P': C→P := Profiles.wick T; let e':= carriage G T e hp hh
  rw [show (Profiles.wick T∘e)=(e'∘P') from funext fun u=>Eq.symm (cargo G T e hp u)] at hc; rw [← Measure.map_map e'.continuous.measurable (illuminated G T).measurable,show (μΦ).map P'=Λ from (illuminated G T).map_eq] at hc; exact hc
lemma drape_b : T.drape (1:P)=1 := by
  funext i; by_cases h:i∈T.trunks; · exact T.on_tree _ ⟨i,h⟩
  exact T.off_tree _ ⟨i,h⟩
lemma wick_b : Profiles.wick T (1:C)=1 := by rw [← drape_b G T]; exact wick_root ..

-- two relevant forms of transport, uniform across ALL pulse paths (provided map at unit stays flat)
def gaugeWalk (k : Site f→G.El) : C ≃ₜ C where
  toFun := Lattice.gauge k
  invFun := Lattice.gauge k⁻¹
  left_inv x:= by funext i; simp [Lattice.gauge]; group
  right_inv x:= by funext i; simp [Lattice.gauge]; group
  continuous_toFun := by apply continuous_pi; intro i; exact (continuous_const.mul (continuous_apply i)).mul continuous_const
  continuous_invFun := by apply continuous_pi; intro i; exact (continuous_const.mul (continuous_apply i)).mul continuous_const
lemma gauge_cart (k : Site f→ G.El) : Cart G T (gaugeWalk G k) := by
  intro h ht x
  have he (i : Site c) : (k*h*k⁻¹) (g.embed i)=1 := by simp [ht i]
  refine Eq.trans ?_ (wick_gauge T (gaugeWalk G k x) _ he)
  apply congr_arg (wick T); funext i; change Lattice.gauge k _ i=Lattice.gauge (k*h*k⁻¹) (Lattice.gauge k x) i
  simp only [Lattice.gauge,Pi.mul_apply, Pi.inv_apply]; group

def signedWalk (m : Side) (s : Signed) : Config G m ≃ₜ Config G m where
  toFun:= pull s 0
  invFun:= pull s⁻¹ 0
  left_inv x:= by simp [pull_pull,affine]
  right_inv x:= by simp [pull_pull,affine]
  continuous_toFun:= continuous_pull ..
  continuous_invFun:= continuous_pull ..
lemma signed_cart (s : Signed) : Cart G T (signedWalk G f s) := by
  intro k h x
  change Profiles.wick T (pull s 0 (Lattice.gauge k x))= Profiles.wick T (pull s 0 x)
  rw [Work.F05.pull_gauge_zero]; refine wick_gauge T _ _ fun i=>?_
  rw [affine,add_zero,← g.signed,h (s.act i)] -- rewrite h applied s.act
end YM.RG08.Reflect
