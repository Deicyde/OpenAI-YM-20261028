import YM.WilsonBulk.Build.Gallery
import YM.Branch.Covariant

/-!
# Orbit movements for Whitney charts

Rooted ordinary real configurations, joint nuisance tape *later*.
Use probability-Haar in chart overlap lemma. Captures any tree choices on
this finite period; theta/smearing not averaged. Retains normalized accounting.
This is not a change-of-measure bound for denominator costs in actual units.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Atelier
open scoped Topology Classical ENNReal BigOperators
open Lattice RG Function Filter Tree Wilson Precision MeasureTheory Set
variable {G : Gauge} {c f n : Side} {S : StepData c f} -- implicit add
-- Root relatives

def Kindred (S : StepData c f) (U V : Config G f) := ∃ k : Site f → G.El, (∀ i,k (S.ratio.embed i)=1) ∧ U=Lattice.gauge k V

lemma followGauge (U : Config G n) (k p : Site n→G.El) : Lattice.gauge k (Lattice.gauge p U) = Lattice.gauge (k*p) U := by
  ext1 i; simp only [Lattice.gauge,Pi.mul_apply]; group
lemma turn_person (u : Config G n) : Lattice.gauge 1 u=u := by ext1 i; simp [Lattice.gauge]
lemma Kindred.trans {U V W : Config G f} (h : Kindred S U V) (he : Kindred S V W) : Kindred S U W := by
  obtain ⟨k,h,rfl⟩:=h; obtain ⟨p,g,rfl⟩:=he; exact ⟨k*p,fun i=>by rw [Pi.mul_apply,h i,g i,mul_one],followGauge ..⟩
lemma Kindred.symm {U V : Config G f} (h : Kindred S U V) : Kindred S V U := by
  obtain ⟨k,h,rfl⟩:=h; exact ⟨k⁻¹,fun i=>by simp [h i],by rw [followGauge,inv_mul_cancel,turn_person]⟩
lemma Kindred.wiped (S : StepData c f) (F : Forest S.ratio) (U : Config G f) : Kindred S (Profiles.wiped F U) U := ⟨F.foldAt U,F.fold_root U,rfl⟩
lemma Kindred.same {U V : Config G f} (h : Kindred S U V) (T : Forest S.ratio) : Profiles.wick T U=Profiles.wick T V := by
  obtain ⟨k,h,h'⟩:=h; rw [h']; exact Profiles.wick_gauge T V k h
lemma Kindred.gauge (U V : Config G f) (h : Kindred S U V) (p : Site f→ G.El) : Kindred S (Lattice.gauge p U) (Lattice.gauge p V) := by
  obtain ⟨k,h,rfl⟩:=h; exact ⟨p*k*p⁻¹,fun i=>by simp [h i],by rw [followGauge,followGauge,inv_mul_cancel_right]⟩
lemma Kindred.pull (U V : Config G f) (s : Signed) (b : Site c) (h : Kindred S U V) : Kindred S (Lattice.pull s (S.ratio.embed b) U) (Lattice.pull s (S.ratio.embed b) V) := by
  obtain ⟨k,h,rfl⟩:= h; let x:= S.ratio.embed b; let g : Site f→G.El:= k ∘ affine s x
  refine ⟨g,fun i=>?_,?_⟩
  · rw [show g (S.ratio.embed i)=_ from congr_arg k (S.port s b i)]; exact h _
  funext ⟨y,i⟩; change Step.read _ (Lattice.gauge k V) _= _
  rw [Step.gauge_read]
  simp only [Lattice.pull,Lattice.gauge,g,Function.comp_apply,affine, Signed.act_add, Step.vec_rotate,Step.vec_pos]; unfold x; rw [add_right_comm]

def rotating (s : Signed) (b : Site c) (S : StepData c f) : Config G f≃ₜ Config G f where
  toFun := pull s (S.ratio.embed b)
  invFun := pull s⁻¹ (S.ratio.embed ((s⁻¹).act (-b))) -- syntax
  left_inv U := by
    rw [pull_pull]; simp only [mul_inv_cancel]; convert! pull_id U; rw [Ratio.signed,affine, Signed.act_inv]; change S.ratio.root (-b)+S.ratio.root b=_; rw [map_neg,neg_add_cancel]
  right_inv U:= by rw [pull_pull]; simp only [inv_mul_cancel]; convert! pull_id U; rw [Ratio.signed,affine, show S.ratio.embed (-b)= -S.ratio.embed b from map_neg S.ratio.root b,Signed.act_neg]; abel
  continuous_toFun:= continuous_pull ..
  continuous_invFun:= continuous_pull ..

def leadingBy (t : Site f → G.El) : Config G f≃ₜ Config G f where
  toFun:=Lattice.gauge t
  invFun:=Lattice.gauge t⁻¹
  left_inv U:= by rw [followGauge,inv_mul_cancel,turn_person]
  right_inv U:= by rw [followGauge,mul_inv_cancel,turn_person]
  continuous_toFun:= by apply continuous_pi; intro i; exact (continuous_const.mul (continuous_apply i)).mul continuous_const
  continuous_invFun:= by apply continuous_pi; intro i; exact (continuous_const.mul (continuous_apply i)).mul continuous_const

/-- Send orbit spaces. Including any two trees, not requiring a turned
fixed prescription. statement strong enough for Ward transfer of arbitrary signed & gauge families.
-/
structure Carries (G : Gauge) (S : StepData c f) where
  routeG : Config G f≃ₜ Config G f
  respects : ∀ U V, Kindred S U V → Kindred S (routeG U) (routeG V)
  reversed : ∀ U V, Kindred S U V → Kindred S (routeG.symm U) (routeG.symm V)
  toll : MeasurePreserving routeG (prior G f) (prior G f)
namespace Carries
variable (S)
def send (s : Signed) (b : Site c) (t : Site f→ G.El) : Carries G S where
  routeG := (rotating s b S).trans (leadingBy t)
  respects _ _ h:= ((h.pull _ _ _ _).gauge _ _ t)
  reversed U V h:= (h.gauge U V t⁻¹).pull _ _ _ _
  toll:= (prior_gauge t).comp (prior_pull s (S.ratio.embed b))
variable {S}
lemma sliceMass (F : Forest S.ratio) : MeasurePreserving (Profiles.wick (G:=G) F) (prior G f) (F.order G) := by
  let f' : Config G f → F.Slice G := Profiles.wick F
  have hh : Measurable f' := (Profiles.continuous_wick F).measurable
  refine ⟨hh, Measure.ext fun s hs=> ?_⟩; rw [Measure.map_apply hh hs]
  let m := (f' ⁻¹' s).indicator (fun _=> (1:ℝ))
  have hu t (ht : ∀ x,t (S.ratio.embed x)=1) u : m (Lattice.gauge t u)=m u := by unfold m; by_cases h : Profiles.wick F u∈s <;> simp [Set.indicator,f',h,Profiles.wick_gauge F u t ht] -- inspect
  have he := F.pack m ((integrable_const _).indicator (hh hs)) hu
  rw [show (fun x : F.Slice G=>m (F.drape x))=s.indicator fun _=>(1:ℝ) from by ext1 x; simp [m,f',indicator,Profiles.wick_root], integral_indicator hs,setIntegral_const] at he
  unfold m at he; rw [integral_indicator (hh hs), setIntegral_const] at he
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  simpa only [smul_eq_mul,mul_one,measureReal_def] using he

variable (Q : Carries G S) (F L : Forest S.ratio)
def slit : F.Slice G ≃ₜ L.Slice G where
  toFun U:= Profiles.wick L (Q.routeG (F.drape U))
  invFun U:= Profiles.wick F (Q.routeG.symm (L.drape U))
  left_inv U:= by dsimp only; rw [Profiles.wears, (Kindred.same (U:= Q.routeG.symm (Profiles.wiped L _)) (Q.reversed _ _ (Kindred.wiped S L (Q.routeG (F.drape U))))), Homeomorph.symm_apply_apply,Profiles.wick_root]
  right_inv U:= by dsimp only; rw [Profiles.wears, (Kindred.same (U:= Q.routeG (Profiles.wiped F _)) (Q.respects _ _ (Kindred.wiped S F (Q.routeG.symm (L.drape U))))), Homeomorph.apply_symm_apply,Profiles.wick_root]
  continuous_toFun:= by fun_prop
  continuous_invFun:= by fun_prop
lemma passing (U) : slit Q F L (Profiles.wick F U)=Profiles.wick L (Q.routeG U) := by change Profiles.wick _ _=_; rw [Profiles.wears]; exact (Q.respects _ _ (Kindred.wiped S F _)).same L
lemma pass_paid : MeasurePreserving (slit Q F L) (F.order G) (L.order G) := by
  have hv:= (sliceMass L).comp Q.toll
  refine ⟨(slit Q F L).continuous.measurable,?_⟩
  rw [← (sliceMass F).map_eq,Measure.map_map (slit Q F L).continuous.measurable (sliceMass F).measurable]; rw [show slit Q F L ∘ Profiles.wick F=Profiles.wick L ∘ Q.routeG from funext (passing Q F L)]; exact hv.map_eq
end Carries
end YM.WilsonBulk.Atelier
