import YM.MultipleContact.Taylor
/-! Direct (total-collapse) estimate for a single kernel after field subtraction, any finite-dimensional Jacobi normal variable.
Proof uses Taylor with common cutoff and radial integrability. -/
set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact.Direct
open Filter MeasureTheory Set TopologicalSpace Metric
open scoped Topology ContDiff MeasureTheory ContDiff BigOperators Classical
variable {E F : Type*}
 [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [(volume : Measure E).IsAddHaarMeasure]
 [BorelSpace E] [NormedAddCommGroup F][NormedSpace ℂ F][NormedSpace ℝ F][IsScalarTower ℝ ℂ F][CompleteSpace F]
local notation "df" => Module.finrank ℝ

def price : Option ℕ→ ℕ
 | none=>0
 | some m=> m+1

def J (p R:ℝ):ℝ:=∫x:E in Metric.ball 0 R, ‖x‖^p

structure Kas (R p A:ℝ)(K:E→F) : Prop where
  pos:0<A
  measurable : AEStronglyMeasurable K (volume.restrict (ball 0 R))
  grow x : x∈ball 0 R→x≠0→ ‖K x‖≤ A*‖x‖^p

variable {R p c:ℝ} {K : E→F} {m:Option ℕ} (hd:1≤df E) (hk:Kas R p c K)
local notation "ρ" => volume.restrict (ball 0 R)
include hd hk
omit hk [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F] in
lemma ae_off:∀ᵐ x∂(ρ:Measure E),x≠0:=by
    letI : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < df E)
    refine Filter.Eventually.filter_mono MeasureTheory.ae_restrict_le (?_)
    rw [Filter.Eventually, mem_ae_iff]; simpa only [Set.compl_def, Set.mem_setOf, not_not, Set.setOf_eq_eq_singleton] using measure_singleton (μ:=volume) (0:E)
omit hk in
lemma integrates_pow {p:ℝ}(hp:p>-(df E:ℝ)) (c:ℝ): IntegrableOn (fun x:E=>c * ‖x‖^p) (ball 0 R):=by
   have he:AEStronglyMeasurable (fun x:E=> ‖x‖^p) volume:=((measurable_norm.pow_const p).aestronglyMeasurable)
   refine Integrable.const_mul (μ:=volume.restrict (ball 0 R)) (integrableOn_ball_of_norm_le_rpow hd (C:=(1:ℝ)) (α:=-p) (by linarith) (ae_restrict_of_ae (Eventually.of_forall fun x=>by rw [neg_neg,one_mul]; exact (Real.norm_of_nonneg (by positivity)).le)) he) c

omit hk [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F] in
lemma dominated (g : E→F) {p':ℝ} (hp:p'>-(df E:ℝ)) (c':ℝ) (hm:AEStronglyMeasurable g ρ) (hb:∀ x∈ball 0 R,x≠0→‖g x‖≤c'*‖x‖^p') :
  IntegrableOn g (ball 0 R) ∧ ‖∫x:E in ball 0 R,g x‖≤ c'*J (E:=E) p' R:=by
   have he:∀ᵐ x∂ρ, ‖g x‖≤ c'*‖x‖^p' :=by
     filter_upwards [ae_off (R:=R) hd,ae_restrict_mem (μ:=volume) isOpen_ball.measurableSet] with x hx he
     exact hb x he hx
   exact ⟨(integrates_pow (R:=R) hd hp c').mono' hm he, (norm_integral_le_of_norm_le (integrates_pow (R:=R) hd hp c') he).trans (integral_const_mul ..).le⟩

-- Explicit bound on unscaled test.
def polyCost (m:Option ℕ)(s:ℝ):ℝ:=(m.map fun i:ℕ=>(i+2:ℝ)*(1+s⁻¹)^(i+1)).getD 1
omit hd [(volume : Measure E).IsAddHaarMeasure] [BorelSpace E] [FiniteDimensional ℝ E] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F] in
lemma atCost {f:E→ℂ}(hf:ContDiff ℝ ∞ f){A:ℝ}(ha:JetBounds (price m) f A){s:ℝ}(hs:0<s){x:E}(hx:x∈ball 0 R)(hw:x≠0):
  ‖diff s m f x • K x‖ ≤ c * (polyCost m s*A) * ‖x‖^(p+(price m:ℝ)):=by
  have hy:‖diff s m f x‖ ≤ (polyCost m s*A)*‖x‖^(price m):=by
    rcases m with _|m
    · exact (ha.value x).trans_eq (by simp [polyCost,price])
    exact (diff_bound hs hf m ha x)
  rw [norm_smul,Real.rpow_add (norm_pos_iff.mpr hw),Real.rpow_natCast]
  refine (mul_le_mul hy (hk.grow x hx hw) (norm_nonneg _) ((norm_nonneg _).trans hy)).trans_eq (?_); ring

def term (R s:ℝ)(m:Option ℕ)(K:E→F)(f:E→ℂ):F:=∫x:E in ball 0 R, diff s m f x • K x

omit [IsScalarTower ℝ ℂ F] [CompleteSpace F] in
lemma localPair {f:E→ℂ}{s A:ℝ} (hf:ContDiff ℝ ∞ f) (ha : JetBounds (price m) f A) (hs:0<s) (hp:p+price m> -(df E:ℝ)):
    IntegrableOn (fun x=>diff s m f x • K x) (ball 0 R) ∧
    ‖term R s m K f‖ ≤ (c * polyCost m s * J (E:=E) (p+(price m:ℝ)) R) * A :=by
    have hx:= dominated hd (fun x:E=>diff s m f x • K x) hp (c * (polyCost m s*A)) ((diff_contDiff hf s m).continuous.aestronglyMeasurable.smul (hk.measurable)) (fun x=>atCost hk hf ha hs)
    exact ⟨hx.1,hx.2.trans_eq (by ring)⟩

-- Scaled estimates. γ is a strictly positive loss in the radial integration.
def admissible (m:Option ℕ)(p γ B:ℝ): Prop:= match m with
 | none=>γ≤p+B
 | some m=> (m:ℝ)+p+B ≤ γ ∧ γ≤m+1+p+B
def scaledCost (m:Option ℕ)(M p γ B:ℝ):ℝ:= match m with
 | none=> M^(p+B-γ)
 | some m=>(m+4:ℝ)
omit hd hk in
lemma scalar_scale {r x:ℝ}(hr:0<r) (hx:0<x) (p γ B:ℝ):
  r^(-B)*(x/r)^(-B+γ-p)* x^p=r^(p-γ)*x^(-B+γ):=by
  rw [Real.div_rpow hx.le hr.le,Real.rpow_sub hx,Real.rpow_sub hr,Real.rpow_add hr,Real.rpow_sub hr]
  field_simp

omit hd in
lemma pointScaled {f:E→ℂ}(hf:ContDiff ℝ ∞ f) {M A:ℝ}(hM:0<M)(hx:∀y:E, f y ≠ 0→‖y‖≤M) (ha:JetBounds (price m) f A) {r s γ:ℝ}(hr:0<r)(hrs:r≤s) (he:admissible m p γ (df E)) {y:E}(hR:y∈ball 0 R)(hy:y≠0):
   ‖diff s m (scaled r f) y • K y‖ ≤ (c * (scaledCost m M p γ (df E)*A) * r^(p-γ)) * ‖y‖^(-(df E:ℝ)+γ):=by
  let B:ℝ:=df E; let W:= -B+γ-p;let t:= ‖y‖/r
  have ht:0<t:=div_pos (norm_pos_iff.mpr hy) hr; let d := (r^(df E))⁻¹
  have hd':r^(-B)=d:=by rw [Real.rpow_neg hr.le,Real.rpow_natCast]
  have hb:=ha.1; have hkpos :=hk.pos; let D:=scaledCost m M p γ (df E)
  suffices hh: ‖diff s m (scaled r f) y‖≤ D*A*r^(-B)*t^W by
      rw [norm_smul]; apply (mul_le_mul hh (hk.grow y hR hy) (norm_nonneg _) ((norm_nonneg _).trans hh)).trans_eq
      calc D*A*r^(-B)*t^W*(c*‖y‖^p)=(c*(D*A))*(r^(-B)*t^W*‖y‖^p):=by ring
           _ = _ := by rw [@scalar_scale r _ hr (norm_pos_iff.mpr hy) p γ B]; unfold D B; ring
  rcases m with _|m
  · have hW:W≤0:=by dsimp [W,B]; linarith only [show γ≤p+df E from he]
    by_cases h:f (r⁻¹ • y)=0
    · dsimp only [diff,scaled]; rw [h,smul_zero,norm_zero]; dsimp [D,scaledCost]; positivity
    rw [hd']; have ht':t≤M:=by convert hx _ h using 1; dsimp [t]; simp [norm_smul,Real.norm_of_nonneg hr.le,div_eq_inv_mul]
    have hS: M^W ≤ t^W:= Real.rpow_le_rpow_of_nonpos ht ht' hW
    have hq : 1≤M^(-W)*t^W:=by
       refine (le_of_eq (show 1=M^(-W)*M^W from ?_)).trans (mul_le_mul_of_nonneg_left hS (Real.rpow_nonneg hM.le _))
       rw [← Real.rpow_add hM,neg_add_cancel,Real.rpow_zero]
    have hv:= mul_le_mul_of_nonneg_left hq (show 0≤A*d by dsimp [d]; positivity)
    refine (show ‖diff s none (scaled r f) y‖≤d*A from ?_).trans ?_
    · simpa only [diff,scaled,norm_smul,Real.norm_of_nonneg (show 0≤(r^(df E))⁻¹ by positivity)] using (mul_le_mul_of_nonneg_left (ha.value (r⁻¹•y)) (show 0≤d by dsimp [d]; positivity))
    dsimp only [D,scaledCost]; rw [show p+(df E:ℝ)-γ= -W by dsimp only [W,B]; ring]; linarith only [hv]
  apply (diff_scaled hf r s hr hrs ha y).trans
  have hm:(m:ℝ)≤ W ∧ W≤ m+1:= by
      change m+p+_≤_ ∧ γ≤_ at he
      dsimp [W,B]; constructor <;> linarith only [he.1,he.2]
  rw [hd']; have hT: min ((‖y‖ / r) ^ (m + 1)) ((‖y‖ / r) ^ m) ≤ t^W := min_le_iff.mpr (by
      dsimp [t] at *
      by_cases ht' : ‖y‖/r ≤ 1
      · left; rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_ge ht ht' (by simpa only [Nat.cast_add,Nat.cast_one] using hm.2)
      right; rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (le_of_not_ge ht') hm.1)
  exact mul_le_mul_of_nonneg_left hT (show 0≤((m:ℝ)+4)*A*(r^df E)⁻¹ by positivity)

lemma scaledTerm {f:E→ℂ}(hf:ContDiff ℝ ∞ f) {M A:ℝ}(hM:0<M)(hx:∀y:E, f y ≠ 0→‖y‖≤M) (ha:JetBounds (price m) f A) {r s γ:ℝ}(hγ:0<γ)(hr:0<r)(hrs:r≤s) (he:admissible m p γ (df E)):
   ‖term R s m K (scaled r f)‖ ≤ (c*(scaledCost m M p γ (df E)*A)*J (E:=E) (-(df E:ℝ)+γ) R) * r^(p-γ) :=by
    have h':ContDiff ℝ ∞ (scaled r f) := (hf.comp (contDiff_const.smul contDiff_id)).const_smul _
    exact ((dominated hd _ (by linarith : (-(df E:ℝ)+γ)> -(df E:ℝ)) (c * (scaledCost m M p γ (df E)*A) * r^(p-γ)) ((diff_contDiff h' s m).continuous.aestronglyMeasurable.smul hk.measurable) (fun y hy hw=>pointScaled hk hf hM hx ha hr hrs he hy hw)).2).trans_eq (by ring)

end YM.MultipleContact.Direct
#print axioms YM.MultipleContact.Direct.scaledTerm
