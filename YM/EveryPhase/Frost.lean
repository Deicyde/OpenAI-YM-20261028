import YM.EveryPhase.Through

/-! # Affine time weights and Schwinger continuation in partial pairings -/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase.Stress
open Function Set Filter MeasureTheory Metric Boundary Next.BOUNDARY Mink Complex Probe Table
open Next.BOUNDARY.Descent
open scoped Topology BigOperators
variable {G : Gauge} {L : Register G} {S U : Table L} {W : Surface S}
  {D : ∀ n, Blanket n} {Z : W.Aurora D} {P : DiffPlan S} {F : Waves S} {n : ℕ}

def cloth (M : Joint n) (j : Fin (n+1)) (g : Test4) := along (chairs j).symm (Probe.combine M g)
lemma clothes (M : Joint n) (j : Fin (n+1)) (g : Test4) (x : Points n) (y : E4) :
    cloth M j g (seat j x y)=M x*g y := by
  change along _ _ (chairs j (x,y))=_
  simp

def pincushion (c : Probe Space3) (f : Probe ℝ) := along divide (Probe.combine c f)
lemma pincushion_at (c : Probe Space3) (f : Probe ℝ) (x : E4) : pincushion c f x=c (spatial x)*f (YM.time x) := by
  simp [pincushion]

def effect {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Killing) (b : Axis) (i : E→L[ℝ] E4) :=
    (SchwartzMap.smulLeftCLM ℂ (fun x : E => ((K.realV (i x) b:ℝ):ℂ)) : Probe E →L[ℂ] Probe E)
lemma effect_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Killing) (b : Axis) (i : E→L[ℝ] E4) (g : Probe E) (x) : effect K b i g x=(K.realV (i x) b:ℂ)*g x := by
  unfold effect
  have hp : HasTemperateGrowth (fun x : E => ((K.realV (i x) b:ℝ):ℂ)) := by
    let A := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin K.V)
    change HasTemperateGrowth (fun x : E => Complex.ofRealCLM ((PiLp.proj 2 (𝕜:=ℝ) _ b) (K.translation+A (i x))))
    fun_prop
  rw [SchwartzMap.smulLeftCLM_apply_apply hp]; rfl

def touch (K : Killing) (b : Axis) := effect K b (ContinuousLinearMap.id ℝ E4)
lemma touch_at (K : Killing) (b : Axis) (f : Test4) (x) : touch K b f x=(K.realV x b:ℂ)*f x := effect_at ..

def arch (t s : ℝ) : ℂ := (t:ℂ)+(s:ℂ)*I

def affect (K : Killing) (b : Axis) (s : ℝ) := zeta b*((K.V b timeAxis:ℂ)*(s:ℂ)*I)
lemma affect_cont (K : Killing) (b) : Continuous (affect K b) := by unfold affect; fun_prop

lemma uplifting (K : Killing) (b : Axis) (x : Space3) (t s : ℝ) : K.w b (lay x (arch t s))=
    zeta b*(K.realV (position x t) b:ℂ)+affect K b s := by
  rw [← K.w_real]; unfold Killing.w affect; rw [arch]
  simp_rw [lay_time,mul_add, Finset.sum_add_distrib]
  simp [mul_ite, mul_add]; ring

def stack (K : Killing) (b : Axis) (s : ℝ) (f : Test4) := zeta b • touch K b f+affect K b s • f
lemma stack_at (K : Killing) (b : Axis) (s : ℝ) (f : Test4) (x : Space3) (t : ℝ) :
    stack K b s f (position x t)=K.w b (lay x (arch t s))*f (position x t) := by
  simp only [stack,_root_.smul_apply,_root_.add_apply,touch_at,uplifting,smul_eq_mul]; ring
lemma stack_zero (K : Killing) (b : Axis) (f) : stack K b 0 f=zeta b • touch K b f := by simp [stack,affect]

def loads (K : Killing) (b : Axis) (s : ℝ) (k : Fin n) (g : Joint n) := zeta b • effect K b (PiLp.proj 2 _ k) g +
    affect K b s • g
lemma loads_at (K : Killing) (b : Axis) (s : Heights n) (k : Fin n) (g : Joint n) (x : Points n) :
    loads K b (s k) k g x=K.w b (fun a => glow x (dawn s) (k,a))*g x := by
  rw [← laid_place]; simp_rw [laid_at]
  simp only [loads,_root_.add_apply,_root_.smul_apply, effect_at, smul_eq_mul]
  rw [show shift x s k=arch (YM.time (x k)) (s k) from rfl, Boundary.trace, uplifting]; rw [position_eta]; simp; ring

def survey (y : Heights n) (x : Points n) (k : Fin n) (s : ℝ) : Dock n := ((Boundary.trace x,shift x y),s-YM.time (x k))
lemma survey_walk (y : Heights n) (k : Fin n) : Continuous (fun p : Points n × ℝ => survey y p.1 k p.2) := by
  unfold survey Boundary.trace shift; fun_prop
lemma dial (y : Heights n) (k : Fin n) (x : Points n) (s) :
    sundial (survey y x k s) k=hole k.succ y (y k) := by
  unfold sundial survey; simp [shift]
lemma town_survey (y : Heights n) (k : Fin n) (x : Points n) (s) : town (survey y x k s) k=arch s (y k) := by
  simp [town,survey,arch,shift]; ring
lemma morn_survey (y : Heights n) (k : Fin n) (x : Points n) (s w : ℝ) :
    morn (survey y x k s) k w= arch s (y k+w) := by rw [morn,town_survey]; unfold arch; push_cast; ring
lemma eve_survey (y : Heights n) (k : Fin n) (x : Points n) (s w : ℝ) :
    eve (survey y x k s) k w= arch s (y k-w) := by rw [eve,town_survey]; unfold arch; push_cast; ring
lemma shift_scene (x : Points n) (y : Heights n) (j : Fin (n+1)) (s w : ℝ) (r : Space3) :
    shift (seat j x (position r s)) (hole j y w)=hole j (shift x y) (arch s w) := by
  funext i; refine Fin.succAboveCases j ?_ ?_ i <;> simp [shift,arch]
lemma shift_strict {y : Heights n} (hy : y∈east n) (x : Points n) : shift x y∈strict n := by
  intro i j hj; simp [shift]; exact hy hj
lemma strict_height (j : Fin (n+1)) {y : Heights n} (s) {t : ℝ} (h : hole j y t∈east (n+1)) (x : Points n) :
    hole j (shift x y) (arch s t) ∈ strict (n+1) := by
  rw [← shift_scene x y j s t 0]; exact shift_strict h _
lemma judge (j : Fin (n+1)) (r : Space3) (u s : ℝ) (x : Points n) (y : Heights n) :
    glow (seat j x (position r u)) (dawn (hole j y s))=
      lodge j (Boundary.trace x) (shift x y) r (arch u s) := by
  rw [← laid_place,shift_scene,lodge]
  congr 1; funext i; refine Fin.succAboveCases j ?_ ?_ i <;> simp [Boundary.trace]

-- RHS response in terms of partialC on external coordinates (no stress).
def mandate (W : Surface S) (D : ∀ n, Blanket n) (K : Killing) (R : S.Rotation) (P : DiffPlan S)
    (v : Fin n → S.Tag) (k : Fin (n+1)) (t : S.Tag) (M : Joint (n+1)) (y : Heights (n+1)) :=
    let ψ := fun (a : S.Tag) => (D (n+1)).partialD (W.W (n+1) (Bid.ink (hole k v a))) (dawn y)
    ψ ⟨t.1,rankAction R t.1 K.V t.2⟩ M+∑ b : Axis,
      ψ ⟨t.1+1,P.deriv t.1 b t.2⟩ (loads K b (y k) k M)

-- stress integrand in terms of partial test
def gavel (W : Surface S) (D : ∀ n, Blanket n) (K : Killing) (T : S.Stress) (v : Fin n → S.Union)
    (j : Fin (n+1)) (M : Joint n) (g : Probe Space3) (f : Probe ℝ) (y : Heights n) (s : ℝ) :=
    ∑ b : Axis, (D (n+1)).partialD (W.W (n+1) (hole j v (S.pin 4 (T timeAxis b)))) (dawn (hole j y s))
      (cloth M j (stack K b s (pincushion g f)))

lemma mandate_int (hZ : Z.FullBody F) (K : Killing) (R : S.Rotation) (P : DiffPlan S)
    (v : Fin n → S.Tag) (k : Fin (n+1)) (t : S.Tag) (M : Joint (n+1)) (y : Heights (n+1)) (hy : y∈east (n+1)) :
    Integrable (fun x => taskC Z K R P v k t (Boundary.trace x,shift x y)*M x) ∧
      mandate W D K R P v k t M y=∫ x, taskC Z K R P v k t (Boundary.trace x,shift x y)*M x := by
  let f := fun a : S.Tag => fun (M : Joint (n+1)) (x : Points (n+1)) => Z.emit (Bid.ink (hole k v a)) (glow x (dawn y))*M x
  let A : S.Tag := ⟨t.1,rankAction R t.1 K.V t.2⟩
  let B (b : Axis) : S.Tag := ⟨t.1+1,P.deriv t.1 b t.2⟩
  have ht x : taskC Z K R P v k t (Boundary.trace x,shift x y)*M x=f A M x+∑ b : Axis, f (B b) (loads K b (y k) k M) x := by
    simp_rw [taskC,laid_place]; simp only [f,A,B,loads_at,add_mul,Finset.sum_mul,mul_assoc]
    congr 1; exact Finset.sum_congr rfl fun i _ => mul_left_comm ..
  have he a M : Integrable (f a M) := hZ.leaned _ _ _ (etched hy) _
  have hh : Integrable (fun x => ∑ b : Axis,f (B b) (loads K b (y k) k M) x) := integrable_finsetSum _ fun i _ => he _ _
  simp_rw [ht]; refine ⟨(he A M).add hh,?_⟩
  rw [integral_add (he A M) hh,integral_finsetSum _ (fun i _ => he _ _)]
  unfold mandate; simp only; simp_rw [hZ.builds _ _ _ (etched hy)]; rfl

lemma harvest (hZ : Z.FullBody F) (K : Killing) (T : S.Stress) (v : Fin n → S.Union) (j : Fin (n+1))
    (y : Heights n) (M : Joint n) (s : ℝ) (h : hole j y s∈east (n+1))
    (g : Probe Space3) (hg : HasCompactSupport ⇑g) (f : Probe ℝ) (hf : HasCompactSupport ⇑f) (hM : HasCompactSupport ⇑M) :
    let q := fun p : Points n × ℝ => M p.1*f p.2*harbors Z K v T g j (Boundary.trace p.1) (shift p.1 y) (arch p.2 s)
    Integrable q ∧ gavel W D K T v j M g f y s=∫ p, q p := by
  intro q
  let B (a : Axis) (x : Points (n+1)) := Z.emit (hole j v (S.pin 4 (T timeAxis a))) (glow x (dawn (hole j y s)))*
    cloth M j (stack K a s (pincushion g f)) x
  have hm a : Integrable (B a) := hZ.leaned _ _ _ (etched h) _
  let b := fun p : Points (n+1) => ∑ a,B a p
  have hb : Integrable b := integrable_finsetSum _ fun i _ => hm i
  have ht (x : Points n) (z : ℝ) : (∫ r : Space3, b (seat j x (position r z)))=q (x,z) := by
    let w := arch z s
    let l (r : Space3) := lodge j (Boundary.trace x) (shift x y) r w
    have he (r) : b (seat j x (position r z))=(M x*f z)*(g r * waveT Z K v T j timeAxis (Boundary.trace x) (shift x y) (arch z s) r) := by
      unfold waveT tide b B
      simp_rw [judge,lodge,laid_at,hole_self,clothes,stack_at,pincushion_at,spatial_position,time_position]
      simp_rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    simp_rw [he,integral_const_mul]; rfl
  have hc : Continuous q := by
    let r := fun p : Points n × ℝ => harbors Z K v T g j (Boundary.trace p.1) (shift p.1 y) (arch p.2 s)
    refine ((M.continuous.comp continuous_fst).mul (f.continuous.comp continuous_snd)).mul (show Continuous r from ?_)
    refine continuousOn_univ.mp (harbors_cont j (x:=fun p : Points n × ℝ => Boundary.trace p.1)
      (u:=fun p : Points n × ℝ => shift p.1 y) (z:=fun p => arch p.2 s) ?_ ?_ ?_ (fun p _ => strict_height j _ h _) K v T g hg hZ)
    all_goals first | (unfold Boundary.trace; fun_prop) | (unfold shift; fun_prop) | (unfold arch; fun_prop)
  have hi : Integrable q := hc.integrable_of_hasCompactSupport (HasCompactSupport.intro (hM.prod hf) fun p hp => by
    by_cases hx : p.1∈tsupport M
    · simp [q,image_eq_zero_of_notMem_tsupport (show p.2∉tsupport f from fun h => hp ⟨hx,h⟩)]
    simp [q,image_eq_zero_of_notMem_tsupport hx])
  refine ⟨hi,?_⟩
  let e := chairs j
  have hj : MeasurePreserving e (volume.prod volume) volume := chairMeasure j
  have hz : Integrable (b ∘ e) (volume.prod volume) := (hj.integrable_comp_emb e.toHomeomorph.measurableEmbedding).mpr hb
  let t (x : Points n) (z : E4) := b (seat j x z)
  unfold gavel; simp_rw [hZ.builds _ _ _ (etched h)]
  change (∑ a,∫ x, B a x)=_
  rw [← integral_finsetSum _ (fun a _ => hm a), ← hj.integral_comp e.toHomeomorph.measurableEmbedding b] -- may b needs change
  change (∫ p, (b ∘ e) p ∂(volume.prod volume))=∫ p, q p ∂(volume.prod volume)
  rw [integral_prod _ hz,integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [hz.prod_right_ae] with x hx
  change (∫ z, t x z)=∫ z, q (x,z)
  change Integrable (t x) at hx
  have hw := (split_space 0 hx).2
  simpa [ht,t] using hw
end YM.EveryPhase.Stress
