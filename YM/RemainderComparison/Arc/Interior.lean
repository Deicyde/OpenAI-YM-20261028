import YM.RemainderComparison.Auxiliary.Day
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Boulevard.Views

/-!
 # Window in AXIAL goods, extended to the flag boundary without differentiating hard mask.

 `sunny P` strict all-good. Call for a residual local label on AUX after
 synchronization. Applications supply its auxiliary torus equality with the
 `Aux.reserve_l`/`divideAux` data on sunny, with all transport and stem costs,
 and group smooth extension to the seam. Here pay the chart width vs normalized
 left derivative order/loss. Window W=S*A*fiery (cost `R` in coupling units)
 to include the root in the same halo even after re-patches. Takes real and
 vector marker values. No comparability with a foreign weather record needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Arc
open Function Filter Lattice RG Pressure Tree Wilson MeasureTheory ProbabilityTheory
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open YM.RemainderComparison.Aux
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c L : Side} {j : ℕ} {P:BudgetPoint} {A p R b x : ℝ}
variable {v : Positions (Uniform.Primary c G)}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Run auxiliary probes on actual scale. -/
def route (G:Gauge) {c:Side} (β:ℝ) (x: Positions (Uniform.Primary c G)) := actual (gStep β • x)
lemma stepper {X F: Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f:X→F} (x:X) (hb:0<b) (hp:Brush j A 1 (fun y=> f (b • y)) x) (hr:1 ≤ R) :
    Brush j (A*R^j) (b*R)⁻¹ f (b • x) := by
  let L := b⁻¹ • ContinuousLinearMap.id ℝ X; have hL: ‖L‖≤ b⁻¹:= by
    unfold L; rw [norm_smul,norm_inv,Real.norm_of_nonneg hb.le]; exact mul_le_of_le_one_right (by positivity) ContinuousLinearMap.norm_id_le
  have hh:L (b • x)=x:= by simp [L,hb.ne']
  have h': Brush j A b⁻¹ f (b • x) := by
    have ht := Brush.reading L (g:=fun y=>f (b • y)) ((hh.symm ▸ hp) : Brush j A 1 _ (L _)) hL
    rw [one_mul] at ht; refine ht.shimmy ?_; filter_upwards with i; simp [L,hb.ne']
  refine ⟨h'.smooth,by positivity,fun i hi=> (h'.order i hi).trans ?_⟩
  let d:=b*R; have he:0<d:=by unfold d; positivity
  have hR:0<R:= zero_lt_one.trans_le hr
  have H : b⁻¹=d⁻¹ * R:= by unfold d; field_simp
  nth_rw 1 [H]
  rw [mul_pow]; change _ ≤ _*d⁻¹^i; rw [mul_right_comm]
  rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr hi) (by positivity)) hp.nonneg

def budgetizer (j:ℕ) (p A:ℝ) := Boulevard.ticket j (A*p^j)
lemma fee_rate {f p : ℝ→ℝ} (he : Reserve G L p) (hp : Reserve G L f) : Reserve G L fun x=> budgetizer j (p x) (f x) :=
  Reserve.mul (Reserve.mul (Reserve.const _) (hp.mul (he.pow _))) (Reserve.const _)

-- properties in unscaled Lie X (direction extracted from ✓ representation)
structure Tracer (P:BudgetPoint) (G:Gauge) (β R : ℝ) : Prop where
  pay (c:Side) (V : Positions (Uniform.Primary c G)) : ‖V‖ ≤ R → ∀ (f:Config G c→ℝ) (q:ℝ),
    Brush P.order q 1 (f ∘ Arc.route G β) V → Push.Local.Chart P.order f (Arc.route G β V) ∧
      ∀ l: List (Directions G c), l.length ≤ P.order → (∀ i∈l, ‖i‖ ≤ P.threshold) →
        ‖leftDerivs f l (Arc.route G β V)‖ ≤ budgetizer P.order R q
  lean (c:Side) (V: Positions (Uniform.Primary c G)): ‖V‖ ≤ R → flags P.threshold (Arc.route G β V)=∅ →
    ∀ᶠ z:ℝ in 𝓝[<] 1, Arc.route G β (z • V)∈ Boulevard.sunny P

-- HA estimates extend within sunny to normal/equality seam IF projection smooth (not just indicator)
lemma Tracer.uses (ht : Tracer P G b R) (g : Config G c → E) (W : Positions (Uniform.Primary c G)) (he : ‖W‖ ≤ R)
    (hV : flags P.threshold (Arc.route G b W)=∅) (hp : ∀ v : Positions (Uniform.Primary c G), ‖v‖ ≤ R → flags P.threshold (Arc.route G b v)=∅→Push.Local.Chart P.order g (Arc.route G b v))
    (hf : ∀ v : Positions (Uniform.Primary c G), ‖v‖ ≤ R → Arc.route G b v∈Boulevard.sunny P → Brush P.order A 1 (g ∘ Arc.route G b) v) :
    ∀ l:List (Directions G c), l.length ≤ P.order → (∀ i∈l, ‖i‖≤P.threshold) → ‖leftDerivs g l (Arc.route G b W)‖ ≤ budgetizer P.order R A := by
  let V:=Arc.route G b W; intro l hl hC; let G' (x:ℝ):= leftDerivs g l (Arc.route G b (x • W))
  have hv : G' 1=leftDerivs g l V:=by unfold G' V; rw [one_smul]
  have hg : Push.Local.Chart 0 (leftDerivs g l) (Arc.route G b W) := Next.Foundations.leftDerivs_chart _ _ ((hp _ he hV).of_le (by simpa using! Nat.cast_le (α:=WithTop ℕ∞)|>.mpr hl))
  have hk : ContinuousAt G' 1:= by
    apply ContDiffAt.continuousAt (n:=0) (𝕜:=ℝ)
    refine Push.Local.chart_comp (W:=fun x=> Arc.route G b (x • W)) (k:=0) (x:=(1:ℝ)) (by rw [one_smul]; exact hg) ?_
    intro i; unfold Arc.route; simp_rw [smul_comm (gStep b)]
    exact Boulevard.radiator 1 (gStep b • W) i
  rw [← show G' 1=leftDerivs g l (Arc.route G b W) from hv]; apply le_of_tendsto (hk.norm.tendsto.mono_left (show (𝓝[<] (1:ℝ)) ≤ 𝓝 1 from nhdsWithin_le_nhds))
  filter_upwards [ht.lean c W he hV, self_mem_nhdsWithin (a:=(1:ℝ)) (s:=Set.Iio 1), (eventually_ge_nhds (show (0:ℝ)<1 by norm_num)).filter_mono (show (𝓝[<] (1:ℝ)) ≤ 𝓝 1 from nhdsWithin_le_nhds)] with x hx hs hX
  let p':= x • W; have hq: ‖p'‖≤R := by unfold p'; rw [norm_smul,Real.norm_of_nonneg hX]; exact (mul_le_of_le_one_left (norm_nonneg _) (show x≤1 from le_of_lt hs)).trans he
  let W':= Arc.route G b p'; have hc:= hf p' hq hx
  obtain ⟨L,hL,h⟩:= exists_dual_vector'' ℝ (G' x)
  have hr : Brush P.order A 1 ((L∘g) ∘ Arc.route G b) p' := (hc.report L hL).climb (by rw [one_mul]) le_rfl
  have hh := (ht.pay c p' hq (L∘g) _ hr).2 l hl hC
  have hQ:= Push.Local.left_linear L l (hp _ hq (Boulevard.smoky hx)) hl
  rw [hQ,show L (leftDerivs g l (Arc.route G b p'))= ‖G' x‖ from h,Real.norm_of_nonneg (norm_nonneg _)] at hh; exact hh

-- radius arbitrary above other geometries. Returns actual per-stage tests.
lemma coverage (G:Gauge) (L:Side) (j:ℕ) (f:ℝ→ℝ) (hf:Reserve G L f) :
    ∃ r : ℝ→ℝ, Reserve G L r ∧ ∀ᶠ x in atTop,
      1≤ r x ∧ 0<furl G L x ∧ furl G L x < r x ∧ |f x|≤ r x ∧
      ∀ β,inBand (betaF G x L) β→ gStep β*(2*r x) < eaves G L x ∧ ∀ P:BudgetPoint, P.threshold=Pressure.temp x → P.threshold ≤ 2*Pressure.fiery G x L → P.order=j →
        Tracer P G β (r x) := by
  obtain ⟨s,hs,h⟩:= oar G j
  obtain ⟨u,b,hP⟩:= cleanly G j 1 zero_lt_one
  obtain ⟨d,hd,hQ⟩:= Boulevard.seek (G:=G) hP.pos
  obtain ⟨p,h',hp⟩:= expCost G 2 1
  let T x:= 2*Pressure.fiery G x L
  let g x:=s*T x; let t x:=(1+(j:ℝ))*g x
  let M x:= Delay.fineMonitor G L x
  let R:=royalty G; have hr : 0<R:=zero_lt_one.trans_le (royalty_ge G)
  let v:= (j.factorial:ℝ)*u*((1+R)*(1+(j:ℝ))*s*4)
  let w x:=1+|f x|+ v*M x
  have hw : Reserve G L w:= ((Reserve.const 1).add hf.absolute).add (Reserve.mul (Reserve.const _) Reserve.monitoring)
  have hv:0≤v:= by have hx:= hP.value; unfold v; positivity
  have hR : Rate G L (-(1/2)) (fun x=>(1+R)*t x):= ((((Rate.flame (G:=G) (L:=L)).mul_left _).mul_left _).mul_left _).mul_left _
  let u' x:= Uniform.shade G* eaves G L x
  have hU : Rate G L vow u':= (Sienna.edge G L).mul_left _
  let f₁ x:=4*(sunLength p (u' x)*R)
  have hV : Rate G L vow f₁:= ((((hU.mul_left (1+1)).mul_left _).mul_right _).mul_left _)
  refine ⟨w,hw,?_⟩; filter_upwards [Access.wide (hw.rate.mul_left 2), Delay.shift_pos G L, Sienna.below' G L hU vow_ok hd,hU.below vow_ok 1 zero_lt_one,
    Sienna.contraction G L (a:=R) (b:=R) hr (p:=vow*2) (hV.pow 2) (show vow*2 < -(1/2:ℝ) by norm_num [vow]), softly G L, hR.below (by norm_num) 1 zero_lt_one,(Sienna.belt G L).below (by norm_num) (1/2) (by norm_num)] with x hx hh hx' hw hX hZ hz hL
  have hy : 0 ≤ v*M x := mul_nonneg hv (Delay.monitor_pos G L x).le
  have hζ : 1 ≤ w x:= (le_add_of_nonneg_right (abs_nonneg _)).trans (le_add_of_nonneg_right hy)
  have hF : 0 < furl G L x := Real.rpow_pos_of_pos hh _
  refine ⟨hζ,hF,(((le_abs_self _).trans hL).trans_lt (by norm_num : (1/2:ℝ)<1)).trans_le hζ,(le_add_of_nonneg_left zero_le_one).trans (le_add_of_nonneg_right hy), fun β hb=>?_⟩
  have hβ:= hx.2 β hb; let g':=gStep β; let W:= w x; have hp':0 ≤ 2*W := by change 1 ≤ W at hζ; positivity
  have hv : g'*(2*W)< eaves G L x:= lt_of_le_of_lt (mul_le_mul_of_nonneg_right hβ.2.le hp') ((abs_of_nonneg hp') ▸ hx.1.2.2.2)
  refine ⟨hv,fun P hs' he hO=> ?_⟩
  have he' : (g' * W) < eaves G L x := (mul_le_mul_of_nonneg_left (by change 1≤W at hζ; linarith) hβ.1.le).trans_lt hv
  have hg : 0 < g x:= mul_pos hs (P.threshold_pos.trans_le he)
  have ht : 0 < t x:= mul_pos (by positivity) hg
  have hC : 0 < g'*W:= mul_pos hβ.1 (zero_lt_one.trans_le hζ); have hΩ : 0 < eaves G L x:= Real.rpow_pos_of_pos hh _
  refine ⟨fun c U hu F q hM=> ?_, fun c U hu hS=>?_⟩
  · have he : Brush P.order (q*W^P.order) (g'*W)⁻¹ (F∘actual) (g' • U):= stepper U hβ.1 hM hζ
    -- threshold accounting
    have hw : gStep (betaF G x L) ≤ g'*2 := by have hh := band_gap (betaF G x L) β hh hb; change gStep (betaF G x L)/2 ≤ g' ∧ _ at hh; linarith only [hh.1]
    have hz' : (j.factorial:ℝ)*u*((1+R)*t x) ≤ g'*W:= by
      refine le_trans (b:=g'*(v*M x)) ?_ (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) hβ.1.le)
      have hp: g x=s*(2*(gStep (betaF G x L)*M x)):= rfl
      have hV :0 ≤ M x:= (Delay.monitor_pos G L x).le
      let A :ℝ:=j.factorial*u*(1+R)*(1+(j:ℝ))*s*2*M x
      have h :0≤A := by have he:= hP.value; unfold A; positivity
      apply le_trans _ ((mul_le_mul_of_nonneg_right hw h).trans _)
      · unfold t; rw [hp]; exact le_of_eq (by unfold A; ring)
      exact le_of_eq (by unfold v A; ring)
    rw [hO] at he
    rw [hO]
    refine Boulevard.hires hP (fun a ha=> hQ a ((ha.trans (mul_le_mul_of_nonneg_left he'.le (Uniform.shade_pos G).le)).trans hx'.le)) hC ((norm_smul g' U).trans_le ?_) he hz' ((le_abs_self _).trans hz)
      (show Sailor G P.threshold (g x) j from ⟨fun c a hv=> h c _ (P.threshold_pos.trans_le (by assumption)).le a (hv.trans (by assumption))⟩) hg ht
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hg.le)
    rw [Real.norm_of_nonneg hβ.1.le]; exact mul_le_mul_of_nonneg_left hu hβ.1.le -- edit
  · have he' : Uniform.shade G * ‖g' • U‖ ≤ u' x := by rw [norm_smul,Real.norm_of_nonneg hβ.1.le]; exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hu hβ.1.le).trans he'.le) (Uniform.shade_pos G).le
    have he'' := sunnySoon p (u' x) hp (g'•U) he' ((le_abs_self _).trans hw) hS (by
      change R*(f₁ x)^2<P.threshold*R; refine hX.trans_le ?_; rw [mul_comm R,hs']; apply mul_le_mul_of_nonneg_right _ hr.le; rw [Real.rpow_neg hh.le]; exact hZ.2)
    filter_upwards [he''] with y hy
    unfold Arc.route; rw [smul_comm]; exact hy
end YM.RemainderComparison.Arc
