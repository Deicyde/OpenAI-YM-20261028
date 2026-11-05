import YM.Frontier6.Normal.Charge
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! The fixed position partition and Taylor-test radial convention. Independent
of cutoff choices, arity, horizons/support. Use normalized s engineering
scale (separate from vacuum log). All test maps conditional only on patches. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Normal
open Function Set TopologicalSpace Filter MeasureTheory Metric
open scoped Topology ContDiff BigOperators Classical
variable {X Y:Type*}[NormedAddCommGroup X][NormedAddCommGroup Y][NormedSpace ℝ Y]
section Vec
variable [NormedSpace ℝ X]
/-- Closed-ball support convention for local tests. -/
def Fits (s:ℝ)(f:Full X):Prop:= tsupport f ⊆ closedBall (0:X) s
lemma Fits.intro {f:Full X}{s:ℝ}(h:∀ x:X,s< ‖x‖→ f x=0) : Fits s f:=closure_minimal (fun x hx=> mem_closedBall_zero_iff.mpr (le_of_not_gt (fun he=> hx (h x he)))) isClosed_closedBall
lemma Fits.out {f:Full X}{s:ℝ}(h:Fits s f)(x:X)(he:s< ‖x‖): f x=0:=image_eq_zero_of_notMem_tsupport (fun hx=> he.not_ge (mem_closedBall_zero_iff.mp (h hx)))
lemma Fits.up {f:Full X}{s r:ℝ}(h:Fits s f)(he:s≤r):Fits r f:= fun _ hx=> closedBall_subset_closedBall he (h hx)
lemma Fits.add {f g:Full X}{s:ℝ}(hf:Fits s f)(hg:Fits s g): Fits s (f+g):= (tsupport_add f g).trans (union_subset hf hg)
lemma Fits.sub {f g:Full X}{s:ℝ}(hf:Fits s f)(hg:Fits s g): Fits s (f-g):= (tsupport_sub f g).trans (union_subset hf hg)
lemma Fits.smul {f:Full X}{s:ℝ}(h:Fits s f)(c:ℂ): Fits s (c • f):= Fits.intro fun x hx=> by simp [h.out x hx]
lemma Fits.rs {f:Full X}{s:ℝ}(h:Fits s f)(c:ℝ):Fits s (c • f):= Fits.intro fun x hx=> by simp [h.out x hx]

lemma blast (s:ℝ)(f:X→Y)(h:Smooth f)(i:ℕ)(x:X):
   iteratedFDeriv ℝ i (fun y=> f (s • y)) x=(s^i) • iteratedFDeriv ℝ i f (s • x):=by
   let T:= s • ContinuousLinearMap.id ℝ X
   have ht(w):T w=s • w:=rfl
   apply ContinuousMultilinearMap.ext; intro m; simp_rw [← ht];
   change iteratedFDeriv ℝ i (f ∘ T) x m= _; rw [ContinuousLinearMap.iteratedFDeriv_comp_right T h _ (natural_le i), ContinuousMultilinearMap.compContinuousLinearMap_apply];
   simp_rw [ht];
   have he:= (iteratedFDeriv ℝ i f (s • x)).map_smul_univ (fun _=> s) m
   simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using! he
lemma Estimate.shrinks {P t s:ℝ}{j:ℕ}{f:X→Y}{L:Set X}(hf:Estimate j t f L P)(h:Smooth f)(hs:0<s):
   Estimate j (s*t) (fun x=> f (s⁻¹ • x)) {x : X | s⁻¹ • x ∈ L} P:=by
   intro i hi x hx; rw [blast _ _ h,norm_smul,Real.norm_of_nonneg (pow_nonneg (inv_pos.mpr hs).le _),mul_pow]
   calc
    _ = t^i * ‖iteratedFDeriv ℝ i f (s⁻¹ • x)‖:= by rw [inv_pow]; field_simp [(pow_ne_zero i hs.ne'),hs.ne']
    _ ≤ _ := hf i hi (s⁻¹ • x) hx

def stretch (s:ℝ)(f:Full X): Full X:= if h:0<s then
    ⟨fun x:X=> f (s⁻¹ • x), f.contDiff.comp (contDiff_const.smul contDiff_id), f.hasCompactSupport.comp_smul (inv_pos.mpr h).ne',subset_univ _⟩ else 0
@[simp] lemma stretch_eval {s:ℝ}(h:0<s)(f:Full X)(x): stretch s f x=f (s⁻¹ • x):=by unfold stretch; rw [dif_pos h]; rfl
lemma stretch_fits {s r:ℝ}(h:0<s){f:Full X}(he:Fits r f): Fits (s*r) (stretch s f):=by
   refine Fits.intro (fun x hx=>?_); rw [stretch_eval h]
   apply he.out; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr h).le,← div_eq_inv_mul]; exact (lt_div_iff₀ h).2 ((mul_comm ..).trans_lt hx)
lemma Charge.stretches {s t P:ℝ}{j:ℕ}(h:0<s){f:Full X}(he:Charge j t (f:X→ℂ) P): Charge j (s*t) (stretch s f:X→ℂ) P:=by
   rw [show (stretch s f:X→ℂ)=fun x=> f (s⁻¹ • x) from funext (stretch_eval h f)]
   exact Estimate.subset (Estimate.shrinks he f.contDiff h) (fun _ _=> mem_univ _)

def focus (s:ℝ)(f:Full X) : Full X:= (s⁻¹ ^ Module.finrank ℝ X) • stretch s f
lemma focused {s:ℝ}(h:0<s)(f:Full X)(x:X): focus s f x=(s^ Module.finrank ℝ X)⁻¹ • f (s⁻¹ • x):=by rw [focus,smul_apply, stretch_eval h, inv_pow]
lemma focus_fits {s r:ℝ}(h:0<s){f:Full X}(he:Fits r f): Fits (s*r) (focus s f):=(stretch_fits h he).rs _
lemma focus_bound {s P:ℝ}(h:0<s){f:Full X}{j:ℕ}(he:Charge j 1 (f:X→ℂ) P): Charge j s (focus s f:X→ℂ) ((s^ Module.finrank ℝ X)⁻¹ * P):=by
   have ht:=Charge.stretches h he; rw [mul_one] at ht
   have hh:=Estimate.smulR (s⁻¹ ^ Module.finrank ℝ X) ht (stretch s f).contDiff; rw [Real.norm_of_nonneg (pow_nonneg (inv_pos.mpr h).le _),inv_pow] at hh;
   unfold focus; rw [inv_pow]; exact hh
end Vec

section Inner
variable (X:Type*) [NormedAddCommGroup X][InnerProductSpace ℝ X][FiniteDimensional ℝ X]
def mask : Full X:= by
  letI := FiniteDimensional.proper ℝ X
  let f(x:X):ℂ:=(Real.smoothTransition ((4-‖x‖^2)/3):ℝ)
  have he:tsupport f⊆ closedBall (0:X) 2:=by
    refine closure_minimal (fun x hx=> ?_) isClosed_closedBall
    refine mem_closedBall_zero_iff.mpr (le_of_not_gt (fun h=> hx ?_))
    unfold f; rw [Real.smoothTransition.zero_of_nonpos (by nlinarith only [h]), Complex.ofReal_zero]
  exact ⟨f,Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (((contDiff_const.sub (contDiff_norm_sq ℝ)).div_const (3:ℝ)))), (isCompact_closedBall (0:X) 2).of_isClosed_subset (isClosed_tsupport _) he,subset_univ _⟩
variable {X}
lemma mask_at (x:X):mask X x= (Real.smoothTransition ((4-‖x‖^2)/3):ℝ):=rfl
@[simp] lemma star_mask (x:X): star (mask X x)=mask X x:=by simp [mask_at]
lemma mask_home (x:X)(h:‖x‖≤1):mask X x=1:=by rw [mask_at,Real.smoothTransition.one_of_one_le (by nlinarith only [h,norm_nonneg x]), Complex.ofReal_one]
lemma mask_away (x:X)(h:2 ≤ ‖x‖):mask X x=0:=by rw [mask_at,Real.smoothTransition.zero_of_nonpos (by nlinarith only [h]),Complex.ofReal_zero]

def shrink (X:Type*) [NormedAddCommGroup X][InnerProductSpace ℝ X][FiniteDimensional ℝ X](s:ℝ): Full X:=stretch s (mask X)
lemma shrink_home {s:ℝ}(h:0<s)(x:X)(he:‖x‖≤s): shrink X s x=1 :=by
   unfold shrink; rw [stretch_eval h]; apply mask_home; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr h).le,← div_eq_inv_mul]; exact div_le_one_of_le₀ he h.le
lemma shrink_fits {s:ℝ}(h:0<s): Fits (2*s) (shrink X s):= by rw [mul_comm]; exact stretch_fits h (Fits.intro (fun x hx=> mask_away x hx.le))

def strip (X:Type*) [NormedAddCommGroup X][InnerProductSpace ℝ X][FiniteDimensional ℝ X](s:ℝ): Full X:= shrink X s - shrink X (s/2)
def Ringed (X:Type*)[NormedAddCommGroup X](s:ℝ): Set X:= {x:X| s/2 ≤ ‖x‖ ∧ ‖x‖≤ 2*s}
lemma ring_closed (s:ℝ): IsClosed (Ringed X s):= IsClosed.preimage (f:=fun x:X=> ‖x‖) continuous_norm isClosed_Icc
lemma strip_ring {s:ℝ}(h:0<s): tsupport (strip X s) ⊆ Ringed X s:=by
   refine closure_minimal (fun x hx=>?_) (ring_closed s)
   have hv: strip X s x≠0:=hx; rw [strip,sub_apply] at hv
   exact And.intro (le_of_not_gt (fun he=> hv (by rw [shrink_home h x (by linarith only [he,h]),shrink_home (half_pos h) x he.le, sub_self]))) (le_of_not_gt (fun he=> hv (by rw [ (shrink_fits h).out x he,(shrink_fits (half_pos h)).out x (by linarith),sub_self])))
lemma shrink_charge (j:ℕ):∃ C:ℝ, 0 ≤ C ∧ ∀ s:ℝ,0<s→ Charge j s (shrink X s:X→ℂ) C:=by
   obtain ⟨C,hC⟩:= exists_charge j (mask X) 1 zero_le_one; refine ⟨C,hC.nonneg,fun s h=> ?_⟩; simpa only [shrink,mul_one] using Charge.stretches h hC
lemma strip_charge (j:ℕ):∃ C:ℝ,0 ≤ C ∧ ∀ s:ℝ,0<s→ Charge j s (strip X s:X→ℂ) C:=by
   obtain ⟨C,hC,h⟩:=shrink_charge (X:=X) j
   refine ⟨C+(2:ℝ)^j*C, by positivity,fun s hs=>?_⟩
   have he:= Estimate.scale_up (h (s/2) (half_pos hs)) (half_pos hs).le hs.le hC (B:=2) (by norm_num) (by linarith)
   exact Estimate.sub (h s hs) he (shrink X s).contDiff (shrink X (s/2)).contDiff hs.le
end Inner
end YM.Frontier6.Normal
#print axioms YM.Frontier6.Normal.Charge.stretches
#print axioms YM.Frontier6.Normal.strip_charge
