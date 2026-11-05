import YM.R2I.Vale.Divide
/-!
# Winding tickets in alias output reattachment

Helper diagonal derivative exchange on sunny. No bound on CFG-radius of that set.
Ray proof akin ProjectorNext.PROJECTOR_EQUIVARIANCE.Line. Uses *known* left
prices both representations on that set, not falsely equating analytic pins.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Averaging.Wind
open Function Filter Set Lattice Wilson RG StressFlux Finset
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace Classical
open PhysicalNext.Repeat Collection Anchor Next.Foundations
variable {G:Gauge}{n:Side}{P:BudgetPoint}{X:Support n}{f:Pot G n}{a b:ℝ}{R:Listing G n}{F:Collection.Source G n}
abbrev Sunny (P:BudgetPoint)(w:Config G n):Prop:= flags P.threshold w = ∅
lemma often : ∀ᶠ w:Config G n in 𝓝 1, Sunny P w:= by
   have hk : (1:Config G n)∈Boulevard.sunny P:= fun i=> by simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read,posDir,negDir] using P.threshold_pos
   filter_upwards [(Boulevard.sky P).mem_nhds hk] with y hy; exact Boulevard.smoky hy
private lemma parallelM (u:Dir G n)(s t:ℝ): increment (increment 1 (s•u)) (t•u)=increment 1 ((t+s)•u):= by
   funext e; apply G.mat_injective; simp only [increment, Pi.smul_apply,G.mat_lieExp,add_smul,map_add,map_smul,mul_one,G.mat_mul,Pi.one_apply]
   haveI : NormedAlgebra ℚ G.Mat := .restrictScalars ℚ ℝ _
   exact (NormedSpace.exp_add_of_commute (((Commute.refl (G.colorMat (u e))).smul_left t).smul_right s)).symm
private lemma eraRay (A:Dir G n): Tendsto (fun t:ℝ=> increment 1 (t•A)) (𝓝 0) (𝓝 1) := by
   let B(s:ℝ):= increment 1 (s • A); have he:B 0=1:= by simp only [B,zero_smul,at_zero]
   have hh : Continuous B:= by unfold B increment; fun_prop
   simpa only [he] using hh.tendsto 0
private lemma spec (v:Dir G n) (t:ℝ) (he: P.Regular X f) (ht: Healthy P.threshold X (increment 1 (t • v))) {m:ℕ}(hm:m<P.order) : HasDerivAt (iteratedDeriv m fun t:ℝ=>f (increment 1 (t • v))) (iteratedDeriv (m+1) (fun t:ℝ=> f (increment 1 (t • v))) t) t := by
   let B(s:ℝ):=increment (1:Config G n) (s • v); let L:= f ∘ B
   have hP: ContDiffAt ℝ P.order L t:= by
     have he' : L=(f∘increment (B t)) ∘ fun s=> (s-t) • v := by funext s; simp only [L,Function.comp_apply,B,parallelM,sub_add_cancel]
     rw [he']; refine ContDiffAt.comp t ?_ (by fun_prop); simp only [sub_self,zero_smul]; exact he.smooth _ ht
   have hz : DifferentiableAt ℝ (iteratedDeriv m L) t:=
     (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => ℝ) ℝ (fun _ => 1)).differentiableAt.comp t (hP.differentiableAt_iteratedFDeriv (Nat.cast_lt.mpr hm))
   rw [iteratedDeriv_succ]; exact hz.hasDerivAt
-- physical unmasked diagonal at ALL cylinder-local labels sum. price grows with Mesh; after combining divide by Volume where needed.
def chat (f:Pot G n) (v:Dir G n) := iteratedDeriv 2 (fun t:ℝ=> f (increment 1 (t•v))) 0
lemma aperture (g:G.Simple)(h:Local R P F a b) (A:Dir G n) (hd:∀ o,P.dirBound o A) : HasSum (fun i=> logHessian (F.logRead i) A A) (chat ((R.read F).additive P) A) := by
   let f(t:ℝ):=increment (1:Config G n) (t•A); let L := (R.read F).additive P; let B (j i : ℕ) := iteratedDeriv j ((F.logRead i) ∘ f)
   obtain ⟨r,hr,hR⟩ := Metric.mem_nhds_iff.mp ((eraRay A).eventually (often (P:=P)))
   let V := Metric.ball (0:ℝ) r; have hV:IsOpen V:=Metric.isOpen_ball; have h0:0∈V:= Metric.mem_ball_self hr
   obtain ⟨k,hk,hD⟩:= RG.Activities.E_total h.unweighted
   have hv (t:ℝ)(ht:t∈V) (X:Support n): Healthy P.threshold X (f t):= by unfold Healthy; rw [(show flags P.threshold (f t)=∅ from hR ht)]; simp
   have hF j (hj:j≤P.order) (i) t (ht:t∈V): ‖B j i t‖≤ k i:=by
     change ‖iteratedDeriv j (fun t:ℝ=> F.logRead i (increment 1 (t • A))) t‖ ≤ _; rw [← leftDerivs_diag]
     refine (hD i).2 _ (hv t ht _) _ (List.length_replicate.trans_le hj) ?_; exact fun _ hh=> (List.mem_replicate.mp hh).2 ▸ hd _
   have hS j (hj:j≤P.order) t (ht:t∈V) : HasSum (fun i=> B j i t) (iteratedDeriv j (L ∘ f) t) := by
     have hs j' (hj':j'≤P.order) t' (ht':t'∈V): Summable fun i=>B j' i t' := Summable.of_norm_bounded hk (fun i=> hF j' hj' i t' ht')
     refine (hs _ hj _ ht).hasSum_iff.mpr ?_
     induction j generalizing t with
     | zero => change _=(L _) ; exact tsum_congr fun i=> (masked_eq _ _ _ _ (hv t ht _)).symm
     | succ j ih =>
       have he : ∀ i t, t∈V → HasDerivAt (B j i) (B (j+1) i t) t:= fun i t hy=> spec A t (h.smooth i) (hv t hy _) hj
       have hy:=hasDerivAt_tsum_of_isPreconnected hk hV Metric.isPreconnected_ball he (hF (j+1) hj) h0 (hs j (Nat.le_of_lt hj) _ h0) ht
       rw [iteratedDeriv_succ]; exact ((hy.congr_of_eventuallyEq (f₁:=iteratedDeriv j (L ∘ f)) (Filter.eventually_of_mem (hV.mem_nhds ht) fun u hu=> (ih (Nat.le_of_lt hj) _ hu).symm)).deriv).symm
   have he i : logHessian (F.logRead i) A A=B 2 i 0:= by
     rw [hessian_diag g (h.smooth i)]; have hi:= leftDerivs_diag 1 A (F.logRead i) 2 0; rw [zero_smul,at_zero] at hi; exact hi
   simp_rw [he]; exact hS _ (by have hh:=P.order_ge; omega) 0 h0

section compare
-- polarization using scaled finite lamp directions. Comparisons log. Planar approximation in shadow, not a pilot.
variable {S:Listing G n} {T:Collection.Source G n}{t w:ℝ} (g:G.Simple)(P:BudgetPoint) (k:PlaqAxes) (x y : Site n)
set_option quotPrecheck false
local notation "λ₀" => (P.threshold / 2 : ℝ)
def ray (x:Site n): Dir G n := λ₀ • lamp k x
local notation "κ" => (Wind.ray P k)
variable (A:Activities G n) (u v: Dir G n)
lemma polar (f:Pot G n) (h:P.Regular X f) : logHessian f u v=(1/2:ℝ) *(logHessian f (u+v) (u+v) - logHessian f u u - logHessian f v v):=by
   simp only [hessian_eq,map_add,add_apply]; simp_rw [← hessian_eq, hessian_symm h v u]; ring
lemma grant : logHessian f (lamp k x) (lamp k y)=(λ₀^2)⁻¹ * logHessian f (κ x) (κ y):= by
   simp only [ray,hessian_eq,map_smul,smul_apply,smul_eq_mul]; have hh:=P.threshold_pos; field_simp
include g
lemma size_ray (e:Edge (Site n)): ‖Wind.ray (G:=G) P k x e‖≤ λ₀:= by unfold ray lamp; rw [Pi.smul_apply,norm_smul,Real.norm_of_nonneg (half_pos P.threshold_pos).le]; apply mul_le_of_le_one_right (half_pos P.threshold_pos).le; by_cases h:e=(x,k.val.2); subst e; simp [spike_norm g]; simp [h]
lemma core (o) : P.dirBound (G:=G) o (κ x) := fun e=> (size_ray g P k x e).trans ((half_le_self P.threshold_pos.le).trans (le_mul_of_one_le_right P.threshold_pos.le (one_le_pow₀ (by simp))))
lemma core' o : P.dirBound (G:=G) o (κ x + κ y):= by
   intro e; rw [Pi.add_apply]; refine (norm_add_le ..).trans ((add_le_add (size_ray g P k x e) (size_ray g P k y e)).trans ?_); rw [add_halves]; exact le_mul_of_one_le_right P.threshold_pos.le (one_le_pow₀ (by simp))

def duet (A:Activities G n) := (λ₀^2)⁻¹ * ((1/2:ℝ)*(chat (A.additive P) (κ x+κ y) - chat (A.additive P) (κ x) - chat (A.additive P) (κ y)))
lemma anything (h:Local R P F a b) : HasSum (fun i=> logHessian (F.logRead i) (lamp k x) (lamp k y)) (duet P k x y (R.read F)):= by
   have he:= aperture g h _ (core g P k x); have hp:=aperture g h _ (core g P k y); have ht:=aperture g h _ (core' g P k x y)
   unfold duet; have H:= (((ht.sub he).sub hp).mul_left (1/2:ℝ)).mul_left ((λ₀^2)⁻¹); exact H.congr_fun (fun i=>(grant P k x y).trans (congr_arg _ (polar P _ _ _ (h.smooth i)))) -- check
def trove (A:Activities G n) := -(1/2:ℝ)* ∑ i:Site n, ∑ j:Site n,(coord i j k.val.1)^2*duet P k i j A
lemma sum_trove (h:Local R P F a b): HasSum (fun i=> Anchor.plane k (F.logRead i)) (trove P k (R.read F)) := by
   refine ((hasSum_sum (s:=Finset.univ) (fun i _=> hasSum_sum (s:=Finset.univ) fun j _=>(anything g P k i j h).mul_left ((coord i j k.val.1)^2))).mul_left (-(1/2:ℝ))) -- f syntactic?
omit g
lemma trove_fare (B:Activities G n)(b:ℝ)(hU:∀ V,Sunny P V→b+A.additive P V=B.additive P V) : trove P k A=trove P k B:= by
  have he (v:Dir G n): chat (A.additive P) v= chat (B.additive P) v:= by
     let r(t:ℝ):= increment (1:Config G n) (t•v); let F:=A.additive P ∘ r; let U:=B.additive P ∘ r
     have hF: (fun s : ℝ=> b+F s)=ᶠ[𝓝 0] U:= by filter_upwards [(eraRay v).eventually (often (P:=P))] with i hi using hU _ hi
     rw [show chat (B.additive P) v=iteratedDeriv 2 U 0 from rfl, ← hF.iteratedDeriv_eq]
     suffices E:deriv (fun s:ℝ=> b+F s)=deriv F by
       change iteratedDeriv 2 F _ = _; simp_rw [show (2:ℕ)= 1+1 from rfl, iteratedDeriv_succ',E]
     funext s; rw [deriv_const_add]
  simp only [trove,duet,he] -- k variable
end compare
end YM.AnalyticBridge.VerifiedReset.Averaging.Wind
#print axioms YM.AnalyticBridge.VerifiedReset.Averaging.Wind.trove_fare
