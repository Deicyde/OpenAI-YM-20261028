import YM.TraceExtension.Pi.River
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Kits
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det Loft MeasureTheory Source Source.Drops Work Planned.PrimaryIntegral295 Place Parts Next.Foundations WardBin StressFlux Labels
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace Classical
variable {G:Gauge}{s:Side}{P:Support s}{F:Peat G s}{H:Hol G}
section Stay
variable (x:Axis) (n:ℤ)(h: Cleric F)(hp:LocalOn P F)(he:Nonwrapping P 0)(hm:n.natAbs ≤ 4)(hs:40 ≤ s.val)(hG:G.Simple)
include h hp he hm hs hG
omit hG in
lemma ratchet (V:Potential G)(y:Link G s): sheen F y (rideC (n • step x) (stepC 0 V))=sheen F y (stepC 0 (revD ((n:ℝ) • basis x) V)):=by
    refine shadeL hp h _ _ _ (fun ⟨i,j⟩ hi _=>?_) ; rw[spin_at]; unfold stepC revD; rw[ContinuousLinearEquiv.apply_symm_apply,ContinuousLinearEquiv.apply_symm_apply]; simp only [sub_zero]; congr 2
    have hv: lift (i+n •step x)=lift i+n •step x:=lift_eq_iff.mpr ⟨by rw[map_add,wrap_lift,map_zsmul,wrap_step],by
        intro k; simp only [Pi.add_apply,Pi.smul_apply,step_apply]; simp only[zsmul_eq_mul,Int.cast_id]; have hh:=he i hi; unfold separation at hh; rw [sub_zero] at hh; have hx:=component_le i k; split <;> omega⟩
    rw[hv]; ext1 k; by_cases h:x=k; · simp [basis_eq,h]
    simp[basis_eq,h,Ne.symm h]
lemma steer0 (V:Taylor G 0)(y:Link G s): sheen F y (rideC (n •step x) (ivy 0 V))= sheen F y (ivy 0 V):=by
    unfold ivy; rw[ratchet x n h hp he hm hs,ride_0,sC_sub,sheen_sub_r]; change _-_=_; rw[show sheen F y (stepC _ (Place.jump _))=0 from cellar (by omega) he hp h hG _ _]; ring
lemma steer1 (V:Taylor G 1)(y:Link G s): sheen F y (rideC (n •step x) (ivy 0 V))=sheen F y (ivy 0 V)+(n:ℝ)*sheen F y (ivy 0 (bentV V x)):=by
    unfold ivy; have hv(q:E4→G.Color): sheen F y (stepC 0 (Place.jump q))=0:=cellar (by omega) he hp h hG _ _
    rw [ratchet x n h hp he hm hs, ride_1 V x,sC_sub,sC_add,sC_weights,sC_sub,sheen_sub_r,sheen_add_r,sheen_scale_r,sheen_sub_r,hv,hv];ring
lemma shine_r (i:ℕ)(A:Taylor G 0)(B:Taylor G i): sheen (rj (n •step x) F) (ivy 0 A) (ivy 0 B)= sheen F (ivy 0 A) (rideC (n •step x) (ivy 0 B)):=by
    rw[show sheen (rj (n •step x) F) (ivy 0 A) (ivy 0 B)= sheen F (rideC (n •step x) (ivy 0 A)) (rideC (n •step x) (ivy 0 B)) from ?_, sheen_symm F h, steer0 x n h hp he hm hs hG, sheen_symm F h]
    unfold sheen; rw[take_px,wired (rideC _) (by rw[map_zero]; exact h.dye.analyticAt),map_zero]; congr 1; funext k;fin_cases k<;>rfl
end Stay
variable (T: Axis→loom G s) (hT:∀ a, LocalOn P (T a).val)(hP:Nonwrapping P 0)(hs:40 ≤ s.val)(hG:G.Simple)
def starling (A: loom G s) : Site s→ loom G s:= fun i=> ⟨rj i A.val,taking_loom i _ A.property⟩
def anis (X Y:Link G s): loom G s→ₗ[ℝ] ℝ:=loom₂ s G ((bite G s).symm (X,0)) ((bite G s).symm (Y,0))
lemma anum (X Y:Link G s)(A:loom G s): anis X Y A=sheen A.val X Y:=by unfold anis; change iteratedFDeriv ℝ 2 (ballX A.val) 0 _=_; rw[loom_banks A.property, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
lemma loom0 (A: loom G s): A.val 1=0:=by
    have hx:=loom_read A.property; change A.val (input _ _ (bite _ _ 0).1)=0∧ _ at hx; simpa using hx.1
def airT (T:Axis→Peat G s):=∑ a:Axis,elm a (fun i=> rj i (T a)) 0
include hT hP hs hG
lemma readable {Z:Label G 5}(ht:JetTest H 0 Z (Complex.ofRealCLM ∘ airT (fun a=> (T a).val)))(J:Jet G): Labels.read J Z.val= (↑(∑ a:Axis,sheen (T a).val (ivy (0:Site s) (J 0)) (ivy 0 (bentV (J 1) a))):ℂ):=by
   let B(a):= elm a (starling (T a)) 0; let A:= ∑ a:Axis,B a
   let W:=ivy (0:Site s) (J 0); let U:=ivy (0:Site s) (J 1)
   have he:A.val=airT fun a=> (T a).val:=by unfold airT A B elm Pull.dTap; simp only [AddSubmonoidClass.coe_finsetSum,Submodule.coe_smul,Submodule.coe_sub];rfl
   rw[← he] at ht; rw[vista5 (show Cleric _ from A.property.1) hG ht J,loom0]; let Q:=anis W W; let V:=anis W U
   have h₂(j:Fin 4): (Pull.steps j)≤4:=by unfold Pull.steps; omega
   have hv(a) : sheen (B a).val W W=0:=by
         rw [← anum]; unfold B elm Pull.dTap; rw [map_sum]; apply sum_eq_zero; intro i hi; rw [map_smul,map_sub]; let m:ℤ:= Pull.steps i
         have hx (n:ℤ)(h:n.natAbs≤4): anis W W (starling (T a) (0+n • step a))= sheen (T a).val W W:=by rw [zero_add,anum,show (starling (T a) (n • step a)).val=rj (n • step a) (T a).val from rfl, shine_r a n (T a|>.property.1) (hT a) hP h hs hG, steer0 a n (T a|>.property.1) (hT a) hP h hs hG]
         rw [hx (0+m) (by simp[m,h₂ i]),hx (0-m) (by simp[m,h₂ i])]; ring
   let η(a:Axis):= sheen (T a).val W (ivy 0 (bentV (J 1) a))
   have h₁(a): sheen (B a).val W U=η a:=by
        rw [← anum]; unfold B elm Pull.dTap; rw [map_sum]; have h':=Pull.credit 1 (by omega); simp only [pow_one,sub_neg_eq_add,if_true] at h'
        have hf(n:ℤ)(hn:n.natAbs≤4): anis W U (starling (T a) (0+n • step a))= sheen (T a).val W U+(n:ℝ)*η a :=by rw[zero_add,anum,show (starling (T a) (n • step a)).val=rj (n • step a) (T a).val from rfl, shine_r a n (T a|>.property.1) (hT a) hP hn hs hG,steer1 a n (T a|>.property.1) (hT a) hP hn hs hG]
        rw[← one_mul (η a),← h',sum_mul]; apply sum_congr rfl; intro j _; rw[map_smul,map_sub,hf _ (by simp [h₂]),hf _ (by simp[h₂])]; push_cast; rw [smul_eq_mul]; ring
   rw [show sheen A.val W W=0 from ?_, show sheen A.val W U=∑ a:Axis,η a from ?_]; rotate_left
   · rw[← anum]; unfold A; rw[map_sum]; exact sum_congr rfl fun i _=> (anum ..).trans (h₁ i)
   · rw[← anum]; unfold A; rw[map_sum]; apply sum_eq_zero; exact fun i _=> (anum ..).trans (hv i)
   rw [zero_add,mul_zero,zero_add]
end YM.Trace.Kits
