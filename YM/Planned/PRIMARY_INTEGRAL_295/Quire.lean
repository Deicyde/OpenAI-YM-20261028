import YM.Planned.PRIMARY_INTEGRAL_295.Little
import YM.Push.STATIONARY_UNIFORM.Calculus


/-!
# From Full-circuit `Allows` on fixed-L log radius to pathwise finite Ember

Saves exact positionwise factor payment in F0,D^D estimate without size
lost to coordinates on period. Through ordered derivatives here measured
real multi-linear at eval y, not require b angular lift analytic; centered
interval p cutoff from Cabin authoritative. No hypothesis radius on
all b on common torus globally; only comes through precursor ledger.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Quire
open Function Filter Set Metric
open Labels Lattice RG Wilson Oval Cedar 
open Push.Uniform
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {E F G I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
   [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
   {n k : ℕ} {b : E→F} {q:F→G} {t r M C : ℝ}

lemma local_join {f:E→F} {g:F→G} (hf : Ember k f M) (hc:ContDiffAt ℝ k g (f 0)) (hq : Envelope (f 0) k g C):
    Ember k (g∘f) (k.factorial*C*(1+M)^k) := by
   have ht:=hf.1; have hv:=hf.2.1; have hC:=hq.1; have he:=hc.comp 0 ht; have hp : 1≤1+M:=by linarith
   let X := interior {z | ContDiffAt ℝ k f z}; let Y:=interior {z|ContDiffAt ℝ k g z}
   have hx : (0:E)∈X:= mem_interior_iff_mem_nhds.mpr (ht.eventually (by simp))
   have hy:f 0∈Y:=mem_interior_iff_mem_nhds.mpr (hc.eventually (by simp)); have hz:Y∈𝓝 (f 0):= isOpen_interior.mem_nhds hy
   obtain ⟨u,hU,hu,hm⟩:= _root_.mem_nhds_iff.mp (inter_mem (isOpen_interior.mem_nhds hx) (ht.continuousAt.preimage_mem_nhds hz))
   have ha : MapsTo f u Y := fun i hi=> (hU hi).2
   have hF : ContDiffOn ℝ k f u:=fun i hi=>(show ContDiffAt ℝ k f _ from interior_subset (hU hi).1).contDiffWithinAt
   have hG : ContDiffOn ℝ k g Y:=fun i hi=>(show ContDiffAt ℝ k g _ from interior_subset hi).contDiffWithinAt
   refine ⟨he,by positivity,fun b hb=>?_⟩
   have hw := norm_iteratedFDerivWithin_comp_le hG hF (Nat.cast_le.mpr hb) (isOpen_interior.uniqueDiffOn) hu.uniqueDiffOn ha hm (C:=C) (D:=1+M)
   rw [iteratedFDerivWithin_of_isOpen _ hu hm] at hw; refine (hw ?_ ?_).trans ?_
   · intro i hi; rw [iteratedFDerivWithin_of_isOpen _ isOpen_interior hy]; exact hq.2 _ (hi.trans hb)
   · intro i hi hd; rw [iteratedFDerivWithin_of_isOpen _ hu hm]; exact ((hf.2.2 i (hd.trans hb)).trans (le_add_of_nonneg_left zero_le_one)).trans (le_self_pow₀ hp (by omega))
   gcongr

-- typography near price* inverse; s=1 cut uses all. real max derivatives, no finiteDimension.
def wavelet (q:F→G) (u:F):= q u-q 0 - fderiv ℝ q 0 u
variable (h : ∀ z:F, ‖z‖≤r→ Allows (k+2) q z C) (hr:0≤r)
include h hr

private lemma bounds (z:F) (hz:‖z‖≤r): ContDiffAt ℝ ω (wavelet q) z ∧ ‖fderiv ℝ (wavelet q) z‖ ≤ C*‖z‖:= by
    let L:= fderiv ℝ q 0; have hx (v) (hv:‖v‖≤r): ContDiffAt ℝ ω q v:= (h v hv).1
    let s:=closedBall (0:F) r; have hh(v) (hv:v∈s): ‖v‖≤r:= by simpa only [s,mem_closedBall,dist_zero_right] using hv
    have hD(v) (hv:v∈s): ContDiffAt ℝ ω (fderiv ℝ q) v:= (hx v (hh v hv)).fderiv_right le_top -- name?
    have hw : ‖fderiv ℝ q z-L‖≤ C*‖z-0‖:= by
      refine (convex_closedBall (0:F) r).norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (fun v hv=>(hD v hv).differentiableAt (by simp))
        ?_ (mem_closedBall_self hr) (show z∈s by simpa only [s,mem_closedBall,dist_zero_right])
      intro v hv; rw [← norm_iteratedFDeriv_one (fderiv ℝ q),norm_iteratedFDeriv_fderiv]; exact (h v (hh v hv)).2 _ (by omega)
    refine ⟨((hx z hz).sub contDiffAt_const).sub L.contDiff.contDiffAt,?_⟩
    have he : fderiv ℝ (wavelet q) z=fderiv ℝ q z - L:=by
       change fderiv ℝ (fun x=>q x-q 0-L x) z=_; rw [fderiv_fun_sub ?_ L.differentiableAt,L.fderiv, fderiv_sub_const]; exact
        ((hx z hz).differentiableAt (by simp)).sub_const _
    rwa [he,show C*‖z‖=C*‖z-0‖ by rw [sub_zero]]

private lemma reached (z:F) (hz:‖z‖≤r): ‖wavelet q z‖≤ C * ‖z‖^2:= by
   have hC := (h 0 (by rwa [norm_zero])).nonneg
   let X:=closedBall (0:F) ‖z‖
   have hx(v)(hv:v∈X): ‖v‖≤‖z‖:= by simpa only [X,mem_closedBall,dist_zero_right] using hv
   have he:= (convex_closedBall (0:F) ‖z‖).norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (f:=wavelet q)
     (fun v hv=>(bounds h hr v ((hx v hv).trans hz)).1.differentiableAt (by simp))
     (fun v hv=> ((bounds h hr v ((hx v hv).trans hz)).2).trans (mul_le_mul_of_nonneg_left (hx v hv) hC))
     (mem_closedBall_self (norm_nonneg z)) (show z∈X by simp [X])
   rwa [show wavelet q 0=0 from by simp [wavelet],sub_zero,sub_zero,mul_assoc,←pow_two] at he

private lemma loft (z:F) (hz:‖z‖≤r) (n:ℕ) (hn: n ≤ k): ‖iteratedFDeriv ℝ n (wavelet q) z‖ ≤ C*‖z‖^(2-n) := by
   by_cases hw:n=0
   · subst n; rw [norm_iteratedFDeriv_zero,Nat.sub_zero]; exact reached h hr z hz
   by_cases hv:n=1
   · subst n; rw [norm_iteratedFDeriv_one,show 2-1= (1:ℕ) from rfl,pow_one]; exact (bounds h hr z hz).2
   have hf:= (h z hz).analytic
   let L:=fderiv ℝ q 0; let u:F→G:=fun _=>q 0
   have hd:=hf.of_le (show (n:WithTop ℕ∞)≤ω from le_top)
   have hp:=show ContDiffAt ℝ n u z from contDiffAt_const
   have ht: iteratedFDeriv ℝ n L z=0:=by
      obtain ⟨m,hm⟩:= Nat.exists_eq_add_of_le (show 2≤n by omega)
      apply norm_eq_zero.mp
      rw [hm,Nat.add_comm 2 m, ←norm_iteratedFDeriv_fderiv]; rw [show fderiv ℝ L=(fun _=>L) from funext (fun i=> ContinuousLinearMap.fderiv L)]; rw [iteratedFDeriv_const_of_ne (by omega : m+1≠0)]; simp
   change ‖iteratedFDeriv ℝ n ((q-u)-(L:F→G)) z‖ ≤ _
   rw [iteratedFDeriv_sub_apply (f:=q-u) (hd.sub hp) L.contDiff.contDiffAt,ht,sub_zero,
       iteratedFDeriv_sub_apply (f:=q) hd hp,show iteratedFDeriv ℝ n u z=0 from by unfold u; rw [iteratedFDeriv_const_of_ne hw]; rfl,sub_zero]
   simpa [show 2-n=0 by omega] using (h z hz).2 n (by omega)

def flake (k:ℕ) (M:ℝ):= (k.factorial:ℝ) * (1+M)^(k+2)
lemma copied {t} (ht:t∈ Ioc (0:ℝ) 1) (hf: Ember k b M) (hc: t*M≤r) :
     Ember k (fun x=> t⁻¹ • wavelet q (t • b x)) (C*t*flake k M):= by
   have hM:=hf.2.1; have ht':=ht.1; have hv :1≤1+M := le_add_of_nonneg_right hM
   have hC := (h 0 (by rwa [norm_zero])).nonneg
   let L:F→L[ℝ] F:= t • ContinuousLinearMap.id ℝ F
   let x:=b 0
   have hx : ‖x‖≤M:=hf.2.value
   have ht0 : ‖L x‖=t*‖x‖:= by rw [show L x=t • x from rfl,norm_smul,Real.norm_of_nonneg ht'.le]
   have hz : ‖L x‖≤r := ht0.trans_le ((mul_le_mul_of_nonneg_left hx ht'.le).trans hc)
   let H:=fun z:F=>t⁻¹ • wavelet q (L z)
   have hH := (bounds h hr (L x) hz).1
   have hs:=hH.comp x L.contDiff.contDiffAt
   have hb : Envelope x k H (C*t*(1+M)^2):=by
      refine ⟨by positivity,fun n hn=>?_⟩
      change ‖iteratedFDeriv ℝ n (t⁻¹ • (wavelet q ∘ L)) _‖ ≤ _
      have hd: ‖L‖ ≤ t:=by unfold L; rw [norm_smul,Real.norm_of_nonneg ht'.le]; exact mul_le_of_le_one_right ht'.le ContinuousLinearMap.norm_id_le
      rw [iteratedFDeriv_const_smul_apply (hs.of_le le_top),norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr ht'.le),WardBin.Lies.liner L (hH.of_le le_top)]
      apply (mul_le_mul_of_nonneg_left (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..) (by positivity : 0≤t⁻¹)).trans
      simp only [Finset.prod_const,Finset.card_univ, Fintype.card_fin]
      refine (mul_le_mul_of_nonneg_left (mul_le_mul (loft h hr (L x) hz n hn) (pow_le_pow_left₀ (norm_nonneg _) hd n) (by positivity) (by positivity)) (show 0≤t⁻¹ by positivity)).trans ?_
      let m:= 2-n
      have hu := pow_le_pow_of_le_one ht'.le ht.2 (show 2 ≤ m+n by omega)
      have hT : ‖x‖^m ≤ (1+M)^2:= (pow_le_pow_left₀ (norm_nonneg x) (hx.trans (le_add_of_nonneg_left zero_le_one)) _).trans
         (pow_le_pow_right₀ hv (Nat.sub_le ..))
      calc
        _ = C*(t⁻¹*t^(m+n))*‖x‖^m:=by rw [ht0,mul_pow,pow_add]; unfold m; ring
        _ ≤ _:= by
          have he : t⁻¹*t^(m+n)≤t:= (mul_le_mul_of_nonneg_left hu (show 0≤t⁻¹ by positivity)).trans_eq (by rw [pow_two,inv_mul_cancel_left₀ ht'.ne'])
          exact mul_le_mul (mul_le_mul_of_nonneg_left he hC) hT (by positivity) (by positivity)
   have he:=local_join hf ((hs.of_le le_top).const_smul t⁻¹) hb
   rw [show (k.factorial:ℝ)*(C*t*(1+M)^2)*(1+M)^k=C*t*flake k M from by unfold flake; rw [pow_add]; ring] at he
   exact he

def spat (q:F→G) (t:ℝ) (b:E→F) (x:E):= q (t • b x)-q 0
lemma lived {t} (ht:t∈Ioc (0:ℝ) 1) (hf:Ember k b M) (hc:t*M≤r):
    Ember k (spat q t b) (C*t*(M+flake k M)):=by
   let L:= fderiv ℝ q 0
   have hp:=h 0 (by rwa [norm_zero])
   have hb : Ember k (L ∘ b) (C*M) := ⟨L.contDiff.contDiffAt.comp _ hf.1, Seas.paidLinear L hf.1 hf.2 (by simpa using (hp.norm_le 1 (by omega)))⟩
   let D:= fun x:E=>t⁻¹ • wavelet q (t • b x)
   have ht' := ht.1; have he': t ≠ 0:= ht.1.ne';
   have he:= Ember.join hb (copied h hr ht hf hc)
   have hh : spat q t b=t • ((L ∘ b) +D):=by ext1 x; unfold spat D wavelet; simp only [comp_apply,Pi.add_apply,Pi.smul_apply,map_smul,smul_add,smul_inv_smul₀ he']; unfold L; abel
   rw [hh]; refine Ember.weakening (Ember.scaled he t) ?_
   have hx:=hp.nonneg; have hm := hf.2.1; have hF: 0≤flake k M:=by unfold flake; positivity
   rw [Real.norm_of_nonneg ht'.le]; have h := ht.2; apply le_trans (mul_le_mul_of_nonneg_left (show C*M+C*t*flake k M ≤ C*M+C*flake k M by
     gcongr; exact mul_le_of_le_one_right hx h) ht'.le); linarith
end YM.Planned.PrimaryIntegral295.Quire
