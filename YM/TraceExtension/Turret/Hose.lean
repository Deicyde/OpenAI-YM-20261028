import YM.TraceExtension.Filch.Wells
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Motif
set_option autoImplicit false
/-! # small-field transfer. Actual crop gauge across whole radius. Uses true predicate Healthy. Includes equality points. -/
noncomputable section
namespace YM.Trace.Turret
open Function Filter Lattice RG Wilson Work AnalyticBridge.SectorAffine.Offset Push.Uniform Planned.AtomRegular.Foliage WardBin.Lies Next.Fluctuations Next.SectorChange PhysicalNext.JointLoad Heir
open Finset
open scoped Topology Matrix.Norms.Frobenius ContDiff Classical
variable {X:Type}[NormedAddCommGroup X] [NormedSpace ℝ X]
variable {G:Gauge}{n: Side}{s C:ℝ}{o:Site n}{F:Config G n→ X}{P:BudgetPoint}{k r i:ℕ}{Q:Support n}

def minor(F:Config G n→ X)(s:ℝ)(x:Directions G n):= F (increment 1 (s • x))
private lemma fool {U:Config G n}{g:Site n→ G.El} (T:Collar G P.order)(hp: Canvas P o r U g P.order (Cube.fee T))(ht:Cube.Wire P r T)(V:Slab G n k)(hV:∀ i,P.dirBound o (V i))(hk:k≤ P.order):
   Through P.order ((Cube.moduleBill P r)⁻¹ • launch U o r g V) 0 (Cube.fee T) :=by
    let Y:= launch U o r g V; let s:= Cube.moduleBill P r; let A:=Cube.fee T; have h : 0<s:= mul_pos P.threshold_pos (pow_pos (a:=1+(r:ℝ)) (by positivity) _); have hr:1 ≤ A:=Cube.fee_one T; have hs:s ≤ 1:=ht.2
    have he: ContDiffAt ℝ P.order Y 0:=hp.ready V
    have hv(i) (hi:i≤P.order):‖iteratedFDeriv ℝ i Y 0‖ ≤ A*s:=by
       have hh(x:Site n)(hx:separation o x ≤ r):1+(separation o x:ℝ) ≤ (1+(r:ℝ))^P.power:= by
          apply le_trans (add_le_add_right (show (separation o x:ℝ) ≤ (r:ℝ) from Nat.cast_le.mpr hx) _); exact le_self_pow₀ (by simp) (by have h:=P.power_ge; omega)
       match i with
       | 0=>
         rw [norm_iteratedFDeriv_zero, show Y 0 = _ from launch_zero (V:=U) (g:=g) (o:=o) (r:=r) V]; apply (pi_norm_le_iff_of_nonneg (show 0 ≤ A*s by positivity)).mpr; intro j; by_cases hj:separation o j.1 ≤ r
         · apply (hp.size j hj).trans; unfold s Cube.moduleBill; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hh _ hj) P.threshold_pos.le) (by positivity)
         rw [crop,if_neg hj,norm_zero]; positivity
       | i+1=>
          let k:=i+1; refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v=>?_
          apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by positivity) (by positivity))).mpr; intro j
          let Z:Directions G n →L[ℝ] G.Color:= ContinuousLinearMap.proj j
          have hw:= hp.derivatives V o hk hV k (by omega) hi j
          have hz : ‖iteratedFDeriv ℝ k (Z ∘ Y) 0‖ ≤ A*s:=by
             let l:= separation o j.1; by_cases hv: l ≤ r
             · rw [if_pos hv] at hw; apply le_trans hw (mul_le_mul_of_nonneg_left _ (by positivity))
               change (P.threshold * (1+(separation j.1 o:ℝ))^P.power)^k ≤ s; rw [separation_comm]; have ht:= P.threshold_pos; exact (pow_le_pow_left₀ (by positivity) (show P.threshold*(1+(l:ℝ))^P.power ≤ s from mul_le_mul_of_nonneg_left (by gcongr) ht.le) k).trans (le_trans (pow_le_pow_of_le_one h.le hs (show 1≤k by omega)) (by simp))
             rw [if_neg hv] at hw; exact hw.trans (by positivity)
          change ‖Z (iteratedFDeriv ℝ k Y 0 v)‖ ≤ _; rw [show Z (iteratedFDeriv ℝ k Y 0 v)=iteratedFDeriv ℝ k (Z ∘ Y) 0 v from (by rw [Z.iteratedFDeriv_comp_left he (Nat.cast_le.mpr hi)];rfl)]
          exact (ContinuousMultilinearMap.le_opNorm ..).trans (mul_le_mul_of_nonneg_right hz (by positivity))
    have hC : Through P.order (s⁻¹ • Y) 0 (|s⁻¹| *(A*s)):= Through.scale (⟨he,hv⟩:Through _ _ _ _) _
    rw [abs_of_pos (inv_pos.mpr h),mul_comm _ s,inv_mul_cancel_left₀ h.ne'] at hC; exact hC
private lemma takes (hf:LocalOn ↑(halo r {o}) F)(hg:GaugeInvariant F){U:Config G n}{g:Site n→ G.El}(hm:Canvas P o r U g i C)(hs:0<s) (D:Slab G n k): F ∘ journey U k D=ᶠ[𝓝 0] minor F s ∘ (s⁻¹ • launch U o r g D):=by
    filter_upwards [(flowJourney U D).eventually hm.seen] with x hx
    let V:=journey U k D x
    rw [Function.comp_apply,Function.comp_apply,Pi.smul_apply,minor,smul_inv_smul₀ hs.ne',← hg g (journey U k D x)]; apply hf; intro j hj _
    obtain ⟨w,hw,he⟩:= halo_spec.mp (show j.1∈halo r {o} from hj); exact hx j (mem_singleton.mp hw ▸ he)
lemma lends {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][MeasurableSpace X]{F:Config G n→ X}(hf:P.Regular Q F) (hP:halo (r+1) {o} ⊆ Q)(hy:LocalOn (halo r {o}) F) (hn:2*(r+1)<n.val) (T:Collar G P.order)(hT:Cube.Wire P r T)(hc:0 ≤ C) (ht:∀ x,‖x‖≤Cube.fee T→Through P.order (minor F (Cube.moduleBill P r)) x C):
    P.supBounds o Q F (composeCost P.order C (Cube.fee T)):=by
    have hp:1≤ Cube.fee T:= Cube.fee_one T; refine ⟨by unfold composeCost; positivity,fun U hv l hl hk=>?_⟩
    obtain ⟨g,hg⟩:= primed hv hP hn T (by have h:=P.order_ge; omega) hT
    let t:=l.length; let D:=l.get; let s:=Cube.moduleBill P r; let Xq:= s⁻¹ • launch U o r g D
    have he:Through P.order Xq 0 (Cube.fee T):= fool T hg hT D (fun i=> hk _ (List.get_mem ..)) hl
    have hs:0<s:=mul_pos P.threshold_pos (pow_pos (a:=1+(r:ℝ)) (by positivity) _)
    have hL:= (takes hy hf.symmetry hg hs D).symm
    have hh:Through P.order (F ∘ journey U t D) 0 (composeCost P.order C (Cube.fee T)):= ((ht (Xq 0) (by rw [← norm_iteratedFDeriv_zero (𝕜:=ℝ)]; exact he.pay 0 (Nat.zero_le _))).comp (f:=Xq) he).germ hL
    rw [show leftDerivs F l U= iteratedFDeriv ℝ l.length (F ∘ journey U l.length l.get) 0 cart from (by simpa only[List.ofFn_get] using Germ.ordered l.get ((show Germ P.order F U from hf.smooth U hv).prod hl))]; refine le_trans (ContinuousMultilinearMap.le_opNorm ..) ?_; rw [prod_eq_one, mul_one]; exact hh.pay _ hl; intro i _; rw[show cart i=bolt i by ext1 j; simp [bolt, cart,Pi.single_apply]]; exact norm_bolt i
end YM.Trace.Turret
