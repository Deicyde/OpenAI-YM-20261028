import YM.TraceExtension.Quince.Cache
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Quince
open Function Filter Set Lattice RG Pressure Wilson Finset Push Local Extra.Histories Next.Foundations Labels Source
open Cub WardBin.Lies
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c f:Side}{n:ℕ}{s:Support c}{w r ε a b :ℝ}{u v F H:Config G c→ℝ}{t:ℂ}{P:BudgetPoint}
def cab (t:ℂ)(F H: Config G c→ℝ): Config G c→ℂ:= t • (Complex.ofRealCLM ∘ F + Complex.I • (Complex.ofRealCLM ∘ H))
lemma routeB (p:Probe G n) (h: Chart n u 1)(hp: Chart n v 1)(hf: Chart n F 1)(hF: Chart n H 1)(Y: Source.Hol G)
   (hw: P.Regular s (cab t u v))(hA:n ≤P.order)(hs:Nonwrapping s 0)
   (he:∀ l:List (Directions G c),l.length≤n→ (∀ A∈l,P.dirBound 0 A)→ ‖leftDerivs u l 1-leftDerivs F l 1‖ ≤ a)
   (hv:∀ l:List (Directions G c),l.length≤ n→(∀ A∈l,P.dirBound 0 A)→‖leftDerivs v l 1-leftDerivs H l 1‖ ≤ a)
   (hO :‖iteratedDeriv p.2.val (F ∘ Y.testLinks n 0 (P.threshold • p.1)) 0‖ ≤ b)
   (hJ :‖iteratedDeriv p.2.val (H ∘ Y.testLinks n 0 (P.threshold • p.1)) 0‖ ≤ b)(hY:n≤P.power):
   ‖Local.sample Y 0 s P.threshold (cab t u v) p‖ ≤ (Local.partPrice Y p)* (Cub.gaugeMeter n* (‖t‖ * (a+a))) + ‖t‖*(b+b):=by
   let W:=Y.testLinks n (0: Site c) (P.threshold • p.1); let K:= cab t F H
   have hh: Chart n K 1:=by
      have hh(U:Config G c→ℝ)(h:Chart n U 1): Chart n (Complex.ofRealCLM ∘ U) 1:= Complex.ofRealCLM.contDiff.contDiffAt.comp _ (show ContDiffAt ℝ _ (U ∘ increment 1) 0 from h)
      change ContDiffAt ℝ n (K ∘ increment 1) 0; exact ((show ContDiffAt ℝ n ((Complex.ofRealCLM ∘ F) ∘ increment 1) 0 from hh F hf).add ((show ContDiffAt ℝ n ((Complex.ofRealCLM ∘ H) ∘ increment 1) 0 from hh H hF).const_smul Complex.I)|>.const_smul t)
   have hz:= speedTest (f:=cab t u v) Y s p ((hw.smooth 1 (one_healthy s _ P.threshold_pos.le)).of_le (Nat.cast_le.mpr hA)) hh (o:=0) (B:=P) (c:=‖t‖*(a+a)) fun l hl hₚ=> cleared h hp hf hF a a l hl t (he l hl hₚ) (hv l hl hₚ)
   have hs' := Local.compareSample hw hA hY hz
   let V₀:=iteratedDeriv p.2.val (K ∘ W) 0; have he:Local.logSample Y (0:Site c) s P.threshold (K ∘ increment 1) p = V₀:=by rw [score, Local.sample,if_pos hs]
   have hv'(U:Config G c→ℝ)(h: Chart n U 1) : ContDiffAt ℝ (p.2.val:WithTop ℕ∞) (U ∘ W) 0:=by
        let Z:=testLog Y n (0:Site c) (P.threshold • p.1)
        have hx:= ((increment_testLog Y n (0:Site c) (P.threshold • p.1)).fun_comp U)
        have hp : Z 0=0:=testLog_zero ..
        exact ContDiffAt.congr_of_eventuallyEq (ContDiffAt.comp 0 (hp.symm ▸ ((show ContDiffAt ℝ (↑n) (U ∘ increment 1) 0 from h).of_le (Nat.cast_le.mpr (Nat.le_of_lt_succ p.2.isLt))) : ContDiffAt ℝ (↑p.2.val) (U ∘ increment 1) (Z 0)) (f:=Z) ((testLog_diff ..).of_le le_top)) hx
   have hw(U:Config G c→ℝ)(h:Chart n U 1):ContDiffAt ℝ (p.2.val:WithTop ℕ∞) ((Complex.ofRealCLM ∘ U) ∘ W) 0:= Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hv' U h)
   have hp' : ‖V₀‖ ≤ ‖t‖*(b+b):=by
       unfold V₀ K cab; let R:= Complex.ofRealCLM; let l:= p.2.val
       have hl(U:Config G c→ℝ)(h:Chart n U 1): iteratedDeriv p.2.val ((Complex.ofRealCLM ∘ U) ∘ W) 0=Complex.ofReal (iteratedDeriv p.2.val (U ∘ W) 0):= DFunLike.congr_fun (R.iteratedFDeriv_comp_left (hv' U h) le_rfl) (fun _=>1)
       rw[show (t • (Complex.ofRealCLM ∘ F+Complex.I • (Complex.ofRealCLM ∘ H))) ∘ W=t • (((Complex.ofRealCLM ∘ F) ∘ W)+ Complex.I • ((Complex.ofRealCLM ∘ H) ∘ W)) from rfl]; have hH: ContDiffAt ℝ (p.2.val:WithTop ℕ∞) (Complex.I • ((Complex.ofRealCLM ∘ H) ∘ W)) 0:=(hw H hF).const_smul Complex.I
       rw [iteratedDeriv_const_smul (show ContDiffAt ℝ (p.2.val:WithTop ℕ∞) (((Complex.ofRealCLM ∘ F) ∘ W)+Complex.I • ((Complex.ofRealCLM ∘ H) ∘ W)) 0 from (hw F hf).add hH),iteratedDeriv_add (hw F hf) hH,iteratedDeriv_const_smul (hw H hF),hl F hf,hl H hF,norm_smul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); apply (norm_add_le ..).trans; rw[norm_smul, Complex.norm_real,Complex.norm_real,Complex.norm_I,one_mul]; exact add_le_add hO hJ
   rw [he] at hs'; exact le_trans (by simpa only[sub_add_cancel] using norm_add_le (Local.sample Y 0 s P.threshold (cab t u v) p-V₀) V₀) (add_le_add hs' hp')
end YM.PhysicalNext.Repeat.Quince
