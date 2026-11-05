import YM.TraceExtension.Quince.Scale
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Quince
open Function Filter Set Lattice Wilson RG Pressure Precision Labels Source Source.Drops
open Push.Local (Probe)
open Push Planned.PrimaryIntegral295 PPX Flutes Place Bazaars Exterior Streets Postcards WardBin.Lies Cabins Bid
open Next Next.Foundations JointLoad JointLoad.Heir Bloch Carrier Next.Free Laurent Cub Finset
open MultiNext.SignedSource
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge} {n c f:Side}
variable {k p d r j u:ℕ}{B:BudgetPoint}{S:StepData c f}{T:Tube G S}
section square
variable {a N b m k:ℕ}{u t π σ M C' w ε R K:ℝ} {Q:Probe G d}(H:Hol G){X:Support f}{Y:Support c}{O:Config G f→ℝ}(hp:B.Regular X O)(hf:B.supBounds 0 X O w)(G':Rights G N)
lemma costs_scaled (v:ℝ)(h:0≤v)(x: Directions G f)(hx:∀ i:Bond f,Mom.needed X i→ ‖x i‖ ≤ v):Lyre.Sized v (Mom.screen X (B.threshold • x)) B 0:=by
    refine ⟨h,fun i=>?_⟩; rw[Mom.screen_at]; split; · next hi=> rw [Pi.smul_apply,norm_smul, Real.norm_of_nonneg B.threshold_pos.le,mul_comm]; exact mul_le_mul (hx _ hi) (le_mul_of_one_le_right B.threshold_pos.le (spine_one B.power _ _)) B.threshold_pos.le h
    rw[norm_zero]; exact mul_nonneg h (Lyre.width_pos B _ _|>.le)
variable {x y:Fin a→ Directions G f}(hV:a≤N)(hB:N≤ B.order)(hK:1 ≤ K)(hε:0≤ε)(he:ε≤K)
    (hq:iteratedFDeriv ℝ a (O ∘ increment 1) 0 (fun i=> B.threshold • y i)=0)
    (h₁:∀ i e, Mom.needed X e→ ‖y i e‖ ≤ K)
    (hδ:∀ i e,Mom.needed X e→‖x i e-y i e‖ ≤ ε)
include hp hf hV hB hK hε he hq h₁ hδ
lemma weigh_inputs : let W:= O∘ increment 1
    ‖iteratedFDeriv ℝ a W 0 (fun i=> B.threshold • x i)‖ ≤ (2:ℝ)^a*(ε*K^a*G'.fee*w):=by
   intro W; let R:=iteratedFDeriv ℝ a W 0; let A(i):= Mom.screen X (B.threshold • y i); let U(i):= Mom.screen X (B.threshold • x i)
   have hm(u:Fin a→Directions G f): R u=R (fun i=>Mom.screen X (u i)):=by
       have hs:ContDiffAt ℝ (a:ℕ∞ω) W 0:= (hp.smooth 1 (one_healthy X _ B.threshold_pos.le)).of_le (Nat.cast_le.mpr (hV.trans hB))
       unfold R; nth_rw 1[show W=W ∘ Mom.screen X from funext fun v=> hp.sites _ _ (fun i hi hh=>by
          change G.lieExp _*_= G.lieExp (Mom.screen X v i)*_; rw [Mom.screen_at,if_pos (show Mom.needed X i from ⟨hi,hh⟩)])]; rw [jets_linear (Mom.screen X (G:=G)) hs]; rfl
   rw [hm _] at hq
   change ‖R _‖ ≤ _; rw [hm (fun i=>B.threshold • x i)]; change ‖R U‖ ≤ _
   let W(s:Finset (Fin a)):= R (s.piecewise (U-A) A); have hu : R U=∑ s:Finset (Fin a),W s:=by rw[← R.map_add_univ (U-A) A]; simp
   have hw(s:Finset (Fin a)): ‖W s‖ ≤ ε*K^a*G'.fee*w:=by
       have hp':=G'.large; have ht:= hf.1; by_cases hs:s.Nonempty
       · obtain ⟨i,hi⟩:=hs; let fg(j):= if j=i then ε else K
         have hh(j): Lyre.Sized (fg j) (s.piecewise (U-A) A j) B 0:=by
             have hh(a:Fin a): Lyre.Sized ε ((U-A) a) B 0:=by rw[show (U-A) a=Mom.screen X (B.threshold • (x a-y a)) from by rw[smul_sub,map_sub];rfl]; exact costs_scaled ε hε _ (hδ a)
             unfold fg Finset.piecewise; by_cases hv:j=i
             · subst j; simp only [hi,if_true]; exact hh i
             rw [if_neg hv]; split; exact Cub.higher (hh j) he; exact costs_scaled K (zero_le_one.trans hK) _ (h₁ j)
         apply (G'.born (1:Config G f) _ fg hV (hV.trans hB) hp hf (one_healthy _ _ B.threshold_pos.le) hh).trans; unfold fg; rw [← Finset.mul_prod_erase _ (fun j=>ite _ _ _) (Finset.mem_univ i)]
         rw [if_pos rfl,prod_congr rfl (g:=fun _=>K) (fun j hj=>by simp[Finset.ne_of_mem_erase hj]),Finset.prod_const]; simp only[Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,Fintype.card_fin]; gcongr; omega
       rw[Finset.not_nonempty_iff_eq_empty.mp hs]; unfold W; rw [Finset.piecewise_empty, hq,norm_zero]; positivity
   rw [hu]; apply (norm_sum_le ..).trans ((sum_le_sum (fun i _=>hw i)).trans (le_of_eq ?_)); simp
end square
end YM.PhysicalNext.Repeat.Quince
