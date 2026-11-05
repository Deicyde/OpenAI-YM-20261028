import YM.TraceExtension.Fen.Eject
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Fen
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side} (R:Rep G n){I:Type} {k:ℕ}{σ a C D:ℝ}
variable {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X] {Y:Gal G n}{F:Peat G n}
lemma soft_mul {f g:X→ℝ}(hf:Allows k f 0 C)(hg:Allows (k+1) g 0 D)(hp:g 0=0) : Allows (k+1) (fun x=> f x*g x) 0 (2^(k+1)*C*D):=by
    let L:=ContinuousLinearMap.mul ℝ ℝ
    have hL:‖L‖≤1:=ContinuousLinearMap.opNorm_mul_le ℝ ℝ
    refine ⟨hf.analytic.mul hg.analytic,fun i hi=> ?_ ⟩
    by_cases h':i < k+1
    · have ht:= (hf.bilinear L (hg.order (k:=k) (by omega)) hL).norm_le i (by omega); simp only[mul_one] at ht
      exact le_trans ht (by have hp:= hf.nonneg; have hv:=hg.nonneg; gcongr <;> norm_num)
    have ho:i=k+1:=by omega
    subst i
    obtain ⟨u,hu,hu',H⟩:=open_patch hf.analytic; obtain ⟨v,hv,hv',Hp⟩:=open_patch hg.analytic
    let S:= u∩v; have ht: (0:X)∈S:=⟨hu,hv⟩
    have hs:IsOpen S:=hu'.inter hv'
    have hx:= L.norm_iteratedFDerivWithin_le_of_bilinear (H.mono (show S⊆ u from Set.inter_subset_left)) (Hp.mono (show S⊆ v from Set.inter_subset_right)) hs.uniqueDiffOn ht (n:=k+1) (by simp)
    simp_rw [iteratedFDerivWithin_of_isOpen _ hs ht] at hx
    apply le_trans hx; have h1:=hf.nonneg; have h2:=hg.nonneg
    calc
     _ ≤ 1 * ∑ i∈ range (k+1+1), ((k+1).choose i:ℝ)*C*D:=by
       refine mul_le_mul hL (Finset.sum_le_sum (fun i hi=>?_)) (Finset.sum_nonneg fun i _=> mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (norm_nonneg _)) zero_le_one; have he:=mem_range.mp hi; by_cases hz: i=k+1
       · subst i; rw [tsub_self,norm_iteratedFDeriv_zero,hp,norm_zero,mul_zero]; positivity
       gcongr
       · exact hf.norm_le _ (by omega)
       exact hg.norm_le _ (by omega)
     _ = _:=by rw [one_mul,← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum,Nat.sum_range_choose,Nat.cast_pow,Nat.cast_ofNat]
def cumulus (G:Gauge)(a:ℝ):ℝ:= Fintype.card (Loc G 1)* countCost a
def gable (G:Gauge)(a:ℝ)(k:ℕ):ℝ:=(1+cumulus G a)^k
lemma cum_n (ha:0<a):0 ≤ cumulus G a:=mul_nonneg (Nat.cast_nonneg _) (count_pos ha).le
lemma para (o:Site n) {F:Link G n→ ℝ}(h:Pet Prod.fst o F a C k)(ha:0<a)(hc:0≤C): Allows k F 0 (C*gable G a k):=by
    have hz:1≤1+cumulus G a:=le_add_of_nonneg_right (cum_n ha)
    refine ⟨h.1,fun i hi=> ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg hc (pow_nonneg (by linarith only[hz]) _)) (fun v=> ?_)⟩; refine le_trans ((congr_arg (fun t:ℝ=> ‖t‖) (show iteratedFDeriv ℝ i F 0 v=∑ p:Fin i→Lines G n 1,(∏ j,v j (p j)) • bank (iteratedFDeriv ℝ i F 0) p from many (.atomic i) (iteratedFDeriv ℝ i F 0) v)).le) ?_; refine le_trans (norm_sum_le ..) ?_
    let f(p:Fin i→ Lines G n 1):= Real.exp (-a* spanSites Prod.fst o p)
    have ht: ∑ i,f i ≤ gable G a k:=by
       have h (p:Fin i→ Lines G n 1): f p= ∏ j,Decay a o (p j).1:=by simp_rw [f, Decay, spanSites, Nat.cast_sum, Finset.mul_sum, Real.exp_sum]
       simp_rw [h]
       rw [← Fintype.prod_sum (f:=fun (_ : Fin i) p=>Decay a o (p:Lines G n 1).1)]
       have hp:= Multiplicity.count (Prod.fst:Lines G n 1 → Site n) (pay_gate G n) ha o
       apply le_trans ?_ (pow_le_pow_right₀ hz hi)
       simp only [Finset.prod_const, Finset.card_univ,Fintype.card_fin]
       exact pow_le_pow_left₀ (sum_nonneg fun i _=>(Real.exp_pos _).le) (le_trans hp (le_add_of_nonneg_left zero_le_one)) _
    let K:=∏ i, ‖v i‖; have hK:0≤K:=prod_nonneg fun _ _=> norm_nonneg _
    apply le_trans (b:= C*(∑ i,f i)*K) _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht hc) hK); rw[mul_sum,Finset.sum_mul]; refine sum_le_sum fun p _=> ?_; rw [norm_smul,norm_prod, mul_comm _ K]
    have hv:‖bank (iteratedFDeriv ℝ i F 0) p‖≤ C*f p:=by
        have he : bank (iteratedFDeriv ℝ i F 0) p=entry F 0 p:=by unfold entry; apply congr_arg (iteratedFDeriv ℝ i F 0); ext a b; simp [desk,Pi.single_apply,bolt]
        rw [he]; exact h.2 i hi p
    exact mul_le_mul (prod_le_prod (fun i _=>norm_nonneg _) (fun i _=> norm_le_pi_norm (v i) (p i))) hv (norm_nonneg _) hK
-- Rill charge
lemma hail (S:Peat G n)(U:Config G n)(Y:Gal G n): rill S Y U= ∑ i:Lines G n 1,Y U i * outD S i U:=by
    let L:= fderiv ℝ (fun v=> S (input G n v*U)) 0; change L _= ∑ i,_*L _
    calc
        _ = L (∑ i: Lines G n 1,Y U i • bolt i):=by congr 1; ext1 i; simp [bolt,Finset.sum_apply,Pi.single_apply]
        _ = _:=by simp[map_sum]
lemma ypro {o:Site n}(hY:Y∈rains G n)(hp:Estate o (bottom Y) a (fun _=>C))(ha:0<a)(hc:0≤C):∀ i:Lines G n 1, Allows 3 (fun z=>Y (input G n z) i) 0 (C*Decay (a/5) o i.1*gable G (a/5) 3):=by
    intro i; exact para o (pea_rain hY hp hc ha.le i) (by positivity) (mul_nonneg hc (Real.exp_pos _).le)
def vocation (G:Gauge)(a C D:ℝ):= (cumulus G (a/5))*(2^(4:ℕ)* C*gable G (a/5) 3 *D)
lemma receives {o:Site n}(hY:Y∈rains G n)(hp:Estate o (bottom Y) a (fun _=>C))(ha:0<a)(hc:0≤C)(hd:0≤ D)(h:∀ i,outD F i 1=0∧Allows 4 (outD F i ∘ input G n) 0 D):
   Allows 4 (rill F Y ∘ input G n) 0 (vocation G a C D):=by
    let f(i:Lines G n 1)(z:Link G n):= outD F i (input G n z)
    have ht(i:Lines G n 1): f i 0=0:=by rw [show f i 0=outD F i _ from rfl,input_zero]; exact (h i).1
    rw [show rill F Y ∘ input G n=(fun x=>∑ i:Lines G n 1,Y (input G n x) i*f i x) from funext (fun i=> hail ..)]
    apply (Allows.mono (allows_sum (f:=fun i x=> Y (input G n x) i*f i x) (fun i _=> soft_mul (ypro hY hp ha hc i) (g:=f i) ((h i).2) (ht i))))
    let D':=2^(4:ℕ)*C*gable G (a/5) 3*D
    have hz :0≤D':=by unfold D' gable; have hx:=cum_n (G:=G) (show 0<a/5 by positivity); positivity
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (Multiplicity.count _ (pay_gate G n (n:=1)) (show 0<a/5 by positivity) o) hz); rw[Finset.sum_mul]; refine le_of_eq (sum_congr rfl (fun i _=>?_)); ring
end YM.Trace.Fen
