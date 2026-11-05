import YM.RG08.Trill.Trell
/-!
# Product hol Taylor allocation engine. Normalization all Staples. Charges elsewhere.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Fete
open Planned.PrimaryIntegral295 Parts WardBin Work.G05 Finset Function
open scoped Classical ContDiff Topology BigOperators
variable {E F J:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
 [NormedAddCommGroup J][NormedSpace ℝ J]{p n:ℕ}
def allocation (p n:ℕ):=Fin n→Fin (p+1)
-- abbrev
abbrev rent {p n:ℕ}(x:Fin n→Fin (p+1)):=∑ i,(x i).val

local notation "flic"=>Tensor.diagonal
lemma atop {g:E→F}{f:F→J}(hg:ContDiffAt ℝ p g 0)(hf:ContDiffAt ℝ p f 0)(hz:g 0=0)(X:E):
 flic (Tensor.coeff (f ∘ g) p 0) X =
  ∑ n∈range (p+1),∑ i:Fin n→Fin (p+1) with rent i=p, Tensor.coeff f n 0 (fun j=>flic (Tensor.coeff g (i j).val 0) X):=by
 let A:=blockTaylor p f;let B:=blockTaylor p g
 have hB:B 0=0:=(blockTaylor_zero p g).trans hz
 have h:= jets_comp hg ((blockTaylor_contDiff p g p).contDiffAt) (hz.symm ▸ hf:ContDiffAt ℝ p f (g 0)) ((blockTaylor_contDiff p f p).contDiffAt) (hz.trans hB.symm) (fun k hk=> (blockTaylor_jets hg k hk).symm) (fun k hk=> by rw [blockTaylor_zero,hz,blockTaylor_jets hf k hk]) p le_rfl
 rw [show Tensor.coeff (f ∘ g) p 0=Tensor.coeff (A ∘ B) p 0 from congrArg (fun v=> (p.factorial:ℝ)⁻¹ • v) h,← leading_tensor X (A ∘ B) ((blockTaylor_contDiff p f p).comp (blockTaylor_contDiff p g p)).contDiffAt]
 let u(i:Fin (p+1)):=flic (Tensor.coeff g i.val 0) X
 have he(s:ℝ):B (s • X)=∑ i:Fin (p+1),s^i.val • u i:=by unfold B blockTaylor;rw [Finset.sum_apply,←Fin.sum_univ_eq_sum_range]; simp_rw [Tensor.homogeneous];rfl
 let v(n:ℕ)(i:Fin n→Fin (p+1)):=Tensor.coeff f n 0 (u ∘ i)
 let w(n:ℕ)(i:Fin n→Fin (p+1))(s:ℝ):=s^(rent i) • v n i
 have hv(s:ℝ):(A ∘ B) (s • X) =∑ n∈range (p+1),∑ i:Fin n→Fin (p+1), w n i s:=by
   unfold A blockTaylor;rw [Function.comp_apply,Finset.sum_apply,he];apply sum_congr rfl;intro n _
   unfold Tensor.diagonal;rw [(Tensor.coeff f n 0).map_sum (fun _ i=>s^i.val • u i)];apply sum_congr rfl;intro i _;rw [(Tensor.coeff f n 0).map_smul_univ,prod_pow_eq_pow_sum];rfl
 have hp(n i):ContDiffAt ℝ p (w n i) 0:=(monoSmooth ..).contDiffAt
 rw [funext hv,lead_sum (n:=p) _ _ (fun j _=> ContDiffAt.sum (fun i _=> hp j i))];apply sum_congr rfl;intro n _
 rw [lead_sum (n:=p) _ _ (fun i _=>hp n i),sum_filter];apply sum_congr rfl;intro i _; unfold w;rw [lead_monomial]; rcases eq_or_ne p (rent i) with h|h
 · rw [if_pos h,if_pos h.symm]; rfl
 rw [if_neg h,if_neg (Ne.symm h)]

end YM.RG08.Fete
