import YM.RG05Readout.Test.Levers

/-!
# The high test complement with contraction in the native cell norm

Output branches are calculated at their **actual displaced** address. Full
segment estimates, including all the derivatives in subsequent steps, hold
with this same order; no paying a loss in test differentiability per step.
Only used in the physical estimate, not a Laurent atom-measure estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Native
open Tensor Analysis Function Set Filter MeasureTheory Push.FiniteDetection.Kelvin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (d : ℕ)
def basicPrice (i:Letter d):= (write_cost i.1.val).choose*((depth i).factorial:ℝ)⁻¹
def pulseFee := 1+ ∑ i:Letter d,basicPrice d i
lemma bpos (i):0<basicPrice d i:=mul_pos ((write_cost (depth i)).choose_spec.1) (by positivity)
lemma feepos:0 < pulseFee d:= add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun i _=> (bpos d i).le)
lemma fees (i:Letter d){x:E4}(hx:x∈box){φ:Body}{c:ℝ}(hp:Cap (d+2) φ c) : ‖readJ i x φ‖ ≤ pulseFee d * c:=by
    apply (record_cost _ i.2 hx (le_trans (Nat.le_of_lt_succ i.1.isLt) (Nat.le_add_right ..)) hp).trans
    exact mul_le_mul_of_nonneg_right ((Finset.single_le_sum (fun i _=>(bpos d i).le) (Finset.mem_univ _)).trans (le_add_of_nonneg_left zero_le_one)) hp.nonneg

def cut (f:Body):Body:=∑ i:Letter d,(readJ i 0 f) • line i
lemma cut_val (f:Body): (cut d f).val= Work.G05.blockTaylor d f.val:=by
    let L(i:Fin (d+1)) := ∑ j:Beam i.val, consider (k:=i.val) j 0 f • guide i.val j
    have hL(i:Fin (d+1)): (L i).val=Tensor.diagonal (Tensor.coeff f.val i.val 0):=by
       let A:=records 0 i.val f
       rw [show L i= lines i.val A from ?_]
       · rfl
       nth_rw 1 [← Module.Basis.sum_repr (BoltBasis i.val) A]
       simp only [map_sum, map_smul]; rfl
    unfold cut; rw [Fintype.sum_sigma]; change (∑ i,L i).val=_
    rw [AddSubmonoidClass.coe_finsetSum]; simp_rw [hL]; exact Fin.sum_univ_eq_sum_range (fun i=> Tensor.diagonal (Tensor.coeff f.val i 0)) (d+1)
lemma preciseAt {i:ℕ}{f:Body} (hi:i≤d) : iteratedFDeriv ℝ i (cut d f).val 0=iteratedFDeriv ℝ i f.val 0:=by
    rw [cut_val]; exact Work.G05.blockTaylor_jets (body_smooth _ _|>.contDiffAt) i hi
lemma wholeCut {s:ℕ}(hd:d<s)(f:Body) : iteratedFDeriv ℝ s (cut d f).val=0:=by
   rw [cut_val,Work.G05.blockTaylor]; funext x
   rw [iteratedFDeriv_sum_apply]
   exact Finset.sum_eq_zero (fun i hi=> congr_fun (mono_vanish (d:=i) ⟨Tensor.coeff f.val i 0,Tensor.coeff_symm (body_smooth f i|>.contDiffAt)⟩ ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans_lt hd)) x)
   intro i _; exact (diag_smooth ..).contDiffAt
lemma segment_charge {φ:Body}{s:ℕ}(hs:d<s){c:ℝ}(hc:0≤c)(h:∀ i, d < i → i ≤ s→∀ x∈box, ‖iteratedFDeriv ℝ i φ.val x‖ ≤ c): Cap s (φ-cut d φ) c:=by
    have he(x:E4)(i:ℕ) : iteratedFDeriv ℝ i (φ-cut d φ).val x = iteratedFDeriv ℝ i φ.val x- iteratedFDeriv ℝ i (cut d φ).val x:= iteratedFDeriv_sub_apply ((body_smooth φ i).contDiffAt) ((body_smooth ..).contDiffAt)
    apply Cap.from_high hc hs (fun i hi=> by rw [he,preciseAt d hi,sub_self])
    intro i hi hz x hx; rw [he,wholeCut d hi, Pi.zero_apply,sub_zero]; exact h i hi hz x hx

-- An unextracted high-test functional. Covariant pulls on D.
def Priced (φ:PulseC)(c:ℝ):Prop:=∀ (f:Body)b, Cap (d+2) f b → ‖φ f‖ ≤ c * b
def Tail (φ:PulseC):Prop:=∀ x:Letter d,φ (line x)=0
protected lemma Priced.nonneg {φ:PulseC}{c:ℝ}(h:Priced d φ c):0≤c:=by
   obtain ⟨b,hb,h₀⟩:=Cap.cost (0:Body) (d+2); exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (h _ _ h₀)) hb
lemma residual (f:Body){φ:PulseC}(h:Tail d φ):φ f=φ (f-cut d f):=by
    simp only [cut,map_sub,map_sum,map_smul];simp_rw [h _,smul_zero,Finset.sum_const_zero,sub_zero]
lemma tail_aff (φ:PulseC){r:ℝ} (hr:0≤r)(hv:r≤1)(δ:E4)(ht:MapsTo (fun x=>δ+r • x) box box)(h:Tail d φ){C:ℝ}(hc: Priced d φ C):
    Tail d (φ.comp (pull δ r)) ∧ Priced d (φ.comp (pull δ r)) (C*r^(d+1)) :=by
    constructor
    · intro y
      let A:=pull δ r (line y); change φ A=0
      rw [residual d A h]; apply norm_le_zero_iff.mp
      apply le_trans (hc (A-cut d A) 0 ?_) (le_of_eq (mul_zero _)); apply segment_charge d (by omega) le_rfl; intro i hi _ x _
      have hB:depth y ≤ d:= Nat.le_of_lt_succ y.1.isLt
      unfold A; rw [pulled]; rw [show (line y).val=Tensor.diagonal (BoltBasis y.1.val y.2).val from rfl,mono_vanish (BoltBasis y.1.val y.2) (hB.trans_lt hi),Pi.zero_apply,smul_zero,norm_zero]
    intro f b hb
    let A:=pull δ r f; change ‖φ A‖≤ _
    rw [residual d A h, mul_assoc]; apply hc (A-cut d A) _; apply segment_charge d (by omega) (mul_nonneg (pow_nonneg hr _) hb.nonneg); intro i hi hz x hx; rw [show A=pull δ r f from rfl, pulled, norm_smul, Real.norm_of_nonneg (pow_nonneg hr _)]
    exact mul_le_mul (pow_le_pow_of_le_one hr hv hi) (hb i hz _ (ht hx)) (norm_nonneg _) (pow_nonneg hr _)
-- low atom expansion into higher-basis tests at coarse, plus single high atom
noncomputable def recollect (φ:PulseC):PulseC:= φ-∑ i: Letter d,φ (line i) • readJ i 0
lemma expands (φ:PulseC)(f:Body): φ f=(∑ i: Letter d,φ (line i) * readJ i 0 f)+recollect d φ f:=by
   unfold recollect; simp only [LinearMap.sub_apply,LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]; abel
lemma recall (φ:PulseC)(f:Body):recollect d φ f=φ (f-cut d f):=by
    unfold recollect cut; simp only [LinearMap.sub_apply,LinearMap.sum_apply,LinearMap.smul_apply,map_sub,map_sum,map_smul,smul_eq_mul]
    congr 1; apply Finset.sum_congr rfl; intro i _; rw [mul_comm]
lemma tail_rec (φ:PulseC):Tail d (recollect d φ):=by
    intro i; unfold recollect
    simp only [LinearMap.sub_apply,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]; simp_rw [headC]; simp
lemma recall_price {c:ℝ}{φ:PulseC}(h:Priced d φ c): Priced d (recollect d φ) c:= by
    intro f b hb; rw [recall]; exact h _ _ (segment_charge d (by omega) hb.nonneg (fun i _ hi=> hb i hi))
lemma recall_read {x:E4}(hx:x∈box) (i:Letter d): Priced d (recollect d (readJ i x)) (pulseFee d):= recall_price _ (fun _ _ hi=> fees d i hx hi)

end YM.RG05Readout.Native
