import YM.RG05Readout.Test.Native
/-!
 
# Coordinates on center test jets

Symmetric tensor basis (factorials displayed, thus change of basis if using
coordinate monomial/partial-derivative convention in consumers). For support
bounds keep address in D around physical root throughout.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Native
open Tensor Analysis Function Set Filter MeasureTheory Push.FiniteDetection.Kelvin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
abbrev Orb (d:ℕ): Submodule ℂ (Tensor.T E4 ℂ d):={
   carrier:={f|Sym f}
   zero_mem' := fun _ _ => rfl
   add_mem' := fun {_ _} ha hb x y => congr_arg₂ (·+·) (ha x y) (hb x y)
   smul_mem':= fun p _ ha x y=> congr_arg (p • ·) (ha x y) }
instance body_finite (d:ℕ):FiniteDimensional ℂ (Orb d):=by
   haveI : FiniteDimensional ℂ (Tensor.T E4 ℂ d) := Module.Finite.of_restrictScalars_finite ℝ _ _
   infer_instance
abbrev Beam (i:ℕ):=Fin (Module.finrank ℂ (Orb i))
abbrev BoltBasis (i:ℕ): Module.Basis (Beam i) ℂ (Orb i):= Module.finBasis ℂ _
def records (x:E4)(d:ℕ) : Body →ₗ[ℂ] Orb d where
   toFun f:= ⟨Tensor.coeff f.val d x,Tensor.coeff_symm (body_smooth f d).contDiffAt⟩
   map_add' a b:=Subtype.ext (coeff_add (body_smooth a d|>.contDiffAt) (body_smooth b d|>.contDiffAt))
   map_smul' a b:=Subtype.ext (show Tensor.coeff (a • b.val) d x=a • Tensor.coeff b.val d x by unfold coeff; rw [iteratedFDeriv_const_smul_apply (body_smooth b d|>.contDiffAt),smul_comm])
-- dual read. analytic kernels would need to convert conventions in any c-diagnosis.
def writeC (j:ℕ): ↥(Orb j)→L[ℂ](Beam j→ℂ):= (Module.Basis.equivFun (BoltBasis j)).toLinearMap.toContinuousLinearMap
def consider {k:ℕ}(i:Beam k) (x:E4): PulseC:= LinearMap.proj (R:=ℂ) (φ:=fun _:Beam k=>ℂ) i ∘ₗ (writeC k).toLinearMap ∘ₗ records x k
lemma rate_consider {k:ℕ}(i:Beam k) (δ:E4)(x:E4) (r:ℝ)(f:Body): consider (k:=k) i x (pull δ r f)=(↑(r^k):ℂ) • consider (k:=k) i (δ+r • x) f:=by
    let w:= (↑(r^k):ℂ)
    have hC : records x k (pull δ r f)=w • records (δ+r • x) k f:= by
       apply Subtype.ext; change Tensor.coeff _ k x = w • Tensor.coeff _ k (δ+r • x); unfold coeff; rw [pulled,smul_comm]; ext1 v; simp [smul_eq_mul,w,Complex.real_smul]
    rw [consider]; change writeC k (records x k (pull δ r f)) i= w • writeC k (records _ k f) i
    rw [hC,map_smul]; rfl
lemma write_cost (d:ℕ):∃ c>0,∀ x:Orb d, ‖writeC d x‖≤ c*‖x‖:= by
   haveI:=FiniteDimensional.proper ℂ (Orb d)
   obtain ⟨c,hc⟩:= (isCompact_closedBall (0:Orb d) 1).exists_bound_of_continuousOn ((writeC d).continuous.continuousOn)
   refine ⟨max 1 c,lt_max_of_lt_left zero_lt_one, fun x=> ?_⟩
   by_cases h:x=0
   · simp [h]
   let z:= ((‖x‖:ℝ):ℂ)
   have hi: 0 < ‖x‖:=norm_pos_iff.mpr h
   have hz: ‖z‖=‖x‖:= by simp [z]
   have hk:‖z⁻¹ • x‖=1:= by change ‖z⁻¹ • x.val‖=_; rw [norm_smul,norm_inv,hz]; exact inv_mul_cancel₀ hi.ne'
   have ht := hc (z⁻¹ • x) (by rw [mem_closedBall_zero_iff]; exact hk.le)
   rw [map_smul,norm_smul,norm_inv,hz] at ht
   rw [mul_comm (‖x‖)⁻¹, ← div_eq_mul_inv] at ht
   exact ((div_le_iff₀ hi).mp ht).trans (mul_le_mul_of_nonneg_right (le_max_right ..) hi.le)
lemma record_cost (d:ℕ) (i:Beam d){s:ℕ} {x:E4}(hx:x∈box)(h:d≤s){f:Body}{C:ℝ}(hv:Cap s f C) :
    
    ‖consider (k:=d) i x f‖≤((write_cost d).choose*(d.factorial:ℝ)⁻¹) * C:=by
   let r:=records x d f
   have ht: ‖r‖ ≤ (d.factorial:ℝ)⁻¹*C:= by
     change ‖Tensor.coeff f.val d x‖ ≤ _; rw [coeff,norm_smul,Real.norm_of_nonneg (by positivity)]
     exact mul_le_mul_of_nonneg_left (hv _ h x hx) (by positivity)
   exact (norm_le_pi_norm (writeC d r) i).trans ((write_cost d|>.choose_spec.2 r).trans ((mul_le_mul_of_nonneg_left ht ((write_cost d).choose_spec.1.le)).trans_eq (mul_assoc ..).symm))
-- monomials from finite basis
noncomputable def lines (d : ℕ) : ↥(Orb d) →ₗ[ℂ] Body where
  toFun p:= ⟨Tensor.diagonal p.val, diag_smooth p.val ∞⟩
  map_add' _ _:=rfl
  map_smul' _ _:=rfl
def guide (d:ℕ)(i:Beam d):= lines d (BoltBasis d i)
lemma look_self (d:ℕ)(i j:Beam d)(x:E4) : consider (k:=d) i x (guide d j)=(if i=j then 1 else 0):=by
    let S:=BoltBasis d j
    have he :=diag_response S.val S.property x
    have hp: records x d (guide d j)=S:=Subtype.ext he
    unfold consider; change writeC d _ i= _; rw [hp]
    change (BoltBasis d).repr S i= _; rw [Module.Basis.repr_self]; simp [Finsupp.single_apply,eq_comm]
lemma mono_vanish {d s:ℕ}(Y:Orb d)(hd:d<s):iteratedFDeriv ℝ s (Tensor.diagonal (Y.val))=0:=by
    obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le hd
    clear hd; induction k with
    | zero => exact funext (diag_above Y.val Y.property)
    | succ k ih=> rw [show d+1+(k+1)=d+1+k+1 by omega,iteratedFDeriv_succ_eq_comp_left,ih]; ext; simp -- hp parameter issues
lemma below (d:ℕ)(i:Beam d) {s:ℕ}(j:Beam s) (hd:d<s)(x:E4) : consider (k:=s) j x (guide d i)=0:=by
    let Y:=BoltBasis d i
    have hp: records x s (guide d i)=0:= by apply Subtype.ext; change Tensor.coeff (Tensor.diagonal Y.val) s x=0; rw [coeff,mono_vanish Y hd,Pi.zero_apply, smul_zero]
    unfold consider; change writeC s _ j=_; rw [hp,map_zero]; rfl
lemma above (d:ℕ)(i:Beam d) {s:ℕ}(j:Beam s) (hd:s<d) : consider (k:=s) j 0 (guide d i)=0:=by
    let Y:=BoltBasis d i
    have hp: records 0 s (guide d i)=0:=by
       apply Subtype.ext; change Tensor.coeff (Tensor.diagonal Y.val) s 0=0
       have hw:=lower_term (s:=fun _=>1) (x:=0) (g:=id) Y.val Y.property contDiffAt_const contDiffAt_id rfl hd
       rw [show dressed Y.val (fun _=>1) id= Tensor.diagonal Y.val from funext (fun x=> by simp [Push.FiniteDetection.Kelvin.dressed])] at hw; exact hw
    unfold consider; change writeC s _ j=_; rw [hp,map_zero]; rfl

abbrev Letter (d:ℕ):= Σ (i:Fin (d+1)),Beam i.val
abbrev depth {d:ℕ}(z:Letter d):ℕ:= z.1.val
def readJ {d:ℕ}(z:Letter d) (x:E4): PulseC:= consider (k:=z.1.val) z.2 x
def line {d:ℕ}(z:Letter d):Body:= guide _ z.2
lemma headC {d:ℕ}(i j:Letter d): readJ i 0 (line j)= if i=j then 1 else 0:=by
    by_cases h : i.1=j.1
    · rcases i with ⟨i,a⟩; rcases j with ⟨j,b⟩
      change i=j at h; subst j
      change consider (k:=i.val) a 0 (guide i.val b)=_; rw [look_self]; split_ifs with hr hv hv; all_goals first | rfl | simp_all
    have hn:i≠j:=fun hh=>h (hh ▸ rfl)
    rw [if_neg hn]; cases lt_or_gt_of_ne h
    · next hz => exact above _ j.2 i.2 hz
    next hz => exact below _ j.2 i.2 hz 0
lemma sliceC {d:ℕ}(i j:Letter d)(x:E4)(h:depth j ≤ depth i):readJ i x (line j)=if i=j then 1 else 0:=by
    rw [← headC]
    by_cases he:j.1=i.1
    · rcases i with ⟨i,a⟩; rcases j with ⟨j,b⟩; change j=i at he; subst j; exact Eq.trans (look_self i a b x) (look_self ..).symm
    have hp:depth j<depth i:= Nat.lt_of_le_of_ne h (fun hg=>he (Fin.ext hg)); exact (below _ j.2 i.2 hp x).trans (below _ j.2 i.2 hp 0).symm
end YM.RG05Readout.Native
