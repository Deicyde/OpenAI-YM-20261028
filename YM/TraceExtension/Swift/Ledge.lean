import YM.TraceExtension.Zn.Onus
import YM.Next.ROTATIONS.Nodes
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Swift
open Function Filter Set Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits Pills Loft Xo Zn
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {X Y:Type}[NormedAddCommGroup X][NormedSpace ℝ X] [NormedAddCommGroup Y][NormedSpace ℝ Y]
variable {a b C:ℝ}
open Outer.Nodes (loc coeff loc_pos sums)
def wage (m i:ℕ):= Polynomial.eval 0 (Outer.Nodes.coeff m i) / loc i
lemma wage_paid(m j:ℕ)(hj:j < m): ∑ i∈range m,wage m i*(loc i)^(j+1)= if j+1=1 then 1 else 0:=by
   rw [show ∑ i∈ range m,_= ∑ i∈range m,(Outer.Nodes.coeff m i).eval 0 * (loc i)^j from ?_,sums m j hj,zero_pow_eq]; congr 1 <;> simp
   apply sum_congr rfl fun i _=>?_ ; unfold wage; rw[pow_succ]; field_simp [(loc_pos i).ne']
def duel (m:ℕ)(h:ℝ) (f:ℝ→Y):=∑ i∈range m,(wage m i) • (f (loc i*h)-f 0)
def kettle (m:ℕ):= loc m
lemma roof (m i:ℕ)(h:i < m): 0 < loc i ∧ loc i ≤ kettle m:=by unfold kettle; refine ⟨loc_pos i,pow_le_pow_left₀ ?_ ?_ 2⟩; exact (Outer.Nodes.num_pos i).le; unfold Outer.Nodes.num; gcongr
private lemma frost(F:ℝ→Y)(m:ℕ)(hm:0 < m)(v:ℝ):
   let K(t:ℝ):=∑ i∈range (m+1),t^i • neap i F 0 1; duel m v K=v • deriv F 0:=by
   intro K; have hz : K 0 = neap 0 F 0 1:=by
       unfold K; rw [sum_eq_single 0]; simp; intro i _ hi; rw [zero_pow hi,zero_smul]; simp
   have hx(j:ℕ) : wage m j • (K (loc j*v)-K 0)=∑ i ∈ (range (m+1)).erase 0, (wage m j*loc j^i) • v^i • neap i F 0 1:=by
        rw [hz,show K (loc j*v)=_ from (show K (loc j*v)= ((loc j*v)^(0:ℕ)) • neap 0 F 0 1+∑ i∈(range (m+1)).erase 0,(loc j*v)^i • neap i F 0 1 from (Finset.add_sum_erase _ _ (show 0∈range (m+1) by simp)).symm),pow_zero,one_smul, add_sub_cancel_left,smul_sum]; simp only [mul_pow,mul_smul]
   unfold duel; simp_rw [hx]; rw [sum_comm]; simp_rw [← Finset.sum_smul]; rw [sum_eq_single 1]; rotate_left
   · intro i hi h; obtain ⟨i,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (ne_of_mem_erase hi); rw [wage_paid _ _ (by have hu:=mem_range.mp (mem_of_mem_erase hi); omega),if_neg h,zero_smul]
   · intro h; exfalso; exact h (mem_erase.mpr ⟨one_ne_zero,mem_range.mpr (by omega)⟩)
   rw [wage_paid m 0 hm,if_pos rfl,pow_one,one_smul, neap1]; rfl
def tome (m:ℕ):ℝ:=(∑ i∈range m, |wage m i| * (loc i)^(m+1)/(m.factorial:ℝ))
lemma tome0 (m):0 ≤ tome m:= by unfold tome; apply sum_nonneg; intro i hi; positivity [loc_pos i]
lemma toll (m:ℕ)(hm:0 < m)(h:ℝ)(hp:0<h)(F:ℝ→Y)(he:∀ t:ℝ,0 ≤ t → t ≤ kettle m*h→Allows (m+1) F t C):
    ‖duel m h F -h • deriv F 0‖ ≤ tome m * C * h^(m+1):=by
    rw [← frost F m hm h]; let K(t:ℝ):=∑ i∈range (m+1),t^i • neap i F 0 1; unfold duel;rw [← sum_sub_distrib]; apply (norm_sum_le ..).trans; unfold tome; simp_rw[Finset.sum_mul]; refine sum_le_sum fun i hi=>?_ ; rw [←smul_sub]
    have hf : F 0=K 0:=by
       unfold K; rw [sum_eq_single 0]; simp[neap0]; intro i _ hi; rw [zero_pow hi,zero_smul]; simp
    let v:=loc i; have hx:=roof m i (mem_range.mp hi); have hz:= Lamp.warm F (kettle m*h) (mul_pos (loc_pos m) hp) (v*h) ⟨mul_nonneg hx.1.le hp.le,mul_le_mul_of_nonneg_right hx.2 hp.le⟩ m (fun t ht=> he t ht.1 ht.2)
    change ‖wage m i • ((F (v*h)-F 0)-(K (v*h)-K 0))‖ ≤ _; nth_rw 1 [hf]; rw [sub_sub_sub_cancel_right,norm_smul, Real.norm_eq_abs]; exact (mul_le_mul_of_nonneg_left hz (abs_nonneg _)).trans_eq (by unfold v; rw[mul_pow]; ring)
end YM.Trace.Swift
