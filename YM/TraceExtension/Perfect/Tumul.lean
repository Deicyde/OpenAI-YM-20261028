import YM.TraceExtension.Perfect.Void
import YM.TraceExtension.Perfect.Blunt

set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset Push.Uniform
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{p:Clip}{η A B σ:ℝ}{i j k:ℕ}
section
variable {f:Side}
lemma coil_be (g: Rays (Lines G f 1)→ℝ)(h:ContDiffAt ℝ ω g 0) (hg:Scatter Prod.fst η (k+1) g 0 A)(x:Lines G f 1) :
    Beacon Prod.fst η k (fun y=> fderiv ℝ g y (desk x)) x.1 0 A:=by
 intro j hj q; let v:=(Fin.snoc q x: Fin (j+1)→Lines G f 1)
 have ht:=hg (j+1) (by omega) v (Fin.last j)
 have he: entry g 0 v = entry (fun y=> fderiv ℝ g y (desk x)) 0 q:=by
    unfold entry; rw[iteratedFDeriv_succ_apply_right]; simp only [v,Fin.snoc_last];
    change _=iteratedFDeriv ℝ j ((ContinuousLinearMap.apply ℝ ℝ (desk x)) ∘ fderiv ℝ g) 0 _
    rw [(ContinuousLinearMap.apply ℝ ℝ (desk x)).iteratedFDeriv_comp_left (h.fderiv_right (m:=ω) (by simp)) le_top];
    simp; rw [show Fin.init (fun i:Fin (j+1)=>bolt (v i))=(fun i=>bolt (q i)) from funext fun i=>by simp [v,Fin.init],show bolt x=desk x by ext k; by_cases he:k=x<;>simp [bolt,desk,he]]
 unfold v spanSites at ht; simp only [← he]; convert ht using 1; simp [spanSites, Fin.sum_univ_castSucc]

lemma arc_degree {Z:Rays (Lines G f 1)→ℝ}(x:Site f)(h:Beacon Prod.fst η k Z x 0 A)(hp:0 ≤ A)(hη:0<η)(j:ℕ)(hj:j≤k): cost (fun v: Lines G f 1=> separation x v.1) (η/2) 0 0 (leaf Z 0 j) ≤ A*((townCost G)*countCost (η/2))^j:=by
 let g y:= Decay (η/2) x y
 let s:= fun i:Lines G f 1=> separation x i.1
 unfold cost; refine (sum_le_sum (g:=fun v: Fin j → Lines G f 1=> A*∏ i:Fin j, g (v i).1) ?_).trans ?_
 · intro u _; have ht: leaf Z 0 j u=entry Z 0 u:=by unfold leaf bank entry; congr 1; ext1 i; ext k; by_cases hh:k=u i<;>simp [desk,bolt,hh]
   rw [ht]; apply (mul_le_mul_of_nonneg_left (h j hj u) (spot_pos .. |>.le)).trans
   rw [mul_left_comm]; apply mul_le_mul_of_nonneg_left _ hp; rw [show (∏ l:Fin j,g (u l).1)=_ from (glaze_prod (n:=f) Prod.fst x u (η/2)).symm]; unfold spot shelter Push.Uniform.glaze;simp only[pow_zero,mul_one,one_mul,sub_zero,Nat.cast_nonneg,max_eq_right,← Real.exp_add]; apply Real.exp_monotone
   let b:=spanSites Prod.fst x u; have hu:limitN s u ≤ b:=by
      unfold limitN; apply Finset.sup_le; intro i _; exact Finset.single_le_sum (f:=fun i=>s (u i)) (fun _ _=> Nat.zero_le _) (mem_univ i)
   have ht:= mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ) |>.mpr hu) hη.le; unfold s b at *; linarith
 rw [← Finset.mul_sum]; apply mul_le_mul_of_nonneg_left _ hp; rw [← Fintype.prod_sum (fun i:Fin j=>fun v:Lines G f 1=>g v.1)]
 have hx:Multiplicity (Prod.fst:Lines G f 1→Site f) (townCost G):=by
   change Multiplicity (ι:=Site f×Loc G 1) _ _; intro x; let v:= (univ:Finset (Loc G 1)); let s:= univ.filter (fun y:Lines G f 1=>y.1=x)
   have he : Set.InjOn (fun i:Lines G f 1=>i.2) (s:Set (Lines G f 1)):=by
      intro i hi j hj hh; exact Prod.ext ((show i.1=x from (mem_filter.mp (show i∈s from hi)).2).trans (show j.1=x from (mem_filter.mp (show j∈s from hj)).2).symm) hh
   apply (card_le_card_of_injOn (fun p:Lines G f 1=>p.2) (t:=v) (fun _ _=>mem_univ _) he).trans; unfold v townCost; rw[Finset.card_univ]; exact Nat.le_add_right ..
 exact le_trans (Finset.prod_le_prod (fun _ _=> Finset.sum_nonneg fun _ _=>(Real.exp_pos _).le) (g:=fun _=> (townCost G:ℝ)*countCost (η/2)) (fun _ _=> hx.count _ (half_pos hη) _)) (le_of_eq (by simp))
end
variable {W:Type*}{n:W→Side}
lemma bore_calm (R:W→PathData G) (Λ:W→ℝ)(hσ:0<σ)(hr:∀ w,(R w).Bounds p σ B (Λ w))(x:∀ w,Lines G (n w) 1): Calm (fun w (v:Lines G (n w) 1)=> separation (x w).1 v.1) (fun w y=> fderiv ℝ (intended (m:=n w) p (R w)) y (desk (x w))) k:=by
 obtain ⟨a,A,s,h,hY⟩:= lone_spread p G σ B hσ (k+1)
 let C:ℝ:=townCost G*countCost (a/2); have h0:= mul_nonneg (show 0 ≤ (townCost G:ℝ) by positivity) (count_pos (half_pos s)).le; change 0 ≤ C at h0
 have hX w:= hY _ _ (hr w) (n w)
 refine ⟨fun w=>(((hX w).1.fderiv_right (by simp)).clm_apply contDiffAt_const),a/2,A*(1+C)^k,half_pos s,by positivity,fun w j hj=>?_⟩
 apply (arc_degree (x w).1 (coil_be _ (hX w).1 (hX w).2 (x w)) h s j hj).trans
 apply mul_le_mul_of_nonneg_left _ h; exact (pow_le_pow_left₀ h0 (show C ≤ 1+C by linarith) _).trans (pow_le_pow_right₀ (by linarith only[h0]) hj)
end YM.Trace.Perfect
