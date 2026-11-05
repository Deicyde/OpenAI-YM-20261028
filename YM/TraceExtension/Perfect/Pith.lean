import YM.TraceExtension.Perfect.Loom

set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Lattice Laurent RG Wilson Function Finset Filter
open scoped BigOperators Topology
namespace Sheaf
variable {A: Type*} [AddCommGroup A] [Module ℝ A]
def grip (P:Axis→Sheaf) := mix (mix (P 0) (P 1)) (mix (P 2) (P 3))
def sass (a:Axis)(P:Axis→Sheaf):=grip fun i=> if a=i then (mon 0) else P i
lemma skip_zero (f:Cover→A): take f (mon 0)=f:=funext (fun x=>by simp [take])
lemma grip_a (P:Axis→Sheaf)(a:Axis)(f:Cover→A): take f (grip P)=take (take f (sass a P)) (P a):=by
 fin_cases a<;> norm_num +decide only [grip,sass,take,↓reduceIte,add_zero] <;> simp only [if_true,if_false,take,add_zero]
 · rfl
 · rw [rope (P 0) (P 1)]; rfl
 · rw [rope (P 1) (P 2),rope (P 0) (P 2)]; rfl
 rw [rope (P 2) (P 3),rope (P 1) (P 3),rope (P 0) (P 3)]; rfl

lemma grip_cost (X:Axis→Sheaf)(u:ℕ)(C:ℝ)(h:0≤C)(hx:∀ i,(X i).radius ≤ u ∧ (X i).debt ≤ C ∧ (X i).gold=1): (grip X).radius≤4*u∧(grip X).debt ≤ C^4∧(grip X).gold=1 :=by
   have p:= hx 0; have v:=hx 1; have q:=hx 2; have s:=hx 3
   simp only [grip,mix,radius,debt,gold,p.2.2,v.2.2,q.2.2,s.2.2,one_mul,eq_self,and_true]
   refine ⟨by omega,?_⟩
   apply (mul_le_mul (mul_le_mul p.2.1 v.2.1 (debt_pos _) h) (mul_le_mul q.2.1 s.2.1 (debt_pos _) h) (mul_nonneg (debt_pos _) (debt_pos _)) (by positivity)).trans_eq
   ring
variable (L: Side)
abbrev v (a:Axis):Cover:= L.val • (step a:Cover)
def main := grip (boil L)
def flank (a:Axis):= sass a (boil L)
lemma fee_main: (Sheaf.main L).radius≤ 56*L.val ∧ (Sheaf.main L).debt ≤ 32^4 ∧ (Sheaf.main L).gold=1:=by
   have hx:= grip_cost (boil L) (14*L.val) 32 (by norm_num) (boil_price L); rw[← mul_assoc] at hx; exact hx
lemma fee_flank (a:Axis): (flank L a).radius ≤ 56*L.val ∧ (flank L a).debt ≤ 32^4 ∧ (flank L a).gold=1 :=by
   have hx:∀ i:Axis,let v:Sheaf:=if a=i then mon 0 else boil L i; v.radius ≤ 14*L.val ∧ v.debt≤32 ∧ v.gold=1:=by intro i; dsimp only; split_ifs; norm_num [radius,debt,gold,Laurent.size]; exact boil_price ..
   have hp:= grip_cost _ _ _ (by norm_num) hx; rw [← mul_assoc] at hp; exact hp
private lemma airy (f:Cover→A)(L:Side)(a:Axis): take f (Sheaf.main L)=take (take (take f (flank L a)) (nigh L a)) (ply L a):=by rw[Sheaf.main,grip_a _ a]; rw [flank,boil,take]
def port (a:Axis) := mix (ply L a) (mix (nigh L a) (flank L a))

def leafEdge (a:Axis):= mix (nigh L a) (flank L a)
def flux (a:Axis):=mix (band (step a)) (mix (ply L a) (flank L a))
lemma fee_flux (a:Axis): (flux L a).radius ≤ 69*L.val ∧ (flux L a).debt ≤ 32^5 ∧ (flux L a).gold=1:=by
   obtain ⟨p,v,t⟩:= band_fee (step a); obtain ⟨h,h',j⟩:= ply_level L a; obtain ⟨hp,hz,H⟩:=fee_flank L a
   rw [size_step_one] at v; refine ⟨by simp only [flux,radius]; have he:1≤L.val:=L.property; omega,?_,?_⟩
   · simp only [flux,debt,h,one_mul]; exact (mul_le_mul t hz (debt_pos _) (by norm_num)).trans_eq (by norm_num)
   simp only [flux,gold,p,h',H,mul_one]
lemma fee_leaf (a:Axis): (leafEdge L a).radius ≤ 69*L.val ∧ (leafEdge L a).debt ≤ 32^5:=by
   obtain ⟨hp,hz,H⟩:=fee_flank L a; obtain ⟨hb,h,t⟩:= nigh_fee L a; refine ⟨by simp only [leafEdge,radius]; omega,?_⟩; exact (mul_le_mul h hz (debt_pos _) (by norm_num)).trans_eq (by norm_num)
lemma main_leaf (a:Axis)(f:Cover→A): take (take f (Δ (step a))) (Sheaf.main L)=((L.val:ℝ))⁻¹ • take (take f (leafEdge L a)) (Δ (v L a)):=by rw [rope,airy f L a,ply_step]; congr 2
lemma flux_delta (a:Axis)(f:Cover→A): (L.val:ℝ) • take (take (take f (band (step a))) (Δ (step a))) (Sheaf.main L)=take (take (take f (flux L a)) (band (v L a))) (Δ (v L a)):=by
   have hz:(L.val:ℝ)≠0:=Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp L.property)
   rw [main_leaf, smul_smul,mul_inv_cancel₀ hz,one_smul]; congr 1
   rw [leafEdge,take,nigh,take,rope (flank L a),rope (ply L a) (band (step a)),flux,take,take]
lemma trail (a:Axis):∃ Y,Y.radius≤ 140*L.val ∧ Y.debt ≤ 1800*32^4 ∧ ∀ f:Cover→A,take f (flux L a)= take f (Sheaf.main L)+take (take f Y) (Δ (v L a)):=by
   let W:=duo (band (step a)) (scale (-1) (nigh L a))
   obtain ⟨p,v',t⟩:= band_fee (step a); rw [size_step_one] at v'
   obtain ⟨x,y,z⟩:= nigh_fee L a; have hl:1≤L.val:= L.property
   obtain ⟨hf,hp,h⟩:= fee_flank L a; let U:Cover:= L.val • step a; have hll:U = (L.val:ℤ) • step a:=by simp[U]
   have hu:Runs a W:=by
      refine ⟨?_,?_,?_⟩
      · simpa only [one_smul] using band_runs (i:=1) a
      · change Runs a (band U); rw [hll]; exact band_runs a
      change Runs a (disk (step a) _); simpa only [one_smul] using disk_runs (i:=1) a L.val
   obtain ⟨Y,hY,hE,H⟩:= draw (A:=A) _ a hu; have he :(W).radius≤ 13*L.val:=by simp only [W,radius]; omega
   have hb : W.gold=0:=by simp only [W,gold,p,z]; ring
   have hy : W.debt ≤ 64:= by simp only [W,debt,abs_neg,abs_one,one_mul]; linarith
   have hx:0 < (L.val:ℝ):= Nat.cast_pos.mpr L.property
   refine ⟨scale ((L.val:ℝ))⁻¹ (mix Y (flank L a)),by simp only [radius]; omega,?_,fun f=>?_⟩
   · simp only [debt,abs_inv,abs_of_pos hx]; have hb:= hE.trans (mul_le_mul (Nat.cast_le.mpr he) hy W.debt_pos (by positivity)); push_cast at hb; rw [← mul_assoc]
     apply (mul_le_mul (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hx.le)) hp (debt_pos _) (by positivity)).trans; apply le_of_le_of_eq (b:= (L.val:ℝ)⁻¹ * (13*L.val*1800/13) * 32^4) (by gcongr <;> nlinarith only[hx]); field_simp <;> ring
   let t':=take f (flank L a); have hv:= congr_arg (fun g=>take g (ply L a)) (H t'); rw [hb,zero_smul,sub_zero] at hv; dsimp only [W] at hv; rw [take,take,add_f,smul_f] at hv
   rw [rope (ply L a) (Δ (step a)),ply_step] at hv
   rw [flux,take,take,take,rope (band (step a)) (ply L a),airy f L a,smul_f,take]
   change take (take t' (band (step a))) _=take (take (take f _) _) _+ ((L.val:ℝ))⁻¹ • take (take t' Y) (Δ (L.val • step a))
   rw [hv]; simp only [t',neg_one_smul]; abel
end Sheaf
end YM.Trace.Perfect
