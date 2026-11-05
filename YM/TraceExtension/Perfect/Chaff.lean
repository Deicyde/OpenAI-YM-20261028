import YM.TraceExtension.Perfect.Labor
import YM.AnalyticNext.QUARTIC_MATCH.Hessian.Grade
import YM.AnalyticNext.QUARTIC_MATCH.Hessian.Stripe

/-! # Lipschitz pivot by two parallel windows. -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Matrix Lattice Precision Laurent Stationary Bloch Next.Free Exterior Finset RG
open YM.AnalyticNext.QuarticMatch.Hessian
open scoped BigOperators Topology ContDiff Classical
variable {c f:Side} (S : StepData c f)
set_option quotPrecheck false
local notation "v"=> S.patch.Small
local notation "L"=> S.ratio.count
lemma across_w (t : Site S.ratio.count) (j:Axis)(h : 2*(lift t j+1) ≤ S.ratio.count.val): lift (t+ step j)=lift t+step j:=by
 ext i; by_cases hi:i=j
 · subst i; rw [grow_lit _ _ h]; simp
 rw [glower_step _ _ _ _ (Ne.symm hi)]; simp [hi]
private def leak (t:Site S.ratio.count)(j:Axis):ℝ:=if S.ratio.count.val<2*(lift t j+1) then 1 else 0
private lemma leaks (i:Axis) : ∑ t:Site S.ratio.count, leak S t i ≤ (S.ratio.count.val:ℝ)^3:=by
 have hL:0<(L).val:= (L).property
 have h (t:Site L): ∑ p : Per L, leak S (Function.update t i p) i ≤1:=by
    let U p:=Function.update t i p
    have hh(a b: Per L)(h:(L).val<2*(lift (U a) i+1))(hk:(L).val<2*(lift (U b) i+1)): a=b:=by
       have hg: lift (U a) i=lift (U b) i:=by have ha:=lift_centers (U a) i; have hb:=lift_centers (U b) i; omega
       have ha (x:Per L): ((lift (U x) i:ℤ):Per L)=x:=by unfold lift; simp [U,ZMod.coe_valMinAbs]
       exact (ha a).symm.trans ((congr_arg (fun x:ℤ=>(x:Per L)) hg).trans (ha b))
    by_cases H:∃ p,(L).val<2*(lift (U p) i+1)
    · obtain ⟨p,hp⟩:=H
      rw [Finset.sum_eq_single p]; rotate_left
      · intro b _ he; unfold leak; exact if_neg (fun hx=> he (hh _ _ hx hp))
      · simp
      rw [leak, if_pos hp]
    push Not at H
    rw [Finset.sum_eq_zero (fun j _=>?_)]
    · norm_num
    unfold leak; exact if_neg (not_lt.mpr (H _))
 have hu (t: Site L): ∑ p:Per L, leak S (t+Pi.single i p) i ≤ 1:=by
     change _ ≤ _ ; have He p:t+Pi.single i p= Function.update t i (p+t i):=by
          ext j; by_cases H:j=i <;> simp [Pi.single_apply, H, Function.update, add_comm]
     simp_rw [He]; rw [show (∑ p:Per L, leak S (Function.update t i (p+t i)) i)=∑ p:Per L,leak S (Function.update t i p) i from Equiv.sum_comp (Equiv.addRight (t i)) (fun p=> leak S (update t i p) i)]; exact h t
 have hh(p:Per L): ∑ t:Site L,leak S (t+Pi.single i p) i = ∑ t:Site L,leak S t i:= Equiv.sum_comp (Equiv.addRight (Pi.single i p:Site L)) (fun t=> leak S t i)
 have he: ∑ t:Site L,∑ p:Per L,leak S (t+Pi.single i p) i≤ ((L).val:ℝ)^4:= (Finset.sum_le_sum (fun j _=> hu j)).trans_eq (by simp [site_card])
 rw [Finset.sum_comm] at he; simp_rw [hh] at he
 apply le_of_mul_le_mul_left _ (side_pos L); simp [ZMod.card,Per] at he; apply he.trans_eq; ring

local notation "sδ"=> fun t:Site S.ratio.count=> wrap f (lift t)
local notation "R_"=> S.ratio.embed
abbrev emits (z : Site f) (k:Site f) :ℝ:= if z=k then 1 else 0
lemma emits_run (z : Site f)(i : Axis)(x:Site f) :
    ∑ b: Site c, |(∑ u : S.patch.Small,∑ t:S.patch.Small, emits (z+step i) (x+wrap f u.val + wrap f t.val + S.ratio.embed b))- (∑ u : S.patch.Small,∑ t:S.patch.Small, emits z (x+wrap f u.val + wrap f t.val+S.ratio.embed b))| ≤ 2*(S.ratio.count.val:ℝ)^3:=by
 let k (z:Site f) (t : Site L) b := ∑ u:S.patch.Small, emits z (x+(sδ t)+wrap f u.val +R_ b)
 have hk (z:Site f) b : (∑ u:S.patch.Small, ∑ t:S.patch.Small, emits z (x+wrap f u.val+wrap f t.val +R_ b))=∑ t:Site L,k z t b:=by
     rw [← (Equiv.ofBijective (window S) (window_onto _)).sum_comp (fun u=> ∑ t:S.patch.Small, emits z (x+wrap f u.val+wrap f t.val+R_ b))]; rfl
 let g (z:Site f) t:= ∑ b:Site c,k z t b
 have hy (z:Site f) t : (∑ b:Site c,k z t b)=1:=by unfold k; rw [tile S _ (emits z)]; unfold emits; simp
 have hf z t b: 0≤k z t b:= Finset.sum_nonneg fun _ _ => by unfold emits; split <;> norm_num
 simp_rw [hk]; let Y:= (Equiv.addRight (step i:Site L)); have hx (b): ∑ t:Site L,k (z+step i) t b=∑ t:Site L,k (z+step i) (Y t) b:= (Equiv.sum_comp Y (fun t=> k (z+step i) t b)).symm
 simp_rw [hx,← Finset.sum_sub_distrib]; apply le_trans (sum_le_sum (fun _ _=> Finset.abs_sum_le_sum_abs ..))
 rw [sum_comm]
 apply le_trans (sum_le_sum (s:=univ) (g:=fun t=> 2*leak S t i) (fun t _=> ?_))
 · rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (leaks S _) (by positivity)
 unfold leak; split_ifs with ht
 · rw [mul_one]; refine (sum_le_sum (s:=univ) (g:=fun b=> k (z+step i) (Y t) b+k z t b) (fun b _ => (abs_sub ..).trans_eq (by rw [abs_of_nonneg (hf ..),abs_of_nonneg (hf ..)]))).trans ?_
   rw [sum_add_distrib,hy,hy];norm_num
 have he : lift (t+step i)=lift t+step i:= across_w S _ _ (le_of_not_gt ht)
 rw [mul_zero, sum_eq_zero (fun b _=>?_)]
 rw [show k (z+step i) (Y t) b=k z t b from ?_]; rotate_left
 · apply Finset.sum_congr rfl; intro u _; have hh z y: emits (z+step i) (y+step i)= emits (f:=f) z y:=by simp [emits]
   rw [show Y t=t+step i from rfl]; dsimp only; rw [he,map_add,wrap_step,show x+(_+step i)+(wrap f) u.val+S.ratio.embed b=x+wrap f (lift t)+wrap f u.val+R_ b+step i from by abel, hh]
 simp

lemma roll_turn (a b : Site f)(i: Axis)(n:ℕ):
   ∑ w : Site c, |(∑ p:Fin (n+2)→ S.patch.Small, emits (b+step i) (a+wrap f (∑ j,(p j).val)+R_ w))- (∑ p:Fin (n+2)→ S.patch.Small, emits b (a+wrap f (∑ j,(p j).val)+ R_ w))| ≤ Fintype.card (Fin n → S.patch.Small)*(2*((L).val:ℝ)^3) :=by
 let H (z : Site f) (w : Site c) (y : Cover):= emits z (a+wrap f y+R_ w)
 let T (u:Fin n→ S.patch.Small)(z:Site f)(w:Site c):= ∑ p:S.patch.Small,∑ t:S.patch.Small, emits z (a+wrap f (∑ j,(u j).val)+wrap f p.val+wrap f t.val+ R_ w)
 let E (n:ℕ) : ((Fin n→S.patch.Small)×S.patch.Small)≃(Fin (n+1)→S.patch.Small) := (Equiv.prodComm ..).trans (Fin.consEquiv (fun _:Fin (n+1)=> S.patch.Small))
 have hE (k:ℕ) (F:(Fin (k+1)→ S.patch.Small)→ℝ): ∑ p,F p=∑ u:Fin k→ S.patch.Small,∑ t:S.patch.Small,F (Fin.cons t u):= by rw [← (E k).sum_comp,Fintype.sum_prod_type];rfl
 have hx z w:(∑ p:Fin (n+2)→ S.patch.Small,H z w (∑ j,(p j).val))=∑ p:Fin n → S.patch.Small,T p z w:=by
    rw [hE (n+1),hE n]; refine sum_congr rfl fun p _=> sum_congr rfl fun t _=> sum_congr rfl fun q _=> ?_
    rw [Fin.sum_univ_succ]; simp_rw [Fin.cons_succ,Fin.cons_zero]; rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero,Fin.cons_succ]; unfold H; rw [map_add,map_add]; congr 2; abel
 change ∑ w: Site c, |(∑ p:Fin (n+2)→ S.patch.Small,H _ w (∑ j,(p j).val))-(∑ p:Fin (n+2)→ S.patch.Small,H _ w (∑ j,(p j).val))| ≤ _
 simp_rw [hx,← sum_sub_distrib]; apply le_trans (sum_le_sum (fun j _=> Finset.abs_sum_le_sum_abs ..)); rw [sum_comm]; exact (sum_le_sum (s:=univ) (fun j _=>emits_run S b i (a+wrap f (∑ k, (j k).val)))).trans_eq (by simp)

lemma polar_turn (a b:Site f)(i:Axis) :
    ∑ w: Site c, |(∑ p:S.patch.Points,S.patch.weight p*emits (b+step i) (a+atPoint S w p))-(∑ p:S.patch.Points,S.patch.weight p*emits b (a+atPoint S w p))| ≤ 2/((L).val:ℝ)^5:=by
 let N:= S.patch.J-2; let n:= Fintype.card S.patch.Rolls; have hL: n>0:=Fintype.card_pos
 have hx (x:S.patch.Small):x.val=x.val:=rfl
 have he z w : ∑ p:S.patch.Points,S.patch.weight p*emits z (a+atPoint S w p)=(n:ℝ)⁻¹ * ∑ p:S.patch.Rolls, emits z (a+wrap f (∑ j,(p j).val)+R_ w):=by
    unfold Patch.weight;simp_rw [sum_mul, ite_mul, zero_mul];rw [sum_comm];simp_rw [sum_ite_eq,mem_univ,if_true];rw [← mul_sum]; congr 1; apply sum_congr rfl; intro i _; unfold atPoint Patch.addRoll; rw [add_assoc]
 have hN:S.patch.J=N+2:=by unfold N; have he:= S.patch.order_cut; omega
 have hh x:(Fintype.card (Fin (x+2)→ S.patch.Small):ℝ)⁻¹ * ∑ w : Site c, |(∑ p:Fin (x+2)→ S.patch.Small, emits (b+step i) (a+wrap f (∑ j,(p j).val)+R_ w))- (∑ p:Fin (x+2)→ S.patch.Small, emits b (a+wrap f (∑ j,(p j).val)+ R_ w))| ≤ 2/((L).val:ℝ)^5:=by
    apply le_trans (mul_le_mul_of_nonneg_left (roll_turn S a b i _) (inv_nonneg.mpr (by positivity)))
    apply le_of_eq; rw [Fintype.card_fun, Fintype.card_fun,Fintype.card_fin,Fintype.card_fin, Nat.cast_pow,Nat.cast_pow,tile_size]; change _=2/(S.patch.L.val:ℝ)^5; rw [show (L)=S.patch.L from rfl]; field_simp; ring
 simp_rw [he,← mul_sub,abs_mul,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg (α:=ℝ) n)), ← mul_sum]; unfold n Patch.Rolls; rw [hN]; exact hh N

lemma mean_shard (x : Site f)(z : Site c)(i j : TypeFace 1): mean S (z,j) (x,i)=if i=j then (∑ p:S.patch.Points,S.patch.weight p*∑ k ∈ range S.patch.L.val, emits x (k • step (axisEquiv.symm j)+atPoint S z p)) else 0 :=by
 rw [show mean S (z,j) (x,i)= (mean S *ᵥ (Pi.single (x,i) 1)) (z,j) from ?_, mean_run_real]; rotate_left
 · rw [Matrix.mulVec_single_one]; rfl
 split_ifs with he
 · subst i; refine sum_congr rfl fun a _=>?_ ; congr 1; apply Finset.sum_congr rfl; intro b _; simp [Pi.single_apply,emits,eq_comm,add_comm]
 apply sum_eq_zero; intro _ _; simp [Pi.single_apply,he,Ne.symm he]

lemma mean_motion (i:TypeFace 1)(x: Site f)(j:Axis): ∑ p : Body 1 c, |mean S p (x+step j,i)-mean S p (x,i)| ≤ 2/((L).val:ℝ)^4:=by
 rw [Fintype.sum_prod_type, sum_comm]; rw [sum_eq_single i]
 rotate_left
 · intro b _ he; simp_rw [mean_shard]; simp only [if_neg (Ne.symm he),sub_zero, abs_zero,sum_const_zero]
 · simp
 simp only [mean_shard,↓reduceIte]; simp_rw [Finset.mul_sum]
 let F (k:ℕ)(p : Site c)(z:Site f):=∑ t:S.patch.Points,S.patch.weight t * emits z (k • step (axisEquiv.symm i)+atPoint S p t)
 let R:= range S.patch.L.val
 have hh p z : ∑ t:S.patch.Points,∑ k∈ R,S.patch.weight t*emits z (k • step (axisEquiv.symm i)+atPoint S p t)=∑ k∈R,F k p z:= Finset.sum_comm
 dsimp only [R] at hh
 simp_rw [hh,← sum_sub_distrib]; apply le_trans (sum_le_sum fun i _=> Finset.abs_sum_le_sum_abs ..); rw [sum_comm]; refine (sum_le_sum (fun k _=> polar_turn S (k • step (axisEquiv.symm i)) x j)).trans_eq ?_; simp [R]; change _=2/(S.patch.L.val:ℝ)^4; field_simp; rfl
end YM.Trace.Perfect
