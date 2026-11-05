import YM.UVExtension.Rainfall.Jet
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Rainfall
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open Eyelet MergeProof Lacing Lacing.RoutesF
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ} {F:Labels.Frame G d} {A:Hol G}
section
variable {n: Side} {R:Rep G n}{κ a b:ℝ}
lemma cliff (Q:Coefficient F n)(h:Eligible Q A R κ)(hp:Tab Q 0 R κ a b) : ‖h.tollE‖ ≤ a:=by
   obtain ⟨v,hv,hθ⟩:=hp.regular
   let W:= takes Q h.form.origin
   let e:=extend W v 0; let K:= key n
   let c(i:Eyelet.Slot n):=e (K.symm i); let Z i:= h.goals i
   have he i:c (K (W i))= v i :=by unfold c; rw [K.symm_apply_apply]; exact W.injective.extend_apply ..
   have hf : SumBudget (fun i=> Eyelet.fee R.p i.1.val*c i) a:= by
       refine sumBudget_pass (W.trans K.toEmbedding) _ ?_ (fun i hi=>?_)
       · change SumBudget (fun i=> Eyelet.fee R.p (K (W i)).1.val*c (K (W i))) _; simp_rw [he, fun i=>show (K (W i)).1.val=Q.support i from (bunch _ _ i).1]; exact hv
       rw [show c i=0 from ?_, mul_zero]; apply extend_apply'; rintro ⟨j,hv⟩; exact hi ⟨j, (congr_arg K hv).trans (K.apply_symm_apply _)⟩
   have hk(i): R.p.supBounds 0 (K i).1.val (graft Q (K i)) (c (K i)):=by
      by_cases hi:i∈ Set.range W
      · obtain ⟨i,rfl⟩:=hi; rw [he, show (K (W i)).1.val=Q.support i from (bunch ..).1, show graft Q (K (W i))= _ from (bunch Q h.form.origin i).2]; exact hθ _
      rw [show graft Q (K i)=0 from sleeps Q h.form.origin i hi, show c (K i)=0 from (congr_arg e (K.symm_apply_apply _)).trans (extend_apply' _ _ _ hi)]; exact (hot ..).2
   have hh : SumBudget (fun i=> ‖h.goals i‖) a:=by
      refine Local.sumBudget_mono hf (fun i=>norm_nonneg _) (fun i=>?_) le_rfl; obtain ⟨i,rfl⟩:=K.surjective i
      rw [Eligible.goals,norm_smul, Complex.norm_real,Real.norm_of_nonneg (toll_pos ..|>.le)]; exact mul_le_mul_of_nonneg_left ((pays d A _ R.p _).1 (hk i)) (toll_pos ..|>.le)
   exact (castL h.tollE).tsum_eq.symm.trans_le hh.2.2

structure Wallet {n:Side}{P:BudgetPoint} (L:Bucket F P A n) (v:F.Coeff)(a b:ℝ) : Prop where
    earns : orbitCost F*F.coeffSize (L.1-v) ≤ a
    rain : turnCost P.order P.power* ‖L.2.1‖≤ b
    stem : ‖L.2.2‖≤ b
variable {P:BudgetPoint}{n:Side}
namespace Wallet
local notation "J!"=> Bucket F P A n
set_option quotPrecheck false
lemma leans {L:Bucket F P A n} {a:ℝ}(h:Wallet L 0 a a): ‖L‖≤ a:=by
    have hp:=h.earns; rw [sub_zero] at hp
    exact max_le ((Local.norm_le_size F _).trans ((le_mul_of_one_le_left (Work.G08.size_nonneg F _) (orbitCost_one_le F)).trans hp)) (max_le ((le_mul_of_one_le_left (norm_nonneg _) (Lacing.RoutesF.turnCost_near _)).trans h.rain) h.stem)
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E]
lemma shuts (L:E→L[ℂ] J!)(a:ℝ) : IsClosed {u:E| Wallet (L u) 0 (a*‖u‖) (a*‖u‖)}:=by
   let f(u:E):= a*‖u‖; have ht:Continuous f:=continuous_const.mul continuous_norm; let g(x:F.Coeff):= orbitCost F* F.coeffSize (x-0); have hg : Continuous g := continuous_const.mul ((show Continuous (fun x=>F.coeffSize x) by unfold Frame.coeffSize; fun_prop).comp (continuous_id.sub continuous_const))
   rw [show {u:E| Wallet (L u) 0 (a*‖u‖) (a*‖u‖)}={x:E| (g ∘ (fun x=> (L x).1)) x ≤ f x} ∩({x:E| turnCost P.order P.power * ‖(L x).2.1‖ ≤ f x}∩{x:E| ‖(L x).2.2‖ ≤ f x}) from Set.ext (fun x=> ⟨fun h=> ⟨(show Wallet (L x) 0 _ _ from h).earns, (show Wallet (L x) 0 _ _ from h).rain,(show Wallet (L x) 0 _ _ from h).stem⟩,fun ⟨h,h1,h2⟩=> Wallet.mk h h1 h2⟩)]
   exact (isClosed_le (hg.comp L.continuous.fst) ht).inter ((isClosed_le (f:=fun u:E=>turnCost P.order P.power* ‖(L u).2.1‖) (continuous_const.mul L.continuous.snd.fst.norm) ht).inter (isClosed_le L.continuous.snd.snd.norm ht))
section
variable {X : Type}[AddCommGroup X][Module ℂ X]
lemma vault (L:X→ₗ[ℂ] E)(D:X→ₗ[ℂ] J!)(c:ℂ)(hc:c≠0)(h:DenseRange L)(a:ℝ)(hp:∀ i, Wallet (D i) 0 (a*‖c • L i‖) (a*‖c • L i‖)):
   ∃ T:E→L[ℂ] J!, (∀ i:X,T (c • L i) = D i) ∧ (∀ x,Wallet (T x) 0 (a*‖x‖) (a*‖x‖)):=by
   let L':= c • L; have hx:DenseRange L':= Dense.mono (by rintro v ⟨i,rfl⟩; exact ⟨c⁻¹ • i, by simp [L',smul_smul,hc]⟩) h
   let T:=D.extendOfNorm L'; have ht(i):T (L' i)= D i:=LinearMap.extendOfNorm_eq hx ⟨a,fun i=>(hp i).leans⟩ i
   exact ⟨T,ht, fun x=> hx.induction_on (p:=fun x=> Wallet (T x) 0 (a*‖x‖) (a*‖x‖)) x (shuts T a) (fun i=>by rw [ht]; exact hp i)⟩
end
end Wallet
end
section
variable (B:SectionData F) (H: History G)(N p m:ℕ)(A:Hol G)
local notation "n"=> H.S.side m p
local notation "n'"=> H.S.side (m+1) p
variable (E:Rep G (H.S.side (m+1) p)) (R:Rep G (H.S.side m p)) (hr:R= H.rep N p m)
variable {g:Config G (H.S.side (m+1) p)→ℂ}{D:GaugeDoor E R}{X:Set Wing}{α:Config G (H.S.side (m+1) p)→ℂ}{ρ:Res G (H.S.side (m+1) p)}{ψ:ℂ}{v:F.Coeff}{c t w:ℝ}{q:Bucket F R.p A (H.S.side m p)}
include hr
-- g may binder not in syntax. expand on failure
lemma alarm (K' : Keeper R.p R.activities)(h: Flees B H N p m A E R D X α ρ ψ g v c t w q) : Wallet q v c t:=by
   subst R; obtain ⟨L,he,-,rfl⟩:=h.mints; have hx:Eligible L A (H.rep N p m) (kappa H m):=⟨⟨K'⟩, he.format,_,he.bound⟩
   rw [hx.vistas]; obtain ⟨a,b,hp,hq⟩:=he.future
   exact ⟨he.leadP, (mul_le_mul_of_nonneg_left (cliff _ hx hp) (pow_nonneg (by positivity) _)).trans ((le_add_of_nonneg_right hp.second).trans hq), (le_add_of_nonneg_left (norm_nonneg _)).trans (hx.costs he.bound)⟩
end
end YM.UVExtension.Rainfall
