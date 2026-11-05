import YM.UVExtension.Eyelet.Emboss
import YM.MergeProof.License
/-! observations and exact counting. important later EVERY duplicated occurrence.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Eyelet
open Function Filter MeasureTheory Set Lattice Wilson RG Source Extra.Histories Labels
open Planned.GuardedAtom Guard Push Local MergeProof Next.Foundations Concert BoundedContinuousFunction Motion
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side}{d :ℕ} {F:Frame G d} {H: Hol G} {p: BudgetPoint}{R:Rep G n} {ι:Type}
variable {v:ℝ}
abbrev Bucket (F:Frame G d)(p:BudgetPoint)(H:Hol G)(n:Side):= F.Coeff × Cow G n p d H

def Eye (P: Coefficient F n)(H:Hol G)(R:Rep G n)(v:ℝ): Bucket F R.p H n:= if h:Eligible P H R v then (P.x,h.tollE,h.tollK) else (P.x,0)
lemma sees (P:Coefficient F n)(H:Hol G)(R:Rep G n)(v:ℝ): (Eye P H R v).1=P.x:=by unfold Eye;split <;> rfl
variable {P:Coefficient F n}
namespace Eligible
lemma vistas (h:Eligible P H R v): Eye P H R v=(P.x,h.tollE,h.tollK):=dif_pos h
lemma scaled (h:Eligible P H R v)(c:ℂ): Eligible (Extra.Histories.stretch c P) H R v:=by obtain ⟨a,hp⟩:=h.pay; exact ⟨h.hK,stretch_format c h.form,_, stretch_rem _ hp⟩
lemma flare (h:Eligible P H R v)(c:ℂ): Eye (Extra.Histories.stretch c P) H R v=c • Eye P H R v:=by
   have hp:=h.scaled c; rw [hp.vistas,h.vistas]; refine Prod.ext rfl (Prod.ext (Roc.ext _ _ _ _ _ fun i t=> ?_) (Coil.ext _ _ _ fun i j=>?_)); swap
   · change tire _ _ _ hp.tollK=tire _ _ _ (c • h.tollK); rw [hp.make, map_smul,h.make,show profile R.activities (Extra.Histories.stretch c P).forced= c • profile R.activities P.forced from profile_scale ..]; simp only [Pi.smul_apply,smul_eq_mul,mul_left_comm c]
   change gaze _ _ _ _ _ hp.tollE=gaze _ _ _ _ _ (c • h.tollE); rw [hp.take,map_smul,h.take]; have he:hp.fernP i= c • h.fernP i:= by
      apply Subtype.ext; change graft (Extra.Histories.stretch c P) i=c • graft P i; unfold graft Extra.Histories.stretch; simp only [Pi.smul_apply]; split_ifs <;> simp
   rw [show t.read (graft (Extra.Histories.stretch c P) i)= c • t.read (graft P i) from ?_]; simp only [smul_eq_mul,mul_left_comm c]
   change flash H d R.p i t (twig (tin d H i.1 R.p) (hp.fernP i))=_; rw [he,map_smul,map_smul]; rfl
-- Sum uses Ledger not def outside current format.Algebra.
end Eligible
variable (H p F n)
def rooms (e:ℕ↪ℕ) : Bucket F p H n →L[ℂ] Bucket F p H n:= ContinuousLinearMap.prodMap (ContinuousLinearMap.id ℂ _) (ContinuousLinearMap.prodMap (duct d H p n e) (ContinuousLinearMap.id ℂ _))
lemma tax (e:ℕ↪ℕ)(v: Bucket F p H n):‖rooms n F H p e v‖ ≤ ‖v‖:= max_le_max le_rfl (max_le_max (duck d H p e _) le_rfl)

private def patches (m:Motion): F.Coeff→ₛₗ[gazeH m] F.Coeff where
    toFun:= Motion.patch F m
    map_add':= patch_add F m
    map_smul':= fun c x=> by rw [tintA]; exact patch_smul ..

def cap (m:Motion)(hn:2≤ n.val) : Bucket F p H n →SL[gazeH m] Bucket F p H n:=by
   let x:F.Coeff→SL[gazeH m] F.Coeff := {
       toLinearMap:=patches F m
       cont:=by
          change Continuous (Motion.patch F m); unfold Motion.patch; split_ifs; exact (F.act _).toContinuousLinearMap.continuous.star; exact (F.act _).toContinuousLinearMap.continuous }
   let P:=spinsE (d:=d) m H p hn; let Q:=spinsK (G:=G) m n p
   exact {
      toFun:=fun v=> (x v.1,P v.2.1,Q v.2.2)
      map_add':=fun v w=> Prod.ext (map_add x _ _) (Prod.ext (map_add P _ _) (map_add Q _ _))
      map_smul':=fun t v=> Prod.ext (map_smulₛₗ x _ _) (Prod.ext (map_smulₛₗ P _ _) (map_smulₛₗ Q _ _))
      cont:=(x.continuous.comp continuous_fst).prodMk ((P.continuous.comp continuous_snd.fst).prodMk (Q.continuous.comp continuous_snd.snd)) }
variable {F H p n}
lemma soar (m:Motion) (S:R.activities.Moves m.1 (0:Site n))(hn:2≤ n.val){h:Eligible P H R v}{Z:Eligible (audition S P) H R v}: Eye (audition S P) H R v= cap n F H R.p m hn (Eye P H R v):=by
   rw [Z.vistas,h.vistas]; refine Prod.ext ?_ (Prod.ext (sprint m S P h Z hn|>.symm) (leaps m S P h Z|>.symm)); change (audition S P).x= Motion.patch F m _; unfold audition Motion.patch; split <;> rfl

variable {T:SectionData F}
lemma rowedE (Q:F.Coeff→ Coefficient F n) (hq:∀ i,Eligible (Q i) H R v)(hr:Ledger F n Q): IsLinearMap ℂ fun i=> Eye (Q i) H R v:=by
   choose c h using fun i=> (hq i).pay; have hT:= inkL Q c hr h; have hz (u) (t:Eyelet.Slot n):= recognizes d H t.1 R.p ((hq u).fernP t) -- replace
   constructor
   · intro x y; simp_rw [fun i=> (hq i).vistas]; refine Prod.ext (hr.x.map_add ..) (Prod.ext (Roc.ext _ _ _ _ _ fun i t=>?_) (Coil.ext _ _ _ fun i j=>?_)); swap
     · change tire _ _ _ (hq _).tollK=tire _ _ _ ((hq x).tollK+(hq y).tollK); rw [Eligible.make,map_add,Eligible.make,Eligible.make, hT.map_add]; exact mul_add ..
     change gaze _ _ _ _ _ (hq _).tollE=gaze _ _ _ _ _ ((hq x).tollE+(hq y).tollE); rw [Eligible.take,map_add,Eligible.take,Eligible.take]; have he:graft (Q (x+y)) i=graft (Q x) i+graft (Q y) i:=by
        unfold graft; rw [hr.tags x,hr.tags y,hr.tags (x+y),hr.reg.map_add]; split <;> simp
     rw [he,show t.read (graft (Q x) i+graft (Q y) i)=t.read (graft (Q x) i)+t.read (graft (Q y) i) from ?_,mul_add]
     exact Local.left_add t.poll ((hz x i).pose.smooth _ t.live) ((hz y i).pose.smooth _ t.live) t.card
   intro a x; have he: Extra.Histories.stretch a (Q x)=Q (a • x):=by
       have hr' :∀ (P T:Coefficient F n), P.x=T.x→P.support=T.support→ P.regular=T.regular→P.forced=T.forced→ P=T:=by rintro ⟨x,y,v,b⟩ ⟨a,h,k,t⟩ h1 h2 h3 h4; congr
       exact hr' _ _ (hr.x.map_smul ..|>.symm) ((hr.tags x).trans (hr.tags ..).symm) (hr.reg.map_smul ..|>.symm) (hr.f.map_smul ..|>.symm)
   rw [← he,(hq x).flare]

variable (e:ℕ≃ι×ℕ) (Q:ι→ Coefficient F n) {t:ι→ℝ}(hw:∀ i,(Q i).remBound 0 R v (t i))(he:Summable t)
include hw he
lemma stanza (h:∀ i,Eligible (Q i) H R v) (hZ:Eligible (Extra.Histories.merge e Q) H R v)(ht:Summable fun i=> F.coeffSize (Q i).x): HasSum (fun i=> rooms n F H R.p (aisleN e i) (Eye (Q i) H R v)) (Eye (Extra.Histories.merge e Q) H R v):=by
   simp_rw [hZ.vistas,fun i=> (h i).vistas]; exact (Size.series F ht|>.of_norm.hasSum).prodMk ((blazeE e Q h hZ hw he).2.prodMk ((blazeK e Q h hZ hw he).2))
end YM.UVExtension.Eyelet
