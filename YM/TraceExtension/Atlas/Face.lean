import YM.UVNext.FREE_STRESS_CERTIFICATE.Size
import YM.UVNext.FREE_STRESS_CERTIFICATE.Cube
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pilot
open Function Set Filter Table Labels Maxwell UVNext.FreeStress Work.A01
open scoped Topology BigOperators InnerProductSpace
namespace Mask

def maskA(a:Axis)(p:Plane) : ℤ:= if p.val.1=a ∨ p.val.2=a then -1 else 1
def marks(a:Axis)(p:Face): ℤ:= maskA a p.val.1 * maskA a p.val.2

def whim(s:Fin 10): Equiv.Perm Axis:= (![Equiv.refl _, Equiv.swap 0 1, Equiv.swap 0 2,Equiv.swap 0 3,Equiv.swap 1 2,Equiv.swap 1 3,Equiv.swap 2 3,(Equiv.swap 0 1).trans (Equiv.swap 2 3), (Equiv.swap 0 2).trans (Equiv.swap 1 3), (Equiv.swap 0 3).trans (Equiv.swap 1 2)] : Fin 10→ Equiv.Perm Axis) s

def exchanges(s:Equiv.Perm Axis)(p q:Plane): Prop:= ((s p.val.1=q.val.1∧s p.val.2=q.val.2) ∨ (s p.val.1=q.val.2∧s p.val.2=q.val.1))
instance (s:Equiv.Perm Axis)(p q:Plane): Decidable (exchanges s p q):= by unfold exchanges; infer_instance
-- enumeration
set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
theorem flag : ∀ (p q:Face), (∃ a:Axis, marks a p = -(marks a q)) ∨
       ∃ s:Fin 10,(exchanges (whim s) p.val.1 q.val.1 ∧ exchanges (whim s) p.val.2 q.val.2) ∨
           (exchanges (whim s) p.val.1 q.val.2 ∧ exchanges (whim s) p.val.2 q.val.1):= by decide
lemma whirls:∀ s x,whim s (whim s x) = x:= by decide
lemma revolver(s): let r:Signed:=⟨whim s,fun _=>false⟩; r*r=1:=by
   intro r; refine Signed.ext (Equiv.ext fun i=>whirls ..) (funext fun i=>rfl)
end Mask
open Mask

variable {G:Gauge}(F:Frames G)(H:(freeTable F).RealSpin)
def tipA (p:Plane×Plane):=(link F 4 le_rfl p.1.val.1 p.1.val.2 p.2.val.1 p.2.val.2)
abbrev petal(F:Frames G)(p:Face):= tipA F p.val
lemma paint (s:Signed) (p:Plane×Plane): (freeTable F).mirror H 4 s (tipA F p)=
    (↑(eps s p.1.val.1*eps s p.1.val.2*(eps s p.2.val.1*eps s p.2.val.2)):ℂ) • flat F (s.perm p.1.val.1) (s.perm p.1.val.2) (s.perm p.2.val.1) (s.perm p.2.val.2):= signed_link ..
lemma axis_e(a:Axis)(p:Face): (freeTable F).mirror H 4 (Signed.mirror a) (petal F p)=(↑(marks a p):ℂ) • petal F p:=by
    unfold petal; rw [paint]; let s:=Signed.mirror a
    have he(p:Plane): (↑(maskA a p):ℝ)=eps s p.val.1*eps s p.val.2:=by
       have hx:=p.property.ne
       simp [maskA,eps, Signed.matrix_at,s,Signed.mirror]; split_ifs <;> first| rfl|simp_all <;> grind
    unfold marks; rw [Int.cast_mul,Complex.ofReal_mul,← he,← he]; push_cast; rfl
lemma swirl(s:Equiv.Perm Axis)(p q:Plane×Plane)(hp: exchanges s p.1 q.1)(hq: exchanges s p.2 q.2):
    let r:Signed:=⟨s,fun _=>false⟩
    ∃ n:ℤ,(n=1 ∨ n= -1) ∧ (freeTable F).mirror H 4 r (tipA F p)=(n:ℂ) • tipA F q
       :=by
    intro r; have he(i): eps r i=1:=by simp [r,eps,Signed.matrix_at]
    rw[paint]; simp only [he,mul_one,Complex.ofReal_one,one_smul]; unfold flat; change ∃ n:ℤ, _ ∧ link F _ _ (s p.1.val.1) (s p.1.val.2) (s p.2.val.1) (s p.2.val.2) = (n:ℂ) • link F _ _ _ _ _ _
    rcases hp with ⟨a,b⟩|⟨a,b⟩ <;> rcases hq with ⟨c,d⟩|⟨c,d⟩ <;> rw [a,b,c,d]
    · exact ⟨1,Or.inl rfl,by simp⟩
    · exact ⟨-1,Or.inr rfl,by simp; rw [right_link F _ _ _ q.2.val.1 q.2.val.2]⟩
    · exact ⟨-1,Or.inr rfl,by simp; rw [left_link F _ q.1.val.1 q.1.val.2]⟩
    exact ⟨1,Or.inl rfl,by simp; rw [left_link F _ q.1.val.1 q.1.val.2,right_link F _ _ _ q.2.val.1 q.2.val.2,neg_neg]⟩
lemma mask_sq (a:Axis)(p:Plane): maskA a p*maskA a p=1:=by unfold maskA; split<;>norm_num
lemma flag_sq (a:Axis)(p:Face): marks a p*marks a p=1:=by unfold marks; rw[mul_mul_mul_comm,mask_sq,mask_sq,one_mul]
lemma flip_sig (p q: Face): (∃ (s:Signed)(c:ℂ), c*c=1 ∧ (freeTable F).mirror H 4 s (petal F p)= c • petal F p∧(freeTable F).mirror H 4 s (petal F q)=(-c) • petal F q)∨
    ∃ (s:Signed)(c:ℂ), c*c=1 ∧ (freeTable F).mirror H 4 s (petal F p)= c • petal F q∧(freeTable F).mirror H 4 s (petal F q)=c • petal F p:=by
    rcases flag p q with ⟨v,hv⟩|⟨v,hv⟩
    · have hs: (↑(marks v p):ℂ)= -(↑(marks v q):ℂ):=by exact_mod_cast hv
      exact Or.inl ⟨Signed.mirror v,(marks v p:ℂ),by exact_mod_cast flag_sq v p, axis_e .., by rw[hs,neg_neg]; exact axis_e ..⟩
    refine Or.inr ?_; let s:Signed:=⟨whim v,fun _=>false⟩; let V:=(freeTable F).mirror H 4 s
    have hm : ∃ n:ℤ,(n=1 ∨ n= -1) ∧ V (petal F p)=(n:ℂ) • petal F q:=by
       rcases hv with ⟨a,b⟩|⟨a,b⟩
       · exact swirl F H (whim v) p.val q.val a b
       obtain ⟨n,hn,ht⟩:= swirl F H (whim v) p.val (q.val.swap) a b; refine ⟨n,hn,ht.trans ?_⟩; exact congr_arg _ (swap_link ..)
    obtain ⟨n,hn,ht⟩:= hm; let c:ℂ:=↑n; have hz:c*c=1:=by unfold c; rcases hn with h|h <;> rw [h] <;> norm_num
    have he(x): V (V x)=x:=by unfold V; rw [← (freeTable F).mirror_mul,show s*s=1 from revolver v, mirror_one]
    refine ⟨s,c,hz,ht,?_⟩; have hx:= congr_arg V ht; rw [he,map_smul] at hx; change _=c • _ at hx; rw [hx,smul_smul, hz,one_smul]
end YM.Trace.Pilot
