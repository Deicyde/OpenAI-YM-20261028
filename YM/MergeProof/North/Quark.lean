import YM.MergeProof.Decaf
import YM.MergeProof.Memo
import YM.MergeProof.North.Botan
import YM.MergeProof.North.SkyFall
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories
open scoped Topology BigOperators Classical
variable {V : Type}[Fintype V][DecidableEq V]{G:Gauge}{f c:Side}{R:Rep G f}{A:Rep G c}{D:GaugeDoor R A}
variable (v:V)(P:V→Motion)(E:V→Site c)(B:V→Equiv.Perm V)
local notation "X"=> Aged V
-- necessary branching Recall. o' migration by anchor from StepData ratio
variable (o:Name V→ Site f)(b:Name V→Site c)
    (L:Name V→ Config G f→ℂ)(K:Name V→ Res G f)(H:Name V→ Res G c)(a t:Bool→ℝ)(g:Name V→ℂ)
    (S:StepData c f) {N:ℕ} {d e u x:ℝ}{w:Name V→ℝ}
def chimes (L:Name V→ Config G f→ℂ)(K:Name V→ Res G f)(H:Name V→ Res G c)(g:Name V→ℂ)(S:StepData c f):Prop:=∀ j,j≠v→ B j v=j ∧∀ i,let m:=P j;let y:=E j;let p:=S.ratio.embed y; let v₀:Name V:=(v,i);let u:Name V:=(j,i)
    o u=affine m.1 p (o v₀) ∧ b u=affine m.1 y (b v₀) ∧ L u=stepUp m p (L v₀)∧ K u=floatUp m p (K v₀)∧H u=floatUp m y (H v₀) ∧ g u=scalar m (g v₀)
def relates (q:Name V→Response G c):Prop:=∀ j,j≠v→ ∀ i, q (j,i)= upwards (P j) (E j) (q (v,i))
-- C J hats union array via Publish b. chooses congruence.
lemma quay (hD:Tunes D)(hs: SoundDoor S D)(hx:chimes v P E B o b L K H g S)(π:∀ i,R.activities.Moves (P i).1 (S.ratio.embed (E i))) (hw:∀ i,0<w i)(hy:∀ i,i≠v→∀ j:Bool,w (i,j)=w (v,j)) (hp:∀ i:Bool, let y:Name V:=(v,i);∃ x:Set Wing,x.Finite∧Tale x (o y) (b y) 1 (L y) (K y) (H y) (g y) (a i) (t i) D) :
   ∃ (I :Bool→Type),∃ _:∀ i,Fintype (I i),∃ (M:(Σ i:Name V,I i.2)→Hat (Aged V) R) (ψ:Name V→Response G c), (∀ i:Name V,Publish i w (o i) (b i) (L i) (K i) (H i) (a i.2) (t i.2) (g i) D (fun j=>M ⟨i,j⟩) (ψ i)) ∧ relates v P E ψ ∧ Cohere v P (fun i=>S.ratio.embed (E i)) B π M:=by
    have hℓ i:=hp i
    obtain ⟨I,hI,M,p,h⟩ : ∃ I:Bool→Type,∃ _:∀ i,Fintype (I i),∃ M:∀ i,I i→Hat (Aged V) R,∃ ψ:Bool→Response G c,∀ i:Bool,let x:Name V:=(v,i);Publish x w (o x) (b x) (L x) (K x) (H x) (a i) (t i) (g x) D (M i) (ψ i) := by
       choose Z hZ J hJ' M f ψ hM using hp
       choose I hI N hK hO hS hF hQ using fun i=> narrow1 (Aged V) (v,i) (hM i) (hZ i) hs hD hw
       exact ⟨I,hI,N,ψ,fun i=>⟨hK _,hO _,(hM _).cost,hS _,hF _,hQ _⟩⟩
    let e (i:Name V):= if i.1=v then M i.2 else ((shuttled (B i.1) (P i.1) (S.ratio.embed (E i.1)) (π i.1)) ∘ M i.2)
    let r(s:Name V):= if s.1=v then p s.2 else upwards (P s.1) (E s.1) (p s.2)
    have hh (j:Name V): Publish j w (o j) (b j) (L j) (K j) (H j) (a j.2) (t j.2) (g j) D (e j) (r j):=by
       rcases j with ⟨j,i⟩; by_cases hH:j=v; subst j; simpa [e,r] using! h i
       obtain ⟨h₀,hp'⟩:= hx j hH; obtain ⟨hm,ht,h',hG,hV,hw⟩:=hp' i; unfold e r; simp only [if_neg hH];
       change o (j,i)= affine (P j).1 _ _ at hm;change b (j,i)= affine (P j).1 _ _ at ht;change L (j,i)= _ at h';change K (j,i)=_ at hG;change H (j,i)=_ at hV;change g (j,i)=_ at hw
       rw [hm,ht,h',hG,hV,hw]; have hz: nome (B j) (v,i)=(j,i):=Prod.ext h₀ rfl
       have he := Publish.updates (h i) (P j) (E j) (B j) (π j) (?_) hs; rwa [hz] at he -- inspect
       change ∀ i:Bool,w (v,i)=w (B j v,i); rw [h₀]; exact fun i=> (hy j hH i).symm
    let u (x : Σ i:Name V,I i.2):= e x.1 x.2
    refine ⟨I,hI,u,r,hh,?_,fun j hj=>?_⟩
    · intro j hj i; simp [r,hj]
    let s (i:Name V) : I i.snd≃ I (nome (B j) i).2:= Equiv.refl _; let Q':Equiv.Perm (Σ i:Name V,I i.2):=(nome (B j)).sigmaCongr s; have Hq(p:Σ i:Name V,I i.2): (u p).s=(X).fire p.1:= (hh p.1|>.ran p.2).1; have hk:= (hx j hj).1
    refine ⟨Q',hk,fun i=> ?_,fun i=> ?_⟩
    · change _ ↔ Focused j (u (Q' i)).s; rw [Hq,Hq,which,which]; change _ ↔ B j _=j; exact (Iff.trans (B j|>.apply_eq_iff_eq|>.symm) (by rw [hk]))
    rcases i with ⟨⟨c,i⟩,b⟩; rw [Hq,which]; intro hi; dsimp only at hi; subst c; suffices hz:u (Q' ⟨(v,i),b⟩)=shuttled (B j) (P j) (S.ratio.embed (E j)) (π j) (u ⟨(v,i),b⟩) by
       rw [hz]; exact ⟨congr_arg (drum (B j)) (Hq _),rfl,rfl⟩ -- after Hq rw replaced rhs maybe
    change e (B j v,i) b=_; simp [hk,e,u,hj]; rw [hk]
end YM.MergeProof.Ribbons
