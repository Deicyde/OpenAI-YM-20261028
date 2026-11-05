import YM.MergeProof.North.Quark
import YM.OPE.Replicas.Botan
import YM.OPE.Replicas.SkyFall

/-!
# Many slots per cell: port of YM/MergeProof/North/Quark.lean

Most of the proof can be shared verbatim with that for pairs. Costs at every step
use the same register though the group being transported can now be quite different.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories
open scoped Topology BigOperators Classical
variable {slotsZ : Type}[Fintype slotsZ][DecidableEq slotsZ] {V : Type}[Fintype V][DecidableEq V]{G:Gauge}{f c:Side}{R:Rep G f}{A:Rep G c}{D:GaugeDoor R A}
variable (v:V)(P:V→Motion)(E:V→Site c)(B:V→Equiv.Perm V)
local notation "X"=> Names V slotsZ
-- necessary branching Recall. o' migration by anchor from StepData ratio
variable (o:(V×slotsZ)→ Site f)(b:(V×slotsZ)→Site c)
    (L:(V×slotsZ)→ Config G f→ℂ)(K:(V×slotsZ)→ Res G f)(H:(V×slotsZ)→ Res G c)(a t:slotsZ→ℝ)(g:(V×slotsZ)→ℂ)
    (S:StepData c f) {N:ℕ} {d e u x:ℝ}{w:(V×slotsZ)→ℝ}
def chimes (L:(V×slotsZ)→ Config G f→ℂ)(K:(V×slotsZ)→ Res G f)(H:(V×slotsZ)→ Res G c)(g:(V×slotsZ)→ℂ)(S:StepData c f):Prop:=∀ j,j≠v→ B j v=j ∧∀ i,let m:=P j;let y:=E j;let p:=S.ratio.embed y; let v₀:(V×slotsZ):=(v,i);let u:(V×slotsZ):=(j,i)
    o u=affine m.1 p (o v₀) ∧ b u=affine m.1 y (b v₀) ∧ L u=stepUp m p (L v₀)∧ K u=floatUp m p (K v₀)∧H u=floatUp m y (H v₀) ∧ g u=scalar m (g v₀)
def relates (q:(V×slotsZ)→Response G c):Prop:=∀ j,j≠v→ ∀ i, q (j,i)= upwards (P j) (E j) (q (v,i))
-- C J hats union array via Publish b. chooses congruence.
lemma quay (hD:Tunes D)(hs: SoundDoor S D)(hx:chimes v P E B o b L K H g S)(π:∀ i,R.activities.Moves (P i).1 (S.ratio.embed (E i))) (hw:∀ i,0<w i)(hy:∀ i,i≠v→∀ j:slotsZ,w (i,j)=w (v,j)) (hp:∀ i:slotsZ, let y:(V×slotsZ):=(v,i);∃ x:Set Wing,x.Finite∧Tale x (o y) (b y) 1 (L y) (K y) (H y) (g y) (a i) (t i) D) :
   ∃ (I :slotsZ→Type),∃ _:∀ i,Fintype (I i),∃ (M:(Σ i:(V×slotsZ),I i.2)→Hat (Names V slotsZ) R) (ψ:(V×slotsZ)→Response G c), (∀ i:(V×slotsZ),Publish i w (o i) (b i) (L i) (K i) (H i) (a i.2) (t i.2) (g i) D (fun j=>M ⟨i,j⟩) (ψ i)) ∧ relates v P E ψ ∧ Cohere v P (fun i=>S.ratio.embed (E i)) B π M:=by
    have hℓ i:=hp i
    obtain ⟨I,hI,M,p,h⟩ : ∃ I:slotsZ→Type,∃ _:∀ i,Fintype (I i),∃ M:∀ i,I i→Hat (Names V slotsZ) R,∃ ψ:slotsZ→Response G c,∀ i:slotsZ,let x:(V×slotsZ):=(v,i);Publish x w (o x) (b x) (L x) (K x) (H x) (a i) (t i) (g x) D (M i) (ψ i) := by
       choose Z hZ J hJ' M f ψ hM using hp
       choose I hI N hK hO hS hF hQ using fun i=> narrow1 (Names V slotsZ) (v,i) (hM i) (hZ i) hs hD hw
       exact ⟨I,hI,N,ψ,fun i=>⟨hK _,hO _,(hM _).cost,hS _,hF _,hQ _⟩⟩
    let e (i:(V×slotsZ)):= if i.1=v then M i.2 else ((shuttled (B i.1) (P i.1) (S.ratio.embed (E i.1)) (π i.1)) ∘ M i.2)
    let r(s:(V×slotsZ)):= if s.1=v then p s.2 else upwards (P s.1) (E s.1) (p s.2)
    have hh (j:(V×slotsZ)): Publish j w (o j) (b j) (L j) (K j) (H j) (a j.2) (t j.2) (g j) D (e j) (r j):=by
       rcases j with ⟨j,i⟩; by_cases hH:j=v; subst j; simpa [e,r] using! h i
       obtain ⟨h₀,hp'⟩:= hx j hH; obtain ⟨hm,ht,h',hG,hV,hw⟩:=hp' i; unfold e r; simp only [if_neg hH];
       change o (j,i)= affine (P j).1 _ _ at hm;change b (j,i)= affine (P j).1 _ _ at ht;change L (j,i)= _ at h';change K (j,i)=_ at hG;change H (j,i)=_ at hV;change g (j,i)=_ at hw
       rw [hm,ht,h',hG,hV,hw]; have hz: nome (B j) (v,i)=(j,i):=Prod.ext h₀ rfl
       have he := Publish.updates (h i) (P j) (E j) (B j) (π j) (?_) hs; rwa [hz] at he -- inspect
       change ∀ i:slotsZ,w (v,i)=w (B j v,i); rw [h₀]; exact fun i=> (hy j hH i).symm
    let u (x : Σ i:(V×slotsZ),I i.2):= e x.1 x.2
    refine ⟨I,hI,u,r,hh,?_,fun j hj=>?_⟩
    · intro j hj i; simp [r,hj]
    let s (i:(V×slotsZ)) : I i.snd≃ I (nome (B j) i).2:= Equiv.refl _; let Q':Equiv.Perm (Σ i:(V×slotsZ),I i.2):=(nome (B j)).sigmaCongr s; have Hq(p:Σ i:(V×slotsZ),I i.2): (u p).s=(X).fire p.1:= (hh p.1|>.ran p.2).1; have hk:= (hx j hj).1
    refine ⟨Q',hk,fun i=> ?_,fun i=> ?_⟩
    · change _ ↔ Focused j (u (Q' i)).s; rw [Hq,Hq,which,which]; change _ ↔ B j _=j; exact (Iff.trans (B j|>.apply_eq_iff_eq|>.symm) (by rw [hk]))
    rcases i with ⟨⟨c,i⟩,b⟩; rw [Hq,which]; intro hi; dsimp only at hi; subst c; suffices hz:u (Q' ⟨(v,i),b⟩)=shuttled (B j) (P j) (S.ratio.embed (E j)) (π j) (u ⟨(v,i),b⟩) by
       rw [hz]; exact ⟨congr_arg (drum (B j)) (Hq _),rfl,rfl⟩ -- after Hq rw replaced rhs maybe
    change e (B j v,i) b=_; simp [hk,e,u,hj]; rw [hk]
end YM.MergeProof.Ribbons.ManyCopies
