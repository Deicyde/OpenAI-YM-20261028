import YM.RG05Readout.Weave.Direction
import YM.MergeProof.North.Verve
import YM.MergeProof.Domino
/-!
# Transport views for the replicated tests

A physical test pull is handled in base orientation (calendar) before `stepUp`.
Thus child test order doesn't rotate into the `readJ` BASIS used there; it is the
coefficient that gets advanced after specializing the slot. For a copy, pays
remain per-marker on that shot and hold with projection tags congruent at the
true masks. Needn't assume arbitrary K representations equivariant.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.View
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Trace.Physical Offsets OPE Copper
open Push Local Planned.GuardedAtom Guard MergeProof Address Motion
open PhysicalNext.Repeat Lotus
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side} {V:Type*} {R:Rep G n} {e d c f v:ℝ} {C:Family G}{N m p:ℕ}
-- sb with offsets.
variable (a:Motion)
variable {x y:Site n} {P Q:Three G n}

structure Signpost (R:Rep G n) (a:Motion)(x:Site n)(P Q:Three G n) : Prop where
    trade : Q.1=stepUp a x P.1
    gate : Q.2.1=stepUp a x P.2.1
    lens : profile R.activities Q.2.2 = floatUp a x (profile R.activities P.2.2)

-- remove nolint
variable (π:R.activities.Moves a.1 x)
def spin (P: Three G n):Three G n:=(stepUp a x P.1,stepUp a x P.2.1,fun i=> stepUp a x (P.2.2 (π.kp.symm i)))
lemma spin_at : Signpost R a x P (spin a π P):= ⟨rfl,rfl,by apply roam a _ π; intro i U; simp only [spin, Equiv.symm_apply_apply]⟩
lemma shift_at {π:R.activities.Moves 1 x}:Signpost R (1,false) x P ((shiftTape x π) P):=spin_at (x:=x) (1,false) π -- conjunction definitional
-- spin linear over real
lemma spin_real (z:ℂ)(hz:scalar a z=z) : spin a π (z • P)=z • spin a π P:=by
    have ht(f:Goods G n): stepUp a x (z • f)= z • stepUp a x f:=by funext U; change scalar a (z*_) = z*_;rw [scalar_mul,hz];rfl
    exact Prod.ext (ht _) (Prod.ext (ht _) (funext fun i=>ht _))
lemma spin_add (U W:Three G n): spin a π (U+W)=spin a π U+spin a π W:=by
    have h(f g:Goods G n):stepUp a x (f+g)=stepUp a x f+stepUp a x g:=funext fun _=>scalar_add ..
    exact Prod.ext (h _ _) (Prod.ext (h _ _) (funext fun i=>h _ _))
lemma spin_zero:spin a π 0=0:= Prod.ext (funext fun _=> scalar_z a) (Prod.ext (funext fun _=>scalar_z a) (funext fun _=>funext fun _=> scalar_z a))
lemma spin_sum (s: Finset V)(f: V→ Three G n) : spin a π (∑ i∈s,f i)=∑ i∈s,spin a π (f i) :=by let v:Three G n→+Three G n:={ toFun:=spin a π, map_zero':= spin_zero .. , map_add':=spin_add a π }; exact map_sum v ..
open Finset
lemma step_cycle (p q:Site n)(t:Motion)(f:Goods G n):stepUp a p (stepUp t q f)=stepUp (twist a t) (affine a.1 p q) f:=by funext U; unfold stepUp; simp_rw [pull_pull,oper];rfl
lemma float_cycle (p q:Site n)(t:Motion)(f:Box n→Goods G n) : floatUp a p (floatUp t q f)=floatUp (twist a t) (affine a.1 p q) f:=by
    have he(i): sky a p (sky t q i)=sky (twist a t) (affine a.1 p q) i:=by
      simp only[shading,image_image]; apply image_congr; intro j _; change affine a.1 p (affine t.1 q j)=affine (twist a t).1 (affine a.1 p q) j; simp only [twist,affine,Signed.act_mul,Signed.act_add]; abel
    have hQ(i): puff a p (puff t q i)=puff (twist a t) (affine a.1 p q) i:= Prod.ext (he _ ) (he _)
    funext i; obtain ⟨i,rfl⟩:= (puff (twist a t) (affine a.1 p q)).surjective i -- syntax
    unfold floatUp; rw [Equiv.symm_apply_apply,← hQ, Equiv.symm_apply_apply, Equiv.symm_apply_apply,step_cycle]
variable {a} {b:Site n}
lemma Signpost.at_child {Q':Three G n} (hp : Signpost R a (affine a.1 y x) P Q') (h:Signpost R (1,false) x P Q):Signpost R a y Q Q':=by
    have hb : twist a (1,false)= a :=by rcases a with ⟨a,_|_⟩ <;> simp [twist]
    exact ⟨by rw [hp.trade,h.trade,step_cycle,hb],by rw [hp.gate,h.gate,step_cycle,hb],by rw [hp.lens,h.lens,float_cycle,hb]⟩
set_option quotPrecheck false
local notation "ζ"=> C.side m p
local notation "Z"=> C.path.rep N p m
local notation "Y"=> C.path.rep N p (m+1)
local notation "K"=>C.path.levels.clock.op m p
local notation "ψ"=> (K).ratio
variable (h:C.Makes)
include h
lemma signpost_use (hk:m≤ N) {P:Three G (C.side m p)}(t:Motion){x:Site (C.side m p)} (η:(C.path.rep N p m).activities.Moves t.1 x)(hp: Useful (C.path.rep N p m) P): Useful (C.path.rep N p m) (spin t η P):=by
    refine ⟨MergeProof.Float.conduits t x P.2.2 hp.normK η,?_,MergeProof.tint t _ _ hp.integr⟩
    exact (MergeProof.Float.warble t C.path h.wilson hk x P.2.1 η).trans (congr_arg _ hp.read)
variable {P P':Three G (C.side (m+1) p)}{Q Q':Three G (C.side m p)} {D:GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)} {A:ℂ}
local notation "L"=> C.S.block m
lemma paid {x:Site (C.side (m+1) p)} {y b:Site (C.side m p)} (hm:m<N) (hS:SoundDoor (K) D) (hc:scalar a A = A)(hr:Ride (K) x b D A P Q e)(hP : Useful (Y) P') (hQ': Useful (Z) Q')(hh: Signpost (Y) a ((ψ).embed y) P P')(hQ:Signpost (Z) a y Q Q'):
    Ride (K) (affine a.1 ((ψ).embed y) x) (affine a.1 y b) D A P' Q' e:=by
    refine ⟨hP,hQ',?_,?_⟩
    · obtain ⟨g,hg,x,hx,hξ⟩:= hr.pays; let k:=(ψ).embed y; obtain ⟨π⟩:= (h.wilson.represents N p (m+1) hm).good.labels.moves a.1 k
      rw [hh.gate,hh.lens,hQ.lens]; exact ⟨_,hg.image _,_,(norm_scalar ..).trans_le hx, hξ.gain hS a y π hc⟩
    rw [hQ.trade,hh.trade,hr.exactStep]
    have he:=unison a C.path m N p 0 y P.1 hr.old.integr; simp only [blast,pow_zero,one_smul] at he
    rw [show (K).push _ _= stepUp a _ _ from he]; funext U; change scalar a (A*_) = A*_; rw [scalar_mul,hc];rfl
end YM.RG05Readout.View
