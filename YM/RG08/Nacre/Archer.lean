import YM.RG08.Nacre.Yard

/-! # Coupled normal form plus all-message lift metrics. No mass assumption on bulk arity zero.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Nacre
open Filter Function Matrix MeasureTheory Finset Lattice Exterior Wilson RG Precision Stationary Work.F05 Tree Carrel Prism Tack Camera Gallery
open Forms Rudder Anchor Isles Laurent Pert.Bulk Packets Mount Glyph Room Bloch Quarry Aggregate Steam Spar Symmetry Roost Sedan
open PowerSeries Finset.Nat
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries ENNReal Matrix.Norms.Frobenius
variable {G:Gauge}(A:Castle G)(hg:G.Simple){r e n k:ℕ}

def torque (e:ℕ):= Loop.reading (A 0 e) hg (1/2)
-- explicit action coupling by entire output Kflat. s retained. q any reader role.

def send : Castle G:=Nacre.size (torque A hg) A
private lemma honorable_meter (h:Honor G 2 (A 0 e)):Loop.Core (A 0 e) ((1/2:ℝ)*(torque A hg e)):=by
 obtain ⟨he,p,b,hp,hb,hT⟩:=h
 convert Loop.plays hg hp.le hb he hT using 1
 unfold torque Loop.reading;ring
-- For iteration, frame `Seed B (A 0 0)` and axial null props.
structure Tires (B:Bed)(A:Castle G):Prop where
 ethos:Fair A
 origin: Seed B (A 0 0)
 cure e: e≠0→Loop.Core (A 0 e) 0
lemma torque_l (hA:Fair A):prudent (torque A hg):=by
 intro i h
 by_contra ht
 rw [torque,Loop.reading,hA.rests 0 i (by simpa only [Live,zero_add,Nat.zero_le,true_and] using ht)] at h
 have he:=Loop.meter_scale (F:=(0:Wheel G)) hg 0
 simp only [zero_smul,zero_mul] at he
 exact h (by rw [he, _root_.zero_div])

private lemma meter_plus {F V: Wheel G}(h:Honor G 2 F)(hs:Honor G 2 V):Loop.measure (F+V) hg=Loop.measure F hg+Loop.measure V hg:=by
 obtain ⟨hf,s,p,hS,hP,hK⟩:=h.plus hs
 obtain ⟨hv,t,z,ht,hz,hQ⟩:=hs
 have he:=Loop.var_meter (F:=F+V) (F':=V) hg hP hz (lt_min hS ht).le (hK.mono (min_le_left ..) le_rfl (fun _=>le_rfl)) (hQ.mono (min_le_right ..) le_rfl (fun _=>le_rfl))
 rw [add_sub_cancel_right,eq_sub_iff_add_eq] at he; exact he.symm

lemma meter_galaxy {I:Type}(s:Finset I)(F:I→Wheel G)(p:I→ℝ)(ht:∀ i∈s,Honor G 2 (F i)):
 Honor G 2 (∑ i∈s,p i • F i) ∧ Loop.measure (∑ i∈s,p i • F i) hg=∑ i∈s,p i*Loop.measure (F i) hg:=by
 induction s using Finset.induction_on with
 | empty=>rw [sum_empty,sum_empty]; refine ⟨Honor.nil,?_⟩
          have he:= Loop.meter_scale (F:= (0:Wheel G)) hg 0;simpa using he
 | insert a s ha ih=>
    obtain ⟨hc,he⟩:=ih (fun i hi=>ht i (mem_insert_of_mem hi))
    have hx:= (ht a (mem_insert_self ..)).smul (p a)
    rw [sum_insert ha,sum_insert ha,meter_plus hg hx hc,he,Loop.meter_scale]; exact ⟨hx.plus hc,rfl⟩

lemma haul (B:Bed)(T:Wheel G)(hT:Seed B T)(h:Fair A)(he:A 0 0=T): Tires B (send A hg):=by
 have hq:torque A hg 0=1:=by unfold torque Loop.reading;rw [he,Loop.measured _ hg hT.main];norm_num
 have hh:=sizeable _ (torque_l A hg h) A h
 have ht : send A hg 0 0=A 0 0:=by unfold send size; simp [square,due_self]
 refine ⟨hh,(ht.trans he).symm ▸ hT,fun e hv=>?_⟩
 obtain ⟨hx,H⟩:= meter_galaxy hg (square e) (fun i=>A 0 i) (fun i=>dues (torque A hg) i 2 e) (fun i _=>h.honor 0 i)
 change Loop.measure (send A hg 0 e) hg=_ at H
 have hu:=honorable_meter (send A hg) hg (hh.honor 0 e)
 unfold torque Loop.reading at hu
 rw [H] at hu
 have hy (x):Loop.measure (A 0 x) hg=(1/2:ℝ)*torque A hg x:=by unfold torque Loop.reading;ring
 simp_rw [hy] at hu
 have hm:=reset _ hq (le_refl e)
 rw [if_neg hv] at hm
 have hR:(∑ i ∈ square e,dues (torque A hg) i 2 e*((1/2:ℝ)*torque A hg i))=0:=by
    simp_rw [mul_left_comm (dues _ _ _ _) (1/2:ℝ),←Finset.mul_sum, show (∑ i ∈ square e, dues _ i 2 e*torque A hg i)=0 from hm,mul_zero]
 rw [hR] at hu;norm_num at hu;exact hu

-- single_step(F) compatibility relevant to independent matching;
-- Ė roofs classes enforce Born etc separately.
def mapped (H:Yard G)(T:Wheel G)(V:Scroll G):Castle G:=send (sorted H V T) hg
lemma proceeds (P:Patch)(K:KernelChoices){B B₀:Bed}{Y:ChartRatio G}(F:Foyer P K B₀ B A Y)(T:Wheel G)(hT:Seed B T)(h:P.Branches K G)(H:Yard G):
 let V := -(Prism.vault G P K h A Y B₀ B); let w :=torque (sorted H V T) hg; let C :=mapped hg H T V
 ; Tires B C ∧ w 0=1 ∧ (∀ i,¬ Even i→w i=0) ∧
 (∀ e n,0<n→ demand C e n=fraction w V e n) ∧
 (∀ n e,e ≤ n→ coeff e (ratio w^2)=coeff e (1+∑ i∈(square n).erase 0,PowerSeries.X^i*(w i • ratio w^i))):=by
 intro V w C
 obtain ⟨hh,hk,hS⟩:= Sedan.harvest H P K B₀ B A Y h F T hT hg
 refine ⟨haul _ hg B T hT hh hk,?_,fun i he=>Classical.not_not.mp (fun h=>he (torque_l _ hg hh i h)),fun e n hn=>?_,fun n i hi=> ?_⟩
 · unfold w torque Loop.reading;rw [hk,Loop.measured _ hg hT.main];norm_num
 · rw [show C=Nacre.size w (sorted H V T) from rfl,sailed w (torque_l _ hg hh) _ hh _ _ hn];unfold fraction;exact Finset.sum_congr rfl fun i _=>congrArg (_ • ·) (hS i n hn)
 exact guaranteed w hi
end YM.RG08.Nacre
