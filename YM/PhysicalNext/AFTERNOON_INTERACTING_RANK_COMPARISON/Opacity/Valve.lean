import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Agreements
import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Channels
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Flux
import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Desk
import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Qualify
import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Packets
import YM.Extra.WILSON_STARTUP.Taylor
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Selection
import YM.Next.RANK.Flux.Chronicle
import YM.Next.RANK.Prepaid
import YM.Progress.STATIONARY_SCENES.Frames
import YM.Push.GRID_APPROXIMATION.AttachDefs
/-!
# Wheel with shifted stencils
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump
open Function Lattice RG Pressure Stores Tree Wilson AnalyticBridge.GaussianFieldAlignment Locations Channels
open scoped Topology BigOperators Classical
variable {c f : Side} {G : Gauge} {S : StepData c f}
abbrev Wheel (c : Side):= Signed × Site c
def meet (p q : Wheel c) : Wheel c := (p.1*q.1,affine p.1 p.2 q.2)
abbrev orient (p : Wheel c) : Equiv.Perm (Site c) := StepData.sendSites p.1 p.2
lemma together (p q : Wheel c) (i : Site c) : orient (meet p q) i=orient p (orient q i):= by
  change (p.1*q.1).act i+affine _ _ _=p.1.act (affine q.1 q.2 i)+p.2; unfold affine; rw [Signed.act_mul,Signed.act_add]; abel
lemma moving (p : Wheel c) (i j : Site c) : separation (orient p i) (orient p j)=separation i j:= Next.Rank.Thirst.s_sep ..

def gear (p : Wheel c) : Equiv.Perm (Wheel c) := (Equiv.mulLeft p.1).prodCongr (orient p)
lemma gear_turn (p q : Wheel c) : gear p q=meet p q:= rfl
lemma chain (p q : Wheel c) (i : Bond c) : sendEdge p.1 p.2 (sendEdge q.1 q.2 i)= sendEdge (meet p q).1 (meet p q).2 i:= by
  change sendEdge p.1 p.2 (((posDir i.2).rotate q.1).used (affine q.1 q.2 i.1))=_; rw [send_used, Step.rotate_mul]; exact congr_arg _ (together p q i.1).symm
lemma arc (s : Signed) (b : Site c) (i : Bond c): (sendEdge s b i).2=s.perm i.2:= by unfold sendEdge Step.used; split <;> rfl
lemma spins (p q : Wheel c) (i : PlaqAxes): PlaqAxes.rotate (meet p q).1 i=PlaqAxes.rotate p.1 (PlaqAxes.rotate q.1 i):= by
  rcases lt_or_gt_of_ne (q.1.perm.injective.ne i.property.ne) with h|h
  · apply Subtype.ext; simp only [PlaqAxes.rotate,PlaqAxes.ordered, meet,min_eq_left h.le, max_eq_right h.le]; rfl
  apply Subtype.ext; simp only [PlaqAxes.rotate,PlaqAxes.ordered, meet,min_eq_right h.le, max_eq_left h.le,Signed.mul_perm_apply]; rw [min_comm, max_comm]

def off (s : Signed) (a : Axis) {c : Side} : Site c:= if s.flip a then -step (s.perm a) else 0
lemma offset_progress (p q : Wheel c) (a : Axis) : off (meet p q).1 a (c:=c) = p.1.act (off q.1 a) + off p.1 (q.1.perm a):= by
  let s:= p.1
  unfold off meet
  simp only [Signed.mul_perm_apply,Signed.mul_flip]
  have hx:s.act (step (q.1.perm a):Site c)= ((posDir _).rotate s).vec:= (Step.vec_rotate (R:=Per c) (posDir _) _).symm
  unfold s at hx
  cases he:q.1.flip a <;> cases h:p.1.flip (q.1.perm a) <;> simp [*,posDir,Step.rotate,Step.vec]
lemma lowers (p : Wheel c) (i : Cell c) : Face.lower i p.1 p.2= orient p i.1+off p.1 i.2.val.1+off p.1 i.2.val.2:= by
  unfold Face.lower atFace orient; cases h:p.1.flip i.2.val.1 <;> cases hz:p.1.flip i.2.val.2 <;> simp [off, *, Step.rotate,Step.vec,posDir, affine] <;> rfl
lemma tracks (p q : Wheel c) (i : Cell c): Face.send p.1 p.2 (Face.send q.1 q.2 i)=Face.send (meet p q).1 (meet p q).2 i := by
  apply Prod.ext ?_ (spins .. |>.symm)
  change Face.lower _ _ _ =Face.lower i _ _; rw [lowers p,lowers (meet ..), together,offset_progress p q,offset_progress p q]
  simp only [Face.send, lowers q]
  rcases lt_or_gt_of_ne (q.1.perm.injective.ne i.2.property.ne) with h|h
  all_goals simp only [PlaqAxes.rotate,PlaqAxes.ordered,max_eq_left h.le, min_eq_right h.le, max_eq_right h.le,min_eq_left h.le]; change affine _ _ _ + off _ _+off _ _ = affine _ _ _+ _+_; simp only [affine,Signed.act_add]; abel
lemma arrives (s : Signed) (p : Patch) (a : p.Points) (t : Signed) : p.offset (s*t) a=p.offset s (p.offset t a):= Subtype.ext (Signed.act_mul ..)
lemma arrival (s : Signed) (p : Patch) (a : p.FrameTag) (t : Signed) : p.orient (s*t) a=p.orient s (p.orient t a):= by
  apply Prod.ext (arrives s p a.1 t); rfl
lemma paying (k : S.Choices) (p q : Wheel c): ticket (meet p q).1 (meet p q).2 k=ticket q.1 q.2 (ticket p.1 p.2 k):= by
  let u:=meet p q
  apply (S.withinChoice u.1 u.2).injective
  let l:=ticket p.1 p.2 k; let l':= ticket q.1 q.2 l
  have hm : S.withinChoice u.1 u.2 l'=S.withinChoice p.1 p.2 (S.withinChoice q.1 q.2 l'):= by
    refine Prod.ext ?_ ?_
    · funext i; obtain ⟨i,rfl⟩:= (orient u).surjective i
      change S.withinSites u.1 u.2 l'.1 (orient u i)=S.withinSites p.1 p.2 (S.withinSites q.1 q.2 l'.1) (orient u i)
      nth_rw 2 [together]
      change (S.withinSites _ _ _) (affine u.1 u.2 i)=(S.withinSites _ _ _) (affine p.1 p.2 (affine q.1 q.2 i)); rw [S.port_site,S.port_site,S.port_site]; exact arrival ..
    · funext i; obtain ⟨i,rfl⟩:= (StepData.sendBonds u.1 u.2).surjective i
      change S.withinBond _ _ l'.2 (sendEdge u.1 u.2 i)=S.withinBond _ _ (S.withinBond _ _ l'.2) (sendEdge u.1 u.2 i)
      rw [S.port_bond, ← chain p q i,S.port_bond,S.port_bond]; exact arrives ..
  unfold ticket; rw [Equiv.apply_symm_apply]; exact Eq.symm (hm.trans (by simp only [l,l',ticket,Equiv.apply_symm_apply]))

def inflow (S : StepData c f) (p : Wheel c) : Wheel f:= (p.1,S.ratio.embed p.2)
lemma grow (S : StepData c f) (p q : Wheel c) : inflow S (meet p q)=meet (inflow S p) (inflow S q):= Prod.ext rfl (Locations.affine_root p.1 p.2 q.2)
lemma merged (p q : Wheel c) (F : Forest S.ratio) : Locations.forest (meet p q).1 (meet p q).2 F=Locations.forest q.1 q.2 (Locations.forest p.1 p.2 F):= by
  have hx (i : Site f) : affine (meet p q).1 (S.ratio.embed (meet p q).2) i=affine p.1 (S.ratio.embed p.2) (affine q.1 (S.ratio.embed q.2) i):= by
    change orient (inflow S (meet p q)) _=_; rw [grow, together];rfl
  apply forest_cast
  · funext i; unfold Locations.forest Locations.up; dsimp only; rw [hx]; change Step.rotate _ (p.1*q.1)⁻¹=_; rw [Step.rotate_mul,mul_inv_rev]
  funext i; exact congr_arg _ (hx i)
where
  forest_cast {F H : Forest S.ratio} (h : F.up=H.up) (e : F.height=H.height): F=H := by cases F; cases H; congr
lemma marks (p q : Wheel c) (A : Stores S) : Locations.book (meet p q).1 (meet p q).2 A=Locations.book q.1 q.2 (Locations.book p.1 p.2 A):= by
  let K:=S.ratio.embed; let u:=meet p q
  have hh (i : Cell f): Face.send (meet p q).1 (K (meet p q).2) i=Face.send p.1 (K p.2) (Face.send q.1 (K q.2) i):= by
    change Face.send (inflow S (meet p q)).1 (inflow S (meet p q)).2 i = _; rw [grow]; exact (tracks (inflow S p) (inflow S q) i).symm
  unfold Locations.book; dsimp only
  congr 1 <;> ext i <;> simp only [Finset.mem_map_equiv,Equiv.symm_symm]
  · change Face.send _ _ _ ∈ _↔ Face.send _ _ _∈_; rw [hh]; exact Iff.rfl
  · exact Iff.of_eq (congr_arg (·∈A.aisles) (chain p q _).symm)
  exact Iff.of_eq (congr_arg (·∈A.flags) (together p q _))
end YM.PhysicalNext.InteractingRank.Pump
