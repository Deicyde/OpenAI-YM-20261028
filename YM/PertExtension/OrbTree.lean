import YM.PertExtension.OrbGeometry
import Mathlib.Data.Fintype.EquivFin

/-! A rooted tree in quotient links, by walking toward the fixed origin. The
orientation section choices below are exact finite ones. No constraint on
unoriented links apart from quotient identification. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.PertExtension.Orb
open Function Set Lattice
open scoped Classical

variable {n : Side}
private def choice {α : Sort*} (p : α → Prop) (h : ∃ x,p x) := Classical.choose h

def vertex (x : Site n) : Site n := choice (fun z=> z=x ∨ z=-x) ⟨x,Or.inl rfl⟩
lemma vertex_spec (x : Site n) : vertex x=x ∨ vertex x=-x := Classical.choose_spec (p:=fun z=> z=x ∨ z=-x) ⟨x,Or.inl rfl⟩
@[simp] lemma vertex_neg (x : Site n) : vertex (-x)=vertex x := by
  unfold vertex
  congr 1
  funext z; apply propext; simp [or_comm]
@[simp] lemma vertex_vertex (x : Site n) : vertex (vertex x)=vertex x := by
  rcases vertex_spec x with e|e
  · rw [e,e]
  rw [e,vertex_neg,e]
@[simp] lemma vertex_zero : vertex (0:Site n)=0 := by have h:=vertex_spec (0:Site n); simp at h; exact h
theorem vertex_eq_iff {x : Site n} : vertex x=0 ↔ x=0 := ⟨fun h=> by
  rcases vertex_spec x with e|e
  · rw [e] at h; exact h
  apply neg_eq_zero.mp; rwa [e] at h, fun e=> by rw [e]; exact vertex_zero⟩

def eR (x : Edge (Site n)) := choice (fun z=> z=x ∨ z=reflect x) ⟨x,Or.inl rfl⟩
lemma eR_spec (x : Edge (Site n)) : eR x=x ∨ eR x=reflect x := Classical.choose_spec (p:=fun z=> z=x ∨ z=reflect x) ⟨x,Or.inl rfl⟩
@[simp] lemma eR_reflect (x : Edge (Site n)) : eR (reflect x)=eR x := by
  unfold eR
  congr 1
  funext z; apply propext; simp [or_comm]
@[simp] lemma eR_eR (x : Edge (Site n)) : eR (eR x)=eR x := by
  rcases eR_spec x with e|e
  · rw [e,e]
  rw [e,eR_reflect,e]

private def reaching (x : Site n) (k : ℕ) := ∃ v : Walk, stop x v=0 ∧ v.length=k
private lemma reaches (x : Site n) : ∃ k,reaching x k :=
  ⟨_,reverse (arrival x),by nth_rw 1 [← arrival_end x]; exact reverse_stop ..,rfl⟩
def depth (x : Site n) := Nat.find (reaches x)

@[simp] lemma depth_zero : depth (0:Site n)=0 := Nat.eq_zero_of_le_zero (Nat.find_min' _ ⟨[],rfl,rfl⟩)
lemma stop_flip (a : Site n)(w : Walk) : stop (-a) (w.map Step.rev) = -(stop a w) := by
  induction w generalizing a with
  | nil => rfl
  | cons d v ih => rw [List.map_cons,stop,stop,Step.vec_rev, ← neg_add]; exact ih _
@[simp] lemma depth_neg (x : Site n) : depth (-x)=depth x := by
  have h (x : Site n) : depth (-x) ≤ depth x := by
    obtain ⟨w,hw,hw'⟩:= Nat.find_spec (reaches x)
    exact Nat.find_min' _ ⟨w.map Step.rev,by rw [stop_flip,hw];exact neg_zero,by rw [List.length_map]; exact show _ = Nat.find _ from hw'⟩ -- w choice issue
  exact le_antisymm (h x) (by simpa using h (-x))
lemma depth_vertex (x : Site n): depth (vertex x)=depth x := by rcases vertex_spec x with h|h <;> simp [h]

def Falls (x : Site n)(d : Step) := depth (x+d.vec) < depth x
private lemma falls_some {x : Site n}(hx : x ≠ 0) : ∃ d,Falls x d := by
  obtain ⟨w,hw,hy⟩:= Nat.find_spec (reaches x)
  match w with
  | [] => exact (hx hw).elim
  | d::v =>
    have hz : depth (x+d.vec) ≤ v.length := Nat.find_min' _ ⟨v,hw,rfl⟩
    exact ⟨d,by unfold Falls; change _ < Nat.find _; rw [← hy]; simpa using Nat.lt_succ_of_le hz⟩
def down (x : Site n) := if h : x ≠ 0 then Classical.choose (falls_some h) else posDir 0
lemma down_spec {x : Site n}(h : x ≠ 0) : Falls x (down x) := by simp only [down,dif_pos h]; exact Classical.choose_spec _

lemma used_flip (d : Step) (x : Site n) : (Step.rev d).used (-x) = reflect (d.used x) := by cases d with
 | mk i h => cases h <;> simp [Step.rev,Step.used, reflect]
/-- Move off representatives by the inversion convention (orientation at fixed
sites only needed at the representative itself). -/
def move (x : Site n) : Step := if vertex x=x then down (vertex x) else Step.rev (down (vertex x))
lemma move_falls {x : Site n}(hx : x ≠ 0) : Falls x (move x) := by
  unfold move; split
  next he => rw [he]; exact down_spec hx
  next he => have ht := (vertex_spec x).resolve_left he
             rw [ht,Falls, ← depth_neg x,← depth_neg (x+_), neg_add, Step.vec_rev, neg_neg]
             exact down_spec (neg_ne_zero.mpr hx)

/-- Independent physical quotient link indices. -/
def OEdge (n : Side) := {x : Edge (Site n) // eR x=x}
deriving instance Fintype for OEdge -- may fail alias
noncomputable instance (n : Side): DecidableEq (OEdge n) := Classical.decEq _

def index (x : Edge (Site n)) : OEdge n := ⟨eR x, eR_eR x⟩
def picked (x : Site n) := index ((move x).used x)
lemma picked_rep (x : Site n) : picked x = picked (vertex x) := by
  unfold picked move; rw [if_pos (vertex_vertex _)]
  split
  next h => rw [h,h]
  next h => obtain ht := (vertex_spec x).resolve_left h
            rw [ht,vertex_neg,ht]
            have hy := show ((down (-x)).rev.used x)=reflect ((down (-x)).used (-x)) from by rw [← used_flip (down (-x)) (-x),neg_neg]
            apply Subtype.ext; exact (congr_arg eR hy).trans (eR_reflect _) -- many rewrites

def Branch (e : OEdge n) := ∃ x : Site n,x≠0 ∧ picked x=e
abbrev Cotree (n : Side) := {e : OEdge n // ¬Branch e}
abbrev Trees (n : Side) := {e : OEdge n // Branch e}

variable {K E : Type*}
section Group

variable [Group K]
/-- Combine Haar representatives for all edge orbits according to marking. -/
def splitLink (b : Trees n → K)(u : Cotree n → K) (e : OEdge n) := if h : Branch e then b ⟨e,h⟩ else u ⟨e,h⟩
def liftLinks (N : OEdge n → K): Links (Per n) K := fun e => if eR e=e then N (index e) else (N (index e))⁻¹
lemma lift_at (u : OEdge n → K) (e : OEdge n) : liftLinks u e.val=u e := by rw [liftLinks,if_pos e.property,show index e.val=e from Subtype.ext e.property]
lemma lift_flip (he : Even n.val) (u : OEdge n → K) (e : Edge (Site n)) : liftLinks u (reflect e)= (liftLinks u e)⁻¹ := by
    unfold liftLinks; simp only [eR_reflect]; rw [show index (reflect e)=index e from Subtype.ext (eR_reflect e)]
    have ht := no_fixed_edge he e
    by_cases H:eR e=e
    · simp only [H,ite_true,if_neg (Ne.symm ht)]
    simp_rw [if_neg H,if_pos ((eR_spec e).resolve_left H)]; simp
lemma index_flip (e : Edge (Site n)) (h:eR e≠ e) : index e= index (reflect e) := Subtype.ext (eR_reflect e).symm
lemma path_law (t : Site n → K)(N : OEdge n → K)(he : ∀ x,t (-x)=t x)
    (e : Edge (Site n)) : gauge t (liftLinks N) e = liftLinks (fun k=>gauge t (liftLinks N) k.val) e := by
  unfold gauge liftLinks; dsimp only [Pi.mul_apply]
  by_cases ht : eR e=e
  · simp [index, ht]
  simp only [if_neg ht,index, eR_eR, dite_true,ite_true, mul_inv_rev, inv_inv]
  have hR := (eR_spec e).resolve_left ht
  rw [show (eR e).1=(reflect e).1 from congr_arg _ hR,show (eR e).2=(reflect e).2 from congr_arg _ hR]; dsimp only [reflect]; rw [show -e.1-step e.2 + step e.2 = -e.1 by abel, he _, ← he (e.1+step e.2)]; rw [show -e.1-step e.2 = -(e.1+step e.2) from by abel,mul_assoc]

open Lattice in
/-- Walk toward the root and transport only on tree links. Implicit global
site gauge fixed at the root identity. -/
def frame (b : Trees n → K)(x : Site n) : K :=
    if hx : vertex x=0 then 1 else
      let d:=down (vertex x)
      have h : depth (vertex x + d.vec) < depth x := (down_spec hx).trans_eq (depth_vertex x)
      frame b (vertex x+d.vec) * (d.read (liftLinks (splitLink b fun _=>1)) (vertex x))⁻¹
termination_by depth x

lemma frame_rep (b : Trees n → K)(x : Site n): frame b x=frame b (vertex x) := by
  nth_rw 1 [frame]
  conv_rhs => rw [frame]
  simp
lemma frame_neg (b : Trees n → K)(x : Site n): frame b (-x)=frame b x := by rw [frame_rep b (-x),vertex_neg,← frame_rep]

abbrev links {n : Side} (b : Trees n → K)(u : Cotree n → K) : Links (Per n) K := liftLinks (splitLink b u)
abbrev aligned (b : Trees n → K)(u : Cotree n → K) := gauge (frame b) (links b u)

lemma on_path (b : Trees n → K)(u v : Cotree n → K)(x : Site n)(hx : x≠0) :
    let d:=down (vertex x)
    d.read (links b u) (vertex x)=d.read (links b v) (vertex x) := by
    intro d
    have H : index (d.used (vertex x))=picked (vertex x) := by unfold picked move; rw [if_pos (vertex_vertex _),vertex_vertex]
    have he : Branch (picked (vertex x)) := ⟨vertex x,(fun h=>hx (vertex_eq_iff.mp h)),rfl⟩
    have hh : splitLink b u (picked (vertex x))=splitLink b v (picked (vertex x)) := by simp [splitLink,he]
    dsimp only [Step.read,links,liftLinks]
    rw [H,hh]

lemma tree_mark (b : Trees n → K)(u : Cotree n → K)(x : Site n)(hx : x≠0) :
    (down (vertex x)).read (aligned b u) (vertex x)=1 := by
  let d:=down (vertex x);let v:=vertex x
  have he:=show frame b v = frame b (v+d.vec) * (d.read (links b u) v)⁻¹ from by
    rw [← frame_rep,frame, dif_neg (fun h=>hx (vertex_eq_iff.mp h))]
    simp only []; rw [on_path b _ u x hx]
  rw [aligned,Step.gauge_read]; change frame b v * _ * _ = _; rw [he]; dsimp only [v,d]; group

lemma tree_zero (he : Even n.val) (b : Trees n → K)(u : Cotree n → K)(i : Trees n) : aligned b u i.val.val=1 := by
  obtain ⟨x,hx,ht⟩:=i.property
  rw [picked_rep] at ht
  let z:=(down (vertex x)).used (vertex x)
  have hz : index z=i.val:= by dsimp only [z];rw [← ht, picked,move, if_pos (vertex_vertex _),vertex_vertex]
  have hf : aligned b u z=1 := by
    have him := tree_mark b u x hx; unfold Step.read at him; split at him <;> simpa [z] using him
  rw [aligned,links,path_law (frame b) (splitLink b u) (frame_neg b) z] at hf
  unfold liftLinks at hf
  change aligned b u _ = 1
  rw [hz] at hf; split at hf
  all_goals change gauge _ (fun q => if eR q=q then _ else _) _ = 1; simpa only [inv_eq_one] using hf

def fresh (b : Trees n → K)(u : Cotree n → K) (e : Cotree n) : K := frame b e.val.val.1 * u e * (frame b (e.val.val.1+step e.val.val.2))⁻¹
lemma alignment (he : Even n.val) (b : Trees n → K)(u : Cotree n → K) :aligned b u = links 1 (fresh b u) := by
  funext q
  dsimp only [links,aligned]
  rw [path_law (frame b) (splitLink b u) (frame_neg b) q]
  apply congr_arg (fun v=> liftLinks v q)
  funext e; change aligned b u _= _
  by_cases h:Branch e
  · rw [tree_zero he b u ⟨e,h⟩,splitLink,dif_pos h]; rfl
  simp only [aligned,links] -- fix
  rw [gauge,lift_at,splitLink,dif_neg h,splitLink,dif_neg h];rfl
end Group
section Linear
variable [AddCommGroup E][Module ℝ E]
def genJet (A : Cotree n → E) (i : OEdge n) := if h : ¬Branch i then A ⟨i,h⟩ else 0
def variation : (Cotree n → E) →ₗ[ℝ] Links (Per n) E where
  toFun A e := if eR e=e then genJet A (index e) else -(genJet A (index e))
  map_add' _ _ := by funext e; dsimp only [genJet,Pi.add_apply]; split_ifs <;> simp [add_comm]
  map_smul' _ _ := by funext e; dsimp only [genJet,Pi.smul_apply]; split_ifs <;> simp [Pi.smul_apply]

lemma variation_invert (he : Even n.val)(A : Cotree n → E) (e : Edge (Site n)) : variation A (reflect e) = - variation A e := by
  change ((if _ then _ else _) : E) = - (if _ then _ else _)
  simp_rw [eR_reflect,show index (reflect e)=index e from Subtype.ext (eR_reflect e)]
  rcases eR_spec e with h|h
  · simp only [h,if_neg (Ne.symm (no_fixed_edge he e)),ite_true]
  simp only [h,if_neg (no_fixed_edge he e),ite_true,neg_neg]
lemma variation_at (A : Cotree n → E) (e : OEdge n) : variation A e.val=genJet A e := by
  change (if _ then _ else _)= _;rw [if_pos e.property,show index e.val=e from Subtype.ext e.property]
lemma variation_branch (A : Cotree n → E) (i : Trees n) : variation A i.val.val=0 := by rw [variation_at A i.val,genJet,dif_neg (not_not.mpr i.property)]
lemma variation_others (A : Cotree n → E) (i : Cotree n) : variation A i.val.val=A i := by rw [variation_at A i.val,genJet,dif_pos i.property]

theorem curl_gap (he : Even n.val)(A : Cotree n → E)(h : Closed (variation A)) : A=0 := by
  have hf : InvLink (variation A):=by
    rintro ⟨x, i⟩
    change -(variation A (reflect (x,i)))= _; rw [variation_invert he,neg_neg]
  obtain ⟨P,hp,hm⟩:=exact_curl hf h
  have hy (x : Site n) : cash (variation A) (move x) x = P (x+(move x).vec) - P x := by
    cases he : move x with | mk i b => cases b <;> simp [cash,Step.vec,Step.used, hm,sub_add,sub_eq_add_neg,add_comm]
  have ht (x : Site n) (hx : x ≠ 0) :variation A ((move x).used x)=0:=by
    let e:=(move x).used x
    have H:=variation_branch A ⟨index e,x,hx,rfl⟩
    change variation A (eR e)=0 at H
    rcases eR_spec e with h|h <;> rw [h] at H
    · exact H
    simpa [variation_invert he] using H
  have hJ (x : Site n) : P x = 0 := by
    induction hz : depth x using Nat.strong_induction_on generalizing x with
    | _ k ih =>
      by_cases hx : x = 0
      · rw [hx,hp]
      have hE := move_falls hx
      have he := ih _ (by rwa [← hz]) (x+(move x).vec) rfl
      -- cash branch = ±0
      have hb := hy x; rw [he,zero_sub] at hb; specialize ht x hx; simp only [cash,ht,neg_zero,ite_self] at hb
      exact neg_eq_zero.mp hb.symm
  funext i; rw [← variation_others A i,hm,hJ,hJ,sub_zero];rfl
end Linear
end YM.PertExtension.Orb
