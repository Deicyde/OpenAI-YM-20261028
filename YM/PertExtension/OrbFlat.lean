import YM.PertExtension.OrbTree
import YM.Wilson.Law
import Mathlib.Data.List.Perm.Basic

/-! Nonabelian flatness check on the inversion lattice. Tori have omitted flat
holonomy saddles in naive Gaussian PT. Here even at finite regulator the
zero-energy point is unique on the tree slice, because each axial fundamental
cycle through 0 is a path between two inversion-fixed sites paired with its
reflect. -/
set_option autoImplicit false
noncomputable section
namespace YM.PertExtension.Orb
open Lattice Function Set Wilson

section Group
variable {n : Side} {K : Type*} [Group K]

local notation "block" => List.replicate
variable {U : Links (Per n) K}
private def exch (d f : Step) (x : Site n) : Prop := d.read U x * f.read U (x+d.vec) = f.read U x * d.read U (x+f.vec)
variable (closed : ∀ x i j, exch (U:=U) (posDir i) (posDir j) x)
variable (inverse : ∀ x i,(negDir i).read U (-x)=(posDir i).read U x)
variable (even : Even n.val)

private lemma exch_symm {d f : Step} (h:∀ x,exch (U:=U) d f x) : ∀ x,exch (U:=U) f d x:=fun x=>(h x).symm
private lemma exch_rev {d f : Step} (h:∀ x,exch (U:=U) d f x) (x) : exch (U:=U) d.rev f x:=by
  specialize h (x+d.rev.vec)
  unfold exch at *
  have hc (y : Site n) : y + d.rev.vec + d.vec=y:=by rw [Step.vec_rev, add_assoc,neg_add_cancel,add_zero]
  have ht (y : Site n) : d.rev.read U y= (d.read U (y+d.rev.vec))⁻¹:=by nth_rw 1 [← hc y];exact d.read_rev U _
  rw [hc] at h; rw [ht x,ht, add_right_comm x]
  calc
    _ = (d.read U (x+d.rev.vec))⁻¹ * (f.read U (x+d.rev.vec) * d.read U (x+d.rev.vec+f.vec)) * (d.read U (x+d.rev.vec+f.vec))⁻¹ := by group
    _ = _ := by rw [← h];group
include closed
private lemma exch_plus (i)(f : Step) : ∀ x, exch (U:=U) (posDir i) f x := by
  rcases f with ⟨j,h|h⟩
  · exact fun x=>closed x i j
  exact exch_symm (exch_rev fun x=>closed x j i)
private lemma exch_all (d f : Step) : ∀ x, exch (U:=U) d f x := by
  rcases d with ⟨i,h|h⟩
  · exact exch_plus closed i f
  exact exch_rev (exch_plus closed i f)
private lemma permute {a b : Walk}(h : a.Perm b) (x : Site n) : travel U x a=travel U x b ∧ stop x a=stop x b := by
  induction h generalizing x with
  | nil => simp
  | cons d h ih =>exact ⟨by rw [travel,(ih _).1];rfl,(ih _).2⟩
  | swap i j w =>
    have ht : x+j.vec+i.vec=x+i.vec+j.vec := add_right_comm ..
    exact ⟨by rw [travel,travel,travel,travel,← mul_assoc,← mul_assoc,(exch_all closed j i x),ht],by simp only [stop,ht]⟩
  | trans h h' ih ih' =>exact ⟨((ih x).1.trans (ih' x).1),((ih x).2.trans (ih' x).2)⟩

omit closed in
private lemma block_at (d : Step)(k)(x : Site n) : stop x (block k d)=x+k • d.vec := by
  induction k generalizing x with
  | zero => simp [stop]
  | succ k ih => rw [List.replicate_succ,stop,ih,add_smul,one_smul]; abel

omit closed in
private lemma go_null (x : Site n) (i) : stop x (block n.val (posDir i)) = x := by
  rw [block_at];ext j
  simp

include inverse in
omit closed in
private lemma travel_inv (w : Walk) (x : Site n) : travel U (-x) (w.map Step.rev) = travel U x w := by
  have he (x i) := inverse (-x) i; simp only [neg_neg] at he
  induction w generalizing x with
  | nil => rfl
  | cons d w ih =>
    rw [List.map_cons,travel,travel,Step.vec_rev, ← neg_add,ih]
    congr 1
    cases d with
    | mk i b => cases b; exact inverse x i; exact (he _ _).symm

include even inverse
omit closed in
private lemma unitLoop (i) : travel U 0 (block n.val (posDir i))=1 := by
  obtain ⟨k,hk⟩:= even
  let w:=block k (posDir i)
  have he : reverse w=w.map Step.rev := by simp [w,reverse]
  have hw : block n.val (posDir i)=w++w := by simp only [hk,List.replicate_add];rfl
  have hx : stop (stop (0:Site n) w) w = 0:= by rw [←stop_append,← hw,go_null]
  have h := travel_reverse w U (stop 0 w);rw [hx,he,← show -(0:Site n)=0 from neg_zero,travel_inv inverse,neg_zero] at h
  rw [hw,travel_append,h,inv_mul_cancel]

private lemma anyLoop (i) (x : Site n) : travel U x (block n.val (posDir i))=1:= by
  let w:=arrival x
  have hp := permute closed (List.perm_append_comm (l₁:=w) (l₂:=block n.val (posDir i))) 0
  simp only [travel_append,go_null,unitLoop inverse even, one_mul] at hp
  replace hp := hp.1
  change travel U 0 w * travel U (stop 0 w) _ = _ at hp
  rw [arrival_end] at hp
  exact mul_left_cancel (hp.trans (mul_one _).symm)

private def expand (n : Side) (d : Step) : Walk := if d.neg then block (n.val-1) (posDir d.dir) else [posDir d.dir]
private lemma expand_one (d : Step) (x : Site n) : travel U x (expand n d)= d.read U x ∧ stop x (expand n d) = x+d.vec := by
  rcases d with ⟨i,h|h⟩
  · exact ⟨by change _*1=_; rw [mul_one]; rfl,rfl⟩
  let y := x-step i
  have ht : y+(posDir i).vec=x:= sub_add_cancel ..
  have ha : block n.val (posDir i) = posDir i :: expand n (negDir i) := by
    nth_rw 1 [← Nat.sub_add_cancel (show 1≤n.val from n.property)]
    rw [List.replicate_succ];rfl
  have h := anyLoop closed inverse even i y; rw [ha,travel,ht] at h
  have hc := go_null y i; rw [ha,stop,ht] at hc
  exact ⟨mul_left_cancel (h.trans (mul_inv_cancel _).symm), (hc.trans (show y=x+-step i by rw [← sub_eq_add_neg] ))⟩
private lemma expanded (w : Walk)(x) : travel U x w = travel U x (w.flatMap (expand n)) ∧ stop x w = stop x (w.flatMap (expand n)) := by
  induction w generalizing x with
  | nil => exact ⟨rfl,rfl⟩
  | cons d w ih =>
    obtain ⟨ht,hs⟩:= expand_one closed inverse even d x
    simp only [List.flatMap_cons,travel,travel_append,stop,stop_append,ht,hs]; exact ⟨congr_arg _ (ih _).1,(ih _).2⟩

private def AllPlus (w : Walk) := ∀ d∈w, d.neg = false
omit closed even inverse in
private lemma countAxis {w : Walk}(ht : AllPlus w)(x : Site n) (i : Axis) : stop x w i=x i+(w.count (posDir i)) := by
  induction w generalizing x with
  | nil => simp [stop]
  | cons d w ih =>
    have hd := ht d List.mem_cons_self
    have hw (d : Step) (_ : d∈w) := ht d (List.mem_cons_of_mem _ ‹d∈w›)
    rw [stop,ih hw];change x i + d.vec i + _= _
    obtain ⟨j,b⟩:=d;change b=false at hd;subst b
    change _ + (step j : Site n) i + _=x i+_
    by_cases he:j=i
    · subst j; simp [posDir,List.count_cons_self]; abel
    simp [step_apply, Ne.symm he, posDir, he]

private lemma multiple (i)(k)(x : Site n) :
    travel U x (block (n.val*k) (posDir i))=1 ∧ stop x (block (n.val*k) (posDir i))=x := by
  induction k generalizing x with
  | zero => simp [stop,travel]
  | succ k ih => rw [Nat.mul_succ,List.replicate_add,travel_append,stop_append,(ih x).2,(ih x).1,one_mul]; exact ⟨anyLoop closed inverse even ..,go_null ..⟩
private lemma positiveLoop (w : Walk)(ht : AllPlus w)(he : stop (0:Site n) w = 0) : travel U 0 w=1 := by
  by_cases H:w=[]
  · rw [H,travel]
  obtain ⟨d,hd⟩ := List.exists_mem_of_ne_nil w H
  let i:=d.dir
  have hd : posDir i∈w := by rwa [show posDir i=d from by cases d;exact congr_arg _ (ht _ hd).symm]
  let j:= w.count (posDir i)
  have hS := countAxis ht (0:Site n) i
  have hk : n.val ∣ j := by rw [← ZMod.natCast_eq_zero_iff];rw [he] at hS;simpa only [Pi.zero_apply,zero_add] using hS.symm
  let v:= w.filter (·!=posDir i)
  have hw : w.Perm (block j (posDir i) ++ v) := by
    rw [← List.filter_beq]
    rw [List.perm_iff_count];intro a; by_cases hh : a = posDir i
    · subst a; rw [List.filter_beq]; simp [v]; apply List.count_eq_zero.mpr; simp
    have hx : posDir i ≠ a := Ne.symm hh
    rw [List.filter_beq]; simp [v,hx,hh]; apply List.count_eq_zero.mpr; simp [hx,hh]
  obtain ⟨k,hk⟩:=hk; have haj := multiple closed inverse even i k 0; rw [← hk] at haj
  have H:=permute closed hw 0
  rw [travel_append,stop_append,haj.1,haj.2,he,one_mul] at H
  rw [H.1]
  apply positiveLoop v _ H.2.symm
  intro d hd; exact ht _ (List.mem_of_mem_filter hd)
termination_by w.length
-- use termination tactic via length_filter_lt_iff_exists
-- auto?
decreasing_by
  have hh:=hw.length_eq;rw [List.length_append,List.length_replicate] at hh
  have hj : 0 < j:=List.count_pos_iff.mpr hd
  dsimp only [v,i] at *
  omega
lemma flat_all {w : Walk}(hw : stop (0:Site n) w = 0) : travel U 0 w=1 := by
  obtain ⟨h,hS⟩:= expanded closed inverse even w 0
  refine h.trans (positiveLoop closed inverse even _ ?_ (hS.symm.trans hw))
  intro d hd; obtain ⟨e,_,he⟩:=List.mem_flatMap.mp hd
  unfold expand at he; split at he
  · obtain rfl := (List.mem_replicate.mp he).elim fun _ hi=>hi
    rfl
  rw [List.mem_singleton] at he; subst d;rfl
end Group
section Eq
variable {n : Side} {K : Type*} [Group K]
variable {U : Links (Per n) K}
variable (flat : ∀ (p:Face (Per n)), faceValue U p=1)
variable (inverse : ∀ x i,(negDir i).read U (-x)=(posDir i).read U x)
variable (even : Even n.val)
private def closed_face (x : Site n)(i j : Axis)(hi : i<j)(ht : travel U x (square i j)=1) : exch (U:=U) (posDir i) (posDir j) x := by
  let a := [posDir i,posDir j];let b := [posDir j,posDir i]
  have ha :square i j=a++reverse b:=rfl
  have H : stop x a=stop x b := by dsimp [a,b,stop]; abel
  rw [ha,travel_append,H,travel_reverse] at ht; unfold exch; simpa [travel,a,b] using! (mul_inv_eq_one.mp ht)
include flat inverse even
private theorem group_equation : ∃ t : Site n→K, t 0=1 ∧ ∀ (d : Step) (x),t x*d.read U x=t (x+d.vec) := by
  have hf (x i j) : exch (U:=U) (posDir i) (posDir j) x := by
    rcases lt_trichotomy i j with hij|e|hji
    · exact closed_face x i j hij (flat (x,⟨(i,j),hij⟩))
    · subst j; rfl
    exact (show _ from (closed_face x j i hji (flat (x,⟨(j,i),hji⟩))).symm)
  refine ⟨fun x=>travel U 0 (arrival x),flat_all hf inverse even (arrival_end 0),fun d x=> ?_⟩
  let a := arrival x++[d]
  let b := arrival (x+d.vec)
  have ht : stop (0:Site n) a=stop 0 b := by dsimp only [a,b]; rw [stop_append,arrival_end,arrival_end];rfl
  have hb : stop 0 (a++reverse b)=(0:Site n) := by rw [stop_append,ht,reverse_stop]
  have he := flat_all hf inverse even hb
  rw [travel_append,ht, travel_reverse] at he
  dsimp only [a,b] at he; rw [travel_append, travel, travel, mul_one,arrival_end] at he
  exact mul_inv_eq_one.mp he
end Eq

section Physical
variable {G : Gauge} {n : Side}
open scoped Matrix.Norms.Frobenius
lemma flat_unique (even : Even n.val) {u : Cotree n → G.El} (he : energy (links 1 u)=0) : u=1 := by
  let U := links 1 u
  have hf (p : Face (Per n)): faceValue U p = 1 := by
    have ht := (Finset.sum_eq_zero_iff_of_nonneg (fun q (_:q∈Finset.univ)=> (G.price_range (faceValue U q)).1)).mp he p (Finset.mem_univ _)
    have hc := G.chord_price (faceValue U p); rw [ht, mul_zero] at hc; have hc : G.chord (faceValue U p)=0 := by nlinarith only [hc]
    apply G.mat_injective
    unfold Gauge.chord at hc
    rw [div_eq_zero_iff] at hc
    rcases hc with hc|hc
    · rw [norm_eq_zero,sub_eq_zero] at hc;exact hc
    exact (Real.sqrt_pos.2 (show (0:ℝ)<G.repDim from by exact_mod_cast G.dimPos)).ne' hc |>.elim
  have hx (x i) : (negDir i).read U (-x) = (posDir i).read U x := by
     change (U (reflect (x,i)))⁻¹=U (x,i); rw [show U (reflect (x,i))=(U (x,i))⁻¹ from lift_flip even ..,inv_inv]
  obtain ⟨t, ht, H⟩:= group_equation (U:=U) hf hx even
  have htP (x): t x=1:=by
    induction m : depth x using Nat.strong_induction_on generalizing x with
    | _ k ih=>
      by_cases h : x=0
      · exact h ▸ ht
      have hv := move_falls h
      have h1 := ih (depth (x+(move x).vec)) (hv.trans_eq m) (x+(move x).vec) rfl
      rw [←H] at h1
      have hZ : U ((move x).used x)=1 := by
          have hu : index ((move x).used x) = picked x:=rfl
          dsimp [U, links,liftLinks]; rw [hu]; rw [splitLink,dif_pos (show Branch (picked x) from ⟨x,h,rfl⟩)]; simp
      change _*(Step.read ..)=1 at h1
      simp [Step.read,hZ] at h1; exact h1
  funext i
  have h := H (posDir i.val.val.2) i.val.val.1
  rw [htP,htP,one_mul] at h
  change liftLinks _ i.val.val = _ at h; rw [lift_at,splitLink,dif_neg i.property] at h; exact h

lemma flat_at_zero : energy (links 1 (1:Cotree n→G.El))=0 := by
  unfold links liftLinks
  have H (x:OEdge n): splitLink (K:=G.El) 1 1 x=1:=by simp only [splitLink];split<;>rfl
  simp only [H,inv_one,ite_self]; exact (Finset.sum_eq_zero fun p (_:p∈Finset.univ) =>show G.price (faceValue (fun _ => (1:G.El)) p)=0 from by simp [faceValue,square,travel,Step.read])

end Physical
end YM.PertExtension.Orb
