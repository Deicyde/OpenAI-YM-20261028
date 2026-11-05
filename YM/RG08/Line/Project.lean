import YM.RG08.Line.Palette

/-!
# Project the joint Hessian onto the rooted local slice
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Line
open Stationary Function Matrix Lattice Exterior Precision RG Tree Wilson Laurent
open scoped Matrix BigOperators Topology
private lemma shard_join (α β : Type) [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] :
    (shardX α β ℝ)ᵀ * shardX α β ℝ + (shardY α β ℝ)ᵀ * shardY α β ℝ =
      (1 : Matrix (α ⊕ β) (α ⊕ β) ℝ) := by
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;>
    simp [shardX, shardY, Matrix.mul_apply, Pi.single_apply, Matrix.one_apply, eq_comm]

variable {c f u: Side} (G : Gauge) (S : StepData c f) (F:Forest S.ratio) (b : Bed)

abbrev back := butt G c f
abbrev cap := brim G c f
include G

section simple
lemma butt_same : back G (c:=c) (f:=f) * (back G (c:=c) (f:=f)).transpose=1:= by
  rw [back,helmet_butt]; ext i j; simp [shardX, Matrix.mul_apply,Pi.single_apply,Matrix.one_apply,eq_comm]
lemma brim_same : cap G (c:=c) (f:=f) * (cap G (c:=c) (f:=f)).transpose=1:= by
  rw [cap,helmet_brim]; ext i j; simp [shardY, Matrix.mul_apply,Pi.single_apply,Matrix.one_apply,eq_comm]
lemma butt_other : back G (c:=c) (f:=f) * (cap G (c:=c) (f:=f)).transpose=0:= by
  rw [back,cap,helmet_butt,helmet_brim]; ext i j; simp [shardX,shardY,Matrix.mul_apply,Fintype.sum_sum_type]
lemma brim_other : cap G (c:=c) (f:=f) * (back G (c:=c) (f:=f)).transpose=0:= by
  rw [back,cap,helmet_brim,helmet_butt]; ext i j; simp [shardX,shardY,Matrix.mul_apply,Fintype.sum_sum_type]
open scoped Classical in
lemma butt_join : (back G (c:=c) (f:=f)).transpose * back G (c:=c) (f:=f) + (cap G (c:=c) (f:=f)).transpose * cap G (c:=c) (f:=f) = (1 : Funds (Bodies G c f)) := by
  rw [back,cap,helmet_brim,helmet_butt]
  exact shard_join (Lines G f 1) (Lines G c 0)

end simple

/-- Correcting gauge for tree+root. -/
def correct : Matrix (Lines G f 0) (Bodies G c f) ℝ :=
   patron G (padMap S) * (cap G (c:=c) (f:=f)+patron G (fixRoot S)*back G (c:=c) (f:=f))- patron G (hikeMap S F)*back G (c:=c) (f:=f)
/-- Full potential response to gauge projection. -/
def project : Matrix (Lines G f 1) (Bodies G c f) ℝ := back G (c:=c) (f:=f)-patron G (d 0 f) * correct G S F
/-- Section from the tree to joint variables. -/
def embark : Matrix (Bodies G c f) (Lines G f 1) ℝ := (back G (c:=c) (f:=f)).transpose-(cap G (c:=c) (f:=f)).transpose*patron G (fixRoot S)

lemma correctSpread : correct G S F * spreadM (G:=G) S=-1 := by
  have hx :
   back G (c:=c) (f:=f) * spreadM (G:=G) S = -patron G (d 0 f) := by
    rw [spreadM, Matrix.mul_sub, ← Matrix.mul_assoc (back G (c:=c) (f:=f)) (butt G c f)ᵀ,←Matrix.mul_assoc (back G (c:=c) (f:=f)) (brim G c f)ᵀ,butt_same,butt_other, Matrix.one_mul,Matrix.zero_mul,sub_zero,mailed_zero]
    rfl
  have hk :
   cap G (c:=c) (f:=f) * spreadM (G:=G) S = -patron G (boxMap S) := by
    rw [spreadM, Matrix.mul_sub, ← Matrix.mul_assoc (cap G (c:=c) (f:=f)) (butt G c f)ᵀ,←Matrix.mul_assoc (cap G (c:=c) (f:=f)) (brim G c f)ᵀ,brim_other,brim_same, Matrix.zero_mul,Matrix.one_mul,zero_sub,ink_box]
  rw [correct,Matrix.sub_mul]
  simp only [Matrix.mul_assoc,Matrix.add_mul,hx,hk,Matrix.mul_neg,← patron_mul, rooted_box,hike_diff S F,ink_sub,ink_id,neg_sub]
  -- simplify
  have he : -patron G (boxMap S) + (patron G (boxMap S) - patron G (baseMap S)) = -patron G (baseMap S) := by abel
  rw [he,Matrix.mul_neg, ← patron_mul]
  abel

lemma project_root : project G S F * spreadM (G:=G) S=0:= by
  rw [project,Matrix.sub_mul, Matrix.mul_assoc,correctSpread, Matrix.mul_neg,Matrix.mul_one, sub_neg_eq_add, spreadM, Matrix.mul_sub, ← Matrix.mul_assoc,←Matrix.mul_assoc (back G (c:=c) (f:=f)) (brim G c f)ᵀ,butt_same,butt_other,Matrix.one_mul,Matrix.zero_mul,sub_zero,mailed_zero]
  change -patron G (d 0 f) + patron G (d 0 f) = 0
  exact neg_add_cancel _

lemma embark_back : back G (c:=c) (f:=f) * embark G S=1 := by unfold embark; rw [Matrix.mul_sub,←Matrix.mul_assoc _ (cap G (c:=c) (f:=f))ᵀ,butt_same,butt_other,Matrix.zero_mul,sub_zero]
lemma embark_base : cap G (c:=c) (f:=f) * embark G S= -(patron G (fixRoot S)):= by unfold embark; rw [Matrix.mul_sub,←Matrix.mul_assoc _ (cap G (c:=c) (f:=f))ᵀ,brim_other,brim_same,Matrix.one_mul,zero_sub]

open scoped Classical in
lemma teamed : embark G S * project G S F = 1 + spreadM (G:=G) S * correct G S F := by
  -- minus spread*correct? ri correct=(−d c,−box c); we projected by adding spread*correct to x, so yes.
  let A:=back G (c:=c) (f:=f); let D:=cap G (c:=c) (f:=f)
  let p:= correct G S F
  have he : patron G (baseMap S)*p = D+patron G (fixRoot S)*A := by
    unfold p correct; dsimp only [D,A]
    rw [Matrix.mul_sub,←Matrix.mul_assoc,←Matrix.mul_assoc _ (patron G (hikeMap S F)), ← patron_mul, ← patron_mul,hike_base S F,base_pad,ink_zero G,ink_id,Matrix.zero_mul,Matrix.one_mul,sub_zero]
  have hL : patron G (boxMap S)*p = D+ patron G (fixRoot S) * (A - patron G (d 0 f)*p) := by
    rw [Matrix.mul_sub,←Matrix.mul_assoc,←patron_mul, rooted_box,ink_sub,Matrix.sub_mul,he]; abel
  rw [← butt_join (c:=c) (f:=f) G]
  change (Aᵀ - Dᵀ * patron G (fixRoot S))*(A - patron G (d 0 f)*p) = Aᵀ*A+Dᵀ*D + spreadM (G:=G) S*p
  rw [Matrix.sub_mul, Matrix.mul_assoc Dᵀ, show patron G (fixRoot S) * (A- patron G (d 0 f)* p) = patron G (boxMap S)*p-D from eq_sub_of_add_eq' hL.symm]
  rw [spreadM,ink_box, Matrix.sub_mul,Matrix.mul_sub Aᵀ,Matrix.mul_sub Dᵀ,mailed_zero]
  change _=Aᵀ*A+Dᵀ*D+(Aᵀ*(-patron G (d 0 f))*p - Dᵀ*patron G (boxMap S)*p)
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]; abel

lemma project_out : project G S F * embark G S=patron G (gaugePin S F):= by
  rw [project,Matrix.sub_mul,embark_back,Matrix.mul_assoc,correct,Matrix.sub_mul];
  simp only [Matrix.mul_assoc,Matrix.add_mul,embark_back,embark_base, Matrix.mul_one]
  rw [neg_add_cancel, Matrix.mul_zero, zero_sub,Matrix.mul_neg, sub_neg_eq_add, gaugePin,ink_add_general,patron_mul,ink_id]

lemma project_range : project G S F= patron G (gaugePin S F) * back G (c:=c) (f:=f)-patron G (gaugeFrame S)*(cap G (c:=c) (f:=f)+patron G (fixRoot S)*back G (c:=c) (f:=f)):=by
  rw [project,gaugePin,ink_add_general,gaugeFrame,patron_mul, patron_mul,ink_id,Matrix.add_mul,Matrix.one_mul,correct,Matrix.mul_sub,Matrix.mul_assoc,Matrix.mul_assoc]; abel

lemma front_mute : frontR G S b * spreadM (G:=G) S=0 := by
  let v:=b.metric.acts f; let a:=patron G (K v)
  let d':=patron G (d 0 f); let c':=patron G (d 0 c)
  let A:=back G (c:=c) (f:=f); let B:=cap G (c:=c) (f:=f)
  let z:=patron G (boxMap S); let M:= patron G (mean S)
  have ht : A*spreadM (G:=G) S= -d':= by
    unfold spreadM; rw [Matrix.mul_sub, ← Matrix.mul_assoc A,← Matrix.mul_assoc A (brim G c f)ᵀ, butt_same, butt_other, Matrix.one_mul, Matrix.zero_mul,sub_zero,mailed_zero]
    rfl
  have he : B*spreadM (G:=G) S= -z:= by
    unfold spreadM; rw [Matrix.mul_sub, ← Matrix.mul_assoc B,← Matrix.mul_assoc B (brim G c f)ᵀ, brim_other,brim_same, Matrix.one_mul, Matrix.zero_mul,zero_sub,ink_box]
  have hv : a*d'=0:=by unfold a d'; rw [← patron_mul,K_kills,ink_zero]
  have hh : M*d'=c'*z := by unfold M d' c' z; rw [← patron_mul,mean_diff,patron_mul]
  change (Aᵀ*a*A+S.kernel.penalty • ((-M*A+c'*B)ᵀ * (-M*A+c'*B)))*spreadM (G:=G) S = 0
  rw [Matrix.add_mul,Matrix.smul_mul,Matrix.mul_assoc ((-M*A+c'*B)ᵀ),Matrix.add_mul,Matrix.mul_assoc (-M),Matrix.mul_assoc c',ht,he,Matrix.mul_assoc _ A,ht, Matrix.mul_assoc Aᵀ]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, hh, hv, add_neg_cancel, Matrix.mul_zero, neg_zero, smul_zero, zero_add]

lemma front_fee : (embark G S)ᵀ * frontR G S b * embark G S=patron G (K (b.metric.acts f)+ S.kernel.penalty • ((probe S)ᵀ * probe S)) := by
  have hX : fortune G S * embark G S= -patron G (probe S) := by
    unfold fortune probe; rw [Matrix.add_mul,Matrix.mul_assoc (-_),Matrix.mul_assoc (patron G _),embark_back,embark_base,bondsM,ink_add_general,patron_mul,Matrix.mul_one, Matrix.mul_neg]; abel -- embark_back definally?
  unfold frontR posting
  simp only [Matrix.mul_add,Matrix.add_mul,ink_add_general,ink_factor_general,Matrix.mul_smul,Matrix.smul_mul]
  rw [patron_mul,patron_star]
  congr 1
  · simp only [← Matrix.mul_assoc]; rw [← transpose_mul]; -- rw may wrong
    rw [embark_back, Matrix.transpose_one, Matrix.one_mul,Matrix.mul_assoc,embark_back,Matrix.mul_one]
  have he : (embark G S)ᵀ * ((fortune G S)ᵀ * fortune G S) * embark G S = (fortune G S * embark G S)ᵀ*(fortune G S * embark G S):= by simp only [transpose_mul,Matrix.mul_assoc]
  rw [he,hX,transpose_neg,Matrix.neg_mul, Matrix.mul_neg,neg_neg]
end YM.RG08.Line
