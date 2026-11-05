import YM.RG08.Needle.Lender
/-!
# Weight/slot triangular inversion of primary jet matrix
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Needle
open RG Laurent Lattice Wilson Bloch Exterior Precision Push.AbsoluteSums Finset Function Filter Matrix Work.F08 Next.Free
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Shade Quire Source Source.Drops Labels Scores Scores.Pages Tall Vale Reflect Staffer Loom PowerSeries
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {I : Type} [Fintype I][DecidableEq I] {x : ℕ}
def hot (A:Session I)(n:ℕ) : Matrix I I ℝ:= A.map (coeff n)
lemma hot_node (P:Session I)(p:ℕ)(i j : I) : hot P p i j=coeff p (P i j):=rfl
lemma hot_mul (A B: Session I)(k): hot (A*B) k=∑ i∈wheel k,(hot A i.1)*(hot B i.2) := by ext i j; rw [hot_node,Matrix.mul_apply,map_sum]; simp_rw [PowerSeries.coeff_mul]; rw [Matrix.sum_apply]; simp_rw [Matrix.mul_apply]; exact sum_comm
lemma hot_m0 (A B: Session I): hot (A*B) 0=hot A 0*hot B 0 := by rw [hot_mul]; simp [wheel]
lemma hot_one (i : ℕ): hot (1:Session I) i=if i=0 then 1 else 0 := by ext j k; rw [hot_node,Matrix.one_apply]; split_ifs <;> simp [*,Matrix.one_apply,coeff_one]

variable {G:Gauge}{L c f p: Side}{w R A B:ℝ}{D d e j r n i k t:ℕ}{τ:ℕ}{F : Labels.Frame G d}
variable {T R':Session (Letter F)}
structure Dilation (T : Session (Letter F)) : Prop where
  stairs i b v: hot T i b v ≠ 0 → slot b ≤ slot v + i
structure Flash (L: Side)(T : Session (Letter F)) : Prop extends Dilation T where
  dollar v : hot T 0 v v=(L.val:ℝ)^(d-fee v)
  emits (u v) : u ≠ v → hot T 0 u v ≠ 0 → slot u=slot v→fee u>fee v
abbrev Loft (F:Labels.Frame G d):=Matrix (Letter F) (Letter F) ℝ
-- nil and countdown

def casc (j:Letter F):= (d-slot j)*(d+1)+fee j
lemma cascade {i j:Letter F}(h:slot i<slot j) : casc i > casc j := by
  have he:= j.bill; change fee j ≤ d at he
  have hc:= slot_le j; have hp : (d-slot j)+1 ≤ (d-slot i):= by omega
  have hv:= Nat.mul_le_mul_right (d+1) hp; unfold casc; nlinarith only [hv,he,Nat.zero_le (fee i)]
lemma cascades {i j:Letter F}(h:slot i=slot j): casc i<casc j ↔ fee i<fee j := by unfold casc; simp [h]
def insolent (F:Labels.Frame G d):ℕ:= d*(d+1)+d+1
lemma ink_well (i:Letter F): casc i< insolent F := Nat.lt_succ_of_le (Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.sub_le ..)) i.bill)
def LitP (T:Loft F): Prop:= ∀ i j,T i j≠0→ slot i≤slot j
def HollowP (T:Loft F): Prop:= LitP T ∧ ∀ i j,T i j≠0→ casc j<casc i
lemma shapeH {A:Loft F}(h:HollowP A) (n:ℕ)(i j : Letter F)(ht: (A^n) i j≠0): slot i≤slot j ∧ casc i≥ casc j+n := by
  induction n generalizing i j with
  | zero=> by_cases he:i=j; subst i; simp; simp [Matrix.one_apply,he] at ht
  | succ n ih=>
    rw [pow_succ', Matrix.mul_apply] at ht
    obtain ⟨b,hb,hA⟩:= exists_ne_zero_of_sum_ne_zero ht
    obtain ⟨hz,he⟩:=mul_ne_zero_iff.mp hA; obtain ⟨hh,H⟩:= ih b j he; have hp:=h.2 i b hz
    exact ⟨(h.1 i b hz).trans hh,by omega⟩
lemma nilP {A:Loft F}(h:HollowP A) : A^(insolent F)=0 := by ext i j; exact not_ne_iff.mp (mt (shapeH h _ i j) (fun g=> by have he:= ink_well i; omega))
def shellP (A:Loft F): Loft F := ∑ i∈range (insolent F),A^i
lemma shellP_ok {A:Loft F}(h:HollowP A): shellP A*(1-A)=1 := by unfold shellP; rw [← neg_sub A, mul_neg, geom_sum_mul,nilP h]; simp
lemma shellP_tri {A:Loft F}(h:HollowP A): LitP (shellP A) ∧ (∀ i j : Letter F, i≠ j→ shellP A i j≠0→ casc j<casc i) ∧ ∀ i:Letter F,shellP A i i=1 := by
  constructor; · intro i j he; rw [shellP,Matrix.sum_apply] at he; obtain ⟨k,hk,hk'⟩:= exists_ne_zero_of_sum_ne_zero he; exact (shapeH h k i j hk').1
  constructor
  · intro i j he hi; rw [shellP,Matrix.sum_apply] at hi
    obtain ⟨k,hk,hk'⟩:= exists_ne_zero_of_sum_ne_zero hi; cases k with
    | zero=> simp [Matrix.one_apply,he] at hk'
    | succ k=> have he:= (shapeH h _ i j hk').2; omega
  intro i; rw [shellP,Matrix.sum_apply,sum_eq_single 0]
  · simp
  · intro j _ hj; exact not_ne_iff.mp (mt (shapeH h j i i) fun P=> by omega)
  intro he; exfalso; exact he (mem_range.mpr (Nat.zero_lt_succ _))

def asset (P:Loft F) : Loft F := Matrix.diagonal fun i=>P i i
def askIT (P:Loft F): Loft F:=Matrix.diagonal fun i=> (P i i)⁻¹
def ace (P:Loft F): Loft F:= 1-P * askIT P
lemma lamp (h:Flash L T)(i:Letter F): 1≤ hot T 0 i i := by rw [h.dollar i]; exact one_le_pow₀ (by exact_mod_cast L.property)
lemma arcades (h:Flash L T) : HollowP (ace (hot T 0)) := by
  let P:=hot T 0
  have hz i : (ace P) i i=0:= by rw [ace,Matrix.sub_apply,Matrix.one_apply_eq,askIT,mul_diagonal, mul_inv_cancel₀ ((zero_lt_one.trans_le (lamp h i)).ne'),sub_self]
  have he {i j:Letter F}(hp : ace P i j≠0): P i j≠0 := by
    intro H; apply hp; by_cases ht:i=j; · subst j; exact hz _
    unfold ace; rw [Matrix.sub_apply,Matrix.one_apply_ne ht,askIT,Matrix.mul_diagonal,H,zero_mul,sub_zero]
  refine ⟨fun i j hp=> by simpa using h.stairs 0 _ _ (he hp),fun i j hx=>?_⟩
  have hp:= h.stairs 0 i j (he hx); rw [add_zero] at hp; rcases hp.eq_or_lt with hV|hV; swap; · exact cascade hV
  apply (cascades hV.symm).2; exact h.emits i j (fun he=> hx (he ▸ hz j)) (he hx) hV

lemma asset_v (h:Flash L T) : askIT (hot T 0)*asset (hot T 0)=1:= by
  ext i j; by_cases he:i=j
  · subst j; rw [askIT, diagonal_mul,asset,diagonal_apply_eq,Matrix.one_apply_eq,inv_mul_cancel₀ ((zero_lt_one.trans_le (lamp h i)).ne')]
  rw [askIT,diagonal_mul,asset,diagonal_apply_ne _ he,Matrix.one_apply_ne he,mul_zero]
lemma constit (h:Flash L T) : hot T 0= (1-ace (hot T 0))*asset (hot T 0):= by unfold ace; rw [sub_sub_cancel, Matrix.mul_assoc, asset_v h, Matrix.mul_one]
lemma inversing (h:Flash L T) : (askIT (hot T 0)*shellP (ace (hot T 0)))*hot T 0=1 := by nth_rw 3 [constit h]; rw [mul_assoc,←mul_assoc (shellP _),shellP_ok (arcades h),one_mul,asset_v h]
lemma assembles (h:Flash L T): IsUnit (hot T 0).det:= Matrix.isUnit_det_of_left_inverse (inversing h)
lemma recoupC (h: Flash L T): IsUnit T.det := by
  refine PowerSeries.isUnit_iff_constantCoeff.mpr ?_
  rw [RingHom.map_det,show constantCoeff.mapMatrix T = hot T 0 from Matrix.ext fun i j=> (coeff_zero_eq_constantCoeff_apply _).symm]; exact assembles h
lemma inclosure (h: Flash L T) : hot T⁻¹ 0=askIT (hot T 0)*shellP (ace (hot T 0)) := by
  apply left_inv_eq_right_inv _ (_root_.mul_eq_one_comm.mpr (inversing h)); rw [← hot_m0, Matrix.nonsing_inv_mul _ (recoupC h),hot_one,if_pos rfl]
end YM.RG08.Needle
