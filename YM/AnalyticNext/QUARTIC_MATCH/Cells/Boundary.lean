import YM.Exterior.Blade

/-!
# Real-space resolution of momentum-constrained tensors

Coordinates for lifting BEFORE periodization. Use unanchored cells and translation
invariance, with decay in RELATIVE coordinates. Last-argument anchoring (hence signs of
its dual contraction) recovered just by passing to the relative coordinates. Can read
these operators without Fourier conventions: moving an argument by d means using its
actual signed *cell boundary*. Axis sorted as in `Exterior`; contractions on different
arguments commute (no total-complex sign).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.BoxChain
open Exterior Lattice Matrix Function
open scoped BigOperators

abbrev Cell (R : Type*) := Four R × Finset Axis
abbrev ArrayC (I R V : Type*) := (I → Cell R) → V

variable {R V I : Type*} [AddCommGroup R] [One R] [AddCommGroup V] [Module ℝ V]

def sign (S : Finset Axis) (i : Axis) := Exterior.parity S i ℝ
lemma sign_remove (b : Finset Axis) (i : Axis) : sign (b.erase i) i = sign b i := by
  unfold sign parity; rw [pre_lo b le_rfl]
lemma sign_insert (b : Finset Axis) (i : Axis) (hi : i∉b) : sign (insert i b) i=sign b i := by
  rw [← sign_remove, Finset.erase_insert hi]

lemma sign_sq (b : Finset Axis) (i : Axis) : sign b i * sign b i = 1 := by
  unfold sign parity; rw [← mul_pow]; simp
lemma sign_switch (b : Finset Axis) (i j : Axis) (h : i<j) (hi : i∉b) (hj : j∉b) :
    sign b i * sign (insert i b) j = -(sign b j * sign (insert j b) i) := by
  have hu := pre_hi (insert i b) h (Finset.mem_insert_self i b)
  have ht := pre_lo (insert j b) h.le
  rw [Finset.erase_insert hi] at hu; rw [Finset.erase_insert hj] at ht
  simp only [sign, parity, ← hu, ← ht]; ring
lemma sign_neg (b : Finset Axis) (i j : Axis) (h : i≠j) (hi : i∉b) (hj : j∉b) :
    sign b i * sign (insert i b) j = -(sign b j * sign (insert j b) i) := by
  rcases lt_or_gt_of_ne h with h|h
  · exact sign_switch b i j h hi hj
  rw [sign_switch b j i h hj hi, neg_neg]

def sect (i : Axis) : (Cell R → V) →ₗ[ℝ] Cell R → V where
  toFun F x := if i∈x.2 then 0 else sign x.2 i • (F (x.1-step i, insert i x.2) - F (x.1,insert i x.2))
  map_add' f g := by
    ext1 x; split <;> rename_i h <;> simp only [Pi.add_apply,h,↓reduceIte,add_zero]
    rw [← smul_add]; congr 1; abel
  map_smul' s f := by
    ext1 x; split <;> rename_i h <;>
      simp only [h, Pi.smul_apply, ↓reduceIte,smul_zero,RingHom.id_apply]
    rw [← smul_sub,smul_comm]

lemma sect_at (i : Axis) (F : Cell R → V) (x : Cell R) : sect i F x = if i∈x.2 then 0 else sign x.2 i •
    (F (x.1-step i, insert i x.2)- F (x.1,insert i x.2)) := rfl
lemma sect_twice (i : Axis) (F : Cell R → V) : sect i (sect i F)=0 := by funext x; simp_rw [sect_at]; simp
lemma sect_swap (i j : Axis) (F : Cell R → V) : sect i (sect j F)= -sect j (sect i F) := by
  by_cases h : i=j
  · rw [h,sect_twice,neg_zero]
  funext ⟨x,b⟩
  simp_rw [Pi.neg_apply,sect_at]
  by_cases hi : i∈b
  · simp [hi]
  by_cases hj : j∈b
  · simp [hj]
  simp only [hi,hj, ↓reduceIte, Finset.mem_insert,h,Ne.symm h,or_self, ← smul_sub, smul_smul]
  rw [sign_neg b i j h hi hj, neg_smul]
  congr 2
  rw [Finset.insert_comm i j b, sub_right_comm x]
  abel

/-- Cell boundary coefficient, on all ranks. -/
def rim : (Cell R → V) →ₗ[ℝ] Cell R → V := ∑ i, sect i
lemma rim_at (F : Cell R → V) (x) : rim F x = ∑ i, sect i F x := by
  simp only [rim,LinearMap.sum_apply,Finset.sum_apply]
lemma rim_twice (F : Cell R → V) : rim (rim F)=0 := by
  unfold rim
  simp_rw [LinearMap.sum_apply,map_sum]
  have he (S : Finset Axis) : ∑ i∈S, ∑ j∈S, sect i (sect j F)=0 := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S h ih =>
      rw [Finset.sum_insert h, Finset.sum_insert h, sect_twice,zero_add]
      simp_rw [Finset.sum_insert h, Finset.sum_add_distrib,ih,add_zero]
      rw [show (∑ j∈S,sect j (sect i F))=-(∑ j∈S,sect i (sect j F)) from ?_,add_neg_cancel]
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun j _ => sect_swap ..
  exact he _

section legs
variable [DecidableEq I]

def peek (l : I) (X : I → Cell R) (F : ArrayC I R V) (x : Cell R) := F (update X l x)

def lower (l : I) : ArrayC I R V →ₗ[ℝ] ArrayC I R V where
  toFun F X := rim (peek l X F) (X l)
  map_add' F D := funext fun X => congr_fun (rim.map_add (peek l X F) (peek l X D)) _
  map_smul' r F := funext fun X => congr_fun (rim.map_smul r (peek l X F)) _

lemma lower_at (l : I) (F : ArrayC I R V) (X) : lower l F X = ∑ i, sect i (peek l X F) (X l) := rim_at ..
lemma peek_lower (l : I) (F : ArrayC I R V) (X) : peek l X (lower l F) = rim (peek l X F) := by
  funext x
  change rim (peek l (update X l x) F) ((update X l x) l) = _
  rw [show peek l (update X l x) F = peek l X F by funext y; simp [peek],update_self]
lemma peek_else (i l : I) (h : i≠l) (F : ArrayC I R V) (X) : peek l X (lower i F) =
    rim (R:=R) (V:=(Cell R→V)) (fun x => peek l (update X i x) F) (X i) := by
  funext y; change lower i F (update X l y) = _
  rw [lower_at,rim_at, Finset.sum_apply, update_of_ne h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sect_at,sect_at]; unfold peek
  simp_rw [update_comm h]
  split <;> rfl

lemma lower_twice (l : I) (F : ArrayC I R V) : lower l (lower l F)=0 := by
  funext X
  change rim (peek l X (lower l F)) (X l)=_
  rw [peek_lower,rim_twice]; rfl

lemma sect_rim (f : Cell R → Cell R → V) (x y : Cell R) (i : Axis) :
    sect i (fun z => rim (f z) y) x = rim (sect i f x) y := by
  simp only [sect_at]; split_ifs
  · rw [map_zero]; rfl
  rw [map_smul, map_sub]; rfl
lemma rim_rim (f : Cell R → Cell R → V) (x y : Cell R) :
    rim (fun z => rim (f z) y) x=rim (rim f x) y := by
  rw [rim_at, rim_at f,map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => sect_rim f x y j

lemma lower_switch (i l : I) (F : ArrayC I R V) : lower l (lower i F)=lower i (lower l F) := by
  funext X; by_cases h : i=l
  · rw [h]
  change rim (peek l X (lower i F)) (X l) = _
  rw [peek_else i l h,← rim_rim]
  change _ = rim (peek i X (lower l F)) (X i)
  apply congr_arg (fun B : Cell R → V => rim B (X i)); funext y
  change _ = rim (peek l (update X i y) F) (update X i y l)
  rw [update_of_ne (Ne.symm h)]

-- Use ungraded Rank/homogeneous-on-arguments

def Rank (F : ArrayC I R V) (l : I) (r : ℕ) := ∀ X, (X l).2.card≠r → F X=0
omit [AddCommGroup R] [One R] [Module ℝ V] [DecidableEq I] in
lemma Rank.neg {F : ArrayC I R V} {l r} (h : Rank F l r) : Rank (-F) l r := by
  intro X H; simp [h X H]
omit [AddCommGroup R] [One R] [Module ℝ V] [DecidableEq I] in
lemma Rank.add {F B : ArrayC I R V} {l r} (h : Rank F l r) (g : Rank B l r) : Rank (F+B) l r := by
  intro X H; simp [h X H,g X H]
omit [AddCommGroup R] [One R] [Module ℝ V] [DecidableEq I] in
lemma Rank.sub {F B : ArrayC I R V} {l r} (h : Rank F l r) (g : Rank B l r) : Rank (F-B) l r := by
  rw [sub_eq_add_neg]; exact h.add g.neg
lemma Rank.descent {F : ArrayC I R V} {l : I} {r} (h : Rank F l (r+1)) : Rank (lower l F) l r := by
  intro X hh
  rw [lower_at]; refine Finset.sum_eq_zero fun i _ => ?_
  rw [sect_at]; split <;> rename_i hi
  · rfl
  have hp (x : Four R) : peek l X F (x,insert i (X l).2)=0 := h _ (by simp [hi,hh])
  rw [hp,hp,sub_self,smul_zero]
lemma Rank.keeps {F : ArrayC I R V} {l i r} (h : Rank F l r) (hp : l≠i) : Rank (lower i F) l r := by
  intro X hh
  have hx : peek i X F=0 := funext fun y => h _ (by simp [hp,hh])
  change rim _ _ = _; rw [hx,map_zero]; rfl
end legs
end YM.AnalyticNext.QuarticMatch.BoxChain
