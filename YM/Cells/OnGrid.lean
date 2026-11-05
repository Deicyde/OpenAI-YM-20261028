import YM.Cells.Margins
import YM.Cells.Packing



/-!
# Finer centered grid inside arbitrary tiling

Site seams too. Compare using TRUE lattice rotations. Odd small widths.
For the axis bracketing use a vertical congruence family with bias depending
on seams. Distinguish being a smaller-grid center from fitting the big cells.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Cells
open Lattice Function Set Filter MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexOrder

variable {k N p : ℕ} (S : Schedule) (h : k ≤ N) (T : Tiling (S.side N p))

abbrev span (S : Schedule) (h : k≤N) (p) := (S.toDepth h p).count.val

def biasFor : ℕ := T.kind.shift * (span S h p / 2)

def homeFor : Site (S.side N p) := fun i => T.base i + (biasFor S h T:ℕ)

/-- All small center points relative to offset `o`. -/
def onCenters (o : Site (S.side N p)) := {x | ∃ v, x=(center S p h o).copyMap v o}

/-- Native grid for contiguous component coordinates. -/
def OnGrid (a : Axis) (q : Per (S.side N p)) := ∃ z : ℤ, q = (homeFor S h T) a + ((z:ℤ):Per (S.side N p)) * (span S h p : ℕ)

lemma handy (o : Site (S.side N p)) (i : Axis) :
    let r := span S h p
    (center S p h o).coordinated 0 o i = r/2 := by
  intro r
  have hr : r/2 < r := Nat.div_lt_self (S.toDepth h p).count.property (by decide)
  have ht : r < (S.side N p).val := Tiling.narrow (center S p h o)
  unfold Tiling.coordinated
  rw [Tiling.starts_zero]; dsimp only [center]
  rw [sub_sub_cancel]; exact ZMod.val_natCast_of_lt (hr.trans ht)

lemma copy_home (o : Site (S.side N p)) (v : (center S p h o).Cell) :
    (center S p h o).copyMap v o = o+(S.toDepth h p).embed v := by
  ext1 i
  let H := center S p h o
  let r := span S h p
  have ht : o i - H.base i= ((r/2 : ℕ):Per (S.side N p)) := sub_sub_cancel ..
  have hs : H.starts v i = o i - ((r/2 : ℕ) : Per (S.side N p)) + (S.toDepth h p).embed v i := rfl
  have he : H.copyMap v o i-H.starts v i=((r/2 : ℕ) : Per (S.side N p)) := by
    rw [H.copy_formula,ht]; split
    · obtain ⟨p,hp⟩ := S.toDepth_odd h p
      have hy : r/2=p := by dsimp [r,span];omega
      change (↑r:Per _) - (↑Kind.link.shift:Per _) - _ = _
      rw [hy,show r=2*p+1 from hp]; unfold Kind.shift; push_cast; ring
    rfl
  calc
    _ = H.copyMap v o i-H.starts v i+H.starts v i := by rw [sub_add_cancel]
    _ = _ := by rw [he,hs]; change _ = o i+_; abel

lemma belongs {x : Site (S.side N p)} : x∈onCenters S h (homeFor S h T) ↔ ∀ a, OnGrid S h T a (x a) := by
  let o := homeFor S h T
  let H := center S p h o
  constructor
  · rintro ⟨v,hv⟩ a
    refine ⟨(lift (n := S.side k p) v) a,?_⟩
    rw [hv,copy_home]; unfold Ratio.embed; simp [wrap, span,mul_comm]
  intro hG
  choose z hz using fun a => hG a
  let v := wrap (S.side k p) z
  refine ⟨v,?_⟩
  rw [copy_home]
  unfold v
  rw [Ratio.embed_wrap]; ext1 i
  rw [hz]
  dsimp only [wrap]; simp [span, mul_comm]

lemma turns {x : Site (S.side N p)} (hx : x∈onCenters S h (homeFor S h T))
    (hd : span S h p ∣ T.side.val) (v : T.Cell) : T.copyMap v x∈onCenters S h (homeFor S h T) := by
  let d := span S h p
  let b := biasFor S h T
  obtain ⟨q,hq⟩ := hd
  rw [belongs]; intro i
  obtain ⟨z,hz⟩ := (belongs S h T).mp hx i
  have ho : T.starts v i=T.base i+ ((v i).val:ℕ)*((T.side.val:ℕ): Per (S.side N p)) := by
    dsimp only [Tiling.starts]; simp only [Pi.add_apply, T.mount,Nat.cast_mul]
  have hy : T.starts v i=T.base i+ ((↑((v i).val*q : ℕ)) : Per (S.side N p))*d := by
    rw [ho,hq]; push_cast; dsimp [d]; ring
  have ht := T.copy_formula v x i
  rw [hy,hz] at ht
  split_ifs at ht with he
  · have hw : T.kind.shift + 2*b = T.kind.shift*d := by
      obtain ⟨l, hl⟩ := S.toDepth_odd h p
      have hs : d/2=l := by dsimp [d,span];omega
      dsimp only [b,biasFor]
      change T.kind.shift+ 2*(T.kind.shift*(d/2))=_
      rw [hs, show d=2*l+1 from hl]; ring
    refine ⟨(((v i).val*q:ℕ):ℤ) + q - T.kind.shift - z,?_⟩
    rw [sub_eq_iff_eq_add.mp ht,hq]
    have ha := congr_arg (fun x : ℕ => (x:Per (S.side N p))) hw
    unfold homeFor; unfold d b at *
    push_cast at *
    linear_combination -ha
  refine ⟨(((v i).val*q:ℕ):ℤ)+z,?_⟩
  rw [sub_eq_iff_eq_add.mp ht]; dsimp only [homeFor]
  push_cast; unfold d; ring

-- any sufficiently interior offset can be bracketed by TWO nearby columns on
-- this axis grid. Need margin w (smaller cell) at EVERY intermediate translate.
-- no accidental data about witnesses other than that one axis changed.
lemma bracket (w : Site (S.side N p)) (hx : w∈T.margin 0 (3*span S h p)) (i : Axis) :
    let d := span S h p
    ∃ v : ℕ → Site (S.side N p), ∃ j : ℕ, j ≤ d ∧ v j=w ∧
    (∀ l ≤ d, v l ∈ T.margin 0 (2 * d)) ∧ (∀ l, l+1 ≤ d → v (l+1)=v l+step i) ∧
      (∀ l a, a≠i → v l a=w a) ∧ OnGrid S h T i (v 0 i) ∧ OnGrid S h T i (v d i) := by
  intro d
  let b := biasFor S h T
  let r := T.coordinated 0 w i
  have hr := show 3*d≤r from hx.2 i |>.1
  have ht := show r+3*d+T.kind.shift≤T.side.val from hx.2 i |>.2
  have hk : 0<d := (S.toDepth h p).count.property
  have hi : b≤d := by unfold b biasFor; change T.kind.shift*(d/2)≤_; cases T.kind <;> simp [Kind.shift,Nat.div_le_self]
  let t := r-b
  let f := t/d
  let j := t%d
  have hh : j<d := Nat.mod_lt _ hk
  have he : b+f*d+j=r := by
    rw [Nat.add_assoc, show f*d+j=t from Nat.div_add_mod' ..]; dsimp only [t];omega
  let v (l : ℕ) := update w i (T.base i+((↑(b+f*d+l): Per _)))
  have hb (s) (l : ℕ) (H : s≠i) : v l s=w s := by simp [v,H]
  have hp (l : ℕ) (hl : l ≤ d) : T.coordinated 0 (v l) i=b+f*d+l := by
    unfold v Tiling.coordinated
    rw [update_self,T.starts_zero,add_sub_cancel_left]
    have hz := T.narrow
    apply ZMod.val_natCast_of_lt; omega
  refine ⟨v,j, hh.le,?_,fun l hl => ?_, fun l hl => ?_, fun l a ha => hb a l ha, ⟨(f:ℤ),?_⟩,⟨((f+1:ℕ):ℤ),?_⟩⟩
  · have hC := T.indent 0 w i; rw [T.starts_zero] at hC
    simp_rw [v,he]; rw [show T.base i+_ = _ from hC]; exact Function.update_eq_self _ _
  · have he := hp l hl
    have hu : 2*d ≤ T.coordinated 0 (v l) i := by omega
    have hw : T.coordinated 0 (v l) i+(2*d)+T.kind.shift ≤ T.side.val := by omega
    refine ⟨fun a => ?_,fun a => ?_⟩
    · by_cases e:a=i; subst a
      · change T.kind.Strict _ (T.coordinated 0 _ i)
        cases T.kind <;> unfold Kind.Strict <;> omega
      rw [hb _ _ e]; exact hx.1 a
    by_cases e:a=i; subst a
    · exact ⟨hu,hw⟩
    have hv := hx.2 a
    rw [show T.coordinated 0 (v l) a=T.coordinated 0 w a by unfold Tiling.coordinated; rw [hb _ _ e]]
    change 3*d ≤ _ ∧ T.coordinated 0 w a+3*d+_ ≤ _ at hv; omega
  · ext1 a; by_cases hu : a=i
    · subst a; simp [v]; ring
    simp [hb a _ hu,hu]
  · simp [v,homeFor]; dsimp only [b,d];ring
  simp [v,homeFor]; dsimp only [b,d];ring
end YM.Cells
