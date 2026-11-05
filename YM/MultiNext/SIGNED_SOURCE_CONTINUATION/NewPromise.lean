import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Banjo
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.TownHall

set_option warningAsError false

/-!
# PMOM third clause applicable to actual fine stencil via evaluated fields

Represent with complete torus values; even though screen in V, the
promise used in Taylor really has every component with Sized.
Require the cover difference/drift estimate with polynomial reposition (doesn't
suffice just at one anchor). Derive even with periodic u via Subdivision soon.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource.Newt
open Function Filter Finset Lattice RG Wilson Labels Laurent
open Pattern Mom Banjo Lyre
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {d b : ℕ} {L M : ℝ} {P : BudgetPoint} {X : Support n} {o : Site n}

def coaster (p : Directions G n) (o : Site n) (i : Axis) (x : Cover) := p (wrap n x+o,i)
def blown (M : ℝ) (P : BudgetPoint) (L : ℝ) (d : ℕ) (o : Site n) (x : Directions G n) :=
    ∀ i, drift P.power d (M*P.threshold) L⁻¹ (coaster x o i)

lemma canal (G : Gauge) (d P : ℕ) (he : d ≤ P) : ∃ C : ℝ,1 ≤ C ∧
    ∀ (n : Side) (X : Support n) (o : Site n) (B : BudgetPoint) (L M : ℝ) (x : Directions G n),
    B.power=P → 1≤ L → 0 ≤ M → blown M B L d o x →
      Promise d (C*M) L⁻¹ B o X x := by
  obtain ⟨c,hc,h⟩:= capital (E:=G.Color) P d he
  let u := fun k : ℕ => (4:ℝ)^k
  refine ⟨c*(u P), one_le_mul_of_one_le_of_one_le hc (one_le_pow₀ (by norm_num)),fun n X o B L M x hP hL hM hX => ?_⟩
  let f := coaster x o
  let y (v : Site n) := lift (v-o)
  let g (i : Fin (d+1)) : Directions G n := fun v => if i.val < d then piece i.val (f v.2) (stamp o v.1)
    else Newt.tail d (f v.2) (y v.1)
  have hp i : drift P d (M*B.threshold) L⁻¹ (f i) := by rw [←hP]; exact hX i
  refine ⟨g,?_,?_,fun i hi => ?_⟩
  · funext i; rw [Finset.sum_apply,Fin.sum_univ_castSucc]
    simp only [g, Fin.val_castSucc, Fin.val_last, lt_self_iff_false, if_false,y,Newt.tail]
    rw [Finset.sum_congr rfl (g:=fun j : Fin d => piece j.val (f i.2) (stamp o i.1)) (fun j _ => if_pos j.isLt),
      Fin.sum_univ_eq_sum_range (fun j => piece j (f i.2) (stamp o i.1)) d]
    unfold f coaster stamp Newt.take; rw [wrap_lift]; simp
  · intro i; refine ⟨by have hc' : 0 ≤ c := zero_le_one.trans hc; unfold u; positivity, fun j => ?_⟩
    have hz := h _ _ hL (mul_nonneg hM B.threshold_pos.le) (f j.2) (hp j.2) (y j.1)
    have hT (k : ℕ) : c*(M*B.threshold)*L⁻¹^(1+k)*(1+(size (y j.1):ℝ))^P ≤ c*u P*M*L⁻¹^(k+1)*Lyre.width B o j := by
      rw [Lyre.width,hP]
      let t : ℝ := separation j.1 o
      have hh : (size (y j.1):ℝ) ≤ 4*t := by
        unfold size; push_cast
        refine le_trans (sum_le_sum (g:=fun _ => t) (fun k _ => ?_)) ?_
        · unfold y t; exact_mod_cast component_le (j.1-o) k
        rw [sum_const,card_univ,nsmul_eq_mul,show Fintype.card Axis=4 by rfl]; norm_num
      have hh' : (1+(size (y j.1):ℝ))^P ≤ u P*(1+t)^P := by
        unfold u; rw [← mul_pow]; gcongr; linarith
      rw [Nat.add_comm 1]
      have hz' e : 0≤ c*(M*B.threshold)*L⁻¹^e := mul_nonneg (mul_nonneg (zero_le_one.trans hc) (mul_nonneg hM B.threshold_pos.le)) (pow_nonneg (by positivity) e)
      refine (mul_le_mul_of_nonneg_left hh' (hz' _)).trans_eq ?_
      unfold t; ring
    unfold g; split <;> rename_i hi
    · exact (hz.1 _ hi).trans (hT _)
    · have ht : i.val=d := by have hb := i.isLt; omega
      apply hz.2.trans
      rw [ht]; exact hT _

  let a (x : Axis) := Newt.piece i.val (f x)
  refine Exists.intro a ⟨fun k => ?_,fun j => ?_⟩
  · simpa using Newt.housed (f _) i.val
  rw [Mom.screen_at]; split; rw [show g i j=_ from if_pos hi]; rfl
end YM.MultiNext.SignedSource.Newt
