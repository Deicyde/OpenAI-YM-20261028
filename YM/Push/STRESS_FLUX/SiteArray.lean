import YM.Next.EXTRACTION.Tails
import YM.Work.B04
import YM.Work.B06

/-!
Aligned **site**-seam arrays for simultaneous root and exterior budgets.

Margin is measured in native fine spacings, using Cells.Tiling.margin
(site walls themselves excluded even at zero margin).

Origins of allowed
seams are exactly aligned to a sub-grid; first find arbitrary offsets with
room to spare, then round down.

Keep the reflection orientation on recentering
and pay for transformed labels of every exterior, not just the unreflected ones.

No platform/field transfer estimate is
invoked off its own hierarchy here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux.SiteArray
open Lattice Wilson Extraction Cells Function Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {n : Side} {k N p : ℕ} (T : Tiling n) (D : ℕ)

def aligned (D : ℕ) (o : Site n) := ∀ i, D ∣ (o i).val

def floor (D : ℕ) (o : Site n) : Site n := fun i => (((o i).val / D * D : ℕ) : Per n)

lemma aligned_floor (o : Site n) : aligned D (floor D o) := by
  intro i; rw [floor,ZMod.val_natCast_of_lt ((Nat.div_mul_le_self _ _).trans_lt (ZMod.val_lt (o i)))]
  exact dvd_mul_left ..

lemma aligned_starts {D : ℕ} (h : aligned D T.base) (ht : D ∣ T.side.val) (v : T.Cell) : aligned D (T.starts v) := by
  have hn : D ∣ n.val := by rw [T.units.exact_size]; exact ht.trans (dvd_mul_left ..)
  intro i
  rw [Tiling.starts,Pi.add_apply,T.mount,ZMod.val_add,ZMod.val_natCast]
  exact (Nat.dvd_mod_iff hn).2 (dvd_add (h i) ((Nat.dvd_mod_iff hn).2 (ht.trans (dvd_mul_left ..))))

lemma keep {D K : ℕ} (hd : 0 < D) (hk : D ≤ K) (v : T.Cell) {y : Site n} (hy : y ∈ T.margin v (2*K)) :
    y ∈ (T.newly (floor D T.base)).margin v K := by
  let V := T.newly (floor D T.base)
  have he i : V.coordinated v y i = T.coordinated v y i + (T.base i).val % D := by
    have hr := (hy.2 i).2; have hb := Nat.mod_lt (T.base i).val hd
    rw [← ZMod.val_natCast_of_lt (n := n.val) (show T.coordinated v y i + (T.base i).val % D < n.val by have := T.narrow; omega)]
    apply congr_arg ZMod.val
    have ha : T.base i = floor D T.base i + (((T.base i).val % D : ℕ) : Per n) := by
      rw [floor,← Nat.cast_add,show (T.base i).val / D * D + (T.base i).val % D = (T.base i).val from Nat.div_add_mod' .., ZMod.natCast_zmod_val]
    rw [Nat.cast_add, Tiling.coordinated, ZMod.natCast_zmod_val]
    change y i - (floor D T.base i + T.units.root v i) = y i - (T.base i + T.units.root v i) + _
    conv_rhs => lhs; rw [ha]
    abel
  have ht i : K ≤ V.coordinated v y i ∧ V.coordinated v y i + K + V.kind.shift ≤ V.side.val := by
    rw [he]; have := hy.2 i; have := Nat.mod_lt (T.base i).val hd
    change _ ∧ _ + K + T.kind.shift ≤ T.side.val; omega
  refine ⟨fun i => ?_,ht⟩
  change V.kind.Strict V.side.val (V.coordinated v y i); have hh := ht i
  cases V.kind <;> unfold Kind.Strict <;> omega

lemma positions {D K m : ℕ} (hd : 0 < D) (ht : D ∣ T.side.val) (hk : D ≤ K) (hr : (m+1)*(2*(2*K)) < T.side.val)
    (y : Fin (m+1) → Site n) (hy : ∀ i j, i≠j → T.side.val < separation (y i) (y j)) : ∃ o : Site n, aligned D o ∧
    ∃ g : Fin (m+1) → T.Cell, Injective g ∧ g 0=0 ∧ ∀ i, y i∈(T.newly o).margin (g i) K := by
  obtain ⟨o,ho⟩ := T.fits_together y (2*K) (by omega) hr
  let X := T.newly o
  let V := X.newly (floor D o)
  let a i := X.which (y i)
  let g i := a i - a 0
  have hb i : y i ∈ V.margin (a i) K := keep X hd hk _ (ho i)
  refine ⟨V.starts (a 0),aligned_starts V (aligned_floor D o) ht _, g,fun i j hh => ?_,sub_self _,fun i => ?_⟩
  · by_contra h
    have hp := (hy i j h).not_ge
    have he : a j = a i := (sub_left_inj.mp hh).symm
    exact hp (V.extent (hb i).1 (he ▸ (hb j).1))
  change y i∈(V.newly _).margin _ _
  exact (Lease.margins V (a 0) (a i) K).symm ▸ hb i

/-- The normalized Wilson test with one central object (already a product,
 difference etc.) and arbitrary fixed-weight exterior fields. -/
def sample {m : ℕ} (F : Config G (C.side N p) → ℂ) (q : Fin m → C.book.Token) (z : Fin m → Site (C.side N p)) :=
  moment (C.beta N p) (fun U => F U * ∏ i, C.seen (q i) (z i) U)

lemma pay (H : C.Makes) {m : ℕ} {q : Fin m → C.book.Token} {A : ℝ}
    (hB : Around.imageBudget q A k N p) {D K : ℕ} {T : Tiling (C.side N p)} (hd : 0 < D)
    (ht : D ∣ T.side.val) (hk : D ≤ K) (hs : Cells.span C.S hB.1 p ∣ T.side.val) (hp : 3 * Cells.span C.S hB.1 p ≤ K)
    (hr : (m+1)*(2*(2*K)) < T.side.val) {E : ℝ} (hE : 0 ≤ E) (y : Fin (m+1) → Site (C.side N p))
    (hy : ∀ i j, i≠j → T.side.val < separation (y i) (y j)) (F : Config G _ → ℂ) (hF : ∀ o, aligned D o →
      y 0 ∈ (T.newly o).margin 0 K → Interior ((T.newly o).chamber 0) F ∧ (T.newly o).rootTest (C.beta N p) F ≤ E) :
    ‖sample F q (Fin.tail y)‖ ≤ E * A^m := by
  obtain ⟨o,ho,g,hg,h0,h⟩ := positions T hd ht hk hr y hy
  let X := T.newly o
  obtain ⟨hI,hR⟩ := hF o ho (h0 ▸ h 0)
  choose B hb hu hv using fun i : Fin m => Lease.alive (T:=X) H i (y i.succ) hB hB.1 hs
    (Lease.fewer X (g i.succ) hp (h i.succ))
  let Y := Fin.cons (α:=fun _ => Config G (C.side N p) → ℂ) F B
  have he := X.planted (seamless H N p) g hg Y (Fin.forall_fin_succ.mpr ⟨hI,fun i => hu i⟩)
  simp_rw [Fin.prod_univ_succ,h0,Y,Fin.cons_zero,Fin.cons_succ,hb] at he
  change ‖moment (C.beta N p) (fun U => X.copy (0 : X.Cell) F U * ∏ x : Fin m, C.seen (q x) (y x.succ) U)‖ ≤ X.rootTest _ F * ∏ i, X.rootTest _ (B i) at he
  simp only [Tiling.copy_zero] at he
  refine he.trans (mul_le_mul hR ?_ (Finset.prod_nonneg (fun i _ => X.root_nonneg _ _)) hE)
  simpa using Finset.prod_le_prod (s:=Finset.univ) (fun i _ => X.root_nonneg (C.beta N p) (B i)) (fun i _ => hv i)

end YM.StressFlux.SiteArray
