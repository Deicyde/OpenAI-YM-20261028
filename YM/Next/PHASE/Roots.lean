import YM.Lane.Lease
import YM.Next.PHASE.Aligned


/-!
# A mixed two-scale chessboard estimate

T is the main array, Y an aligned subdivision used for exterior fields.
An exterior group may need several fields in the *same* cell of T.
Bound the root of that group by applying the full-array inequality in Y to
all the copies in the root. Both types of fields use the bracketing and centered
bounds, each on its own budget. All moments here are with the same Wilson law,
without absolute values inside the integral.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Phase
open Cells Lattice Extraction Extraction.Spin Wilson Function
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexOrder

variable {G : Gauge} {C : Family G} {N p : ℕ}

/-- One-field budget includes its entire oriented multiplet, in the same centered-test
and stencil-fit senses already used to price uncentered fields. -/
def Single (C : Family G) (v : C.book.Token) (A : ℝ) (k N p : ℕ) :=
  Around.imageBudget (C := C) (fun _ : Fin 1 => v) A k N p

lemma Single.moves {v : C.book.Token} {k : ℕ} {A : ℝ} (h : Single C v A k N p) (b : Frame) :
    Single C (token _ v b) A k N p := by
  refine ⟨h.1, fun i t => ?_⟩
  simp only [orientation]
  exact h.2 0 _

variable {T Y : Tiling (C.side N p)} {ι κ : Type*} [Fintype ι] [Fintype κ]

private lemma copy_prod (c : T.Cell) (F : ι → Config G (C.side N p) → ℂ) (U : Config G (C.side N p)) :
    T.copy c (fun x => ∏ i, F i x) U = ∏ i, T.copy c (F i) U := by
  classical
  by_cases h : T.hand c <;> simp [Tiling.copy,h,star_prod]

/-- Price the root of an entire exterior group, not a product of coarse-cell
one-field root assumptions. Even the empty group may be used. -/
lemma exterior_group (H : C.Makes) (yh : Y.kind=.link) (th : T.kind=.link) (offset : Y.base=T.base)
    (tiles : Y.side.val ∣ T.side.val) {b : ℕ} (hb : b ≤ N) (hf : span C.S hb p ∣ Y.side.val)
    (v : κ → C.book.Token) (x : κ → Site (C.side N p)) (o : T.Cell) (hx : ∀ i, T.which (x i) = o)
    (margins : ∀ i, Inside Y (3 * span C.S hb p) (x i))
    (sep : ∀ i j, i ≠ j → Y.side.val < separation (x i) (x j))
    (B : ℝ) (hB : 0 ≤ B) (funds : ∀ i, Single C (v i) B b N p) :
    ∃ F : Config G (C.side N p) → ℂ, T.copy o F = (fun U => ∏ i, C.seen (v i) (x i) U) ∧
      Interior (T.chamber 0) F ∧ T.rootTest (C.beta N p) F ≤ B ^ Fintype.card κ := by
  classical
  let M := 3 * span C.S hb p
  choose y hy using fun i => T.pointed o (x i)
  let f : Frame := ((way T o).1⁻¹, (way T o).2)
  let w i := token C.book (v i) f
  let g i := C.seen (w i) (y i)
  let F := fun U => ∏ i, g i U
  have Hc (i) : Interior (T.chamber 0) (g i) := by
    have hc : Inside T M (x i) := shared_inside _ _ offset yh th tiles _ _ (margins i)
    unfold Inside at hc
    rw [hx] at hc
    have hm : y i ∈ T.margin 0 M := (T.reflected_margin _ _ _).mpr ((hy i).symm ▸ hc)
    refine Around.figure H _ (w i) M (y i) hm ?_
    intro z hz a
    have hh : (z a).natAbs < span C.S hb p := ((funds i).2 0 f).2.choose_spec z hz a
    unfold M; omega
  have Hw (i) : C.ref (w i).1 ≤ N := ((funds i).2 0 f).1.choose_spec.1
  have Ht i : T.copy o (g i) = C.seen (v i) (x i) := by
    change T.copy o (C.seen (w i) (y i)) = _
    rw [Extraction.Spin.uses H T o (y i) (w i) (Hw i),hy,
      show token C.book (w i) (way T o) = v i from isotropy ..]
  refine ⟨F,funext (fun U => ?_),Interior.combines _ _ (fun i _ => Hc i),?_⟩
  · simp_rw [F,copy_prod,Ht]
  let z : T.Cell × κ → Site (C.side N p) := fun i => T.copyMap i.1 (y i.2)
  let W (i : T.Cell × κ) := token C.book (w i.2) (way T i.1)
  let c (i : T.Cell × κ) := Y.which (z i)
  have Hm (i) : Inside Y M (z i) := by
    have hi : Inside Y M (T.copyMap o (y i.2)) := by rw [hy]; exact margins _
    exact (inside_reflected T Y offset tiles th yh i.1 _ _).mpr ((inside_reflected T Y offset tiles th yh o _ _).mp hi)
  have hc : Injective c := by
    rintro ⟨s,i⟩ ⟨t,j⟩ he
    have h : T.which (z (s,i)) = T.which (z (t,j)) := shared_cell T Y offset tiles he
    have heq k i : T.which (z (k,i))=k := by
      refine T.which_chamber (T.enumerate k ((T.reflected_chamber _ o).mpr ?_))
      rw [hy, ← hx i]; exact (shared_inside T Y offset yh th tiles M _ (margins i)).1
    rw [heq,heq] at h
    subst t; congr 1; by_contra H
    have hg := (Hm (s,i)).1
    have hh := Y.extent hg (x := z (s,i)) (y := z (s,j)) (show z (s,j) ∈ Y.chamber (c (s,i)) from he ▸ (Hm (s,j)).1)
    have ht : separation (z (s,i)) (z (s,j)) = separation (x i) (x j) := by
      dsimp only [z]
      rw [separation_copy, ← separation_copy T o,hy,hy]
    exact (sep i j H).not_ge (ht ▸ hh)
  have hi (i : T.Cell × κ) : Around.imageBudget (C := C) (fun _ : Fin 1 => W i) B b N p :=
    ((funds i.2).moves f).moves (way T i.1)
  choose D hD h₁ h₂ using fun i : T.Cell × κ =>
    Lease.alive H (0 : Fin 1) (z i) (hi i) hb hf (z := c i) (Hm i)
  have he (U : Config G (C.side N p)) :
      T.fullAt (fun _ => F) U = ∏ i : T.Cell × κ, Y.copy (c i) (D i) U := by
    unfold Tiling.fullAt F
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [copy_prod]; apply Finset.prod_congr rfl; intro i _
    rw [hD]
    exact congrFun (Extraction.Spin.uses H T k (y i) (w i) (Hw i)) U
  apply le_of_pow_le_pow_left₀ (T.cells_positive.ne') (pow_nonneg hB _)
  rw [T.powering]
  change ‖moment _ (T.fullAt _)‖ ≤ _
  rw [show T.fullAt (fun _ => F)=_ from funext he]
  apply le_trans ((Y.planted (seamless H ..) _ hc D h₁).trans
    (Finset.prod_le_prod (fun i _ => Y.root_nonneg _ _) (fun i _ => h₂ i)))
  rw [Finset.prod_const,Finset.card_univ,Fintype.card_prod,pow_mul']

private lemma gather {α : Type*} [Fintype α] {U : Type*} [CommMonoid U] (f : κ → α)
    [(i : α) → Fintype {x // f x=i}] (g : κ → U) :
    (∏ i : α, ∏ j : {x // f x=i}, g j.val) = ∏ j : κ, g j := by
  have he := Equiv.prod_comp (Equiv.sigmaFiberEquiv f) g
  rw [Fintype.prod_sigma] at he; exact he



/-- Cutoff bound for main/exterior factors on coextensive coarse and fine link
 tilings, respectively. Main stays out of all other occupied coarse cells.
 Nothing is assumed about how many exterior factors a coarse cell contains. -/
theorem cutoff_bound (H : C.Makes) (yh : Y.kind=.link) (th : T.kind=.link) (offset : Y.base=T.base)
    (tiles : Y.side.val ∣ T.side.val) {k b : ℕ}
    (hk : k ≤ N) (hb : b ≤ N) (hT : span C.S hk p ∣ T.side.val) (hY : span C.S hb p ∣ Y.side.val)
    (u : ι → C.book.Token) (v : κ → C.book.Token)
    (x : ι → Site (C.side N p)) (y : κ → Site (C.side N p))
    (hx : ∀ i, Inside T (3 * span C.S hk p) (x i)) (hy : ∀ i, Inside Y (3 * span C.S hb p) (y i))
    (hs : ∀ i j, i≠j → T.side.val < separation (x i) (x j))
    (he : ∀ i j, T.side.val < separation (x i) (y j))
    (hp : ∀ i j, i≠j → Y.side.val < separation (y i) (y j))
    (A B : ℝ) (hB : 0 ≤ B) (ha : ∀ i, Single C (u i) A k N p) (hd : ∀ i, Single C (v i) B b N p) :
    ‖moment (C.beta N p) (fun U => (∏ i, C.seen (u i) (x i) U)*(∏ j, C.seen (v j) (y j) U))‖
      ≤ A ^ Fintype.card ι * B ^ Fintype.card κ := by
  classical
  let c (i) := T.which (x i)
  let e (i) := T.which (y i)
  let s := Set.range e
  let f : κ → s := Set.rangeFactorization e
  let D := Sum.elim c (fun p : s => p.val)
  letI : Fintype s := Fintype.ofFinite _
  have hi : Injective c := by
    intro i j h; by_contra w
    exact (hs i j w).not_ge (T.extent (v := c i) (hx i).1 (by rw [h]; exact (hx j).1))
  have hec i (a : s) : c i ≠ a.val := by
    obtain ⟨j,h⟩ := a.property
    rw [← h]; intro hh
    have hi := shared_inside T Y offset yh th tiles (3 * span C.S hb p) (y j) (hy j)
    exact (he i j).not_ge (T.extent (v := c i) (hx i).1 (hh ▸ hi.1))
  have hInj : Injective D := by
    rintro (i|i) (j|j) h
    · rw [hi h]
    · exact (hec i j h).elim
    · exact (hec j i h.symm).elim
    rw [Subtype.ext (show i.val = j.val from h)]
  choose F hF hr hA using fun i => Lease.alive H (0 : Fin 1) (x i)
    (q := fun _ => u i) (ha i) hk hT (z := c i) (hx i)
  choose E hE hw hg using fun i : s =>
    exterior_group (κ := {x // f x=i}) H yh th offset tiles hb hY (fun j => v j.val) (fun j => y j.val) i.val
      (fun j => congrArg Subtype.val j.property) (fun j => hy _) (fun j l h => hp _ _ (Subtype.val_injective.ne h))
      B hB (fun j => hd _)
  let V := Sum.elim F E
  let W := Sum.elim (fun _ : ι => A) (fun i : s => ∏ _j : {x // f x=i}, B)
  have ht i : T.rootTest (C.beta N p) (V i) ≤ W i := by
    rcases i with i|i
    · exact hA i
    change T.rootTest _ (E i) ≤ ∏ _j : {x // f x=i}, B
    rw [Finset.prod_const,Finset.card_univ]; exact hg i
  have hv (U : Config G (C.side N p)) :
      (∏ i, C.seen (u i) (x i) U) * (∏ j, C.seen (v j) (y j) U) = ∏ i, T.copy (D i) (V i) U := by
    rw [Fintype.prod_sum_type, ← gather f (fun j => C.seen (v j) (y j) U)]
    simp only [D,V,Sum.elim_inr,Sum.elim_inl,hE,hF]
  rw [funext hv]
  apply (le_trans <| (T.planted (seamless H ..) D hInj V (by rintro (i|i); exacts [hr _,hw _])).trans
    (Finset.prod_le_prod (fun _ _ => T.root_nonneg _ _) (fun i _ => ht i)))
  unfold W; rw [Fintype.prod_sum_type]; simp only [Sum.elim_inl,Sum.elim_inr]
  rw [gather f (fun _ => B)]; simp

end YM.Next.Phase
