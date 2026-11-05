import YM.Extraction.Held
/-!
# Propagate one cell error before *any* estimated mesh smearing

Root column touches own cell zero, other cells have own orientations.

Can take cofinal lease after family requests; no period-independent threshold
assumed for discrepancy.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extraction.Lease
open Function Set Filter Lattice Cells MeasureTheory Wilson Spin Around
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {C : Family G} {f : Order} {n : ℕ} {k N p : ℕ}

abbrev Trial (C : Family G) := (N p : ℕ) → Site (C.side N p) → Config G (C.side N p) → ℂ

/-- Demand only for *arbitrarily* fine k with tolerance fixed first. -/
def rents (F : Trial C) (y : ℕ→ℕ→ℝ) (f : Order) := ∀ j : ℕ,∀ m : ℕ,∃ k≥m, f.late fun N p =>
    ∃ h : k ≤ N,∀ T : Tiling (C.side N p), T.side.val=Cells.span C.S h p → T.kind=Kind.link →
    ∀ x∈ T.margin 0 (T.side.val/(8*(j+1))), Interior (T.chamber 0) (F N p x) ∧ T.rootTest (C.beta N p) (F N p x) ≤ y N p

private lemma swerves {n : Side} (A : Tiling n) (L i : A.Cell) : (A.newly (A.starts L)).starts (i-L) = A.starts i := by
  change (A.base+A.units.root L)+A.units.root (i-L)=A.base+ A.units.root i
  rw [map_sub]; abel
lemma margins {n : Side} (A : Tiling n) (L i : A.Cell) (k : ℕ) : (A.newly (A.starts L)).margin (i-L) k=A.margin i k := by
  simp only [Tiling.margin,Tiling.coordinated,Tiling.chamber,swerves A];rfl
lemma fewer {n : Side} (A : Tiling n) (L : A.Cell) {k i} (h : i ≤ k) : A.margin L k ⊆ A.margin L i := fun _ hv =>
    ⟨hv.1, fun j => ⟨h.trans ((hv.2 j).1), le_trans (add_le_add_left (Nat.add_le_add_left h _) _) ((hv.2 j).2)⟩⟩

lemma alive {T : Tiling (C.side N p)} {q : Fin n → C.book.Token} (H : C.Makes) (j : Fin n) (y : Site (C.side N p))
    {A : ℝ} (p' : imageBudget q A k N p) (hD : k ≤ N)
    (hp : Cells.span C.S hD p ∣ T.side.val) {z : T.Cell}
    (hz : y ∈ T.margin z (3*Cells.span C.S hD p)) : ∃ U : Config G (C.side N p) → ℂ,
    T.copy z U=C.seen (q j) y ∧ Interior (T.chamber 0) U ∧ T.rootTest (C.beta N p) U ≤ A := by
  let t := Cells.span C.S hD p
  obtain ⟨a,ha⟩ := T.pointed z y
  let B := token C.book (q j) ((way T z).1⁻¹,(way T z).2)
  have hQ : a∈T.margin 0 (3*t) := (T.reflected_margin a ..).2 (ha.symm ▸ hz)
  obtain ⟨h,hT⟩ := p'.2 j ((way T z).1⁻¹,(way T z).2)
  let U := C.seen B a
  have he : C.ref B.1≤N := h.choose_spec.1
  have Hs : ∀ z∈(C.localSection B.1).stencil, ∀ b, (z b).natAbs<t := hT.choose_spec
  refine ⟨U,(Spin.uses H T z a B he).trans ?_,figure H _ B (3*t) a hQ (fun z hz b => by have := Hs z hz b; omega),?_⟩
  · rw [ha]; simp [B]
  apply interior_from T B H hD hp A _ _ _ hQ
  · intro b; simp_rw [B,orientation]; exact (p'.2 _ _).1
  intro o ho; exact figure H _ B (2*t) o ho (fun z hz b => by have := Hs z hz b; omega)

def featuring (F : Trial C) (q : Fin n → C.book.Token) (u : Fin n) (N p : ℕ) (z : Fin n → Site (C.side N p)) :=
    moment (C.beta N p) (fun v => ∏ i : Fin n, if i=u then F N p (z u) v else C.seen (q i) (z i) v)

def gain (F : Trial C) (f : Order) (y : ℕ→ℕ→ℝ) := ∀ n (q : Fin n → C.book.Token) (u : Fin n) (δ : ℝ),0 < δ → ∃ A : ℝ, 0 ≤ A ∧
    f.late fun N p => ∀ z, (∀ i j : Fin n,i ≠ j → δ ≤ C.S.a N * separation (z i) (z j)) → ‖featuring F q u N p z‖ ≤ A*y N p

theorem take (H : C.Makes) (h : CenteredBook C f) {F : Trial C} {y : ℕ→ℕ→ℝ} (he : rents F y f) : gain F f y := by
  intro n q u δ hδ
  obtain ⟨m,hm⟩ := eventually_atTop.mp (C.S.shrinks.eventually (gt_mem_nhds hδ))
  obtain ⟨k,hk,H1⟩:=he n m
  let J := 8*(n+1)
  have hk : C.S.a k<δ:=hm k hk
  have he : ∀ᶠ j : ℕ in atTop, (3*J:ℕ)*C.S.a j ≤ C.S.a k := by
    have hu := (C.S.shrinks.const_mul ((3*J:ℕ):ℝ)).eventually (ge_mem_nhds (show ((3*J:ℕ):ℝ)*0 < C.S.a k by rw [mul_zero]; exact C.S.a_pos _))
    exact hu
  obtain ⟨j,H2,hS,A,hA,hq⟩:=((eventually_ge_atTop k).and (he.and ((image_ q h).2))).exists
  let p (s : Fin n) := if s=u then (1:ℝ) else A
  let Z := ∏ s ∈ Finset.univ.erase u,p s
  refine ⟨Z,Finset.prod_nonneg (fun k _ => by unfold p; split <;> linarith),?_⟩
  unfold Order.late at H1 hq ⊢
  filter_upwards [H1,hq] with r hr ht
  filter_upwards [hr,ht] with N hv hx z hdist
  obtain ⟨Hk,o⟩:=hv
  let D := f.mesh N; let Q:=f.per r
  let B := C.side D Q
  let U := y D Q
  let T := center C.S Q Hk 0
  let L := T.side.val
  let d := Cells.span C.S hx.1 Q
  let β := C.beta D Q
  have hd : 0<d := (C.S.toDepth hx.1 Q).count.property
  have hl : 0<L := T.side.property
  have hs : C.S.a D * d = C.S.a j := C.S.embeds_scale (C.S.toDepth hx.1 Q)
  have he : C.S.a D * L=C.S.a k := C.S.embeds_scale (C.S.toDepth Hk Q)
  have hb : 3*d ≤ L/J := by
    apply (Nat.le_div_iff_mul_le (show 0<J by unfold J;omega)).2
    apply (Nat.cast_le (α:=ℝ)).1; apply le_of_mul_le_mul_left _ (C.S.a_pos D)
    rw [he]; rw [← hs] at hS
    push_cast at *; linarith
  have hp : n*(2*(L/J))<L := by
    have hP := Nat.mul_div_le L J
    have ht : 2*n < J := by dsimp [J]; omega
    nlinarith
  obtain ⟨i,hi⟩ := T.fits_together z (L/J) (by omega) hp
  let V := T.newly i
  let s := V.which (z u)
  let X := V.newly (V.starts s)
  let g (i : Fin n) := V.which (z i)-s
  have ha : X.side.val=L:=rfl
  have h0 s : z s∈X.margin (g s) (L/J) := (margins V _ _ _).symm ▸ hi s
  have hgm : Injective g := by
    intro i j hh; by_contra h
    have hp := X.extent ((h0 i).1) (show z j ∈ X.chamber (g i) from hh ▸ (h0 j).1)
    exact hk.not_ge ((hdist i j h).trans ((mul_le_mul_of_nonneg_left (show (separation (z i) (z j):ℝ) ≤ L by exact_mod_cast hp) (C.S.a_pos _).le).trans_eq he))
  have hU : g u=(0:X.Cell) := sub_self _
  choose W hw hh hT using fun i : Fin n=> alive (T:=X) H i (z i) hx hx.1 (inherits (C:=C) H2 hx.1) (fewer X (g i) hb (h0 i))
  let Y : Fin n → Config G B → ℂ := update W u (F D Q (z u))
  have hz : z u ∈ X.margin 0 (L/J) := hU ▸ h0 u
  have hZ := o X (show X.side.val=_ from rfl) (show X.kind=.link from rfl) (z u) hz
  have hg (b : Fin n) (v : Config G B) : (if b=u then F D Q (z u) v else C.seen (q b) (z b) v)= X.copy (g b) (Y b) v := by
    by_cases h : b=u; subst b; rw [hU]; simp [Y]; simp [Y,h,hw]
  have hz (i) : Interior (X.chamber 0) (Y i) := by
    by_cases h : i=u; subst i; simp only [Y,update_self]; exact hZ.1
    simp only [Y,update_of_ne h]; exact hh _
  have ha i (h : i ∈ Finset.univ.erase u) : X.rootTest β (Y i) ≤ p i := by
    have hb : i≠u := Finset.ne_of_mem_erase h
    simp only [Y,update_of_ne hb,p, if_neg hb]; exact hT i
  unfold featuring
  change ‖moment β _‖ ≤ _
  apply le_trans ?_ (mul_le_mul (Finset.prod_le_prod (fun i (_:i∈Finset.univ.erase u) => X.root_nonneg β (Y i)) ha) hZ.2
    (X.root_nonneg _ _) (by exact Finset.prod_nonneg (fun k _ => by unfold p; split <;> linarith)))
  conv_rhs => rw [show F D Q (z u) = Y u by simp [Y],Finset.prod_erase_mul _ _ (Finset.mem_univ _)]
  change ‖moment β (fun v => ∏ b : Fin n, if b=u then F D Q _ v else C.seen (q b) (z b) v)‖ ≤ _
  simp_rw [hg]; exact X.planted (seamless H ..) g hgm Y hz
end YM.Extraction.Lease
