import YM.Push.RELAY_MARK.Rising

/-!
# Spell linear samples in the polynomial conventions, BEFORE invariance

Include the restriction test at comparing different Snap orders;
this is how lower weights linearized with the *same slot* are compared
when making larger-degree products. It is not a comparison of transfers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function Set Filter MeasureTheory Wilson Lattice RG Source Source.Drops Labels
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {j d k : ℕ}


abbrev AtomAt (G : Gauge) (j : ℕ) := Taylor G j →ₗ[ℝ] ℝ

def literal (q : AtomAt G j) : Pol G := ∑ i : Fin (dim G j),
    (q (axes G j i) : ℂ) • (MvPolynomial.X ⟨j,i⟩)

lemma read_literal (q : AtomAt G j) (A : Jet G) : read A (literal q)=(q (A j):ℂ) := by
  conv_rhs => rw [← (axes G j).sum_repr (A j)]
  unfold literal
  simp only [map_sum, map_smul, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul,
    Labels.read, MvPolynomial.aeval_X, coord]
  apply Finset.sum_congr rfl; intro i _; rw [mul_comm]

lemma literal_tier (q : AtomAt G j) : literal q ∈ sector (j+2,1) := Submodule.sum_mem _ fun i _ =>
  Submodule.smul_mem _ _ (show (MvPolynomial.X ⟨j,i⟩ : Pol G)∈_ from MvPolynomial.isWeightedHomogeneous_X ℂ bidegree ⟨j,i⟩)


lemma literal_x (i : Key G) : (MvPolynomial.X i : Pol G) = literal ((axes G i.1).coord i.2) := by
  apply eval_ext
  intro A; rw [read_literal,Labels.read,MvPolynomial.aeval_X]; rfl

abbrev Pulled (G : Gauge) (d : ℕ) := Snap G d →ₗ[ℝ] ℝ

-- AtomAt is the independent real coordinates used even when the color space is trivial.
def spell (d : ℕ) (q : Pulled G d) : Pol G :=
    ∑ i : Fin (d-1), literal (j:=i.val) (q.comp (LinearMap.single ℝ (fun i : Fin (d-1) => Taylor G i.val) i))

lemma spell_reads (q : Pulled G d) (A : Jet G) : read A (spell d q)=(q (trunk d A):ℂ) := by
  rw [show trunk d A=∑ i : Fin (d-1), LinearMap.single ℝ (fun i : Fin (d-1) => Taylor G i.val) i (A i.val) by
    symm; exact (Finset.univ_sum_single (trunk d A)),
    map_sum,Complex.ofReal_sum,spell,map_sum]
  refine Finset.sum_congr rfl fun i hi => read_literal ..

lemma spell_limited (q : Pulled G d) : spell d q ∈ limited G d := by
  unfold spell; apply Submodule.sum_mem; intro i _
  exact sector_limited (i.val+2,1) (by change i.val+2≤d; have := i.isLt; omega) (literal_tier _)
lemma spell_slot (q : Pulled G d) : spell d q∈floorSlots 1 := by
  unfold spell; apply Submodule.sum_mem; intro i _
  exact slot_sector (i.val+2,1) (literal_tier (j:=i.val) _)

def spellMap (G : Gauge) (d : ℕ) : Pulled G d →ₗ[ℝ] Pol G where
  toFun := spell d
  map_add' p q := eval_ext _ _ (fun A => by simp [spell_reads])
  map_smul' c p := eval_ext _ _ (fun A => by
    simp only [spell_reads, RingHom.id_apply];
    rw [show c • spell d p=(c:ℂ) • spell d p from ?_, map_smul, spell_reads]
    · simp
    · exact (IsScalarTower.algebraMap_smul ℂ c (spell d p)).symm)

lemma spell_explicit {j : Fin (d-1)} (q : AtomAt G j.val) :
    spell d (q ∘ₗ (LinearMap.proj (φ:=fun k : Fin (d-1) => Taylor G k.val) j))=literal q := by
  apply eval_ext; intro A; rw [spell_reads,read_literal]; rfl

section Embed

variable (h : k ≤ d)

def wider : Snap G k →ₗ[ℝ] Snap G d where
  toFun x := trunk d (expand k x)
  map_add' x y := by
    funext i
    by_cases ha : i.val < k-1 <;> simp [trunk,expand,ha]
  map_smul' c x := by
    funext i
    by_cases ha : i.val < k-1 <;> simp [trunk,expand,ha]

include h

lemma longer (s : Slot) (A : Snap G k) : glow (d:=d) (wider A) s = glow A s := by
  rw [samples,samples]
  let f (j : ℕ) := Work.G03.net (expand k A j) s.plaq.val.1 s.plaq.val.2 (Work.G03.castPos s.offset) 1
  have hh : expand d (wider A) = expand k A := by
    funext j
    by_cases H : j < d-1
    · exact dif_pos H
    have he : ¬ j < k-1 := by omega
    simp [expand,H,he]
  rw [hh]; change ∑ i∈ Finset.range (d-1), f i = ∑ i∈ Finset.range (k-1), f i
  symm; exact Finset.sum_subset (Finset.range_mono (by omega)) (fun i hi hj => by
    unfold f; rw [expand, dif_neg (by simpa only [Finset.mem_range] using hj), Work.G03.net_zero])

lemma expanded (H : Hol G) (w : Point) (hp : Peg H k) (hv : Peg H d) (j : G.ColorIndex) :
    positiveLinear H d w j ∘ₗ wider=positiveLinear H k w j := by
  apply LinearMap.ext; intro A
  change linearForce H d w.w w.e.2 (wider A) j = linearForce H k w.w w.e.2 A j
  rw [force_glow _ _ _ hp,force_glow _ _ _ hv, show glow (d:=d) (wider A)=glow A from funext fun s => longer h s A]

lemma wide_atom (i : Fin (k-1)) (v : Taylor G i.val) :
    wider (d:=d) (k:=k) (LinearMap.single ℝ _ i v) = LinearMap.single ℝ _ (Fin.castLE (Nat.sub_le_sub_right h 1) i) v := by
  rcases i with ⟨i,hi⟩; funext ⟨x,hx⟩
  by_cases he : x=i
  · subst i; simp [wider,trunk,expand,hi]; symm; apply Pi.single_eq_same
  by_cases hg : x < k-1 <;> simp [wider,trunk,expand,hg,he] <;> symm <;> apply Pi.single_eq_of_ne <;> (intro hh; exact he (congr_arg Fin.val hh))

end Embed

/-- Engineering truncation of the first-order part agrees under
actual cut-extension on the same slot/force. -/
lemma cropping (h : k ≤ d) (q : Pulled G d) :
    Next.Foundations.capRead k (spell d q) = spell k (q ∘ₗ wider) := by
  classical
  rw [spell,cap_is,map_sum,spell]
  symm
  refine Finset.sum_of_injOn (Fin.castLE (Nat.sub_le_sub_right h 1)) ?_ (fun _ _ => Finset.mem_univ _) ?_ ?_
  · rintro ⟨x,hx⟩ _ ⟨y,hy⟩ _ he
    simp only [Fin.ext_iff] at *; exact he
  · intro i hi hx
    have H : k < i.val+2 := by
      rcases i with ⟨i,hi⟩
      by_contra! he
      change i+2≤k at he
      exact hx ⟨⟨i,(by omega)⟩, by simp,rfl⟩
    rw [← cap_is]
    ext b
    rw [Next.Foundations.coeff_capRead]
    split
    next hv =>
      rw [MvPolynomial.coeff_zero]
      by_contra! hb
      have he := (of_sector (i.val+2,1) _).mp (literal_tier _) hb
      rw [weight_slot] at he
      have hh := congr_arg Prod.fst he; dsimp only at hh
      omega
    simp
  intro i _
  rw [← cap_is, ← Next.Foundations.limited_cap k _ (sector_limited _ (by change i.val+2 ≤ k; have := i.isLt; omega) (literal_tier _))]
  congr 1; congr 1
  apply LinearMap.ext; intro A
  exact congr_arg q (wide_atom h i A)

lemma higher_linear (h : k≤d) (q : Pulled G d) :
    spell d q-spell k (q ∘ₗ wider) ∈ above (k,1) := by
  classical
  apply (MvPolynomial.mem_restrictSupport_iff ℂ).mpr
  intro i hi
  have hz := MvPolynomial.mem_support_iff.mp hi
  rw [MvPolynomial.coeff_sub,← cropping h, Next.Foundations.coeff_capRead] at hz
  split at hz
  next he => simp at hz
  next he =>
    have hj : 1 ≤ (weight i).2 := stamp_monotone
      (a:=(0,1)) (b:=weight i) ((MvPolynomial.mem_restrictSupport_iff ℂ).mp
        (show spell d q∈floorSlots 1 from spell_slot q) (MvPolynomial.mem_support_iff.mpr (by simpa using hz)))
    change stamp (k,1) < stamp (weight i)
    rw [Prod.Lex.lt_iff]; unfold weight at *; rw [weight_slot]; rw [weight_slot] at hj
    simp only [stamp,ofLex_toLex] at *; omega
end YM.Push.Mark
