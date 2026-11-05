import YM.Bid.Phase


/-!
# Reflection positivity after applying any of the characters

Apply the character to the *whole* quadratic expression (built from
whole words). Though factored at the level of CLMs between Hilbert spaces
of the unselected state, the positivity test has to work on the character's
subalgebra. Use spectral permanence. No measure-theoretic "almost all"
or choice of phase.

For RPSmear we can form just the Schwinger Hilbert space of the table and
axis in question, from the point Gram estimates. It suffices to integrate
compactly supported continuous Hilbert-valued functions into that one space,
then take another Gram form.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.B08
open Set Filter Function MeasureTheory OS OS.Ground Table Word Analysis
open scoped Topology InnerProductSpace BigOperators ComplexOrder

/-- A useful form of positivity inheritance: selfadjoint with nonnegative
spectrum also in this closed subalgebra (it has the very same spectrum),
so in particular any character value is nonnegative. -/
lemma char_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (B : StarSubalgebra ℂ (E →L[ℂ] E)) (hc : IsClosed (B : Set (E →L[ℂ] E)))
    (φ : B →⋆ₐ[ℂ] ℂ) (x : B) (hx : x.val.IsPositive) : 0 ≤ φ x := by
  haveI : IsClosed (B : Set (E →L[ℂ] E)) := hc
  have hr : φ x ∈ spectrum ℂ x := AlgHom.apply_mem_spectrum φ.toAlgHom x
  have hs := B.mem_spectrum_iff.mp hr
  exact spectrum_nonneg_of_nonneg ((ContinuousLinearMap.nonneg_iff_isPositive x.val).2 hx) hs

section Time
variable {G : Gauge} {C : Family G} {S : Table C.book} {V : Chamber S timeAxis}

private theorem timeGram (A : Spread V) (P : A.Resolution) {T : Table C.book} {α : P.X}
    (H : S.Hierarchy) (hv : Steady V) (h : P.receives T α)
    (m : ℕ) (w : Fin m → C.book.Word) (p : ∀ i, Positive (w i) timeAxis) (c : Fin m → ℂ) :
    0 ≤ ∑ i : Fin m, ∑ j : Fin m, star (c i) * c j * T.gram timeAxis (w i) (w j) := by
  let v (i : Fin m) : Future C.book timeAxis := ⟨w i, p i⟩
  let U (i : Fin m) := X A (v i)
  let b (i j : Fin m) := M A _ (twoSides (p i) (p j))
  have hb (i j : Fin m) : (b i j).val = (U i).adjoint.comp (U j) := slim A H hv (v i) (v j)
  let y : A.algebra := ∑ i : Fin m, ∑ j : Fin m, (star (c i) * c j) • b i j
  let F := ∑ i : Fin m, c i • U i
  have he : y.val = F.adjoint.comp F := by
    let q : (↥A.algebra) →ₗ[ℂ] V.VacuumOp := A.algebra.subtype.toAlgHom.toLinearMap
    have hq (i j : Fin m) : q (b i j) = (U i).adjoint.comp (U j) := hb i j
    change q _ = _
    ext1 x
    simp only [F, map_sum, map_smul, map_smulₛₗ, hq, ContinuousLinearMap.comp_apply,
      sum_apply, smul_apply, Finset.smul_sum, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    exact smul_comm (star (c j)) (c i) _
  have hpos : y.val.IsPositive := he ▸ F.isPositive_adjoint_comp_self
  have hχ := char_nonneg A.algebra isClosed_closure (P.character α) y hpos
  let f : (↥A.algebra) →ₗ[ℂ] ℂ := (P.character α).toAlgHom.toLinearMap
  change 0 ≤ f y at hχ
  have hg (i j : Fin m) : f (b i j) = T.gram timeAxis (w i) (w j) :=
    Extraction.Retain.pops A P h _ _
  simpa only [y, map_sum, map_smul, hg, smul_eq_mul] using hχ
end Time

variable {G : Gauge} {L : Register G} {T : Table L}

private lemma product_act (s t : Signed) (w : L.Word) : act (s*t) w = act s (act t w) := by
  simp only [act, List.map_map]
  congr 1; ext1 p; rcases p with ⟨x, d, v⟩
  have he : (s*t).ortho = s.ortho * t.ortho := map_mul Signed.inclusionO s t
  simp [he, Ortho.move_mul, Register.move]

private lemma commutes_conjugate (s : Signed) (w : L.Word) : conjugate (act s w) = act s (conjugate w) := by
  simp only [conjugate, act, List.map_map]
  congr 1; ext1 p; rcases p with ⟨x, d, v⟩
  simp [Register.move, Register.conjugate]

private lemma compatible (s : Signed) (a : Axis) (w : L.Word) : reflect (act s w) (s.perm a) = act s (reflect w a) := by
  have hm : Signed.mirror (s.perm a) * s = s * Signed.mirror a := by
    apply Signed.ext
    · ext i; simp [Signed.mirror]
    funext i
    by_cases h : i = a <;> cases hx : s.flip i <;> simp_all [Signed.mirror]
  rw [reflect, reflect, show (act s w).reverse = act s w.reverse from (List.map_reverse ..).symm,
    commutes_conjugate, ← product_act, hm, product_act]

private lemma acts_read (s : Signed) (H : T.RealSpin) {w : L.Word} (h : distinct w) : T.expect (act s w) = T.expect w := by
  have he : act s w = realize (L.move s ∘ tokens w) (Points.move s.ortho (positions w)) := by
    let f := fun p : L.Plant => (Ortho.move s.ortho p.1, L.move s p.2)
    have hm : (List.ofFn w.get).map f = List.ofFn (f ∘ w.get) := List.map_ofFn
    rw [List.ofFn_get] at hm; exact hm
  rw [he, T.readAt]; exact H.mirror s h _

private lemma acts_positive (s : Signed) {a : Axis} (hp : s.flip a = false)
    {w : L.Word} (h : Positive w a) : Positive (act s w) (s.perm a) := by
  constructor
  · rw [locations, show (act s w).map Prod.fst = (w.map Prod.fst).map (Ortho.move s.ortho) from by
      simp only [act, List.map_map]; rfl]
    exact (locations.mp h.1).map (Ortho.move_injective _)
  intro z hz; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
  change 0 < Ortho.move s.ortho x.1 (s.perm a); simpa [Signed.ortho_move, hp] using h.2 x hx

private theorem allGram (H : T.RealSpin)
    (h : ∀ (m : ℕ) (w : Fin m → L.Word), (∀ i, Positive (w i) timeAxis) → ∀ c : Fin m → ℂ,
      0 ≤ ∑ i : Fin m, ∑ j : Fin m, star (c i)*c j*T.gram timeAxis (w i) (w j)) : T.RP := by
  intro a m w p c
  let s : Signed := ⟨Equiv.swap a timeAxis, fun _ => false⟩
  have ha : s.perm a = timeAxis := Equiv.swap_apply_left ..
  have he (i j : Fin m) : T.gram timeAxis (act s (w i)) (act s (w j))=T.gram a (w i) (w j) := by
    unfold Table.gram
    rw [← ha, compatible, ← show act s (reflect (w i) a ++ w j) =
      act s (reflect (w i) a) ++ act s (w j) from List.map_append]
    exact acts_read s H (twoSides (p i) (p j))
  have hb := h m (fun i => act s (w i)) (fun i => ha ▸ acts_positive s rfl (p i)) c
  simpa only [he] using hb

section Tests
open Pairing
variable {a : Axis}

-- Like OS.nonnegative, but can't invoke that version since T doesn't yet
-- have a Hierarchy (in particular we don't already have RPSmear).
private lemma nnPoint (H : T.Basic) (hv : T.RealSpin) (hp : T.RP) :
    NNKernel (fun (x y : Future L a) => T.gram a x.val y.val) := by
  apply NNKernel.criterion
  · intro x y
    have he : distinct (reflect y.val a ++ x.val) := twoSides y.property x.property
    have hh (u v : L.Word) : reflect (u++v) a = reflect v a ++ reflect u a := by simp [reflectedPoint]
    change star (T.expect _) = T.expect _
    rw [← twice_expect H hv a _ he, hh, OS.reflect_twice]
  intro m x c
  have he := hp a m (fun i => (x i).val) (fun i => (x i).property) c
  exact he.trans (le_of_eq (Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => mul_right_comm _ _ _))

private lemma smeared_continuous (H : T.Symmetric) (hv : T.Smooth) (Q R : PastTest L a) :
    Continuous (T.smeared a Q R) := by
  let f := withOther Q R
  let K (x) := T.read x (tied Q.v R.v a)
  have he : Continuous (fun x : Points (Q.n+R.n) => f x * K x) := continuous_of_tsupport (by
    intro x hx
    have hm : x ∈ conf _ := f.tsupport_subset (tsupport_mul_subset_left hx)
    exact f.continuous.continuousAt.mul (((T.smooth_read hv _).continuousOn x hm).continuousAt
      ((conf_open _).mem_nhds hm)))
  have hh : T.smeared a Q R = (fun x => f x * K x) ∘ (pairIso a).symm := funext fun z =>
    (corresponding T H Q R z.1 z.2).symm
  rw [hh]; exact he.comp (pairIso a).symm.continuous

variable (Z : Schwinger T a)

open scoped Classical in
private def atWord (Q : PastTest L a) (x : Points Q.n) : Future L a :=
  if h : single x a then ⟨realize Q.v x, living Q.v h⟩ else air a

private def ket (Q : PastTest L a) (x : Points Q.n) : Z.H := Q.f x • Z.plant (atWord Q x)

private lemma ket_inner (Q R : PastTest L a) (x : Points Q.n) (y : Points R.n) :
    inner ℂ (ket Z Q x) (ket Z R y) = T.smeared a Q R (x,y) := by
  rw [ket, ket, inner_smul_left, inner_smul_right, Z.measure]
  by_cases hx : x ∈ tsupport Q.f
  swap
  · rw [Table.smeared]
    simp [image_eq_zero_of_notMem_tsupport hx]
  by_cases hy : y ∈ tsupport R.f
  swap
  · rw [Table.smeared]
    simp [image_eq_zero_of_notMem_tsupport hy]
  simp only [atWord, dif_pos (stays Q hx), dif_pos (stays R hy), smeared, mul_assoc]; rfl

private lemma ket_integrable (H : T.Symmetric) (hv : T.Smooth) (Q : PastTest L a) :
    Integrable (ket Z Q) := by
  have he := smeared_continuous H hv Q Q
  have ht : Continuous (ket Z Q) := continuous_iff_continuousAt.mpr fun x => ketC (D := Z.H) _ x
    (by simp_rw [ket_inner]; exact (he.comp (continuous_id.prodMk continuous_id)).continuousAt)
    (by simp_rw [ket_inner]; exact (he.comp (continuous_const.prodMk continuous_id)).continuousAt)
  apply ht.integrable_of_hasCompactSupport
  exact (show HasCompactSupport ((Q.f : Points Q.n → ℂ) • (Z.plant ∘ atWord Q)) from
    Q.f.hasCompactSupport.smul_right)

private lemma test_gram (H : T.Symmetric) (hv : T.Smooth) (Q R : PastTest L a) :
    (∫ z, T.smeared a Q R z) = inner ℂ (∫ x, ket Z Q x) (∫ y, ket Z R y) := by
  have hi := pairedIntegrable T H hv Q R
  change (∫ z, T.smeared a Q R z ∂(volume.prod volume)) = _
  rw [integral_prod _ hi]
  simp_rw [← ket_inner Z, integral_inner (ket_integrable Z H hv R)]
  rw [← inner_conj_symm (∫ x, ket Z Q x), ← integral_inner (ket_integrable Z H hv Q), ← integral_conj]
  simp only [inner_conj_symm]

/-- Point Gram bounds suffice also for arbitrary joint `PastTest`s with
    Basic, RealSpin and Smooth. No requirement for the rest of Hierarchy. -/
theorem smear (H : T.Basic) (hspin : T.RealSpin) (hv : T.Smooth) (hp : T.RP) : T.RPSmear := by
  constructor
  · exact fun _ Q R => pairedIntegrable T H.toSymmetric hv Q R
  intro a m w c
  let Z : Schwinger T a := Classical.choice (Kernel.host (nnPoint H hspin hp))
  let W (i : Fin m) := ∫ x, ket Z (w i) x
  have hx (x : Z.H) : 0 ≤ inner ℂ x x :=
    ⟨inner_self_nonneg (𝕜 := ℂ), (inner_self_im (𝕜 := ℂ) x).symm⟩
  have he := hx (∑ i : Fin m, c i • W i)
  simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right] at he
  simpa only [test_gram Z H.toSymmetric hv, Complex.star_def, mul_assoc] using he
end Tests

theorem answer : YM.Bid.B08 := by
  intro G C S V A P X H _ hv _ p hp α
  have hr := allGram (hp.HOnly α) (timeGram A P H hv (hp.threads α))
  exact ⟨hr, smear (hp.basics α) (hp.HOnly α) (hp.smooth α) hr⟩
end YM.Work.B08
