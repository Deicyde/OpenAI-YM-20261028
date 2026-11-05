import YM.Cells.Packing
import YM.Cells.Present
import YM.Slice.Ordered




/-!
# Use actual cylinder on these tours

Centered link tiling widths use subdivisions at schedules, powers p pair count
tracks the SAME p in moment. Centered estimates only on one law assumed.
Check on transported star (regular lattice labels), any list. Needed both on
fixed-volume patch and expanding ones.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extraction.Difference
open Lattice Wilson MeasureTheory Measure Slice Time Cells Function Set
open scoped Topology Matrix.Norms.Frobenius BigOperators ComplexOrder
variable {G : Gauge} {n : Side}
variable {m N ℓ p : ℕ}

lemma chrono {v : Fin (m+1)→Per n} (i : Fin (m+1)) (h : Injective v) :
    ∃ P : Equiv.Perm (Fin (m+1)), P 0=i ∧ StrictMono (minutes (v ∘ P)) := by
  let f (j : Fin (m+1)) := (v j - v i).val
  have he : Injective f := by
    intro s t H; apply h; apply sub_left_injective (b := v i)
    exact ZMod.val_injective _ H
  let e := Tuple.sort f
  have hw : StrictMono (f ∘ e) := (Tuple.monotone_sort _).strictMono_of_injective (he.comp e.injective)
  have ht := hw.monotone (show 0 ≤ e.symm i from Fin.zero_le _)
  simp [Function.comp_apply] at ht
  have hg : e 0=i := he (by simp [show f i=0 from by simp [f]] at ht ⊢; exact ht)
  exact ⟨e,hg,show StrictMono _ from by unfold minutes; simp only [Function.comp_apply,hg];exact hw⟩

lemma stars {C : Family G} (A : C.Makes) (B : C.book.Token) (he : C.ref B.1 ≤ N) (o : Site (C.side N p))
    (T : Tiling (C.side N p)) (a : Axis) (U : Config G (C.side N p)) :
    C.seen (C.book.reflectedToken a B) o U = star (C.seen B o ((T.locus a o).pullC G U)) := by
  let Q := T.locus a o
  have hp : Q.reflect o = o := by
    funext i; by_cases h : i=a
    · subst i
      change Q.reflect o Q.pos = _; rw [Cut.reflect_here]; simp [Q,Tiling.locus,Kind.shift,Tiling.bandCut]; ring
    exact Q.reflect_there _ h
  change C.O N p ((C.labels.level B.1).act (Signed.mirror a).ortho (star B.2)) o U = _
  conv_lhs => rw [← hp]
  change C.O N p _ (affine Q.flip Q.slide o) U = _
  exact (C.rotated A he (star B.2) (Signed.mirror a) o Q.slide U).trans (C.reality A he B.2 o _)

lemma reading {C : Family G} (h : C.Makes) {D} (ho : D ≤ N) (a : Axis) (o : Site (C.side N p))
    (v : C.book.Token) (hV : C.ref v.1 ≤ N)
    (d : ℕ) (hr : d=(C.S.toDepth ho p).count.val)
    (M : ℕ) (hM : 0 < M) (he : (C.side N p).val=(M+M)*(2*d))
    (c : ℝ)
    (H : ∀ w : C.book.Token, w=v ∨ w=C.book.reflectedToken a v →
      Interior ((center C.S p ho o).chamber 0) (C.seen w o) ∧
      (center C.S p ho o).rootTest (C.beta N p) (C.seen w o) ≤ c) :
    let t := o a-d
    ∃ B : Brick a G (C.side N p), B.width=2*d ∧
      C.seen v o = B.value t ∧ ‖moment (C.beta N p) (Time.word (column B M) t)‖^(Holder.rate M) ≤ c := by
  intro t
  let T := center C.S p ho o
  have hw (x) (hx : x∈T.chamber 0) : (x a-t).val < 2*d := by
    have hz := Kind.strict_lt (hx a)
    rw [T.starts_zero] at hz
    let e := (x a-T.base a).val
    have hE : e<d := hr ▸ hz
    let c := e+d-d/2
    have hd : d/2 ≤ d := Nat.div_le_self _ _
    have hy : c<2*d := by unfold c; omega
    rw [show x a-t=(c : Per (C.side N p)) by
      unfold c; rw [Nat.cast_sub (by omega),Nat.cast_add]
      have hc : (e : Per (C.side N p)) = x a-T.base a := by unfold e; simp [Per]
      rw [hc]; dsimp only [T,Cells.center,t]; rw [← hr]; abel, ZMod.val_natCast_of_lt]
    exacts [hy, hy.trans_le (by rw [he]; nlinarith)]
  have hz : 0 < d := hr ▸ (C.S.toDepth ho p).count.property
  have hy : 2*d-1+1=2*d := by omega
  let g := C.seen v o
  have hG := (H v (Or.inl rfl)).1
  obtain ⟨B,hB,Hb⟩ := Time.selects (a := a) (m := 2*d-1) g (C.continuousO N p v.1 v.2 _) t (by rw [hy,he]; nlinarith)
    (fun U V h => hG.localSites U V (agrees_mono h (fun x hx => hy.symm ▸ hw x hx)))
  rw [hy] at hB
  obtain ⟨Hj,hh⟩ := H (C.book.reflectedToken a v) (Or.inr rfl)
  exact ⟨B,hB,Hb,T.enough a (seamless h N p) o (by change t + _ = _; unfold t; rw [hr]; exact sub_add_cancel ..) B
    (hr ▸ hB) hM (hB.symm ▸ he.symm) g (C.seen (C.book.reflectedToken a v) o) c Hb (stars h v hV o T a) hG Hj
    (H v (Or.inl rfl)).2 hh⟩

/-- One primitive directional comparison. Tail passage separate. -/
theorem primitive {C : Family G} (h : C.Makes) (a : Axis) (v : Fin (m+1) → C.book.Token)
    (hV : C.sufficient N v) {D} (hD : D≤N)
    (d : ℕ) (hr : d=(C.S.toDepth hD p).count.val)
    (c : Fin (m+1) → ℝ) (hm : 0 < m) (x : Fin (m+1) → Site (C.side N p))
    (r : ℝ) (ht : 0<r) (he : ∀ i j, i≠j → (2*d:ℝ)+ 2*r < ((x j a-x i a).val:ℝ))
    (H : ∀ (i : Fin (m+1)) (w : C.book.Token), w=v i ∨ w=C.book.reflectedToken a (v i) →
      Interior ((center C.S p hD (x i)).chamber 0) (C.seen w (x i)) ∧
      (center C.S p hD (x i)).rootTest (C.beta N p) (C.seen w (x i)) ≤ c i)
    (u : Fin (m+1)) (ℓ : ℕ) (hℓ : (ℓ:ℝ) ≤ r) :
    ‖C.numeric N p v (update x u (x u+offset a (ℓ:Per (C.side N p))))-C.numeric N p v x‖ ≤ (∏ i, c i)/r*(ℓ:ℝ) := by
  let M : ℕ := (C.side D p).val / 4
  have hM : (C.side D p).val=4*M := by
    have hh := C.S.side_four D p; change 4∣ (C.side D p).val at hh; unfold M; omega
  have hz : 0 < M := by have hp : 0 < (C.side D p).val := (C.side D p).property; omega
  have hk : (C.side N p).val=(M+M)*(2*d) := by
    rw [(C.S.toDepth hD p).exact_size]
    -- can't rw inside dependent toDepth
    have hh := hr
    rw [← hh,hM]; ring
  let y i := x i a-(d:Per _)
  have hp i j : y j-y i=x j a-x i a := by unfold y; abel
  have hw : Injective y := by
    intro i j hs; by_contra h'
    have hh := he i j h'
    rw [← hp,hs,sub_self] at hh
    simp only [ZMod.val_zero,Nat.cast_zero] at hh; linarith [Nat.cast_nonneg (α := ℝ) d]
  obtain ⟨P,hP,hS⟩ := chrono u hw
  choose B hB Hb hn using fun i => reading h hD a (x i) (v i) (hV i) d hr M hz hk (c i) (H i)
  let b := fun i => B (P i)
  have hd := le_trans (div_nonneg (zero_le_one.trans (C.path.levels.fits.delayed N).le) (by norm_num)) (h.wilson.represents N p N le_rfl).band.1
  have hx (i j) (H : i ≠ j) : (((2*d:ℕ):ℝ))+2*r < (((y ∘ P) j-(y ∘ P) i).val:ℝ) := by
    simp only [Function.comp_apply, hp]; exact_mod_cast he _ _ (P.injective.ne H)
  have hj := organized (B := b) (2*d) (fun i => hB _) M hz hk hS r ht hm hx _ hd hℓ (K := c ∘ P) (fun i => hn (P i))
  let X' := fun i => if i=(0:Fin (m+1)) then (y ∘ P) i +(ℓ:Per _) else (y ∘ P) i
  change ‖moment _ (fun U => ∏ i, (b i).value (X' i) U)-moment _ _‖ ≤ _ at hj
  have hI (U : Config G (C.side N p)) : ∏ i, ((b i).value ((y ∘ P) i) U) = ∏ i, C.seen (v i) (x i) U := by
    conv_rhs => rw [← Equiv.prod_comp P]
    apply Finset.prod_congr rfl; intro i _
    exact congr_fun (Hb (P i)).symm U
  let V := update x u (x u+offset a (ℓ:Per _))
  have hq (U : Config G (C.side N p)) : ∏ i, ((b i).value (X' i) U) = ∏ i, C.seen (v i) (V i) U := by
    conv_rhs => rw [← Equiv.prod_comp P]
    apply Finset.prod_congr rfl
    intro i _
    by_cases he : i=0
    · subst i; unfold V; rw [hP, update_self]
      change _ = C.O _ _ _ _ _
      rw [← C.translation]
      change _ = C.seen _ _ _
      unfold X'
      rw [Hb, Time.translation]; simp [y,b,hP]
    unfold V; rw [Function.update_of_ne (fun h => he (P.injective (h.trans hP.symm)))]
    unfold X'; rw [if_neg he]; exact congr_fun (Hb _).symm U
  change ‖moment _ (fun U => ∏ i, (b i).value (X' i) U)-moment _ (fun U => ∏ i, (b i).value ((y ∘ P) i) U)‖ ≤ (∏ i, c (P i))/r*ℓ at hj
  simp_rw [hI,hq,show ∏ i, c (P i) = _ from Equiv.prod_comp P c] at hj
  exact hj
end YM.Extraction.Difference
