import YM.Cells.Embedded
import YM.Slice.Calendar
import YM.Slice.Resident


/-!
# The full replicated column cost, 

Centered at cube base (through an axis); height between slabs `2w`.
Occupy EVERY OTHER cell. This doesn't need volume p-independent
numerical bound and includes orientation cost at reflected copies. Supply actual
costs, normalization, conjugation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Cells.Tiling
open MeasureTheory Measure Filter Function Set Lattice Wilson Slice Time
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexOrder
variable {n : Side} {G : Gauge} (T : Tiling n)

def plank (a : Axis) (x : ℕ) : T.Cell := x • step a

lemma plank_pos (a : Axis) (x : ℕ) : T.plank a x a=x := by simp [plank]
lemma plank_inj (a : Axis) {x y : ℕ} (hx : x<T.period.val) (hy : y<T.period.val) : T.plank a x=T.plank a y → x=y := by
  intro h
  have ht := congr_arg (fun p : T.Cell => (p a).val) h
  simpa only [T.plank_pos,ZMod.val_natCast_of_lt hx, ZMod.val_natCast_of_lt hy] using ht

lemma plank_even (a : Axis) (x : ℕ) : T.omega (T.plank a (x+x))=1 := by
  refine Signed.ext rfl ?_; ext i
  change decide (T.parity ((T.plank a (x+x)) i) ≠ 0) = _
  have he : (x : ZMod 2)+x=0 := by rw [← two_mul,show (2 : ZMod 2)=0 from rfl,zero_mul]
  by_cases h : i=a
  · subst i; simp only [T.plank_pos, parity,map_natCast]; simp [he]
  simp [plank,h]

lemma plank_translation (a : Axis) (x : ℕ) : T.translateBy (T.plank a (x+x)) = offset a ((((x+x)*T.side.val : ℕ):Per n)) := by
  have he : T.bias (T.plank a (x+x))=0 := by ext1 i; simp [bias, T.plank_even]
  unfold translateBy; rw [T.plank_even,he,Signed.act_one, starts]
  simp only [add_sub_cancel_left,add_zero]
  rw [plank,map_nsmul,T.root_step]; ext1 i; by_cases h : i=a <;> simp [offset,h]

lemma plank_copies (a : Axis) (x) (u : Config G n) (F : Config G n → ℂ) :
    T.copy (T.plank a (x+x)) F u = F (translate (offset a (↑((x+x)*T.side.val : ℕ))) u) := by
  have he : ¬ T.hand (T.plank a (x+x)) := by simp [hand,T.plank_even,Finset.filter_false_of_mem]
  rw [copy,if_neg he,T.plank_even,T.plank_translation,pull_one]

def locus (a : Axis) (o : Site n) : Cut n :=
    { T.bandCut 0 a with baseLine := o a, kind := .site }

variable (a : Axis)

/-- Start on slice t. Anchored time inside initial cell. -/
lemma turns_ref (t : Per n) (o : Site n) (H : t+T.side.val=o a) (B : Brick a G n)
    (he : B.width=2*T.side.val) (F : Config G n) : B.reflect.value t F =
    star (B.value t ((T.locus a o).pullC G F)) :=
  (flipValue (T.locus a o) T.side.val rfl B t H.symm ((two_mul T.side.val) ▸ he) F).symm

lemma adjacency (B : Brick a G n) (he : B.width=2*T.side.val) (U : Config G n) (t : Per n) (p : ℕ) :
    Time.word (Time.column B p) t U = ∏ i : Fin p,
      T.copy (T.plank a (2 * (2*i.val))) (B.reflect.value t) U * T.copy (T.plank a (2 * (2*i.val+1))) (B.value t) U := by
  induction p with
  | zero => simp [Time.column]
  | succ p ih =>
    rw [show Time.column B (p+1)=Time.column B p ++ [B.reflect,B] by
      unfold Time.column; rw [List.replicate_succ',List.flatten_append];simp,Time.distributed]
    rw [Fin.prod_univ_castSucc]
    rw [ih]; congr 1
    rw [Time.read,Time.read,Time.word_nil,mul_one]
    simp only [Time.clockTime,Brick.reflect_width,he,Fin.val_last]
    rw [two_mul (2*p), two_mul (2*p+1),plank_copies,plank_copies]
    rw [translation,translation]
    push_cast
    ring_nf

theorem enough {β} (H : Seam G n β) {t : Per n} (o : Site n) (hq : t+T.side.val=o a) (B : Brick a G n)
    (h : B.width=2*T.side.val) {p : ℕ} (hp : 0<p) (hC : (p+p)*B.width=n.val)
    (F J : Config G n → ℂ) (A : ℝ) (hf : F=B.value t) (hw : ∀ x, J x=star (F ((T.locus a o).pullC G x)))
    (ha : Interior (T.chamber 0) F) (hb : Interior (T.chamber 0) J)
    (he : T.rootTest β F≤A) (hr : T.rootTest β J≤A) :
    ‖moment β (Time.word (Time.column B p) t)‖^(Holder.rate p) ≤ A := by
  classical
  let g := Sum.elim (fun i : Fin p => 2*(2*i.val)) (fun i : Fin p => 2*(2*i.val+1))
  let f := Sum.elim (fun _ : Fin p => J) (fun _ : Fin p => F)
  have hi : T.period.val=(p+p)*2 := by
    rw [h,T.units.exact_size,← Nat.mul_assoc] at hC
    exact (Nat.eq_of_mul_eq_mul_right T.side.property hC).symm
  have hH (x) : g x < T.period.val := by
    rcases x with i|i <;> have hv := i.isLt <;> simp only [hi,g, Sum.elim_inl,Sum.elim_inr] <;> omega
  have hv : Injective (T.plank a ∘ g) := by
    have H (p q) : g p=g q → p=q := by
      intro hp
      rcases p with p|p <;> rcases q with q|q <;> simp only [g,Sum.elim_inl,Sum.elim_inr] at hp
      · rw [Fin.ext (show p.val=q.val by omega)]
      · omega
      · omega
      rw [Fin.ext (show p.val=q.val by omega)]
    exact fun i j hh => H _ _ (T.plank_inj a (hH _) (hH _) hh)
  have hd := T.planted H _ hv f (fun x => by cases x; exacts [hb,ha])
  have hB : (fun U => ∏ j, T.copy (T.plank a (g j)) (f j) U) = Time.word (Time.column B p) t := by
    funext U
    rw [adjacency T a B h U t,Finset.prod_mul_distrib, Fintype.prod_sum_type]
    unfold f; rw [show J=B.reflect.value t from funext fun x => by rw [hw,hf, T.turns_ref a t o hq B h],hf]
    rfl
  change ‖moment β (fun U => ∏ j, T.copy (T.plank a (g j)) (f j) U)‖ ≤ _ at hd
  rw [hB] at hd
  have he := hd.trans <| Finset.prod_le_prod (fun i _ => T.root_nonneg β _)
    (fun i _ => show T.rootTest β (f i) ≤ A from by cases i; exacts [hr,he])
  simp only [Finset.prod_const,Fintype.card_fin,Finset.card_univ,Fintype.card_sum] at he
  apply le_trans (Real.rpow_le_rpow (norm_nonneg _) he (inv_nonneg.mpr (by exact_mod_cast (show 0 ≤ p+p by omega)))) _
  rw [Real.pow_rpow_inv_natCast]; exacts [(T.root_nonneg β J).trans hr, by omega]
end YM.Cells.Tiling
