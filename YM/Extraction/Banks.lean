import YM.Euclid.Words
import YM.Extraction.Inherited


/-!
# Separated Euclidean test vectors at finite N,p. Strict temporal fit

Everywhere-positive compact room used for sites & all stencil bodies. Values
with right-closed seam at capped times dealt with explicitly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extraction.Banks
open Function Set MeasureTheory Filter Lattice Wilson Cells
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexOrder

variable {G : Gauge} (C : Family G) {a : Axis}

def plane (N p : ℕ) (a : Axis) : Cut (C.side N p) := ⟨half C.S N p, original C.S N p, .site, a,0⟩

variable {m N p : ℕ}

def supported (Q : Table.PastTest C.book a) (p : ℕ) := suitable C.S p Q.f

def weightValue (Q : Table.PastTest C.book a) (N p) (r : Fin Q.n→ Site (C.side N p)) := Q.f (Order.cells C N p r)
def base (Q : Table.PastTest C.book a) (N p) (r : Fin Q.n → Site (C.side N p)) (U : Config G (C.side N p)) :=
    (((C.S.a N:ℂ)^(4*Q.n)) * weightValue C Q N p r) * ∏ i, C.seen (Q.v i) (r i) U
def stem (Q : Table.PastTest C.book a) (N p) (U : Config G (C.side N p)) := ∑ r, base C Q N p r U

lemma elementary (Q : Table.PastTest C.book a) (r) : Continuous (base C Q N p r) := continuous_const.mul
  (continuous_finsetProd Finset.univ fun i _ => C.continuousO N p (Q.v i).1 (Q.v i).2 _)

lemma limits_test (Q : Table.PastTest C.book a) (p : ℕ) (hv : supported C Q p) {i : Fin Q.n} :
    ∃ r : ℝ, 0<r ∧ ∀ x∈ tsupport Q.f, r ≤ x i a ∧ x i a ≤ C.S.radius p - r := by
  rcases (tsupport Q.f).eq_empty_or_nonempty with h|h; exact ⟨1,zero_lt_one,by simp [h]⟩
  have hc : ContinuousOn (fun x : Points Q.n => x i a) (tsupport Q.f) := (show Continuous _ from by fun_prop).continuousOn
  obtain ⟨x,hx,H⟩ := Q.f.hasCompactSupport.exists_isMinOn h hc
  obtain ⟨y,hy,he⟩ := Q.f.hasCompactSupport.exists_isMaxOn h hc
  let r := min (x i a) (C.S.radius p-y i a)
  have hm := Q.past x hx i
  exact ⟨r,lt_min hm (sub_pos.mpr (hv hy i a).2), fun z hz => ⟨(min_le_left ..).trans (H hz),
    le_trans (he hz) (by dsimp only; linarith [show r≤C.S.radius p - y i a from min_le_right ..])⟩⟩

lemma hair (H : C.Makes) (f : Order) (Q : Table.PastTest C.book a) (p : ℕ) (hv : supported C Q p) (i : Fin Q.n) :
    ∀ᶠ j in atTop, ∀ r, weightValue C Q (f.mesh j) p r ≠ 0 → Interior (plane C (f.mesh j) p a).sector
      (C.seen (Q.v i) (r i)) := by
  let S := C.localSection (Q.v i).1
  obtain ⟨t,ht,hg⟩ := limits_test C Q p hv (i := i)
  have hh (u : Cover) : ∀ᶠ j : ℕ in atTop, C.S.a (f.mesh j)*|(u a:ℝ)|<t := by
    have he : Tendsto (fun j => C.S.a (f.mesh j)*|(u a:ℝ)|) atTop (𝓝 0) := by
      simpa only [zero_mul,Function.comp_apply] using ((C.S.shrinks.comp f.mesh.cofinal).mul_const |(u a:ℝ)|)
    exact he.eventually (gt_mem_nhds ht)
  filter_upwards [eventually_all_finset S.stencil |>.mpr (fun u _ => hh u)] with j hi x hq
  let N := f.mesh j
  have hc : Continuous (C.seen (Q.v i) (x i)) := C.continuousO N p (Q.v i).1 (Q.v i).2 _
  let P := plane C N p a
  let o := x i
  have he := hg (Order.cells C N p x) (subset_closure hq)
  refine ⟨C.invariant H N p (Q.v i).1 _ _,hc.measurable,fun U V h => ?_,hc.bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)⟩
  apply C.localO N p (Q.v i).1 _ o U V (agrees_mono h ?_)
  intro q hq
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hq
  let z : ℤ := lift o a + u a
  have hb : C.S.radius p=C.S.a N*(P.half.val:ℕ) := by
    have hl := C.S.span_side N p; rw [show (C.S.side N p).val=2*P.half.val from P.even] at hl
    unfold Schedule.radius; rw [← hl]; push_cast; ring
  have hw : 0 < z ∧ z < (P.half.val : ℤ) := by
    have hz : (z:ℝ)= ((lift o a:ℤ):ℝ) + u a := Int.cast_add ..
    change t≤ C.S.a N*((lift o a:ℤ):ℝ) ∧ C.S.a N*((lift o a:ℤ):ℝ) ≤ C.S.radius p -t at he
    have ht : C.S.a N*|(u a:ℝ)|<t := hi u hu
    rw [← abs_of_pos (C.S.a_pos N), ← abs_mul,abs_lt] at ht
    rw [hb] at he
    have hh : (0:ℝ)<z ∧ (z:ℝ)<P.half.val := by constructor <;> nlinarith [C.S.a_pos N,ht.1,ht.2]
    exact_mod_cast hh
  have ha := P.even
  change 0 < _ ∧ _ < P.half.val
  rw [show (P.distance ((wrap (C.side N p)) u + o))=z.toNat by
    unfold Cut.distance
    have hy : (((wrap (C.side N p)) u + o) P.pos - P.baseLine)=(↑(z.toNat): Per (C.side N p)) := by
      rw [← Int.cast_natCast,Int.toNat_of_nonneg hw.1.le]
      change (u a:Per (C.side N p))+o a-0=(z:ℤ)
      unfold z; simp only [Int.cast_add,lift, ZMod.coe_valMinAbs, sub_zero]; abel
    rw [hy,ZMod.val_natCast_of_lt]
    omega]
  omega

private lemma added {n : Side} {ι : Type*} (x : Finset ι) (c : ι→ Config G n→ℂ) (S : Set (Site n))
    (h : ∀ i ∈ x, Interior S (c i)) : Interior S fun U => ∑ i∈x,c i U := by
  classical
  induction x using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact Interior.constant _ _
  | @insert a b hb ih => simp_rw [Finset.sum_insert hb]; exact (h a (Finset.mem_insert_self ..)).plus (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma kept (H : C.Makes) (f : Order) (Q : Table.PastTest C.book a) :
    ∀ᶠ i in f.fuse, Interior (plane C i.1 i.2 a).sector (stem C Q i.1 i.2) := by
  rw [Order.fused,Order.late]
  filter_upwards [f.per.cofinal.eventually (reading C.S Q.f)] with p hp
  filter_upwards [eventually_all.mpr (hair C H f Q _ hp)] with i hi
  unfold stem; apply added; intro r _
  by_cases Hm : weightValue C Q (f.mesh i) (f.per p) r=0
  · rw [show base C Q _ _ r=(fun _ => 0) by ext1; simp [base,Hm]]; exact Interior.constant _ _
  exact Interior.scale _ (Interior.combines (fun v => C.seen (Q.v v) (r v)) _ (fun j _ => hi j r Hm))

end YM.Extraction.Banks
