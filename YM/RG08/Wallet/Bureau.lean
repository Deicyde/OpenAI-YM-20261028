import YM.RG08.Peals.Heat

/-! # Lex filtered uniform estate

Index may vary gauges/geometries/coarsest/start/cutoff freely. Wallet must
be supplied ONCE on whole family. Age >= 1. Do not use little-oh at local
coupling to iterate. Width lives in pre calls. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Exterior Precision Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix
open scoped Topology ContDiff Classical
variable {I J : Type} {α β : I→Type}
variable {y δ w v f g h : I → ℝ}
variable {a c : ℝ} {r s : ℕ}

def Audience (y : I → ℝ) := ∀ i, 1 ≤ y i
def Weighed (y f : I→ℝ) := ∃ (A : ℝ) (p : ℕ), 0 ≤ A ∧ ∀ i,0 ≤ f i ∧ f i ≤ A*(y i)^p

lemma Weighed.positive (h : Weighed y f) : 0 ≤ f := fun i=> (h.choose_spec.choose_spec.2 i).1
lemma Weighed.constant (y : I → ℝ) (h : 0≤c) : Weighed y (fun _=>c) := ⟨c,0,h,fun _=>⟨h,by simp⟩⟩
lemma Weighed.zero : Weighed y 0 := Weighed.constant y le_rfl
lemma Weighed.one : Weighed y 1 := Weighed.constant y zero_le_one
lemma Weighed.power (x : I → ℝ) (h : Audience x) (p) : Weighed x (x^p) :=
  ⟨1,p,zero_le_one,fun i=> by rw [Pi.pow_apply]; exact ⟨pow_nonneg ((h i).trans' zero_le_one) _,by simp⟩⟩
lemma Weighed.times (h : Weighed y f) (g : Weighed y v) : Weighed y (f*v) := by
  obtain ⟨c,p,hc,H⟩ := h; obtain ⟨a,q,ha,R⟩ := g; refine ⟨c*a,p+q,mul_nonneg hc ha,fun i=> ⟨mul_nonneg (H i).1 (R i).1,?_⟩⟩
  rw [pow_add,mul_mul_mul_comm]; exact mul_le_mul (H i).2 (R i).2 (R i).1 ((H i).1.trans (H i).2)
lemma Weighed.plus (h : Weighed y f) (g : Weighed y v) (hx : Audience y) : Weighed y (f+v) := by
  obtain ⟨c,p,hc,H⟩:=h; obtain ⟨a,q,ha,R⟩:=g; refine ⟨c+a,max p q,add_nonneg hc ha,fun i=>⟨add_nonneg (H i).1 (R i).1,?_⟩⟩; rw [add_mul,Pi.add_apply]; apply add_le_add
  exacts [le_trans (H i).2 (by gcongr; exact hx i; exact le_max_left ..), le_trans (R i).2 (by gcongr; exact hx i; exact le_max_right ..)]
lemma Weighed.mono (h : Weighed y f) (hv : 0 ≤ v) (he : v ≤ f) : Weighed y v :=
  ⟨_,_,h.choose_spec.choose_spec.1,fun i=>⟨hv i,(he i).trans (h.choose_spec.choose_spec.2 i).2⟩⟩

-- Factor δ large not assumed small; definite scales used with correct orientation only!
def Voucher (y δ : I → ℝ) (U : ∀ i,Shale (α i) r) (w : I → ℝ) :=
    ∃ f, Weighed y f ∧ ∀ i, Glow (U i) (w i) (f i*δ i)
def SafeRow (y δ : I → ℝ) (H : ∀ i, Row (α i) (β i)) (w : I→ℝ) :=
    ∃ f, Weighed y f ∧ ∀ i,(H i).strip (w i) (f i*δ i)

variable {U V T : ∀ i, Shale (α i) r} {H L : ∀ i,Row (α i) (β i)}
lemma Voucher.soften (h : Voucher y δ U w) (hp : v ≤ w) : Voucher y δ U v :=
  ⟨_,h.choose_spec.1,fun i=>glow_less (h.choose_spec.2 i) (hp i) le_rfl⟩
lemma Voucher.raise (h : Voucher y δ U w) (hp : δ ≤ v) : Voucher y v U w :=
  ⟨_,h.choose_spec.1,fun i=>glow_less (h.choose_spec.2 i) le_rfl (mul_le_mul_of_nonneg_left (hp i) (h.choose_spec.1.positive i))⟩
lemma Voucher.scale (h : Voucher y δ U w) {f : I→ℝ} (b : Weighed y (fun i=> ‖f i‖)) : Voucher y δ (fun i=> f i • U i) w :=
  ⟨_, Weighed.times b h.choose_spec.1,fun i=> by rw [Pi.mul_apply,mul_assoc]; exact (h.choose_spec.2 i).scale _⟩
lemma Voucher.weight (h : Voucher y δ U w) (a : ℝ) : Voucher y δ (a • U) w := h.scale (Weighed.constant y (norm_nonneg a))
lemma Voucher.zero : Voucher y δ (0:∀ i,Shale (α i) r) w := by
  refine ⟨0,Weighed.zero,fun i=>?_⟩; rw [Pi.zero_apply,Pi.zero_apply,zero_mul]; exact Charge.zero _
lemma Voucher.plus (h : Voucher y δ U w) (g : Voucher y δ V w) (hp : Audience y) : Voucher y δ (U+V) w := by
  obtain ⟨v,hv,H⟩:=h; obtain ⟨u,hu,R⟩:=g; exact ⟨_,hv.plus hu hp,fun i=>by rw [Pi.add_apply (g:=u),add_mul]; exact (H i).add (R i) (fun i=> (ling_pos _ _).le)⟩
lemma Voucher.sub (h : Voucher y δ U w) (g : Voucher y δ V w) (hp : Audience y) : Voucher y δ (U-V) w := by simpa [sub_eq_add_neg] using h.plus (g.weight (-1)) hp
lemma Voucher.list (s : Finset J) {H : J→∀ i, Shale (α i) r} (u : Audience y) (h : ∀ b∈s, Voucher y δ (H b) w) : Voucher y δ (fun i=> ∑ b∈s,H b i) w := by
  rw [← show (∑ b∈s,H b)=(fun i=> ∑ b∈s,H b i) from funext fun i=>Finset.sum_apply i ..];
  induction s using Finset.induction_on with
  | empty => rw [sum_empty]; exact Voucher.zero
  | insert i s hi ih => rw [sum_insert hi]; exact (h i (mem_insert_self ..)).plus (ih fun j hj=> h j (mem_insert_of_mem hj)) u
lemma SafeRow.status (h : SafeRow y δ H w) (hp : ∀ i, 0<w i) (i) : Whole (H i) :=
  ⟨_,_,hp i,h.choose_spec.2 i⟩
lemma SafeRow.raise (h : SafeRow y δ H w) (hp : δ ≤ v) : SafeRow y v H w :=
  ⟨_,h.choose_spec.1,fun i=> Work.F08.strip_mono (h.choose_spec.2 i) le_rfl (mul_le_mul_of_nonneg_left (hp i) (h.choose_spec.1.positive i))⟩
lemma SafeRow.soften (h : SafeRow y δ H w) (hp : v ≤ w) : SafeRow y δ H v := ⟨_,h.choose_spec.1,fun i=> Work.F08.strip_mono (h.choose_spec.2 i) (hp i) le_rfl⟩

structure Both (y δ : I → ℝ) (U V : ∀ i, Shale (α i) r) (w : I → ℝ) : Prop where
    fresh : Voucher y 1 U w
    again : Voucher y 1 V w
    moves : Voucher y δ (U-V) w

namespace Both
lemma zero : Both y δ (0:∀ i,Shale (α i) r) 0 w := ⟨Voucher.zero,Voucher.zero,by rw [sub_self]; exact Voucher.zero⟩
lemma self (h : Voucher y 1 U w) : Both y δ U U w := ⟨h,h,by rw [sub_self]; exact Voucher.zero⟩
lemma add {P Q : ∀ i,Shale (α i) r} (h : Both y δ U V w) (e : Both y δ P Q w) (hp : Audience y) : Both y δ (U+P) (V+Q) w :=
  ⟨h.fresh.plus e.fresh hp,h.again.plus e.again hp,by rw [show _-_ = (U-V)+(P-Q) by abel]; exact h.moves.plus e.moves hp⟩
lemma weight (h : Both y δ U V w) (s : ℝ) : Both y δ (s • U) (s • V) w :=
  ⟨h.fresh.weight s,h.again.weight s,by rw [← smul_sub]; exact h.moves.weight _⟩
lemma sub {P Q : ∀ i,Shale (α i) r} (h : Both y δ U V w) (e : Both y δ P Q w) (hp : Audience y) : Both y δ (U-P) (V-Q) w := by simpa [sub_eq_add_neg] using h.add (e.weight (-1)) hp
lemma list (s : Finset J) {F H : J→∀ i, Shale (α i) r}
    (u : Audience y) (h : ∀ b∈s, Both y δ (F b) (H b) w) : Both y δ (fun i=> ∑ b∈s,F b i) (fun i=>∑ b∈s,H b i) w := by
  refine ⟨Voucher.list _ u (fun i hi=>(h i hi).fresh), Voucher.list _ u (fun i hi=>(h i hi).again),?_⟩
  rw [show _-_=(fun i=>∑ b∈s,(F b-H b) i) from funext fun i=> by simp only [Pi.sub_apply]; rw [sum_sub_distrib]]; exact Voucher.list _ u fun b hb=>(h b hb).moves
lemma soften (h : Both y δ U V w) (hp : v ≤ w) : Both y δ U V v := ⟨h.fresh.soften hp,h.again.soften hp,h.moves.soften hp⟩
lemma raise (h : Both y δ U V w) (he : δ ≤ v) : Both y v U V w := ⟨h.1,h.2,h.moves.raise he⟩
end Both
structure RowBoth (y δ : I → ℝ) (H L : ∀ i, Row (α i) (β i)) (w : I→ℝ) : Prop where
    fresh : SafeRow y 1 H w
    again : SafeRow y 1 L w
    moves : SafeRow y δ (H-L) w
end YM.RG08
