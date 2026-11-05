import Mathlib.Data.Set.Finite.List
import YM.Further.CURVED_GAUSSIAN_JETS.DirectV
import YM.Further.CURVED_GAUSSIAN_JETS.Motion

/-!
# Pricing rectangular Gram derivatives at either end, with room for the inverse
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Further.CurvedGaussianJets.ChangeV
open Tree Lattice Wilson RG Precision Bid Exterior SectorNext.Vacuum Pockets Work Set Metric Matrix Function Filter WardBin.Lies Push.Uniform Progress.StationaryScenes Pressure Shape Next.Fluctuations Jets
open Green (wt)
open Jets.Weights (spice)
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {G : Gauge} {c f : Side} {I J : Type*} [Fintype I] [Fintype J]
    {a : I→ Site f} {b : J → Site f} {r : Ratio c f} {o : Site f} {t δ C D v w : ℝ} (ht : 0≤t) (hδ : 0<δ) {k q h : ℕ} {V : Config G c}

def rule (a : I → Site f) (o : Site f) (q : ℕ) (ht : 0≤t) (hδ : 0<δ) : Jets.Weights a where
  τ := cap q t o ∘ a
  fee := δ
  budget := spice q δ
  nonneg _ := mul_nonneg ht (by positivity)
  room := hδ
  price := (Weights.polynomial a o q δ hδ).price
  moves i j := (mul_le_mul_of_nonneg_left ((Weights.polynomial a o q δ hδ).moves i j) ht).trans_eq (by simp [cap,Weights.polynomial]; ring)

def stockCost (δ v w C : ℝ) (q k M : ℕ) := C*spice q δ^k*M*Push.Uniform.countCost (w-v)
include hδ in
lemma stock_nonneg (hv : v<w) (hc : 0≤C) (q k M : ℕ) : 0 ≤ stockCost δ v w C q k M := by
  have hp := Push.Uniform.count_pos (sub_pos.mpr hv); unfold stockCost Weights.spice; positivity

variable {A B : Jets.Field G c I}
lemma Items.cash (h : Items r o a a w t q k V A C) {M : ℕ} (hM : Multiplicity a M) (hv : v<w) (hc : 0 ≤ C) : Cash (rule a o q ht hδ) v k (Due r.embed o q t) V A (stockCost δ v w C q k M) := by
  let s := rule a o q ht hδ
  have hp : 1 ≤ spice q δ := s.price
  intro l hl hd
  have he (i j : I) : wt w (a i) (a j) * |jet l A V i j| ≤ C*s.τ i^l.length := (h i j).paid l hl hd
  constructor
  · apply Weights.from_points (s:=s) hv hM _ (mul_nonneg hc (by positivity)); intro i j
    apply le_trans _ ((he i j).trans _)
    · unfold wt; gcongr; exact sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) s.room.le)
    gcongr; exact pow_nonneg (s.nonneg _) _; exact le_mul_of_one_le_right hc (one_le_pow₀ hp)
  apply Weights.from_points (s:=s) hv hM _ (mul_nonneg hc (by positivity)); intro i j
  have hx := mul_le_mul_of_nonneg_left (s.goes i j l.length) hc
  let d := l.length
  have hm : wt (s.width w d) (a i) (a j)*wt (d*s.fee) (a i) (a j)=wt w (a j) (a i) := by simp only [wt,Weights.width,separation_comm (a j),←Real.exp_add]; congr 1; ring
  apply le_of_mul_le_mul_right (a:=wt (d*s.fee) (a i) (a j)) ?_ (Green.wt_pos ..); rw [mul_right_comm,hm]
  calc
    _ ≤ _ := (he j i).trans hx
    _ ≤ C * (spice q δ^k * wt (d*s.fee) (a i) (a j)*s.τ i^d) := by gcongr; exact pow_nonneg (s.nonneg _) _; exact (Green.wt_pos ..).le; exact pow_le_pow_right₀ hp hl
    _ = _ := by ring

structure Stock (w : ℝ) (Q : Directions G c → Prop) (s : Jets.Weights a) (k : ℕ) (A : Jets.Field G c I) (V : Config G c) (C : ℝ) : Prop where
  has : 0≤C
  good : Good A k V
  cash : Cash s w k Q V A C

lemma Items.stock (h : Items r o a a w t q k V A C) {M : ℕ} (hM : Multiplicity a M) (hv : v<w) (hc : 0 ≤ C) : Stock v (Due r.embed o q t) (rule a o q ht hδ) k A V (stockCost δ v w C q k M) := ⟨stock_nonneg hδ hv hc ..,fun i j=>(h i j).good,h.cash ht hδ hM hv hc⟩

namespace Stock
variable {Q : Directions G c → Prop} {s : Jets.Weights a} (hh : Stock w Q s k A V C)
include hh
lemma transpose : Stock w Q s k (fun u=> (A u).transpose) V C := ⟨hh.has,hh.good.transpose,hh.cash.transpose⟩
lemma prod (hs : 0≤s.width w k) (hB : Stock w Q s k B V D) : Stock w Q s k (fun u=> A u*B u) V (s.pay k*C*D) := ⟨mul_nonneg (mul_nonneg (s.pay_pos _).le hh.has) hB.has,hh.good.prod hB.good,hh.cash.product hB.cash hh.good hB.good hs hh.has hB.has⟩
lemma gram_paid (hs : 0≤s.width w k) : Stock w Q s k (fun u=>gram (A u)) V (s.pay k*C*C) := hh.transpose.prod hs hh
lemma restrict (e : J ↪ I) : Stock w Q (s.restrict e) k (fun u=> (A u).submatrix e e) V C := ⟨hh.has,hh.good.restrict _, fun l hl hd=> (hh.cash l hl hd).restrict e⟩
lemma plus (hB : Stock w Q s k B V D) : Stock w Q s k (fun u=>A u+B u) V (C+D) := ⟨add_nonneg hh.has hB.has,hh.good.plus hB.good,hh.cash.plus hB.cash hh.good hB.good⟩
lemma scale (z : ℝ) : Stock w Q s k (fun u=> z • A u) V (|z| * C) :=
    ⟨mul_nonneg (abs_nonneg z) hh.has,hh.good.scale z,fun l hl hd=> by rw [jet_scale]; exact (hh.cash l hl hd).scale _⟩
lemma larger (h : C ≤ D) : Stock w Q s k A V D := ⟨hh.has.trans h,hh.good,hh.cash.mono le_rfl h⟩
end Stock

def duplex (B : Matrix I J ℝ) : Table (I ⊕ J) := fromBlocks 0 B 0 0
def crown (J : Type*) (A : Table I) : Table (I ⊕ J) := fromBlocks A 0 0 0
include ht in
lemma duplex_items {B : Config G c → Matrix I J ℝ} (hh : Items r o a b w t q k V B C) (hC : 0≤C) : Items r o (Sum.elim a b) (Sum.elim a b) w t q k V (fun u=> duplex (B u)) C := by rintro (i|i) (j|j); exact sticker_zero rfl ht hC; exact hh i j; exact sticker_zero rfl ht hC; exact sticker_zero rfl ht hC
include ht in
lemma crown_items (b : J→Site f) (hh : Items r o a a w t q k V A C) (hC : 0≤C) : Items r o (Sum.elim a b) (Sum.elim a b) w t q k V (fun u=> crown J (A u)) C := by rintro (i|i) (j|j); exact hh i j; exact sticker_zero rfl ht hC; exact sticker_zero rfl ht hC; exact sticker_zero rfl ht hC
lemma duplex_count {M N : ℕ} (ha : Multiplicity a M) (hb : Multiplicity b N) : Multiplicity (Sum.elim a b) (M+N) := by
  intro i; simpa only [Finset.card_filter,Fintype.sum_sum_type,Sum.elim_inl, Sum.elim_inr] using! Nat.add_le_add (ha i) (hb i)
lemma duplex_gram (B : Matrix I J ℝ) : (gram (duplex B)).submatrix Sum.inr Sum.inr = gram B := by rw [duplex,gram,fromBlocks_transpose,fromBlocks_multiply]; ext; simp [gram]
lemma duplex_product (A : Table I) (B : Matrix I J ℝ) : crown J A*duplex B=duplex (A*B) := by rw [crown,duplex,duplex,fromBlocks_multiply]; simp


def fromSides (q k : ℕ) (δ : ℝ) := (2:ℝ)^k*spice q δ^k
variable {B₁ : Config G c → Matrix I J ℝ} {M N : ℕ}
lemma gram_stock (ha : Multiplicity a M) (hb : Multiplicity b N) (he : 0≤v-(k:ℝ)*δ) (hv : v < w) (hC : 0≤C) (hh : Items r o a b w t q k V B₁ C) : let F := stockCost δ v w C q k (M+N)
    Stock v (Due r.embed o q t) (rule b o q ht hδ) k (fun u=> gram (B₁ u)) V (fromSides q k δ * F * F) := by
  intro F; let s := rule (Sum.elim a b) o q ht hδ
  have he := ((duplex_items ht hh hC).stock ht hδ (duplex_count ha hb) hv hC).gram_paid he |>.restrict (.inr (α:=I))
  change Stock _ _ (s.restrict Sum.inr) _ (fun u=> (gram (duplex (B₁ u))).submatrix Sum.inr Sum.inr) _ _ at he
  simp_rw [duplex_gram] at he; exact he

lemma crown_stock (ha : Multiplicity a M) (hb : Multiplicity b N) (he : 0≤v-(k:ℝ)*δ) (hv : v < w) (hC : 0≤C) (hD : 0≤D)
    (hh : Items r o a b w t q k V B₁ C) (hA : Items r o a a w t q k V A D) : let z := fromSides q k δ
    let F := z * stockCost δ v w D q k (M+N) * stockCost δ v w C q k (M+N)
    Stock v (Due r.embed o q t) (rule b o q ht hδ) k (fun u=> gram (A u * B₁ u)) V (z*F*F) := by
  intro z F; let s := rule (Sum.elim a b) o q ht hδ
  have hc := duplex_count ha hb
  have hx := (((crown_items ht b hA hD).stock ht hδ hc hv hD).prod he ((duplex_items ht hh hC).stock ht hδ hc hv hC)).gram_paid he |>.restrict (.inr (α:=I))
  change Stock _ _ (s.restrict Sum.inr) _ (fun u=> (gram (crown J (A u)*duplex (B₁ u))).submatrix Sum.inr Sum.inr) _ _ at hx
  simp_rw [duplex_product,duplex_gram] at hx; exact hx
end YM.Further.CurvedGaussianJets.ChangeV
