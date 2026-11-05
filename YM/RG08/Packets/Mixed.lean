import YM.RG08.Packets.Norm
import YM.Pert.Bulk.Keys

/-!
# Cover substitution with true widths, in both-source and mixed-rank kernels

`change L K T U`: first (held) root leg travels via T; other legs independently U_i,
possibly depending also on the first input/root (for subtractions). Gives `fullTransmit`
when the tail laws coincide. Use a different predictor on each leg when comparing hierarchies.
Keep distinct output and input width choices (critical when the infinite UV tail moves between
plateaus). Rank one here = two curvature slots total.
-/
noncomputable section
namespace YM.RG08.Packets
open Filter Finset Pert.Bulk Laurent Lattice
open scoped Topology ENNReal

set_option autoImplicit false
universe v w u
variable {α β : Type}

abbrev Feed (r : ℕ) (α β : Type) := Fin r → Market α → Kernel α β
variable {r : ℕ} {L : Side}

def push (K : Packet r α) (T : Kernel α β) (U : Feed r α β) : Packet r β := fun y z=>
  ∑'x, T x y * ∑'w,K x w * ∏ i,U i x (w i) (z i)

def term (K : Packet r α) (T : Kernel α β) (U : Feed r α β) (z : Fin r→Market β) (y : Market β) (x : Market α) (w : Fin r→Market α) := (T x y * K x w) * ∏ i,U i x (w i) (z i)

theorem push_unify (K : Packet r α) (T : Kernel α β) (V : Market α→Kernel α β) : push K T (fun _=>V) = fullTransmit K T V := rfl

variable (K : Packet r α) (T : Kernel α β) (U : Feed r α β) {σ τ : ℝ}

theorem price_one (L : Side) (z y x w) (hs : 0 ≤ σ) : bill (term K T U z y x w) (charge β r σ y z) ≤
   bill (T x y) (r*σ*delta L x.1 y.1) * bill (K x w) 0 * ∏ i,bill (U i x (w i) (z i)) (σ*delta L x.1 (z i).1) := by
  exact (bill_mono (x:=term K T U z y x w) le_rfl (expense_sep (L:=L) x y z σ hs)).trans_eq (by rw [term,purchase,bill_products, ← add_zero (r*σ*delta L ..), purchase]; simp)

def purse (L : Side) (σ τ : ℝ) (q : Fin r → ℝ≥0∞) :=
    ∀ i x v, (∑'z,bill (U i x v z) (σ*delta L x.1 z.1)) ≤ q i * bill 1 (τ*sep x.1 v.1)

theorem sends (L : Side) (q : Fin r→ℝ≥0∞) (hU : purse U L σ τ q) (x y w) (hs : 0 ≤ σ) :
  (∑'z,bill (term K T U z y x w) (charge β r σ y z)) ≤
    bill (T x y) (r*σ*delta L x.1 y.1) * (∏ i,q i) * bill (K x w) (charge α r τ x w) := by
  let b := bill (T x y) (r*σ*delta L x.1 y.1)
  calc _ ≤ ∑'z : Fin r → Market β,b * bill (K x w) 0 * ∏ i,bill (U i x (w i) (z i)) (σ*delta L x.1 (z i).1) := ENNReal.tsum_le_tsum fun z=>price_one K T U L z y x w hs
       _ ≤ b*bill (K x w) 0 * ∏ i,(q i*bill 1 (τ*sep x.1 (w i).1)) := by
         rw [ENNReal.tsum_mul_left, all_Δ (a:=fun i (z:Market β)=>bill (U i x (w i) z) (σ*delta L x.1 z.1))]
         apply mul_le_mul_right
         exact Finset.prod_le_prod' (fun i _=>hU i x (w i))
       _ = _ := by
         rw [prod_mul_distrib, mul_mul_mul_comm b, ← bill_products,prod_const_one,← Finset.mul_sum, ← purchase,mul_one,zero_add]; rfl

theorem revenue (L : Side) (q : Fin r→ℝ≥0∞) (c p : ℝ≥0∞)
    (hU : purse U L σ τ q) (hK : ∀ x, ∑'w,bill (K x w) (charge α r τ x w) ≤ p)
    (hs : 0 ≤ σ) (hT : ∀ y, (∑' x,bill (T x y) (r*σ*delta L x.1 y.1)) ≤ c) (y) :
    (∑' z, ∑' a : Market α × (Fin r→Market α), bill (term K T U z y a.1 a.2) (charge β r σ y z)) ≤ (c*(∏ i,q i))*p := by
  let e (z) (x w):=bill (term K T U z y x w) (charge β r σ y z)
  let b (x : Market α) := bill (T x y) (r*σ*delta L x.1 y.1)
  change (∑' z,∑' a: Market α × _,e z a.1 a.2) ≤ _
  calc
    _ = ∑'x:Market α, ∑'w:Fin r→Market α, ∑'z,e z x w := by
      simp_rw [ENNReal.tsum_comm (f:=fun z (a : Market α × (Fin r → Market α))=>e z a.1 a.2), ENNReal.tsum_prod (f:=fun x w=> ∑'z,e z x w)]
    _ ≤ (∑'x:Market α,b x)*(∏ i,q i)*p := by
      rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right]
      refine ENNReal.tsum_le_tsum fun x=>?_
      exact (ENNReal.tsum_le_tsum fun w=>sends K T U L q hU x y w hs).trans (by rw [ENNReal.tsum_mul_left]; gcongr; exact hK _)
    _ ≤ _ := by gcongr; exact hT y

theorem push_tsum (y z) : push K T U y z = ∑'x,∑'w,term K T U z y x w := by
  simp_rw [term,push,mul_assoc, tsum_mul_left]

theorem push_est (L : Side) (q : Fin r→ℝ) (c p : ℝ)
    (hU : purse U L σ τ fun i=> ENNReal.ofReal (q i)) (hK : Folded τ K p)
    (hs : 0 ≤ σ) (hT : ∀ y, (∑' x,bill (T x y) (r*σ*delta L x.1 y.1)) ≤ ENNReal.ofReal c) (hc : 0 ≤ c) (hq : ∀ i,0 ≤ q i) :
    Folded σ (push K T U) (c*(∏ i,q i)*p) := by
  intro y
  let e (z) (x w):=bill (term K T U z y x w) (charge β r σ y z)
  calc
    _ ≤ ∑' z,∑' a: Market α × (Fin r→Market α),e z a.1 a.2 := ENNReal.tsum_le_tsum fun z=> by
      rw [ENNReal.tsum_prod (f:=fun x w=> e z x w),push_tsum]
      exact (bill_tsum ..).trans (ENNReal.tsum_le_tsum fun x=> bill_tsum ..)
    _ ≤ (ENNReal.ofReal c * ∏ i,ENNReal.ofReal (q i)) * ENNReal.ofReal p := revenue K T U L _ _ _ hU hK hs hT y
    _ = _ := by
      have H (s : Finset (Fin r)) : ENNReal.ofReal (∏ i∈s,q i) = ∏ i∈s,ENNReal.ofReal (q i) := by
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih => rw [prod_insert ha,prod_insert ha,ENNReal.ofReal_mul (hq _),ih]
      rw [ENNReal.ofReal_mul (mul_nonneg hc (prod_nonneg fun i _=>hq i)), ENNReal.ofReal_mul hc, H]

theorem pushes (L : Side) (q : Fin r→ℝ) (c p : ℝ)
    (hU : purse U L σ τ fun i=> ENNReal.ofReal (q i)) (hK : Folded τ K p)
    (hs : 0 ≤ σ) (hT : ∀ y, (∑' x,bill (T x y) (r*σ*delta L x.1 y.1)) ≤ ENNReal.ofReal c) (y z) :
    Summable (fun a: Market α × (Fin r→Market α)=>term K T U z y a.1 a.2) := by
  apply summable_from_receipt (fun _=>mul_nonneg hs (expense_nonneg y z))
  have he := revenue K T U L (fun i=>ENNReal.ofReal (q i)) (ENNReal.ofReal c) (ENNReal.ofReal p) hU hK hs hT y
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (show ENNReal.ofReal c ≠ ⊤ by simp) (by
    have ht (s : Finset (Fin r)) : (∏ i∈s, ENNReal.ofReal (q i)) ≠ ⊤ := by
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [prod_insert ha]; exact ENNReal.mul_ne_top (by simp) ih
    exact ht Finset.univ)) (show ENNReal.ofReal p ≠ ⊤ by simp)) ((ENNReal.le_tsum (f:=fun z=> ∑' a: Market α × (Fin r→Market α),bill (term K T U z y a.1 a.2) (charge _ _ σ y z)) z).trans he)

theorem push_full (y z) (h : Summable (fun a: Market α × (Fin r→Market α)=>term K T U z y a.1 a.2)) :
    push K T U y z= ∑' a : Market α × (Fin r→Market α),term K T U z y a.1 a.2 := by
  rw [push_tsum,h.tsum_prod]

end YM.RG08.Packets
