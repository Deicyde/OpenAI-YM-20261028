import YM.WilsonBulk.Solve.Ranks

/-!
# Appetite supplier for single- and dual-history propagation

All previous costs enlargements polynomial in AGE. No transfer of mask tariffs. Use
`Refill` with stage where `L` available at region post-pay. Calibration proof
therefore still requires a pre-L ν, σ receipt (separate in `Land`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Parapet.Shop
open Function Filter Lattice Laurent RG Schedule Finset Precision Exterior Stationary Audience Recall Pert.Bulk Sheet Atelier Bloch Work.F08
open scoped Topology Classical ENNReal BigOperators
variable {G : Gauge} {A : Levels G} {H : Horizon A} {ℓ i k n N N' e : ℕ} {x C θ δ : ℝ} {p q r : ℝ→ℝ}
variable {U : Shop H}

def refill (U : Shop H) (p : ℝ→ℝ) := fun x=>U.book x+p (x+U.book x)
lemma refillCost (U : Shop H) (p : ℝ→ℝ) (h : Tariff p) : Tariff (refill U p):= U.ticket.add (h.composed (Tariff.one.add U.ticket))
lemma refilled (h : Tariff p) : Prizes U.book (refill U p) := prizes_right (h.composed (Tariff.one.add U.ticket))
lemma refill_orig (h : Tariff p) : Prizes p (refill U p) := by
  intro x hx; have ht := zero_le_one.trans hx; exact (h.2.1 x (x+U.book x) ht (le_add_of_nonneg_right (U.ticket.1 x ht))).trans (le_add_of_nonneg_left (U.ticket.1 x ht))
lemma refill_more (h : Prizes p q) : Prizes (refill U p) (refill U q):= by
  intro x hx; exact add_le_add_right (h _ (hx.trans (le_add_of_nonneg_right (U.ticket.1 x (zero_le_one.trans hx))))) _

namespace Land
variable (h : Land U ℓ k x)
include h
lemma refill_neighbor (hp : Tariff p) (hi : ℓ ≤ i) : p (age A.S k x (i+1)) ≤ refill U p (age A.S k x i) := (hp.2.1 _ _ (zero_le_one.trans (h.wisdom _)) ((age_fade (k:=k) A.S i x).trans (add_le_add_right (h.sizes _ hi) _))).trans (le_add_of_nonneg_left (zero_le_one.trans (h.payload hi)))

-- earlier grade receipts. cost pRefund majorizes both preflight and all requirements. At phase overlap use next step's δ ≥ current δ automatically; price C = announced cover growth at root.
lemma past_income (hp : Tariff p) (hf : PriorGoods U p e n) (hi : ℓ ≤ i) (hN : i < N) (h' : N ≤ N') (ht : refill U p (age A.S k x i) ≤ C) : Intake (lawn (Cloth G)) (U.σ (i+1)) (U.fall (i+1) N) C (U.main N (i+1)) (U.main N' (i+1)) e n :=
 fun j hj y hy hh hx=> ((hf j y ⟨hh,hj,hx⟩).1 ℓ k x h (i+1) N N' (by omega) hN h').more le_rfl ((h.refill_neighbor hp hi).trans ht) le_rfl
lemma past_rest (hp : Tariff p) (hf : PriorGoods U p e n) (hi : ℓ ≤ i) (hN : i < N) (h' : N ≤ N') (ht : refill U p (age A.S k x i) ≤ C) : Rest (U.σ i) (U.fall (i+1) N) C e (U.raw N i) (U.raw N' i) := by
  intro j hj k'; by_cases he : k' ≤ j+2
  · exact ((hf j k' ⟨he, hj.le,(by omega)⟩).2 ℓ k x h _ _ _ hi hN h').more (fall_ge h) ((refill_orig hp _ (h.wisdom i)).trans ht) le_rfl
  exact ((rankHuge U hp (lt_of_not_ge he)).2 ℓ k x h _ _ _ hi hN h').more (fall_ge h) ((refill_orig hp _ (h.wisdom i)).trans ht) le_rfl
lemma Levied (hp : Tariff p) (hf : PriorGoods U p e (n+1)) (hi : ℓ ≤ i) (hN : i < N)
    (hs : G.Simple) (he : 0<e) (hE : e≤U.E) (hk : 1≤n) (hn : n ≤ e+1)
    (ht : refill U p (age A.S k x i) ≤ C) (hx : U.Mora U.main (i+1) N e (n+1) δ) :
    U.Mora U.raw i N e (n+1) (U.cDeep i n*δ+levy G U.E e n C) := by
  exact fee_levy ((h.tarmac i N hi hN).more ((refilled hp _ (h.wisdom i)).trans ht)) hs (U.top_healthy (i+1)) (U.main_welfare N (i+1) hN) hn hk he hE (past_income h hp hf hi hN le_rfl ht) (damp_pos ..).le (cDeep_small h hi hk (by omega)) hx
lemma LeviedΔ (hp : Tariff p) (hf : PriorGoods U p e (n+1)) (hi : ℓ ≤ i) (hN : i < N) (h' : N≤N')
    (hs : G.Simple) (he : 0 < e) (hE : e ≤ U.E) (hk : 1≤n) (hn : n ≤ e+1)
    (ht : refill U p (age A.S k x i) ≤ C) (hx : U.Mora U.main (i+1) N' e (n+1) C) (hV : Within (lawn (Cloth G)) (U.σ (i+1)) δ ((U.main N (i+1)-U.main N' (i+1)) e (n+1))) :
    Within (lawn (Cloth G)) (U.σ i) (U.cDeep i n * δ + U.fall (i+1) N*levyΔ G U.E e n C) ((U.raw N i-U.raw N' i) e (n+1)) := by
  have hh : U.book (age A.S k x i) ≤ C:= (refilled hp _ (h.wisdom i)).trans ht; have hw:= (h.toll i N N' hi hN h').more hh
  exact fee_variation ((h.tarmac i N hi hN).more hh) ((h.tarmac i N' hi (by omega)).more hh) hs hw (U.main_welfare N _ hN) (U.main_welfare N' _ (by omega)) hn hk he hE (past_income h hp hf hi hN h' ht) hx hV
lemma Welled (hp : Tariff p) (hf : PriorGoods U p e (n+1)) (hi : ℓ ≤ i) (hN : i < N)
   (he : 0 < e) (ht : refill U p (age A.S k x i) ≤ C) (hx : U.Mora U.raw i N e (n+1) δ) :
   U.Mora U.main i N e (n+1) (U.rDeep i*δ+hopPrice e n C) := by
  unfold Mora; rw [U.awaken N i hN]; exact Tarmac.hop ((h.tarmac _ _ hi hN).more ((refilled hp _ (h.wisdom i)).trans ht)) (U.main_welfare N (i+1) hN) (damp_pos A.S U.b (i+1) N).le he (h.past_rest hp hf hi hN le_rfl ht) hx
lemma WelledΔ (hp : Tariff p) (hf : PriorGoods U p e (n+1)) (hi : ℓ ≤ i) (hN : i < N) (h' : N ≤ N')
    (he : 0<e) (ht : refill U p (age A.S k x i) ≤ C) (hx : U.Mora U.raw i N' e (n+1) C) (hV : Within (lawn _) (U.σ i) δ ((U.raw N i-U.raw N' i) e (n+1))) :
    Within (lawn _) (U.σ i) (U.rDeep i*δ+U.fall (i+1) N*hopDiff e n C) ((U.main N i-U.main N' i) e (n+1)) := by
  have hh : U.book (age A.S k x i) ≤ C:= (refilled hp _ (h.wisdom i)).trans ht; have hv:= hN.trans_le h'
  rw [U.awaken N i hN,U.awaken N' i hv]; exact Tarmac.hop_delta ((h.tarmac i N hi hN).more hh) ((h.tarmac i N' hi hv).more hh) (U.main_welfare _ _ hN) (U.main_welfare _ _ hv) ((h.toll _ _ _ hi hN h').more hh) he (h.past_rest hp hf hi hN h' ht) hx hV
end Land
end Parapet.Shop
end YM.WilsonBulk
