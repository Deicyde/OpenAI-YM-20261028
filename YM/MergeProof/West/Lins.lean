import YM.MergeProof.West.Melt
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Trails



/-!
# Paying all Rank addresses in the common venue.

Masks and horizon d from Rank request; clouds on a branch/held pole.
Even horizon access is after purchasing the canvas on that period,
not just expressing widths as comparison to the *free* curves.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open YM.Next.Rank.Tapes.West
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
    RankCovariance Next.Rank Tapes Perch Paint Spindle Station Peak Ac Corona Value Glyph Thirst
    MeasureTheory AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid Work.E04
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian FreeResolvent Wisps
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {N i p k n q d : ℕ} {b : ℝ}
local notation "St" => C.path.levels.clock.op i p
local notation "A" => C.path.levels
local notation "x" => C.path.levels.clock.hatBeta i
local notation "y" => C.path.levels.clock.hatBeta (i+1)

variable (X : Points n)
lemma root_b (h : roomTest A b k p d q) (H : i<k) (hp : middle A b k ≤ i)
    (k' : PatchPt X b A p d (show i+1≤k from H)) (a : Fin n) (ha : a∈(tag k'.val).val.val) :
    separation (core A X b p H.le (Head k'.val)) (core A X b p H.le a) ≤ walls x := by
  rw [itinerary A X b p H,itinerary A X b p H]; exact spends_aloft _ h H hp _ _ (le_trans (p_rized (C:=C) k' a ha) (Nat.mul_le_mul_right _ ((Nat.le_add_right d 10).trans h.radius)))

lemma shades_w (h : roomTest A b k p d q) (H : i<k) (hp : middle A b k ≤ i) (a : Bale C k b p d X H.le) (z : PatchPt X b A p d (show i+1≤k from H)) (hz : t_ests X b H a.2.val z)
    (j : Bond (C.side (i+1) p)) (hi : j∈parasol (core A X b p (show i+1≤k from H) (Head z.val)) (q*walls y)) :
    separation (core A X b p H.le (Head a.2.val)) ((C.path.levels.clock.op i p).ratio.parent j.1)+walls x+2 ≤ q*walls x := by
  let B:= walls x; let s:=core A X b p H.le
  have he : separation (s (Head a.2.val)) (s (Head z.val))≤ d*B:= p_rized (C:=C) a.2 _ (hz (head_member _))
  have hh : separation (s (Head z.val)) ((C.path.levels.clock.op i p).ratio.parent j.1) ≤ B+8 :=
    (congr_arg (separation · _) (itinerary A X b p H (Head z.val))).trans_le (tall_walk h H hp _ j hi)
  have hu := (separation_triangle _ _ _).trans (add_le_add he hh)
  have hB : 8≤B := h.birth _ hp H.le
  have hk : (d+10)*B ≤ q*B := Nat.mul_le_mul_right _ h.radius
  exact (Nat.add_le_add_right (Nat.add_le_add_right hu B) 2).trans (by rw [add_mul] at hk; change _≤q*B; omega) -- orientation

lemma roads_w (h : roomTest A b k p d q) (H : i<k) (hp : middle A b k ≤ i) (a : Bale C k b p d X H.le)
    (j : Incidence G (C.side (i+1) p)) (hi : j∈sp_okes X b H d a.2.val (C:=C)) :
    separation (core A X b p H.le (Head a.2.val)) ((C.path.levels.clock.op i p).ratio.parent j.1)+walls x+1 ≤ q*walls x := by
  obtain ⟨z,hz,hj⟩:= (mem_filter.mp hi).2
  have ht := (therm (q*walls y) _ (fromBead G j) (n_earby X b H z.val j hj h)).1
  have hp := shades_w X h H hp a z hz (j.1,j.2.1.val.1) (Room_advances (Nat.le_add_right _ _) ht)
  exact le_trans (Nat.le_succ _) hp

variable (ht:k≤N)
lemma under_w (Q : CellP C k b p) (H : i<k) (hp : middle A b k ≤ i) (Y) (V : Config G (C.side (i+1) p)) (q B t) :
    Healthy t (Spindle.patch (q*B) (core A X b p (show i+1≤k from H) (Head Y))) (watches C b p ht (i+1) (hp.trans (Nat.le_succ i)) Q V) ↔
    Healthy t (d_olm X b q B ht H (C:=C) Q Y) V := by
  rw [rising ht Q V hp,_root_.YM.Next.Rank.Thirst.s_healthy,d_olm,fine_read X ht Q (Head Y) H hp,Spindle.patch,swath_iffHalo]; unfold swath; rw [image_singleton]; rfl
end YM.PhysicalNext.InteractingRank
