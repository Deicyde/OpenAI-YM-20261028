import YM.Extra.ITERATION_NO_LOSS.Mechanism
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Awning
import YM.PhysicalNext.RANK_COVARIANCE_ATLAS.Atlas

/-!
# Paying all Rank addresses in the common venue.

Masks and horizon d from Rank request; clouds on a branch/held pole.
Even horizon access is after purchasing the canvas on that period,
not just expressing widths as comparison to the *free* curves.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
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

lemma tall_walk (h : roomTest A b k p d q) (H : i<k) (hp : middle A b k ≤ i) (s : Site (C.side (i+1) p)) (j : Bond (C.side (i+1) p)) (hj : j∈parasol s (q*walls y)) :
    separation ((C.path.levels.clock.op i p).ratio.parent s) ((C.path.levels.clock.op i p).ratio.parent j.1) ≤ walls x+8 := by
  have hi := (mem_filter.mp hj).2
  have he : separation s j.1 ≤ q*walls y+8 := (Spindle.doors _).1 hi.1
  let P:= (C.path.levels.clock.op i p).ratio; let v:=P.count.val
  have hz:= foreshorten P s j.1
  have hh : q*walls y+v ≤ walls x*v := h.fresh i hp H; have hv : 0<v := P.count.property
  apply Nat.le_of_mul_le_mul_left _ hv; apply hz.trans
  have ho : 8≤v*8 := Nat.le_mul_of_pos_left _ hv; change _+v≤v*_ ; nlinarith only [he,hh,ho]

variable (X : Points n)
lemma root_bounded (h : roomTest A b k p d q) (H : i<k) (hp : middle A b k ≤ i)
    (k' : Index X b A p d (show i+1≤k from H)) (a : Fin n) (ha : a∈(tale k'.val).val.val) :
    separation (core A X b p H.le (headMark k'.val)) (core A X b p H.le a) ≤ walls x := by
  rw [itinerary A X b p H,itinerary A X b p H]; exact spends_aloft _ h H hp _ _ (le_trans (prized (C:=C) k' a ha) (Nat.mul_le_mul_right _ ((Nat.le_add_right d 10).trans h.radius)))

lemma shades_buy (h : roomTest A b k p d q) (H : i<k) (hp : middle A b k ≤ i) (a : Lane C k b p d X H.le) (z : Index X b A p d (show i+1≤k from H)) (hz : tests X b H a.2.val z)
    (j : Bond (C.side (i+1) p)) (hi : j∈parasol (core A X b p (show i+1≤k from H) (headMark z.val)) (q*walls y)) :
    separation (core A X b p H.le (headMark a.2.val)) ((C.path.levels.clock.op i p).ratio.parent j.1)+walls x+2 ≤ q*walls x := by
  let B:= walls x; let s:=core A X b p H.le
  have he : separation (s (headMark a.2.val)) (s (headMark z.val))≤ d*B:= prized (C:=C) a.2 _ (hz (member_mark _))
  have hh : separation (s (headMark z.val)) ((C.path.levels.clock.op i p).ratio.parent j.1) ≤ B+8 :=
    (congr_arg (separation · _) (itinerary A X b p H (headMark z.val))).trans_le (tall_walk h H hp _ j hi)
  have hu := (separation_triangle _ _ _).trans (add_le_add he hh)
  have hB : 8≤B := h.birth _ hp H.le
  have hk : (d+10)*B ≤ q*B := Nat.mul_le_mul_right _ h.radius
  exact (Nat.add_le_add_right (Nat.add_le_add_right hu B) 2).trans (by rw [add_mul] at hk; change _≤q*B; omega) -- orientation

lemma roads_buy (h : roomTest A b k p d q) (H : i<k) (hp : middle A b k ≤ i) (a : Lane C k b p d X H.le)
    (j : Incidence G (C.side (i+1) p)) (hi : j∈spokes X b H d a.2.val (C:=C)) :
    separation (core A X b p H.le (headMark a.2.val)) ((C.path.levels.clock.op i p).ratio.parent j.1)+walls x+1 ≤ q*walls x := by
  obtain ⟨z,hz,hj⟩:= (mem_filter.mp hi).2
  have ht := (therm (q*walls y) _ (fromBead G j) (nearby X b H z.val j hj h)).1
  have hp := shades_buy X h H hp a z hz (j.1,j.2.1.val.1) (Room_advances (Nat.le_add_right _ _) ht)
  exact le_trans (Nat.le_succ _) hp

-- native orientation on BOTH masks and gauges.
variable (ht : k≤N)
lemma rising (Y : CellP C k b p) (F : Config G (C.side (i+1) p)) (hp : middle A b k ≤ i) :
    watches C b p ht (i+1) (hp.trans (Nat.le_succ i)) Y F =
      pull ((Ship.yard C b ht p).omega Y) ((C.path.levels.clock.op i p).ratio.embed (spreadC C b p ((Station.wider ..).trans hp) Y)) F := by
  unfold watches
  rw [spreadC, embed_comp (C.S.toDepth ((Station.wider ..).trans hp) p) (C.path.levels.clock.op i p).ratio]; rfl
lemma fine_read (Y : CellP C k b p) (a : Fin n) (h : i<k) (hp : middle A b k ≤ i) :
    Peak.readers (C:=C) (b:=b) (p:=p) X ht (show i+1≤N from (show i+1≤k from h).trans ht) (Y,a)=
      affine ((Ship.yard C b ht p).omega Y) ((C.path.levels.clock.op i p).ratio.embed (spreadC C b p ((Station.wider ..).trans hp) Y)) (core A X b p (show i+1≤k from h) a) := by
  rw [fills C X b p ht (show i+1≤k from h) ((Station.wider ..).trans (hp.trans (Nat.le_succ i))),spreadC,embed_comp (C.S.toDepth ((Station.wider ..).trans hp) p) (C.path.levels.clock.op i p).ratio]; rfl
lemma under_watch (Q : CellP C k b p) (H : i<k) (hp : middle A b k ≤ i) (Y) (V : Config G (C.side (i+1) p)) (q B t) :
    Healthy t (Spindle.patch (q*B) (core A X b p (show i+1≤k from H) (headMark Y))) (watches C b p ht (i+1) (hp.trans (Nat.le_succ i)) Q V) ↔
    Healthy t (dolmens X b q B ht H (C:=C) Q Y) V := by
  rw [rising ht Q V hp,_root_.YM.Next.Rank.Thirst.s_healthy,dolmens,fine_read X ht Q (headMark Y) H hp,Spindle.patch,swath_iffHalo]; unfold swath; rw [image_singleton]; rfl
end YM.PhysicalNext.InteractingRank
