import YM.Next.RANK.Camps
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Coordinates
import YM.TraceExtension.Prom.Hill.Memorandum
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Hill.Tuning
/-!
  Variant of YM.Next.RANK.Camps for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Cells Station Ac Alarm Thirst Corona Value
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {S : Schedule} {C : Family G} {A : Levels G} {i k l j m p q n D N d : ℕ}
variable (A) (x : Points n) (s : ℝ)

section copies
variable (C)
local notation "A'" => C.path.levels

def spreadCSky (p) (h : Station.widthSky A' s k ≤ i) (x : Site (C.S.side (Station.widthSky A' s k) p)) : Site (C.S.side i p):= (C.S.toDepth h p).embed x
lemma fillsSky (p) (hN : k≤N) (h : i≤k) (hv : Station.widthSky A' s k ≤ i) (u : Site (C.S.side (Station.widthSky A' s k) p) × Fin n) :
    let T:=Cells.center C.S p hv 0
    Peak.readersSky (C:=C) (b:=s) (p:=p) x hN (h.trans hN) u=affine (T.omega u.1) (spreadCSky C s p hv u.1) (core A' x s p h u.2):= by
  intro T
  let r:= C.S.toDepth h p
  let Q : i ≤ N:= h.trans hN
  unfold Peak.readersSky ancestor; rw [exact_campSky,parent_nested (C.S.toDepth h p) (C.S.toDepth hN p) _ (C.S.toDepth_odd _ _) (C.S.toDepth_odd _ _),Ratio.embed_parent]
  rw [Tiling.copyMap,affine,translateBy0,embed_comp (C.S.toDepth hv p) r,parent_offset,Ratio.parent_signed _ (C.S.toDepth_odd h p)]; rfl

-- site and hull level shorthand
variable {C}
lemma togetherSky (p) (hN : k≤N) (h : i≤k) (hp : Station.widthSky A' s k ≤ i) (v : (Ship.yardSky C s hN p).Cell) (a b) :
    separation (readersSky (C:=C) (b:=s) (p:=p) x hN (h.trans hN) (v,a)) (readersSky (C:=C) (b:=s) (p:=p) x hN (h.trans hN) (v,b))=
      separation (core A' x s p h a) (core A' x s p h b):= by rw [fillsSky C x s p hN h hp,fillsSky C x s p hN h hp]; exact s_sep ..

end copies

section
variable {c f : Side} (r : Ratio c f)
private lemma parent_WaySky (x y : Site f) : r.count.val*separation (r.parent x) (r.parent y) ≤ separation x y+r.count.val := by
  rw [← Station.both r]; have he:=separation_triangle (r.embed (r.parent x)) x (r.embed (r.parent y)); have hz:=separation_triangle x y (r.embed (r.parent y)); have h:=near r x; have hp:=near r y; rw [separation_comm _ x] at he; omega

end

lemma periodsSky (p) {hN : k≤N} (ha : AllowedSky C.path.levels s k) (hx : FitSky C.path.levels s k x) {h : i≤k} (hv : middleSky C.path.levels s k≤ i) (u v : (Ship.yardSky C s hN p).Cell × Fin n) (hi : u.1 ≠ v.1) (ℓ : ℕ) (hp : ℓ+3 ≤ (C.path.levels.clock.coverSize k)^10) :
    ℓ < separation (readersSky (C:=C) (b:=s) (p:=p) x hN (h.trans hN) u) (readersSky (C:=C) (b:=s) (p:=p) x hN (h.trans hN) v):= by
  let r:=C.S.toDepth hv p; let t:=C.S.toDepth (h.trans hN) p; let ζ:= readersSky (C:=C) (b:=s) (p:=p) x hN (h.trans hN); let b:= C.S.toDepth (widerSky C.path.levels s k) p
  have he (i : (Ship.yardSky C s hN p).Cell× Fin n): r.parent (ζ i)=b.embed i.1 := Eq.trans (parent_nested r t (C.S.toDepth (hv.trans (h.trans hN)) p) (C.S.toDepth_odd hv p) (C.S.toDepth_odd _ _) _).symm (hx.stop ..)
  have ht : ℓ+3≤ separation (r.parent (ζ u)) (r.parent (ζ v)) := by rw [he,he, Station.both]; exact (hp.trans (ha.surplusage p)).trans (Nat.le_mul_of_pos_right _ (separation_pos u.1 v.1 hi))
  exact spends r (i_1:=ζ u) (i_2:=ζ v) (by omega) ℓ (by omega)

-- radii ticket at this plateau. s marker radius
structure roomTestSky (k p c q : ℕ) : Prop where
  parent : 10 ≤ c
  radius : c+10 ≤ q
  suite i (h : middleSky A s k ≤ i) (H : i ≤ k): 2*(q*walls (clim A i)+1) < (A.S.side i p).val
  fresh i (h : middleSky A s k ≤ i) (H : i<k) :
    let r:= (A.clock.op i p).ratio
    q*walls (clim A (i+1))+r.count.val ≤ walls (clim A i)*r.count.val
  birth : ∀ i,middleSky A s k≤ i → i≤k → 8 ≤ walls (clim A i)
  apart : ∀ i,middleSky A s k≤ i → i≤k → 3*q*walls (clim A i)+3 ≤ (A.clock.coverSize k)^10

lemma spends_aloftSky {s} (h : roomTestSky A s k p d q) (hs : j<k) (hi : middleSky A s k≤j) (u v : Site (A.S.side (j+1) p)) (hf : separation u v ≤ q*walls (clim A (j+1))) :
    let r:= (A.clock.op j p).ratio
    separation (r.parent u) (r.parent v) ≤ walls (clim A j):= by
  intro r
  apply Nat.le_of_mul_le_mul_left _ r.count.property
  exact ((parent_WaySky r u v).trans ((Nat.add_le_add_right hf _).trans (h.fresh _ hi hs))).trans_eq (mul_comm ..)
end YM.Next.Rank.Tapes
