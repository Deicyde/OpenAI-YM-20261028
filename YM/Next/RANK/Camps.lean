import YM.Next.RANK.Pennant
import YM.Next.RANK.Tilt

/-!
# Gradient footprints of k-to-l W

All copies of the SAME tiling. Honor plateaux, canvas is centered on
one chosen center ancestor. Each sh projection will operate on true lifts with
room for mask stencils. Closeness convention on any potentially nonzero
marker pair (single flag budgets can still wind after transfer). -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Cells Station Ac Alarm Thirst Corona Value
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {S : Schedule} {C : Family G} {A : Levels G} {i k l j m p q n D N d : ℕ}
variable (A) (x : Points n) (s : ℝ)

def core (p) (h : i≤k) (a : Fin n) := ancestor A.S p i h (wrap _ (Station.choose A s k x a))
def headMark (f : pennant n) : Fin n := Sum.elim id (fun i=> i.val.1) f

def fog (p d B : ℕ) (h : i≤k) (a : Fin n) (j : Chamber G A.S i p) := separation (core A x s p h a) j.1 ≤ d*B
def cozy (p cₚ B : ℕ) (h : i≤k) : pennant n → Prop := Sum.elim (fun _=> True) (fun i=> separation (core A x s p h i.val.1) (core A x s p h i.val.2) ≤ cₚ * B)

lemma itinerary (p) (h : j<k) (i : Fin n) : core A x s p h.le i=(A.clock.op j p).ratio.parent (core A x s p (show j+1≤k from h) i):= parent_nested _ _ _ (A.S.block_odd _) (A.S.toDepth_odd _ _) _
lemma homeHere (a : Fin n) (k p) : core A x s p (k:=k) le_rfl a= wrap (A.S.side k p) (Station.choose A s k x a):= by
  let r:=A.S.toDepth (show k≤k from le_rfl) p
  have h : r.count.val=1:= Nat.eq_of_mul_eq_mul_left (A.S.side k p).property (r.exact_size.symm.trans (Nat.mul_one _).symm)
  let y:= wrap (A.S.side k p) (Station.choose A s k x a)
  have hp:r.embed y=y:=by rw [Ratio.embed,h,one_smul,wrap_lift]
  change r.parent y=y; exact (congr_arg r.parent hp.symm).trans (r.embed_parent ..)
lemma fifth (i : ℕ) : 0<walls (clim A i):=pow_pos (A.budget i).B_pos _

section copies
variable (C)
local notation "A'" => C.path.levels

def spreadC (p) (h : Station.width A' s k ≤ i) (x : Site (C.S.side (Station.width A' s k) p)) : Site (C.S.side i p):= (C.S.toDepth h p).embed x
lemma fills (p) (hN : k≤N) (h : i≤k) (hv : Station.width A' s k ≤ i) (u : Site (C.S.side (Station.width A' s k) p) × Fin n) :
    let T:=Cells.center C.S p hv 0
    Peak.readers (C:=C) (b:=s) (p:=p) x hN (h.trans hN) u=affine (T.omega u.1) (spreadC C s p hv u.1) (core A' x s p h u.2):= by
  intro T
  let r:= C.S.toDepth h p
  let Q : i ≤ N:= h.trans hN
  unfold Peak.readers ancestor; rw [exact_camp,parent_nested (C.S.toDepth h p) (C.S.toDepth hN p) _ (C.S.toDepth_odd _ _) (C.S.toDepth_odd _ _),Ratio.embed_parent]
  rw [Tiling.copyMap,affine,translateBy0,embed_comp (C.S.toDepth hv p) r,parent_offset,Ratio.parent_signed _ (C.S.toDepth_odd h p)]; rfl

-- site and hull level shorthand
variable {C}
lemma together (p) (hN : k≤N) (h : i≤k) (hp : Station.width A' s k ≤ i) (v : (Ship.yard C s hN p).Cell) (a b) :
    separation (readers (C:=C) (b:=s) (p:=p) x hN (h.trans hN) (v,a)) (readers (C:=C) (b:=s) (p:=p) x hN (h.trans hN) (v,b))=
      separation (core A' x s p h a) (core A' x s p h b):= by rw [fills C x s p hN h hp,fills C x s p hN h hp]; exact s_sep ..

end copies

section
variable {c f : Side} (r : Ratio c f)
private lemma parent_Way (x y : Site f) : r.count.val*separation (r.parent x) (r.parent y) ≤ separation x y+r.count.val := by
  rw [← Station.both r]; have he:=separation_triangle (r.embed (r.parent x)) x (r.embed (r.parent y)); have hz:=separation_triangle x y (r.embed (r.parent y)); have h:=near r x; have hp:=near r y; rw [separation_comm _ x] at he; omega
lemma spends {i_1 i_2} (_h : 3 ≤ separation (r.parent i_1) (r.parent i_2)) (j) (hh : j+2 ≤ separation (r.parent i_1) (r.parent i_2)) : j < separation i_1 i_2 := by
  let y:=separation (r.parent i_1) (r.parent i_2)
  have hp:=parent_Way r i_1 i_2; have he:= Nat.mul_le_mul_left r.count.val hh; have ht:j≤r.count.val*j:= Nat.le_mul_of_pos_left j r.count.property; have hz:0<r.count.val:=r.count.property; linarith only [hp,he,ht,hz]
end

lemma periods (p) {hN : k≤N} (ha : Allowed C.path.levels s k) (hx : Fit C.path.levels s k x) {h : i≤k} (hv : middle C.path.levels s k≤ i) (u v : (Ship.yard C s hN p).Cell × Fin n) (hi : u.1 ≠ v.1) (ℓ : ℕ) (hp : ℓ+3 ≤ (C.path.levels.clock.coverSize k)^10) :
    ℓ < separation (readers (C:=C) (b:=s) (p:=p) x hN (h.trans hN) u) (readers (C:=C) (b:=s) (p:=p) x hN (h.trans hN) v):= by
  let r:=C.S.toDepth hv p; let t:=C.S.toDepth (h.trans hN) p; let ζ:= readers (C:=C) (b:=s) (p:=p) x hN (h.trans hN); let b:= C.S.toDepth (wider C.path.levels s k) p
  have he (i : (Ship.yard C s hN p).Cell× Fin n): r.parent (ζ i)=b.embed i.1 := Eq.trans (parent_nested r t (C.S.toDepth (hv.trans (h.trans hN)) p) (C.S.toDepth_odd hv p) (C.S.toDepth_odd _ _) _).symm (hx.stop ..)
  have ht : ℓ+3≤ separation (r.parent (ζ u)) (r.parent (ζ v)) := by rw [he,he, Station.both]; exact (hp.trans (ha.surplusage p)).trans (Nat.le_mul_of_pos_right _ (separation_pos u.1 v.1 hi))
  exact spends r (i_1:=ζ u) (i_2:=ζ v) (by omega) ℓ (by omega)

-- radii ticket at this plateau. s marker radius
structure roomTest (k p c q : ℕ) : Prop where
  parent : 10 ≤ c
  radius : c+10 ≤ q
  suite i (h : middle A s k ≤ i) (H : i ≤ k): 2*(q*walls (clim A i)+1) < (A.S.side i p).val
  fresh i (h : middle A s k ≤ i) (H : i<k) :
    let r:= (A.clock.op i p).ratio
    q*walls (clim A (i+1))+r.count.val ≤ walls (clim A i)*r.count.val
  birth : ∀ i,middle A s k≤ i → i≤k → 8 ≤ walls (clim A i)
  apart : ∀ i,middle A s k≤ i → i≤k → 3*q*walls (clim A i)+3 ≤ (A.clock.coverSize k)^10

lemma spends_aloft {s} (h : roomTest A s k p d q) (hs : j<k) (hi : middle A s k≤j) (u v : Site (A.S.side (j+1) p)) (hf : separation u v ≤ q*walls (clim A (j+1))) :
    let r:= (A.clock.op j p).ratio
    separation (r.parent u) (r.parent v) ≤ walls (clim A j):= by
  intro r
  apply Nat.le_of_mul_le_mul_left _ r.count.property
  exact ((parent_Way r u v).trans ((Nat.add_le_add_right hf _).trans (h.fresh _ hi hs))).trans_eq (mul_comm ..)
end YM.Next.Rank.Tapes
