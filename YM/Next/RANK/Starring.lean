import YM.Next.RANK.Invite
import YM.Next.RANK.Tilt

/-!
# Initial uncorrected array receipt

See Setup (Ratchet and Concord); supplies into comparison for this epoch
including orientations of replicated stamps. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Ribbon
open Function Filter RG Thirst Baler Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Station Cells Spindle Atlas Edition Normal LiftMark Rise Paint MvPolynomial
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {C : Family G} {N k p j d D m : ℕ}
variable {X : Points (m+1)} (P : Fin (m+1) → C.label d)

def kicks {Q Y X Q₀} (P : Fin (m+1) → C.label d) (F : StampDuty C k N p d D Y Q X) (s : ℝ) (hN : k ≤ N) :=readyH m (scouts C k) Q₀ s hN P (fun j=> F.coupon (P j))

-- Exact boot result at this stamp; radius from caller (will use same value for repainting at l). Additional data requested at k across n all fiend tests.
structure Boot (k d D : ℕ) (a : ℝ) (m : ℕ) (s y : ℝ) (Q : Points (m+1)) (P : Fin (m+1) → C.label d) (H : C.Makes) : Prop where
  parcel (hp : C.ref d≤ k) (hv : year C D k) {N p : ℕ} (hN : k≤N) (F : Course C N p k) (L : Rep G (C.side k p))
      {v u x} (K : TableReady C k x v u) (J : survivors C N k p K L) {q c S} (Φ : StampDuty C k N p d D L q S)
      (hS : Rocket y v x u c q D a (clim C.path.levels k) (C.path.levels.params k)) (hZ : Allowed C.path.levels s k) (hi : Fit C.path.levels s k Q) :
    ∀ V : Fin (m+1) → C.label d,(∀ i, Price.Solves C (Station.mag C.path.levels s k) d k N p Φ.T (P i) (V i)) →
      let b:=clim C.path.levels k
      let e:=s*d + saves C d
      (∀ i,coin (Φ.W (V i))≤bill e b) ∧ (Stake m Q s hN V H hp F (Hat b^a) →
        Rod m Q s hN V F L (kicks V Φ s hN (Q₀:=Q)) v (bill y b) (bill (-(c:ℝ)) b) (Real.exp (-trib u b)))

theorem boot (g : G.Simple) (h : C.Makes) (b : ℝ) (X : Points (m+1)) (hx : X∈generic _) (s y : ℝ) (hs : 0<s) (hy : y+s*d+saves C d ≤ -8) (D : ℕ) :
    ∀ᶠ k in atTop, Boot k d D b m s y X P h:= by
  filter_upwards [Edition.raise C X g hx hs, eventually_all.mpr (fun i=> StampDuty.procure C g h d D (P i) s hs y hy)] with k hP hQ
  refine ⟨fun hp hv {N p} hN F L {v u x} K J q c S Φ hS hZ hi V H=> ?_⟩
  let B:=clim C.path.levels k; let E:= s*d+saves C d
  have he (i): Perch.bill y B*moneys C d k N p (V i) ≤ bill (-8) B ∧ coin (Φ.W (V i))≤Perch.bill E B:= hQ i hv N p hN Φ _ (H i)
  exact ⟨fun i=>(he i).2, admits h hp hN K J m c D q X V F hS (fun i=>signet 0 _ (Φ.W (V i))) s (hP hi hZ p N hN) (fun i=> (he i).1) (fun i => Φ.coupon (V i))⟩

end YM.Next.Rank.Ribbon
