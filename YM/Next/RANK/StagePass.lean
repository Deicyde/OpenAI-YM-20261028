import YM.Next.RANK.ShapeS

/-!
# Repeated value step on the request

Offer through Numeric, Pleases and Lens gates. Same weighted marker family,
including non-linear cumulant at every allowed subset. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function MeasureTheory Filter Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset Relation EntryWord
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge}
variable {C : Family G} {i k l j m p q d D a N : ℕ} {R : Lead G C.S p}
variable {hN : k≤N} {b : ℝ} {x : Points m}
variable {c : Course C N p k}
variable {ξ : Purse}
variable {P : (i : ℕ) → Rep G (C.side i p)} {X : AtlasData G C.S p}

-- Mall. A step affidavit Cγ. property Path - sparse hierarchy specialized to window after k producers.
structure MarketGrant (c : Course C N p k) (P : (i : ℕ) → Rep G (C.side i p)) (X : AtlasData G C.S p) (R : Lead G C.S p)
    (ξ : Purse) : Prop where
  fund i : Station.width C.path.levels ξ.band k ≤ i → ∀ h : i ≤ k, Candle c i (P i) (h.trans c.allow)
  paths : ReadySh (A:=C.path.levels) ξ.band X ξ.horizon ξ.era.coast.Q k R
  probes : KFlux (C:=C) k (middle C.path.levels ξ.band k) X ξ R
  invariant : invariantAt (C:=C) k (wood C.path.levels k) p X
  stencil : Hail C k p ξ.taylor X

structure Crew (c : Course C N p k) (P : (i : ℕ) → Rep G (C.side i p)) (R : Lead G C.S p) (ξ : Purse) (x : Points m) : Prop where
  ignition (g : ℕ) (h : g<k) (hk : middle C.path.levels ξ.band k ≤ g) :
    let t:=clim C.path.levels k
    ∃ y : Ignition R ξ.band x c h hk ξ.era.coast.Q ξ.horizon (P (g+1)).p (P g).p (ξ.sends t),
      Pleases ξ.era (P (g+1)) (P g) (ξ.sends t) ξ.goal (a:=ξ.horizon) y (ξ.cash t)
  vitality i : Station.width C.path.levels ξ.band k ≤ i → i<middle C.path.levels ξ.band k →
    NonLeading ξ.era x (Ship.allowance C.path.levels 2 k) c i (P (i+1)) (P i) ξ.band

namespace MarketGrant
variable (F : MarketGrant c P X R ξ)
include F
lemma path : Perch.Path c P c.allow ξ.band:= fun i h H=> F.fund i h (H.trans (before ..))
lemma fixture (H : middle C.path.levels ξ.band k ≤ i) (h : i≤ k) : Candle c i (P i) (h.trans c.allow) := F.fund i ((Station.wider ..).trans H) h
end MarketGrant

variable (F : MarketGrant c P X R ξ)
include F in
lemma alignment (h : Corridor C.path.levels ξ.band ξ k) (hm : middle C.path.levels ξ.band k ≤ j) (hk : j<k) :
    let s:=clim C.path.levels k
    Metal ξ.band c R hk (ξ.sends s) (P (j+1)).p.threshold (P j).p.threshold (knox s) (torque s) ξ.L:= by
  intro s; let A:=C.path.levels;let u:= (show middle A ξ.band k≤ j+1 from hm.trans (Nat.le_succ _))
  have ht(i : ℕ) (he : middle A ξ.band k ≤ i) (hv : i ≤ k) : (P i).p.threshold / anneals C c i ≤ torque s := (Candle.small _ (F.fixture he hv)).trans (h.spend.lots _ (h.court _ ((Station.wider ..).trans he) hv))
  exact ⟨F.paths.withers j hm hk,(F.probes.steps j hm hk).pay,Glimmer.costed _ _ zero_le_one,h.spend.calm,(ht _ u hk).trans h.spend.inside, ht _ hm hk.le,h.spend.transverse,h.spend.budget,F.probes.realPath _ hm hk⟩

variable (O : StampDuty C k N p d ξ.taylor (P k) ξ.era.coast.Q X)
variable (v : Fin m→ C.label d)
variable (H : Corridor C.path.levels ξ.band ξ k) (he : Fit C.path.levels ξ.band k x)
variable (hn : m≤2) (Hv : Crew c P R ξ x)

-- passage at fixed F, x,v; W forecast includes all R.Inc budgets already accumulated



include H he hn Hv F



end YM.Next.Rank.Tapes
