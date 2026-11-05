import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Grows
/-!
# Connecting to Rank (StagePass etc argument) with softer test

Nylon used instead of MarketGrant. STILL markets actual ephemeral shadow at
(allowed different) β for applying already available theorems that **do not
depend on these density inputs**; have equality at k. Not substituting those
for the density comparisons. Soft exposes Choir on actual c, other
stamp/marker/rank estimates, and softened structure enough for checkout. Does
not provide actual stronger input to Interaction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
    RankCovariance Next.Rank Tapes Perch Paint Spindle Station Peak Ac Thirst Glyph Atlas Value Flux Marker Rise Normal Ribbon Spindle Glyph Exponential Camp Cells Edition Relation EntryWord Alarm Corona
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {N i p k : ℕ} {w r l a : ℝ}
local notation "St" => C.path.levels.clock.op i p
local notation "D" => C.path.levels
local notation "x" => C.path.levels.clock.hatBeta i
local notation "s" => clim C.path.levels k
section
-- terminal family comparison with *end receipts* to use independently of heating
structure Ferm (O : Rep G (C.side i p)) (c : Course C N p k) (hm : i ≤ N):Prop where
  tied : c.Uses i hm O
  proper : ∃ σ g A δ w : ℝ, Station.Meets C.path.levels i p O g A δ ∧ Tissue O σ (C.path.levels.params i).paths A δ w
structure Novice (c : Course C N p k) (i : ℕ) (P : Rep G (C.side i p)) (h : i ≤ N):Prop where
  chand : Ferm P c h
  budget : P.p.B=Perch.walls (C.path.levels.clock.hatBeta i)
  threshold : P.p.threshold=C.path.levels.clock.hatCoupling i* Perch.hot (C.path.levels.clock.hatBeta i)

structure Nylon (c : Course C N p k) (P : (i : ℕ)→ Rep G (C.side i p)) (X : AtlasData G C.S p) (R : Lead G C.S p) (ξ : Purse):Prop where
  use_ i (h : Station.width C.path.levels ξ.band k ≤ i) (H : i ≤ k): Novice c i (P i) (H.trans c.allow)
  backing : ∃ (T : (i:ℕ)→ Rep G (C.side i p)) (c' : Course C N p k), MarketGrant c' T X R ξ ∧ T k=P k
namespace Nylon
variable {P : (i:ℕ)→ Rep G (C.side i p)} {c : Course C N p k} {X R ξ} (F : Nylon c P X R ξ)
include F
lemma fixture (H : middle C.path.levels ξ.band k ≤ i) (h : i≤ k) : Novice c i (P i) (h.trans c.allow):= F.use_ i ((Station.wider ..).trans H) h
lemma paths : ReadySh (A:=C.path.levels) ξ.band X ξ.horizon ξ.era.coast.Q k R:= F.backing.choose_spec.choose_spec.1.paths
lemma probes : KFlux (C:=C) k (middle C.path.levels ξ.band k) X ξ R:= F.backing.choose_spec.choose_spec.1.probes
lemma invariant : invariantAt (C:=C) k (wood C.path.levels k) p X:= F.backing.choose_spec.choose_spec.1.invariant
lemma stencil : Hail C k p ξ.taylor X := F.backing.choose_spec.choose_spec.1.stencil
end Nylon
end
section construct
variable (B : Binding C) (J : ChartRatio G) (F : Course C N p k) (ξ : Purse) (M : C.Makes)
    (H : ShowHours J B ξ k w l r) (Z : Vents B ξ J l r k) (O : Launch C k ξ w a)
    (V : (i:ℕ)→ Rep G (C.side i p)) (A : Whip B J ξ H O F V (Station.width C.path.levels ξ.band k) le_rfl)
include Z O A M
lemma embroidered (hb : 0≤ ξ.band) : Nylon F V (stamp D N p) (short B N p) ξ:= by
  have hx := H.flash.monitor; let L:=Station.width C.path.levels ξ.band k; let G':= (C.path.levels.params k)
  constructor
  · intro i hp hv; by_cases h:i=k
    · subst i
      obtain ⟨⟨T,σ,g,h,h₁,h₂,hu,ht⟩,W,Y⟩:= Paint.lights C F.allow F M O.pane _ A.stops
      exact ⟨⟨T,_,_,_,_,_,hu,cloth _ ht⟩,W,Y⟩
    have hi:i<k:= lt_of_le_of_ne hv h
    obtain ⟨P,U⟩:= A.outer i hp hv
    have he := P.pets
    have hk:(V i).p= _:= P.warm.used
    refine ⟨⟨U,?_⟩,hk ▸ rfl,hk ▸ rfl⟩
    obtain ⟨g,X,e,W,z,hg,h⟩:= groom B J ξ O.coup P.warm
    have hz:= O.coup; have hf:= elongation B J ξ Z O.coup hi hp hb (p:=p)
    have hl : k-i ≤ stretch (C.S.block i).val ξ.band s := by
      rw [show C.S.block i=_ from (sizes_at ξ O.coup hp hi p).1];change _≤ height C.path.levels ξ.band k + surplus C.path.levels k
      rw [← hz.heft.full,← hz.heft.shift]; have hL := (wider (C.path.levels) ξ.band k).trans (before ..); have hv:=wider (C.path.levels) ξ.band k; have ht := before (C.path.levels) ξ.band k; omega
    refine ⟨_,g,_,_,_,⟨hg.same,hg.cap,hg.assigned,hg.positive,hg.entrance,hg.max_threshold,hf.1.rate _ hl, le_rfl⟩,he⟩
  obtain ⟨Y,h,hV,T⟩:= earn_epoch B ξ M O F.allow hx H.oldPrices (H.canvas p)
  let R:= Function.update Y k (V k)
  have hR: R k=V k:= Function.update_self ..
  refine ⟨R,keeping M p N k F.allow,orders B ξ hx O.coup (H.canvas p) _ _ ?_,hR⟩
  intro i hp he; by_cases Hi:i=k
  · subst i; rw [hR]; exact Paint.lights C F.allow _ M O.pane _ A.stops
  rw [show R i=Y i from Function.update_of_ne Hi ..]; exact hV.fund _ hp he
end construct
-- Chorus on these Novices, same Pleases
lemma premiere {m : ℕ} {X R P} {ξ : Purse} {c : Course C N p k} (x' : Points m) (hn : m≤2) (H : Nylon c P X R ξ) (ht : Corridor C.path.levels ξ.band ξ k) (hp : Choir ξ c P R x')
    (hv : Fit C.path.levels ξ.band k x') (hx : ∀ P : BudgetPoint,P.B ≤ walls s →Tickets P (kinetics s)): Crew c P R ξ x':= by
  have hQ i (h : Station.width D ξ.band k ≤ i) (hg : i≤k) := hx (P i).p (show (P i).p.B≤_ by
    have hh : 1 ≤ clim D i:= ((D).fits.delayed _).le; rw [(H.use_ i h hg).budget]; exact wall_mono hh ((D).fits.delayed k|>.le) (ht.court i h hg|>.2))
  constructor
  · intro g h hk t; obtain ⟨v,B,hv₀⟩:= hp.rewrites g h hk
    refine ⟨v,taps (S:=ξ.era) v B hn ht.heft H.paths.canvas hv (H.fixture hk h.le).budget (Real.exp_pos _) (hQ g ((Station.wider ..).trans hk) h.le) hv₀⟩
  intro i h hl; obtain ⟨B,hb⟩:= hp.applies i h hl
  exact tapped _ _ _ (hQ i h (hl.le.trans (before ..))) hb (Real.exp_pos _)
end YM.PhysicalNext.InteractingRank.Soft
