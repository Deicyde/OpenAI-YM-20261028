import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.District

/-!
# Drows stencil congruences, tested even in flagged regions

At fixed K use Turn. Sector selections & κ distribution later.
No V clipping tricks on hard rows. True path/cut. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.LocalRows
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f n d : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {x : ℝ} {L : Side}

section travel
variable (o : Site n→ Site d) (ho : ∀ x: Site n, ∀ i:Axis,separation (o x) (o (x+step i)) ≤ 1)
variable (W Y : Config G n) (i : Cell n)
include ho
lemma facesight (h : AgreeNear o (o i.1) 4 W Y) : faceValue W i=faceValue Y i :=
    travel_near _ ho _ _ _ _ 4 le_rfl h

lemma fitting (p : Clip) {t : ℝ} {B : ℕ} (he : ∀ k : Site n,t*Real.exp ((separation i.1 k:ℝ)/p.relaxation)<2 →
    separation (o i.1) (o k)+4 ≤ B) (hh : AgreeNear o (o i.1) B W Y) :
    PathData.kept p t i.1 W ↔ PathData.kept p t i.1 Y := by
  unfold PathData.kept; refine forall_congr' fun j => ?_; by_cases hk : t * Real.exp ((separation i.1 j.1 : ℝ)/p.relaxation)<2
  · rw [facesight _ ho _ _ j (hh.shrink (he _ hk))]
  exact iff_of_true ((G.chord_le_two _).trans (le_of_not_gt hk)) ((G.chord_le_two _).trans (le_of_not_gt hk))
end travel

variable {V W : Config G c} {U U' : Config G f}
variable (h : Room P S T x)
include h
lemma ufront (p : Cell f) (hp : AgreeNear S.ratio.parent (S.ratio.parent p.1) (radiusB x/8) U U') :
    crown T.up T.high (till x) 1 (Pressure.fiery G x S.patch.L) U p=crown T.up T.high (till x) 1 (Pressure.fiery G x S.patch.L) U' p := by
  have hh := h.sight
  have he' : PathData.kept T.high (Pressure.fiery G x S.patch.L) p.1 U ↔ PathData.kept _ _ _ U' :=
    fitting _ (parent_step S) U U' p _ (fun i hi => (by
      have he := h.laneU _ hi
      have hk := Work.E04.parent_separation S.ratio p.1 i; omega)) hp
  unfold crown Pressure.trunk; rw [he',facesight _ (parent_step S) U U' p
    (hp.shrink (by rw [separation_self]; omega))]
  split
  next hk => rw [show shorten _ _ _ _ p=shorten T.up (till x) 1 U' p from plotted_near _
    (parent_step S) U U' T.high T.up (till x) 1 (p,true) le_rfl (hp.shrink (by
      change separation (S.ratio.parent p.1) (S.ratio.parent p.1)+_ ≤ _; rw [separation_self]; omega))]
  rfl

lemma coastfront (p : Cell c) (hp : AgreeNear id p.1 (radiusB x/8) V W) :
    let h:=Pressure.temp x; let R:=till x; let A:=T.low
    crown T.down A R S.patch.L.val h V p=crown T.down A R S.patch.L.val h W p ∧
      ∀ i, T.vision R h V (p,i)=T.vision R h W (p,i) := by
  intro u R A; have he := h.sight
  have hp' (p' : Cell c) (hf : separation p.1 p'.1 +4 ≤ radiusB x/8) : faceValue V p'=faceValue W p' :=
    facesight _ (sep_step (c:=c)) V W _ (hp.shrink hf)
  have hh : PathData.kept A u p.1 V ↔ PathData.kept _ _ _ W := fitting id (sep_step (c:=c)) V W p _ (fun i hi => by
    have he' := h.laneV _ hi; change separation p.1 i+_≤_; omega) hp
  have hv : faceValue V p=faceValue W p := hp' p (by rw [separation_self]; omega)
  have hz : shorten T.down R S.patch.L.val V p=shorten T.down R S.patch.L.val W p :=
    plotted_near id (sep_step (c:=c)) V W A T.down R _ (p,true) S.patch.L.property (hp.shrink (by
      change separation p.1 p.1+ (R+4)≤_; rw [separation_self]; unfold R; omega))
  refine ⟨by simp only [crown,Pressure.trunk,hh,hv,hz],fun i=>?_⟩
  change thinned T.down A _ _ _ _ _=thinned T.down A _ _ _ _ _
  simp only [thinned, Pressure.toll, shoot, hh,hv,hz]

lemma sharePay {ι : Type} (Q : Config G c→ι→Twin c→Pay G) (p : ι → Site c)
    (hq : Rule (till x) Q p (fun i => i.1.1)) (i : ι)
    (he : AgreeNear id (p i) (radiusB x/4) V W) :
    zip (Q V) (T.vision (till x) (Pressure.temp x) V) i = zip (Q W) (T.vision (till x) (Pressure.temp x) W) i := by
  have ht := h.sight
  unfold Pressure.zip; refine sum_congr rfl fun j _=> ?_
  rw [hq.stencil _ _ _ (he.shrink (by rw [separation_self]; omega)) _]
  by_cases hh : Q W i j=0
  · rw [hh,_root_.zero_apply,_root_.zero_apply]
  have hy := hq.reach W i j hh
  rw [(coastfront h j.1 (he.shrink (by omega))).2]

lemma costsX (p : Rod c f) (he : AgreeNear id (focus S p) (radiusB x/4) V W) : guide T x V p=guide T x W p := by
  rcases p with j|j
  · exact sharePay h (T.Φ (till x)) (fun i=> S.ratio.parent i.1.1) (crosses _ _ _ h.accepted) _ he
  exact sharePay h (T.Φ' (till x)) Prod.fst (sameLevel _ _ S.patch.L.property T.R.mn
    (Row.rights _ _ h.accepted.crosses.1 P.width.le) pole mesh) _ he

lemma costsy (p : Rod c f) {Z Y : Config G c} (he : AgreeNear id (focus S p) 0 V W)
    (hp : AgreeNear id (focus S p) 0 Z Y) (hh : AgreeNear S.ratio.parent (focus S p) (radiusB x/4) U U') :
    Sum.elim (T.Xf (till x) U) (Tube.Z S Z V) p=Sum.elim (T.Xf (till x) U') (Tube.Z S Y W) p := by
  rcases p with p|p
  · change AgreeNear S.ratio.parent (S.ratio.parent p.1.1) _ _ _ at hh
    exact plotted_near _ (parent_step S) U U' T.high T.up _ _ p le_rfl (hh.shrink (by
      rw [separation_self]; have hz := h.sight; omega))
  simp only [Sum.elim,Tube.Z]; rw [he p (by simp [focus]),hp p (by simp [focus])]
end YM.ConnectedActivityE6.LocalRows
