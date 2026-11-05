import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Zone

/-!
 Adapted (necessary new cross-Forest support) from accepted E6 Zone.
# Knitting local sector reads
Count weather on a real-sector row in full. No global reusing an off-path
frame or under-budget flags. `V` at physical ends. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel LocalRows
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f n d : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio}
variable {x q : Site c}

/-- Numerical stencil quote (no-mask variant). -/
structure Tuft (X : Coat T F) (X' : Coat T F') (o : Site c) (a : ℕ) : Prop where
  temp : X.x=X'.x
  width : X.width=X'.width
  chi : X.χ=X'.χ
  places y (hi : separation o y ≤ a) : y∈X.seeds.place ↔ y∈X'.seeds.place
  wood (p : Bond f) (hp : distAt S p o≤a) : (p∈F.trunks ↔ p∈F'.trunks) ∧ F.drape X.Y p=F'.drape X'.Y p
  pay : AgreeNear id o a X.V X'.V
  site y (hp : separation o y≤a) : X.k.1 y=X'.k.1 y
  bond p (hp : separation o p.1≤a) : X.k.2 p=X'.k.2 p

namespace Tuft
variable {X : Coat T F} {X' : Coat T F'} {a b : ℕ}
variable (h : Tuft X X' x a)
include h

lemma tune_down (he : separation x q + b ≤ a) : Tuft X X' q b := by
  have he y (hp : separation q y ≤ b) : separation x y ≤ a := (separation_triangle x q y).trans (by omega)
  exact ⟨h.temp,h.width,h.chi,fun i hi=> h.places i (he _ hi),fun i hi=> h.wood i (he _ hi), fun i hi=> h.pay i (he _ hi),fun i hi=> h.site _ (he _ hi),fun i hi=> h.bond _ (he _ hi)⟩

lemma covert (y : Site c) (hi : separation x y+b ≤ a) : Inside y X.seeds b ↔ Inside y X'.seeds b := by
  have he t (hp : separation t y≤b) := h.places t (by rw [separation_comm] at hp; exact (separation_triangle x y t).trans (by omega))
  unfold Inside dome; simp only [halo_spec]; constructor
  · rintro ⟨i,hk,hp⟩; exact ⟨i,(he _ hp).mp hk,hp⟩
  rintro ⟨i,hk,hp⟩; exact ⟨i,(he _ hp).mpr hk,hp⟩
lemma forward (p : Bond f) (he : distAt S p x+1+b≤a) : voyage X.seeds b p ↔ voyage X'.seeds b p := by
  have hf i (hp : i∈ends S p) : Inside i X.seeds b ↔ Inside i X'.seeds b :=
    h.covert i (by have hh := stride p hp; unfold distAt at *; rw [separation_comm] at hh; have hz := separation_triangle x (atEdge S p) i; omega)
  unfold voyage; simp only [not_disjoint_iff]; constructor
  · rintro ⟨a,hk,hp⟩; exact ⟨a,(hf a hp).1 hk,hp⟩
  rintro ⟨a,hk,hp⟩; exact ⟨a,(hf a hp).2 hk,hp⟩
lemma tides (p : Bond f) (he : distAt S p x+1+10*X.B≤a) : X.Hot p ↔ X'.Hot p := by
  unfold Hot Shell.active; rw [show X'.B=X.B from congr_arg radiusB h.temp.symm]
  exact and_congr (h.wood p (by omega)).1.not (h.forward p he).not
lemma replica_here (p : Bond f) (he : distAt S p x≤a) : replica S.ratio X.V p=replica S.ratio X'.V p := by
  unfold replica; split
  · rfl
  next hz => exact h.pay _ he
lemma reports (p : Bond f) (he : distAt S p x+1+10*X.B≤a) {u w : Directions G f} (hg : X.Hot p → u p=w p) :
      X.input u p=X'.input w p ∧ X.signal u p=X'.signal w p := by
  by_cases H : X.Hot p
  · have hf := (h.tides p he).1 H
    rw [X.viewing u p H, X'.viewing w p hf, X.at_hot u p H,X'.at_hot w p hf]; unfold increment
    rw [hg H, h.replica_here p (by omega)]; exact ⟨rfl,rfl⟩
  have hf := mt (h.tides p he).mpr H
  obtain ⟨hz,hx⟩ := h.wood p (by omega)
  rw [X.dormant _ _ H,X'.dormant _ _ hf]; refine ⟨hx,?_⟩
  simp only [signal, Coat.lens,saved, H,hf,if_false,or_false, hz,Pi.add_apply,add_zero]
  split
  · rfl
  unfold small; rw [h.chi,h.width,hx,h.replica_here p (by omega),show X.t=X'.t from by unfold Coat.t; rw [h.temp]]

lemma predicts (p : Site c) (hm : separation x p+b+predReach S.patch+1 ≤ a) (U U' : Config G f)
    (hp : AgreeNear S.ratio.parent p (b+predReach S.patch+1) U U') (hZ : Room P S T X.x) :
    AgreeNear id p b (S.prediction U X.k) (S.prediction U' X'.k) := by
  have hv := funds_branch hZ.accepted
  intro i hi
  change separation p i.1 ≤ b at hi
  have ht := separation_triangle x p i.1
  apply (Emblems.choices U U' i X.k X'.k hv (h.site _ (by omega)) (h.site _ ?_) (h.bond i (by omega)) (hp.shrink (by omega))).2.2
  have hs := separation_triangle x i.1 (i.1+step i.2); have hj := sep_step i.1 i.2; omega

lemma patrol (s : Signed) (p : Rod c f) (hq : x=s.act (focus S p)) (he : X.B ≤ a) (hp : Room P S T X.x) :
    request T X.x (choice s X.k) (pull s 0 X.V) p=request T X'.x (choice s X'.k) (pull s 0 X'.V) p := by
  subst x
  have hm := funds_branch hp.accepted
  let z := replica S.ratio X.V; let z' := replica S.ratio X'.V
  let x:= focus S p; let B:=X.B
  have hB : 4* X.R+4+predReach S.patch ≤ X.B/100 := hp.sight.2
  have hb : AgreeNear S.ratio.parent (s.act x) a z z' := fun i hi=> h.replica_here i hi
  have hc := Zone.nearV s (q':=x) (b:=X.B/4) (h.pay.shrink (by change separation (s.act x) (s.act x)+_ ≤ a; rw [separation_self]; omega))
  unfold request baseStroke; rw [← h.temp,costsX hp p hc]
  unfold entryCost; rw [← Channel.pulls_replica (S:=S) s X.V, ← Channel.pulls_replica (S:=S) s X'.V,(carry s hm X.k (replica S.ratio X.V)).2,(carry s hm X'.k (replica S.ratio X'.V)).2]
  rw [costsy hp p (hc.shrink (by rw [separation_self]; omega)) ?_ ?_]
  swap
  · refine Zone.nearU S s (hb.shrink ?_); change separation (s.act x) (s.act x)+ (X.B/4+1)≤a; rw [separation_self]; omega
  apply Zone.nearV s (h.predicts (s.act x) ?_ z z' ?_ hp)
  · change separation (s.act x) (s.act x)+ (0+1)+_+_≤_; rw [separation_self]; omega
  apply hb.shrink; rw [separation_self]; omega
lemma blanked : Tuft X.blank X'.blank x a := ⟨h.temp,h.width,h.chi,fun _ _ => Iff.rfl, h.wood,fun _ _=>rfl,h.site,h.bond⟩
end Tuft
end YM.ConnectedActivityE6
