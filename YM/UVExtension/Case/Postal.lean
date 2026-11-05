import YM.UVExtension.Case.Valence
import YM.UVExtension.Reward.Lights

/-! Retarget full-sequence receipt. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Case
open Lattice RG Precision Bloch Laurent Filter Function Finset Reward
open WilsonStartup WilsonStartup.Change
open scoped Topology BigOperators Classical
variable {G : Gauge} {a : Levels G} {V W:Horizon a} {P K : MapPrices} {O : ChartRatio G} {s : Supply.Sheet G} {n:ℕ→ℕ}

def actualPay (C : Supply.Sheet G) (P : MapPrices): MapPrices:= (retarget_arc C P).choose
lemma storeReport (h:Free.Report V P)(hv:W.Suffices K)(he: ∀ m,∀ᶠ n in atTop,W.H n m=V.H n m)(hh:∀ m,∀ᶠ n in atTop,W.towers n m=V.towers n m):Free.Report W K:=by
  refine ⟨fun m=>?_,fun i=>?_⟩
  · obtain ⟨T,hT⟩:=h.bed m
    have hp : ∀ᶠ n in atTop,(W.H n m).covered (K.α (a.clock.J m)) (K.Ω (a.clock.J m)):= (eventually_ge_atTop _).mono fun n hn=> hv.rows n m hn
    refine ⟨T,Free.reported (hT.diag.entries.congr' ((he m).mono fun _ hn=> congr_arg Bed.diagonal hn.symm)) (hp.mono fun _ h=> h.1),Free.reported (hT.dual.entries.congr' ((he m).mono fun _ hn=> congr_arg Bed.dual_diag hn.symm)) (hp.mono fun _ h=> h.2.2.2.2),Free.reported (hT.metric.entries.congr' ((he m).mono fun _ hn=> congr_arg Bed.metric hn.symm)) (hp.mono fun _ h=> h.2.1),Free.reported (hT.inverse.entries.congr' ((he m).mono fun _ hn=> congr_arg Bed.inverse hn.symm)) (hp.mono fun _ h=> h.2.2.1),Free.reported (hT.roots.entries.congr' ((he m).mono fun _ hn=> congr_arg Bed.roots hn.symm)) (hp.mono fun _ h=> h.2.2.2.1)⟩
  let j:=a.clock.J (i+1)
  obtain ⟨p,A,B,C,D,E⟩:=h.columns i
  have hu:∀ᶠ n in atTop,(W.towers n i).Deep (K.α j) (K.Ω j) (j-2):=(eventually_gt_atTop _).mono fun n h=> hv.costs n i h
  refine ⟨p, Free.reported (A.entries.congr' ((hh i).mono fun _ h=> congr_arg Towers.A0 h.symm)) (hu.mono fun _ h=> ((h.2.2.2 [] (Nat.zero_le _)).1)), Free.reported (B.entries.congr' ((hh i).mono fun _ h=> congr_arg Towers.T h.symm)) (hu.mono fun _ h=> (h.2.2.2 [] (Nat.zero_le _)).2), Free.reported (C.entries.congr' ((hh i).mono fun _ h=> congr_arg Towers.mf h.symm)) (hu.mono fun _ h=> h.2.2.1),Free.reported (D.entries.congr' ((hh i).mono fun _ h=> congr_arg Towers.mn h.symm)) (hu.mono fun _ h=> h.1),Free.reported (E.entries.congr' ((hh i).mono fun _ h=> congr_arg Towers.o h.symm)) (hu.mono fun _ h=> h.2.1)⟩
end YM.UVExtension.Case
