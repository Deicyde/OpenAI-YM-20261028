import YM.Next.RANK.Flux.Grader
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Coordinates
import YM.TraceExtension.Prom.Hill.Memorandum
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Hill.Tuning
/-!
Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG Wilson MeasureTheory Tapes Spindle Atlas Station Peak Cells Perch Edition Filter Thirst
open scoped BigOperators Classical Topology

variable {V ι κ : Type} [DecidableEq V] [Fintype V] {G : Gauge} {n : Side} {Q : Rep G n} {x : V→Site n} {C : Family G} {N m v k p : ℕ} {s t u y z r e b : ℝ}

lemma ancestor_PSky (Y : Points v) (h : k≤N) (hk : Station.widthSky C.path.levels b k ≤ m) (hu : m ≤ N) (H : FitSky C.path.levels b k Y) : Pertains (Peak.readersSky (C:=C) (b:=b) (p:=p) Y h hu) v:= by
  intro i; let A : (Ship.yardSky C b h p).Cell × Fin v → Site (C.side m p):=readersSky (C:=C) (p:=p) Y h hu (b:=b)
  let F:= C.path.levels; let W:= F.S.toDepth hk p;let B:= F.S.toDepth hu p;let s:= univ.filter fun j=> A j=i
  have hx j: W.parent (A j)=j.1:= by
    let X:= stampSiteSky C b Y h p j
    let v: Station.widthSky F b k ≤ N:= hk.trans hu
    let t:middleSky F b k ≤ N:= (Station.beforeSky F b k).trans h
    let T:= F.S.toDepth (Station.widerSky F b k) p
    have ht := Station.parent_nested T (F.S.toDepth t p) (F.S.toDepth v p) (F.S.toDepth_odd _ _) (F.S.toDepth_odd t _) X
    have hP :(F.S.toDepth t p).parent X=T.embed j.1:= H.stop ..
    change W.parent (B.parent X)=_
    rw [← parent_nested W B (F.S.toDepth v p) (F.S.toDepth_odd _ _) (F.S.toDepth_odd _ _), ht,hP,T.embed_parent]
  change s.card ≤ _; apply (card_le_card (show s ⊆ {W.parent i} ×ˢ (univ (α:=Fin v)) from ?_)).trans
  · rw [card_product,card_univ,Fintype.card_fin]; exact (le_of_eq (congr_arg (· * v) (card_singleton (show (Ship.yardSky C b h p).Cell from W.parent i)) |>.trans (one_mul _)))
  intro j hj; exact mem_product.mpr ⟨mem_singleton.mpr ((mem_filter.mp hj).2 ▸ (hx j).symm),mem_univ _⟩

section
variable [Fintype ι]

end
end YM.Next.Rank.Flux
