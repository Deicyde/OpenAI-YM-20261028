import YM.WilsonBulk.Broadcast.Home
import YM.WilsonBulk.Bunting.Rewards
import YM.AnalyticNext.QUARTIC_MATCH.Mint.Layout

/-!
# Public structural receipt for exact step on all permitted meshes

Footprint at this step in supplied Horizon.

No L threshold yet (can plan
  narrower widths and height-growth later).

Positivity obtained independently
  and not assumed about living clouds.

Reuses accepted lemma extending A0
  matrix trial to any period.

No reliance on actual chosen divisibility.

`Seek` specific P L, Q lattice and flat witnesses, no assumptions
  on W Swedish regulator.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Parapet
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius
open Lattice Laurent Filter Equiv Function Bloch Matrix Precision Stationary Audience Exterior Wilson Tree
open Work.F08 RG Sheet Pert.Bulk Atelier FreeResolvent Work.F08 Lifted
open AnalyticNext.QuarticMatch
variable {G : Gauge} {c f : Side} {B Q : Bed} {P : Patch} {K : KernelChoices} {T : Model P K} {J : ChartRatio G}

abbrev draftAt := Sheets.stepAt
abbrev trimSide (P : Patch) (c : Side) := c*P.L
structure Passage (J : ChartRatio G) (B Q : Bed) (T : Model P K) : Prop where
  stool : P.Branches K G
  toll : LocalRatio J
  harbor_funds : ∃ q>0,∃ C,B.metric.strip q C
  roof : ∃ η>0,∃ C, Q.metric.strip η C
  chairs : ∀ n : Side, ∃ q>0, Ticket q n B
  choice : ∀ c : Side, Consoles B Q (Sheets.stepAt P K c)
  spectral : ∃ σ>0,∃ C:ℝ,0≤ C ∧ Serves G T B σ C
namespace Passage
variable (h : Passage J B Q T)
include h
lemma summit_here : Pamphlet (summit G B) := by obtain ⟨q,hq,C,hv⟩:= h.harbor_funds; exact summit_public _ (actionKernel_strip hq.le hv) hq
lemma summit_next : Pamphlet (summit G Q) := by obtain ⟨q,hq,C,hv⟩:= h.roof; exact summit_public _ (actionKernel_strip hq.le hv) hq
lemma auditions (n : Side) : volumeTape (Sheet.issue n (summit G B))= grains (matrixK G n B) := by obtain ⟨q,hq,C,hv⟩:= h.harbor_funds; exact summit_tape _ hq.le hv n
lemma auditions_next (n : Side) : volumeTape (Sheet.issue n (summit G Q))= grains (matrixK G n Q) := by obtain ⟨q,hq,C,hv⟩:= h.roof; exact summit_tape _ hq.le hv n
lemma perimeter {D : ℕ→ Side} (hD : Tendsto (fun i=> (D i).val) atTop atTop) : ∀ᶠ i in atTop,Bid.Larger (G:=G) (draftAt P K (D i)) := by
  obtain ⟨m,hm⟩:= Primitives.TwoWave.RealSlice.dock_larger P K h.stool; exact (hD.eventually_ge_atTop m).mono (fun i hi=>hm _ hi)
lemma hears {I : Library G} (hu : Pamphlet I) : Pamphlet (pressureI J T B Q I) := by
  obtain ⟨σ,hs,C,hC,hh⟩:= h.spectral
  obtain ⟨p,hp,hA⟩:= (Stamped.flare (G:=G) (P:=P)).bound σ
  exact press_public J T B Q I hu h.summit_next hs hh.width (charge T B hs.le hh.width hA) hC
lemma peers {D : ℕ→ Side} (hd : Tendsto (fun i=> (D i).val) atTop atTop) {I : Library G} (hu : Pamphlet I) : dean D (fun i=> torch J T B Q I (D i)) (pressureI J T B Q I) := by
  obtain ⟨σ,hs,C,hC,hh⟩:= h.spectral; obtain ⟨p,hp,hA⟩:= (Stamped.flare (G:=G) (P:=P)).bound σ
  obtain ⟨q,hq,L,hL⟩:= h.roof
  exact arrival J T B Q I hd hu hs (actionKernel_strip hq.le hL) hq hh.width (charge T B hs.le hh.width hA) hC
omit h in
lemma actual {A : Levels G} {i N : ℕ} {H : Horizon A} {F : MapPrices}
    (hF : H.Suffices F) (he : i<N) (T : historyModel A i) (hJ : LocalRatio J) : Passage J (H.H N (i+1)) (H.H N i) T := by
  let σ j:= F.α (stage A j); let L j:= F.Ω (stage A j); let P:=historyPatch A i
  have hx (j : ℕ) : 0<σ j:=F.alpha_pos _
  have hr j (h:j≤N) : (H.H N j).metric.strip (σ j) (L j):= (hF.rows N j h).2.1
  have hl : P.Branches A.clock.kernel G := (A.blocks i 0).branches
  refine ⟨hl,hJ,⟨σ (i+1),hx _,L (i+1),hr _ he⟩,⟨σ i,hx i,L i,hr i he.le⟩,fun n=>⟨F.η (stage A (i+1)), F.eta_pos _,floor_qual (hF.all _ _ he n)⟩,fun c=> ⟨_, (Mint.visit hF he c).2⟩,?_⟩
  obtain ⟨S,HX,HW⟩:= preflight G A.clock.kernel F; obtain ⟨p,hp,hQ,hk⟩:= HW _ P rfl hl T
  exact ⟨S (stage A (i+1)),(HX _).1,p,hp,hk A H hF (i+1) N he rfl⟩
end Passage
end Parapet
end YM.WilsonBulk
