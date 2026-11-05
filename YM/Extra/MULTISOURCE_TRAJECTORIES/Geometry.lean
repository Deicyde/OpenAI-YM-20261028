import YM.Extra.MULTISOURCE_TRAJECTORIES.Localization
import YM.Extra.MULTISOURCE_TRAJECTORIES.Probes
import YM.Work.I03
/-!
# Transporting actual stencil receipts, collisions and phase positions

Retain every marked name through parent projections; image on SITES does not
quotient names (even when points coincide). The core of every local coefficient
includes the entire projected physical stencil. Its window and final flag tests
are additional dependencies; no claim that integration is local just on the
parent-projected cores.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories
open Wilson RG Lattice Function Finset Marker Overlay Mix
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {N p : ℕ}

def ancestor (H : History G) (p N j : ℕ) : Site (H.S.side N p) → Site (H.S.side j p) :=
  if h : j=N then by subst j; exact id else if j<N then (H.levels.clock.op j p).ratio.parent ∘ ancestor H p N (j+1) else 0
termination_by N-j

@[simp] lemma ancestor_top (H : History G) : ancestor H p N N = id := by rw [ancestor]; simp
lemma ancestor_step (H : History G) {j : ℕ} (hj : j<N) : ancestor H p N j = (H.levels.clock.op j p).ratio.parent ∘ ancestor H p N (j+1) := by
  rw [ancestor]; simp [hj,hj.ne]

variable {C : Family G} {V : Type}
namespace Probes
variable (Q : Probes C V N p)

def positions (j : ℕ) (i : V) := ancestor C.path p N j (Q.place i)
def cores (j : ℕ) (i : V) := (Q.footprint i).image (ancestor C.path p N j)
lemma anchored (h : C.Makes) (j : ℕ) (i : V) : Q.positions j i ∈ Q.cores j i := mem_image_of_mem _ (Q.marked h i)
lemma parent_step {j : ℕ} (hj : j<N) (i : V) : (C.path.levels.clock.op j p).ratio.parent (Q.positions (j+1) i) = Q.positions j i := by simp [positions,ancestor_step _ hj]


lemma center_positions {m d j : ℕ} (C : Family G) (p : ℕ) (hm : m≤N) (v : C.label d)
    (h₁ : m≤j) (h₂ : j ≤ N) (k) : (center C p hm v).positions j k = camp C p m j k := by
  have ht (hn : m≤N) : (center C p hn v).positions N k = camp C p m N k := by rw [positions,ancestor_top,id_eq,center_place]
  revert hm
  induction h₂ using Nat.decreasingInduction with
  | self => exact ht
  | of_succ i hi ih =>
    intro hN
    rw [← Probes.parent_step _ hi,ih (h₁.trans (Nat.le_succ i)),← Work.I03.camp_step C p h₁,Ratio.embed_parent]

variable [Fintype V] [DecidableEq V] (R : Census V) {j : ℕ} (W : Windows (C.side j p))
abbrev layers := Q.toInsertions.fragments R W (Q.positions j) (Q.cores j)

lemma ready (h : C.Makes) (hj : j≤N) : (Q.layers R W).Ready := Q.toInsertions.ready R W _ _ (Q.symmetric h) hj (Q.anchored h _)







/-- Separation for feeding Stubs and recycling a mixed provisional radius
*if* the current shape really uses the promised cover size, big enough. -/
lemma center_far {m i d : ℕ} (hN : m≤N) (v : C.label d) (h : C.Makes) {t : ℝ} (ht : 1≤t)
    (hh : ticket C t N p m i hN) (hb : 8 ≤ C.path.levels.clock.coverSize j)
    (hi : i≤j) (hm : m≤j) (hj : j ≤ N) :
    Stubs.far (A:=((center C p hN v).layers (Stock.census _) W).bands) := by
  intro a b hab; have he := hh.2.2 j hi hj a b hab
  have hv : ((C.path.levels.clock.coverSize j)^2:ℕ) ≤ separation (camp C p m j a) (camp C p m j b) := by
    exact_mod_cast ((le_mul_of_one_le_right (sq_nonneg _) ht).trans he)
  unfold Layers.bands layers Insertions.fragments; dsimp only
  rw [center_positions C p hN v hm hj,center_positions C p hN v hm hj,(h.wilson.represents N p j hj).vac]; exact ⟨hb,by simpa [Levels.budget,pow_two] using hv⟩
end Probes

section Reverse
 
variable {c f : Side} (S : StepData c f)








end Reverse
end YM.Extra.Trajectories
