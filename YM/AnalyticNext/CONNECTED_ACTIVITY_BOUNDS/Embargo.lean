import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Mint
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Palace


/-!
# Packet attachment masks

Profiles are *partition weights*. All put on the candidate in full,
with near/far predicate via ANY touch (preassigned radii on projected
footprints). Tags and V flags read in the same sector. Stipulated JOIN
radius on seed halos for words is 500B; `Installed` suffices for
retaining the exact payments even in standalone uses where off-support
V flags retained for estimating would have enlarged a packet. The local
formula still tests the answer with the same p, not a saturated p after
that hypothetical off-support change.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Rates
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S}

section masks
variable (p : Stores S)

-- location rule independent of p except place; we can keep radii even
-- where projection counts unwrapped large enough to cover full torus

def padF (p : Stores S) (d : ℕ) := univ.filter (fun i => ¬ Disjoint (p.dome d) (startPos S i))
def padI (p : Stores S) (d : ℕ) := univ.filter (fun i => ¬ Disjoint (p.dome d) (pinPos i))
def padB (p : Stores S) (d : ℕ) := univ.filter (fun i => ¬ Disjoint (p.dome d) (points S i))

structure Installed (A : Stores S) (d : ℕ) : Prop where
  part : Packets.seeds S p ⊆ Packets.seeds S A
  sealed : ∀ i ∈ Packets.seeds S A, ¬ Disjoint (p.dome d) (Packets.points S i) → i∈Packets.seeds S p





lemma facesLocal {m b : ℕ} {a v : Site c} (hx : a∈p.dome b) (h : separation a v+b ≤ m) :
    v∈p.dome m := by
  obtain ⟨o,ho,he⟩ := halo_spec.mp hx; exact halo_spec.mpr ⟨o,ho,(separation_triangle o a v).trans (by omega)⟩

-- use p recipe at arbitrary z for assignment against A; doesn't need
-- seed Halo disjoint through 500*2 from actual completion


def fine (q : Chi) (x : ℝ) (U : Config G f) (i : Cell f) :=
    let h := q.innerShare (fiery G x S.patch.L / 4) (toll U i)
    if i∈p.costs then 1-h else h

def wireMask (q : Chi) (W x : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c) (i : Bond c) :=
    let h := q.innerShare (W*fiery G x S.patch.L) (wire (S.prediction U k) V i)
    if i∈p.aisles then 1-h else h

lemma thread (q : Chi) (W x : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c)
    (h : p.flags= RG.flags (temp x) V) : q.distribute p x W U k V =
      (∏ i, fine p q x U i)* ∏ i, wireMask p q W x U k V i := by
  unfold fine wireMask Chi.distribute; rw [if_pos h.symm]; unfold Chi.fineShare Chi.bondShare Chi.share
  have he {ι : Type} [Fintype ι] [DecidableEq ι] (s : Finset ι) (v : ι→ℝ) : (∏ i,if i ∈ s then 1-v i else v i) =
      (∏ i∈s,(1-v i))*(∏ i∈sᶜ,v i) := by
    let w i := if i∈s then 1-v i else v i
    rw [← show ((∏ i∈s,w i)*∏ i∈sᶜ,w i) = _ from Finset.prod_mul_prod_compl s w]
    exact congr_arg₂ _ (prod_congr rfl fun i hi => if_pos hi) (prod_congr rfl fun i hi => if_neg (mem_compl.mp hi))
  -- Classical defeq proof eq
  exact congr_arg₂ _ (he p.costs (fun i => q.innerShare (fiery G x S.patch.L / 4) (toll U i))).symm
    (he p.aisles (fun i => q.innerShare (W*fiery G x S.patch.L) (wire (S.prediction U k) V i))).symm

/-- The compulsory masks, at all physical locations. q_x factors (on U,
would-be missing flag indicators) depend on K choices; charge separately. -/
def curb (V : Config G c) (k : S.Choices) (W x : ℝ) (q : Chi) (U : Config G f) :=
    let R := 300*radiusB x
    (∏ i∈ padF p R, fine p q x U i)*
      (∏ i∈ padI p R, wireMask p q W x U k V i)*
        (∏ i∈ p.dome R, αSite U i k)* (∏ i∈ padI p R, αBond U i k)

-- local guard, preserve real η likelihood incl on boundaries.
structure Check (V : Config G c) (W x : ℝ) (U : Config G f) (k : S.Choices) (d : ℕ) : Prop where
  fine : ∀ i ∈ padF p d, (i∈p.costs → fiery G x S.patch.L/4 ≤ toll U i) ∧
    (i ∉ p.costs → toll U i ≤ fiery G x S.patch.L/2)
  wire : ∀ i ∈ padI p d, (i∈p.aisles → W*fiery G x S.patch.L ≤ wire (S.prediction U k) V i) ∧
    (i∉p.aisles → wire (S.prediction U k) V i ≤ 2*W*fiery G x S.patch.L)
  α : ∀ i ∈ p.dome d, 0 < S.patch.frameMass S.kernel (expandAt (S.ratio.embed i) U) (k.1 i)




end masks
end YM.AnalyticNext.ConnectedActivity.Aff
