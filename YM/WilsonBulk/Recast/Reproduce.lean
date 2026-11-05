import YM.WilsonBulk.Recast.Fees

/-!
# Producer on ANY finite depth cutoff with complete general-order recursion and invariance.

Not a representation-quantitative contract on repeated estimates yet (later consumer).
Exports theory exactly with same positivity width lenses & reset ratio as specified upTerm,
using ANY fitted construction passing horizon and stage. Gives true formal-Wilson
coefficients (here unmarked vacuum) at all pertinent orders. These enter marks. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Parapet
open Recall Topology Function Filter Finset Lattice Laurent RG Precision Pert.Bulk Sheet
open PowerSeries
open scoped Topology BigOperators Classical
variable {G : Gauge} {A : Levels G} {H : Horizon A} {F : MapPrices}
-- formal choices B crossing, colors unified ANY. T repeated across blocks ALL periods.
-- supplied tree later can specialize to stated translated coordinate tree, tree law reindexes.
structure Motions (A : Levels G) where
  j : ChartRatio G
  k : G.ColorIndex
  tree (i : ℕ) : historyModel A i
lemma Motions.exists (A : Levels G) (h : G.Simple) (J : ChartRatio G) : Nonempty (Motions A) := by
  have hx : Nonempty G.ColorIndex := by
    haveI := Gauge.Simple.nontrivial_color h; obtain ⟨x,y,H⟩:= exists_pair_ne G.Color; obtain ⟨i,_⟩: ∃ i:G.ColorIndex,x i ≠ y i:=by contrapose! H; ext i; exact H _
    exact ⟨i⟩
  exact ⟨⟨J,hx.some,fun i=> Primitives.TwoWave.RealSlice.model ..⟩⟩
variable (H) (M : Motions A)
def theatre (k i : ℕ) (V : Library G) := pressureI M.j (M.tree i) (H.H k (i+1)) (H.H k i) V
def apotheosis (k : ℕ) : ℕ → Library G
| i=> if i < k then resetI M.k (theatre H M k i (apotheosis k (i+1))) else if i=k then upstream G else 0
termination_by i=> k-i
decreasing_by omega
lemma initiated (i : ℕ) : apotheosis H M i i=upstream G := by rw [apotheosis,if_neg (lt_irrefl _),if_pos rfl]
lemma recursed {i k : ℕ} (hi : i < k) : apotheosis H M k i= resetI M.k (theatre H M k i (apotheosis H M k (i+1))) := by rw [apotheosis, if_pos hi]
variable {M} {H}
-- expose complete kinetics and ratio reset to future consumers
lemma kernel_run (hJ : LocalRatio M.j) (he : H.Suffices F) (k m : ℕ) (hm : m ≤ k) : Healthy M.k (apotheosis H M k m) (H.H k m) := by
  induction hm using Nat.decreasingInduction with
  | self=> rw [initiated]; exact starts _ he k
  | of_succ i hi h => rw [recursed H M hi]; exact shelf _ _ _ _ _ (Passage.actual he hi (M.tree i) hJ) _ h.report h.crests (price_at_horizon he hi.le M.k)
def drive (H : Horizon A) (M : Motions A) (i j) := revenue M.k (theatre H M i j (apotheosis H M i (j+1))) -- j < i pad
lemma ratio_rule (hJ : LocalRatio M.j) (hf : H.Suffices F) (i j : ℕ) (hj : j < i) :
    let V := theatre H M i j (apotheosis H M i (j+1)); let X:= drive H M i j; constantCoeff X=1 ∧ Pall X ∧ (∀ d, coeff d X=subdue M.k (V d 2)) ∧
    ∃! (r : Word × Word), (constantCoeff r.1=1 ∧ r.1^2=bar r.1 X) ∧ (constantCoeff r.2=1 ∧ r.2^2*X=1) ∧ bar r.1 (tempo r.2)=PowerSeries.X ∧ bar r.2 (tempo r.1)=PowerSeries.X ∧
      apotheosis H M i j=reorder r.1 (recover r.1) V := by
  intro V X; have he:= kernel_run hJ hf i _ hj; have hV:= Passage.actual hf hj (M.tree j) hJ
  have hv : Whisper V:=whispers_post hV he.report he.crests
  have h : constantCoeff X=1:=revenue_anchor M.k (B:=H.H i j) (I:=V) (funext fun j' => press_lead _ _ _ _ _ he.report.style j') (price_at_horizon hf hj.le _)
  exact ⟨h,revenue_parity M.k hv.style,fun i=> earnings .., (polling X,yesterday X), ⟨poll_rule h,counterpart h,castoff h,coastal h,recursed H M hj⟩, fun y hy=>  Prod.ext (poll_only h hy.1.1 hy.1.2) (yesterday_only h hy.2.1.1 hy.2.1.2)⟩ -- Note exists! includes r field; instead output lemma uniqueness just equations/use supplemental
end Parapet
end YM.WilsonBulk
