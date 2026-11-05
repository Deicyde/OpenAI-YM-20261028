import YM.AnalyticNext.QUARTIC_MATCH.Local.Peak
import YM.AnalyticNext.QUARTIC_MATCH.Mint.Affairs

/-!
# Top quotation

Every size incl from N=0, every side. Use signed normalization Top on the exact retention oath.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Mint
open Filter Function Lattice Laurent Matrix RG Precision Exterior Bid Wilson Branch Bloch
open Progress.StationaryScenes Next Tree Joint BoxChain Mail Analyzers
open Progress.Joint Local Local.Budget Local.Rotate Local.Wages Hessian Scheduling
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
namespace Affairs
open Residual
variable {G : Gauge} {a : Levels G} {N : ℕ} {K : MapPrices} {H : Horizon a}

def Flows (a : Levels G) (N : ℕ) (p : Clip) (W : PathData G) (n : ℕ) := ∀ (i j : ℕ), j ≤ n →
    SameJet j wilsonAt (baseAt (c:=a.S.side N i) p W)


variable (G : Gauge) (K : MapPrices) (i : ℕ)

def Entry (P : Printed 2) (s C : ℝ) := ∀ (a : Levels G) (H : Horizon a),Swears H → H.Suffices K →
    ∀ N : ℕ,a.clock.J N=i → ∀ W : PathData G, Funded H N N W → (∀ j,(W.cubic j).coeff=0) →
    (∀ j,(W.quartic j).coeff=0) → Shortens W K i → ∃ A : rootArray G 2,Ink (letters P A) s C ∧
      Flows a N (a.params N).clip (third W (letters P A)) 3

def AddOn (P : Printed 3) (s C δ D : ℝ) := ∀ (a : Levels G) (H : Horizon a),Swears H → H.Suffices K →
    ∀ N : ℕ,a.clock.J N=i → ∀ W : PathData G, Funded H N N W → (∀ j,(W.quartic j).coeff=0) →
    Shortens W K i → Ink W.cubic s C → Flows a N (a.params N).clip W 3 →
      ∃ A : rootArray G 3,Ink (letters P A) δ D ∧ Flows a N (a.params N).clip (fourth W (letters P A)) 4

private lemma flow_bound {G : Gauge} {a : Levels G} {W : PathData G} {p : Clip} {N n : ℕ} (h : Flows a N p W n) :
    ∀ i k,k<n+1 → iteratedFDeriv ℝ k (wilsonAt (G:=G) (c:=a.S.side N i)) 0=iteratedFDeriv ℝ k (baseAt p W) 0 :=
  fun i k hk => (h i k (by omega)).2.2



lemma sign4 (P : Printed 3) (s C : ℝ) (hp : 0<s) : ∃ δ D,0<δ ∧ 0≤D ∧ AddOn G K i P s C δ D := by
  obtain ⟨u,hH,-,-,h₂,hb⟩ := narrows K i i s hp
  obtain ⟨δ,D,hδ,hD,H⟩ := Peak.top_cost G 3 0 (by decide) (by decide) u (rowBill K i) C 0 hH P
  refine ⟨δ,D,hδ,hD,?_⟩
  intro a H' hw h N hi W hW hy hE hI hT
  let p := (a.params N).clip
  have ht : Rotate.Led W 1 (3+1) (boom u) (min (K.α i) 1) (rowBill K i) C 0 :=
    ⟨lt_min (K.alpha_pos i) one_pos, by norm_num; exact le_min_iff.mp h₂,hE,.clears hp (by norm_num; exact hb) hI,.missing hy le_rfl⟩
  obtain ⟨A,hA,hk⟩ := H p W _ _ _ _ hW.bound ht (a.S.side N) (tends a N) (flow_bound hT)
  refine ⟨A,hA,fun n j hj => ?_⟩
  rw [base_more hy]; exact hk n j hj
end Affairs
end YM.AnalyticNext.QuarticMatch.Mint
