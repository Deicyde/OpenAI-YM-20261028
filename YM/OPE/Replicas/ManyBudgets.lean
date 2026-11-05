import YM.MergeProof.North.Siroco
import YM.OPE.Replicas.Thunder

/-!
# Keep induction facts at n-ary consumption

Strengthening of YM/MergeProof/North/Siroco.lean; most of the proof is
the *same* construction. Adapted from that file, retaining the baseline.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Station Next.Rank.Spindle Cells
open scoped Topology BigOperators Classical
section
open Relay Exponential Extraction Bid PhysicalNext.Repeat.Legato.Bandage
variable {G:Gauge}(C:Family G)(N p J k j m D d h:ℕ) {r:ℕ→ℕ} {W:Bid.Worth} {u ψ φ δ:ℕ→ℝ} {μ:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "H"=> C.path
local notation "P"=> C.path.levels.budget
local notation "Y"=> C.path.levels
local notation "V"=> Site (C.side J p)
local notation "rad"=> fuga C.path.levels (m+1)
variable (x:Cover)(B: C.label d) (T:C.label 4) (hf:J ≤ k) (hk:k ≤ m) (hm:m+1 < j) (hj:j<N)
local notation "f"=> Next.UVStress.fragment (C:=C) (D:=D) (d:=d) h rad T B j x N p
local notation "τ"=> center C.S p (le_trans hf (le_trans hk (le_trans (m.le_succ) (le_trans hm.le hj.le)))) 0
variable (hh:C.Makes)(hR:Created C)(hp:Scrim C W u ψ φ δ (fly C.path.levels) r μ)
variable {i₀:ℕ}{σ χ:ℕ→ℝ}
variable (b a e X η c:ℝ)
local notation "A"=> whims C j m d h b a
variable (hB:(C.labels.level d).coeffSize B ≤ a) (hT:(C.labels.level 4).coeffSize T ≤ b)
local notation "ℓ"=> wrap (C.side j p) x
local notation "L"=> bites C J j p ℓ
local notation "O"=> Cells.location C.S j N p x
local notation "W'"=> ventola C.path.levels j (m+1) δ φ η A
local notation "P'"=> (C.path.levels.budget (m+1))
local notation "k₀"=> scurry C.path.levels r χ η (m+1)
local notation "h!"=> lt_of_lt_of_le (Nat.lt_succ_self m) (le_trans hm.le hj.le)
structure SwornClusterCuts (i₀ D : ℕ) (χ:ℕ→ℝ)(η X:ℕ→ℝ):Prop where
    city : ∃ σ : ℕ→ℝ, ManyCopies.Thor C.path δ r μ σ χ i₀
    crisp j : i₀ ≤ j → χ j ≤ 1
    funs i : i₀≤ i→ 0 < η i ∧ η i ≤1
    bars i : i₀ ≤ i → (((Y|>.budget i).B+(Y|>.budget i).B+1 :ℕ):ℝ)^4*scurry C.path.levels r χ (η i) i≤1/2 ∧ Real.exp (scurry C.path.levels r χ (η i) i)-1≤1
    dollars i : i₀ ≤ i→1 ≤ X i
    brings (i): i₀ ≤ i → ∀ N p:ℕ,∀ hi:i<N, MergeProof.Float.Runs (μ N p i hi) (C.path.levels.clock.op i p) (6*((C.S.block i).val:ℝ)) ∧ Throws C.path N p i (μ N p i hi) (Next.Foundations.hol G) (Next.Foundations.localSection G D) (X i)

end
end YM.MergeProof.Ribbons
