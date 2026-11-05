import YM.SharpGram.Weak.Access
import YM.SharpGram.Common

/-! Gram bounds and coercivity in the measuring frame constructed on each finite horizon. -/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram
open Function Filter Set Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Next.Rank PhysicalNext.RankCovariance
open Org Spec Next.Rank.Station Further.CorrectedLift Next.UVStress Climb Ward
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open OPE OPE.Log Weak Weak.Portfolio
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}(U:Final C f S)
variable {D:ℕ}{u:Filter (ℕ×ℕ)} (X : Weak.Portfolio C U.room.cutoff D u)
local notation "F" => Cells.standard C
local notation "σ" => U.room.kernel.spin
local notation "θ" => Maxwell.Free.spin_free C.labels
local notation "V" => U.sector.derivatives
local notation "P" => C.path.levels.clock.hatBeta
local notation "a" => C.S.a

-- Additional cost -- true physical only
structure BasisMeter (Y : ℕ → ∀ d : ℕ, YM.Spin.change S d) : Prop where
  graded : ∀ᶠ k in atTop, Extra.WeakScaling.Graded V (Maxwell.Free.scheme C.labels) σ θ (Y k) D
  price (d : Fin (D+1)) : ∃ δ K : ℝ, 0 < δ ∧ 0≤ K ∧
    ∀ᶠ k : ℕ in atTop, ‖inBasis U X k d (Y k d)‖ ≤ K ∧ coercive (inBasis U X k d (Y k d)) δ

structure PricedIn (Y : ℕ → ∀ d : ℕ, YM.Spin.change S d) : Prop extends BasisMeter U X Y where
  sources (d : Fin (D+1)) : ∃ p : ℕ, ∀ᶠ k : ℕ in atTop, ∀ x : S.Field d,
     ∃ (y : C.label d) (q : ℕ×ℕ → C.label d), S.project d y=x ∧ Tendsto q u (𝓝 y) ∧
       ∀ᶠ i in u, quota C d k i.1 i.2 (q i) ≤ P k^p * a k ^ d.val * ‖(Y k d).symm x‖
  reads (d : Fin (D+1)) : ∃ K : ℝ, 0 ≤ K ∧
     ∀ᶠ k in atTop, ∀ (v : Filter (ℕ×ℕ)) [v.NeBot], v ≤ u →
          ∀ (q : ℕ×ℕ → C.label d)(x : C.label d)(z:ℝ),
            (∀ᶠ i in v, quota C d k i.1 i.2 (q i) ≤ z) → Tendsto q v (𝓝 x) →
              ‖(Y k d).symm (S.project d x)‖ ≤ K / a k ^ d.val * z

variable (T : Facilities C f S)
variable {Y : ℕ → ∀ d : ℕ, YM.Spin.change S d}

/-- operator-norm residual estimate (not circular) via exact tilted detector. -/
lemma basisTest (h : ∀ᶠ k in atTop, Extra.WeakScaling.Graded V (Maxwell.Free.scheme C.labels) σ θ (Y k) D)
    (he : ∀ d : Fin (D+1), Tendsto (fun k => inBasis U X k d (Y k d)) atTop (𝓝 (Portfolio.model C d))) :
    BasisMeter U X Y := by
  refine ⟨h,fun d => ?_⟩; obtain ⟨δ, hp, hT⟩ := Portfolio.freely (C:=C) d
  let K := Portfolio.model C d
  refine ⟨δ/2, δ/2+‖K‖, half_pos hp, by positivity, ?_⟩
  filter_upwards [SharpGram.stayNear (he d) (half_pos hp)] with k hk
  exact ⟨Portfolio.normBy hk,absorb K _ δ (δ/2) hT (by simpa only [sub_half] using hk)⟩

variable [u.NeBot] (hf : u ≤ f.fuse)
include hf T
lemma access (hB : BasisMeter U X Y) : PricedIn U X Y := by
  obtain ⟨w,r,D',hT⟩:=T.costlier
  have ht := hT.toTableTickets
  refine ⟨hB,fun d=>?_,fun d=>?_⟩
  · obtain ⟨δ,K,H,hK,H'⟩:= hB.price d
    obtain ⟨p,hp⟩ := Portfolio.entryUse U X ht hf T.simpleGate d K hK
    exact ⟨p,(hp.and H').mono fun i hi => hi.1 (Y i d) hi.2.1⟩
  obtain ⟨δ,K,H,hK,H'⟩:= hB.price d
  have hP := Portfolio.departUse U X ht hf T.simpleGate d δ H
  exact ⟨_, mul_nonneg (Real.sqrt_nonneg _) zero_le_two, (hP.and H').mono fun i hi => hi.1 (Y i d) hi.2.2⟩

lemma attains : ∃ Y : ℕ → ∀ d : ℕ, YM.Spin.change S d,
    PricedIn U X Y ∧
    ∀ d : Fin (D+1), Tendsto (fun k => inBasis U X k d (Y k d)) atTop (𝓝 (Portfolio.model C d)) := by
  obtain ⟨w,r,L,H'⟩:=T.costlier
  obtain ⟨p,hp,hA⟩ := X.tune_grades U H'.toTableTickets hf T.simpleGate
  have h d := aligned U X H'.toTableTickets hf T.simpleGate d (he:=hA d)
  exact ⟨p,access U X T hf (basisTest U X hp h),h⟩

end YM.SharpGram
