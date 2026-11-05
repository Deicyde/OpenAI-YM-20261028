import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Ribbon
import YM.TraceExtension.Prom.Port.Leading
/-!
  Variant of YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Ribbon for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
    RankCovariance Next.Rank Tapes Perch Rise Spindle Atlas WeightedGaussianMarginal45C.Issue.Cut
    AnalyticBridge.LocalGaussianLaws Work.F08 FreeResolvent Exterior
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge}
section linear
variable {α β : Type} [Fintype α] [Fintype β]

open ColorBook

end linear

variable {C : Family G} (B : Binding C) {N i p : ℕ}

variable (h : i < N)

-- Bounds reserved before block lengths. `Purse.L` should buy these.

local notation "X" => stamp C.path.levels N p

def capitalSky (K : KernelChoices) (Z : MapPrices) (J I : ℕ) :=
   let b:= ticket (TypeFace 2) (psiBudget (max (Z.Ω J) (Z.Ω I))); let P:= RankCovariance.prepared K; let c:= max 0 (max (P.centers J) (P.centers I)); max 1 (max b (c+b^2*c))

lemma paths_budgetSky (hI : i < N) (d : ℝ)
    (hd : capitalSky C.path.levels.clock.kernel B.prices (C.path.levels.clock.J (i+1)) (C.path.levels.clock.J i) ≤ d) :
    (short B N p i).Fair d ∧ (track X i).Fair d := by
  let A:= C.path.levels; let J:= A.clock.J i; let U:= A.clock.J (i+1); let P:= RankCovariance.prepared A.clock.kernel; let c := max 0 (max (P.centers U) (P.centers J)); let z := max (B.prices.Ω U) (B.prices.Ω J)
  let a:= psiBudget z; let b:= ticket (TypeFace 2) a
  let S:=short B N p i; let T:=track X i
  have he : ∀ q, q ≤ N → 0 ≤ B.prices.Ω (A.clock.J q) := by
    intro q hq; let k := plaquette ⟨(0,1),by decide⟩; have he := ((B.pays.rows N q hq).1 k k)
    exact (tsum_nonneg he.1).trans he.2.2
  have hj : 0≤c := le_max_left ..
  have hz : 0 ≤ z:= (he i hI.le).trans (le_max_right ..)
  have ha: 0 ≤ a := psiBudget_nn z hz
  have hb: 0 ≤ b := ticket_nonneg _ ha
  let r:=((C.S.block i).val:ℝ)
  have hx : 1 ≤ r := by unfold r; exact_mod_cast (show 1 ≤ _ from Nat.succ_le_of_lt (C.S.block i).property)
  have hr : ticket (TypeFace 2) (a/r^2) ≤ b := by unfold b ticket; gcongr; exact div_le_self ha (one_le_pow₀ hx)
  have hc u : (∑ v, ‖T.H u v‖) ≤ b := (high_rowsSky B hI u).1.trans hr
  have hP j (hp:P.centers (A.clock.J j) ≤ c) (i v : Chamber G A.S j p) : ‖((stamp A N p).κ j).cov i v‖ ≤ c := by
    rw [← stamp_real A N j p,Complex.norm_real,Real.norm_eq_abs]
    exact ((RankCovariance.prepared A.clock.kernel).earns _ (A.clock.adm _) A rfl N j p rfl i v).trans hp
  obtain ⟨h',hb',hv⟩:= show 1≤d ∧ b≤d ∧ c+b^2*c≤d by
    unfold capitalSky at hd; rcases max_le_iff.mp hd with ⟨h,hq⟩; exact ⟨h,max_le_iff.mp hq⟩
  have hf : T.Fair d := {
    positive:=h'
    charge := fun i => ((coin_pay _).trans (hc i)).trans hb'
    tide := fun u v=> by
      apply le_trans _ hv
      change ‖((stamp A N p).κ (i+1)).cov u v+ - (Normal.scope T.H ((stamp A N p).κ i)).cov u v‖ ≤ _
      apply (norm_add_le ..).trans
      rw [norm_neg]; exact add_le_add (hP _ ((le_max_left ..).trans (le_max_right ..)) _ _) (scope_price _ _ hc hb hj (hP i ((le_max_right ..).trans (le_max_right ..))) u v)
  }
  refine ⟨⟨h',fun u=> ((coin_pay _).trans ((exact_short_price B (lt_min (B.prices.alpha_pos U) (B.prices.alpha_pos J)) (sufficient_rowsSky B hI) u).trans hr)).trans hb', fun u v =>?_⟩,hf⟩
  unfold short Qrow; dsimp only
  split
  · exact hf.tide u v
  rw [norm_zero]; exact zero_le_one.trans h'
end YM.PhysicalNext.InteractingRank
