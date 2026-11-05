import YM.Extra.WEAK_SCALING_ACTLAW.Five
import YM.Next.BOUNDARY.Synchronize

/-!
# Common Order option retaining all finite comparisons & column limits

Unlike `Supply` which only needs SOME further refinement of the given f
per request (for use by `act` directly without selecting a new f), here to
reach an Order with **all** the estimates explicitly still on it, assume the
possibility of supplying the finite comparisons from arbitrary refinements.
Uses the proven synchronization methods on their true two-axis filters. No
assertion that the price of this input is already met. On the output Order
no switch across Tracks needed for evaluating any of the submitted estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.WeakScaling
open Filter Function Set Extraction Org Spec Climb Next.BOUNDARY
open scoped Topology
variable {G : Gauge} {C : Family G} {f f' : Order} {h : (Free C).RealSpin}
variable {W : MaxwellData C} {S S₀ : Table C.book} {V : DiffPlan S} {I : IR (C:=C) S} {P : ℕ → Table C.book}

structure Ready (b : Stations C) (f : Order) (a : ∀ (_ d : ℕ), Column C d) (h : (Free C).RealSpin) (M D : ℕ) (Q : ℝ) : Prop where
  costs : FiniteCosts b f h M D Q
  limits k d : ∃ p₀ : ℕ, f.limits (fun p => p₀ ≤ p) (b.coef k d) (a k d)

lemma Ready.down {b : Stations C} {M D Q a} (hr : Ready b f a h M D Q) (he : Refines f' f) {R : ℝ} (hR : 1 ≤ R) (hQ : R ≤ Q) :
    Ready b f' a h M D R where
  costs := {
    bounded k d := by
      obtain ⟨A,hA,p₀,hp⟩ := hr.costs.bounded k d
      exact ⟨A,hA,p₀,fun p h => show ∀ᶠ N in Filter.map (fun i => f'.mesh i) atTop, ‖b.coef k d N p‖ ≤ A from
        Eventually.filter_mono he.mesh (hp p h)⟩
    sym k d hd := he.late (hr.costs.sym k d hd)
    center n hn v hv := by
      obtain ⟨A,hA,hl,H⟩ := hr.costs.center n hn v hv
      refine ⟨A,hA,hl,H.mono ?_⟩
      rintro k ⟨m,j,hj,h₁,h₂,h₃,h'⟩
      have ht := b.positive k
      exact ⟨m,j,hj,h₁.trans_le (by gcongr), h₂, h₃.trans_le (by gcongr),he.late h'⟩
    aligned n hn v hv ε hε := by
      refine (hr.costs.aligned n hn v hv ε hε).mono fun k hk u hu h => he.late (hk u ⟨hu.1.trans_le hQ,?_⟩ h)
      intro i j he; obtain ⟨a,ha⟩ := hu.2 i j he
      exact ⟨a,ha.trans_le' (by exact (inv_le_inv₀ (by linarith) (by linarith)).mpr hQ)⟩ }
  limits k d := ⟨_, he.limits (hr.limits k d).choose_spec⟩

def Workshop (C : Family G) (f : Order) (h : (Free C).RealSpin) := ∀ M D Q, (1:ℝ) ≤ Q → ∃ b a, Ready b f a h M D Q

lemma Workshop.down (hc : Workshop C f h) (hr : Refines f' f) : Workshop C f' h := by
  intro M D Q hQ; obtain ⟨b,a,H⟩ := hc M D Q hQ; exact ⟨b,a,H.down hr hQ le_rfl⟩









end YM.Extra.WeakScaling
