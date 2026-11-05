import YM.Euclid.Differential

/-!
# The common label vector space

Realize as a directed
union of *responses* when the inclusions hold, so testing equality even across
different degrees is simple.

This really uses the all-spectator quotient.

Reusable gluing for stress and for the Wightman word domain.
-/
set_option autoImplicit false
noncomputable section
namespace YM
open Function Set Filter
open scoped ContDiff Topology BigOperators
variable {G : Gauge} {L : Register G}
namespace Table
variable (S : Table L)

def observations : Submodule ℂ (Exterior L → ℂ) := ⨆ d, LinearMap.range (S.spectra d)
abbrev Union := ↥S.observations

def pin d : S.Field d →ₗ[ℂ] S.Union :=
  (S.spectra d).codRestrict S.observations fun x => Submodule.mem_iSup_of_mem d ⟨x,rfl⟩

theorem pin_inj d : Injective (S.pin d) := fun _ _ h =>
  S.faithfully _ (congr_arg Subtype.val h)
end Table

namespace DiffPlan
variable {S : Table L} (P : DiffPlan S) (hs : S.Symmetric) (hp : P.Inclusions S)
include hs hp

theorem stays {d e : ℕ} (h : d ≤ e) (p : S.Field d) : S.pin e (P.rise h p) = S.pin d p :=
  Subtype.ext (P.through_limit hs hp h p)

theorem covered (p : S.Union) : ∃ (n : ℕ) (x : S.Field n), S.pin n x = p := by
  have H : Monotone (fun d => LinearMap.range (S.spectra d)) := by
    rintro d e h _ ⟨y,rfl⟩
    exact ⟨_,P.through_limit hs hp h y⟩
  obtain ⟨d,y,Hy⟩ := (Submodule.mem_iSup_of_directed _ H.directed_le).mp p.property
  exact ⟨d,y,Subtype.ext Hy⟩

theorem joint {ι : Type*} [Fintype ι] (v : ι → S.Union) :
    ∃ (n : ℕ) (x : ι → S.Field n), v = S.pin n ∘ x := by
  classical
  choose m x hx using fun i => P.covered hs hp (v i)
  let n := Finset.univ.sup m
  have he (i) : m i ≤ n := Finset.le_sup (f := m) (Finset.mem_univ _)
  exact ⟨n,fun i => P.rise (he i) (x i),funext fun i => ((P.stays hs hp (he i) _).trans (hx i)).symm⟩

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {t : ℂ →+* ℂ}
-- no surj assumption on scalars needed to define colimit lift.
def compatible (P : DiffPlan S) (F : (j : ℕ) → S.Field j →ₛₗ[t] V) :=
    ∀ (d e : ℕ) (h : d ≤ e) p, F e (P.rise h p) = F d p

/-- Construct a map out of all the compatible finite-degree maps. -/
theorem uniqueLift (F : (j : ℕ) → S.Field j →ₛₗ[t] V) (H : P.compatible F) :
    ∃! T : S.Union →ₛₗ[t] V, ∀ n p, T (S.pin n p) = F n p := by
  choose n x he using P.covered hs hp
  let f (v : S.Union) := F (n v) (x v)
  have ht (i p) : f (S.pin i p) = F i p := by
    let v := S.pin i p
    change F (n v) (x v) = _
    rw [← H _ _ (le_max_left (n v) i), ← H i _ (le_max_right (n v) i)]
    congr 1
    apply S.pin_inj
    rw [P.stays hs hp, P.stays hs hp,he]
  let T : S.Union →ₛₗ[t] V :=
    { toFun := f
      map_add' := by
        intro a b
        obtain ⟨i,p,rfl⟩ := P.covered hs hp a; obtain ⟨j,q,rfl⟩ := P.covered hs hp b
        rw [← P.stays hs hp (le_max_left i j), ← P.stays hs hp (le_max_right i j),← map_add,ht,ht,ht,map_add]
      map_smul' := by
        intro c a; obtain ⟨i,b,rfl⟩ := P.covered hs hp a
        rw [← map_smul,ht,ht,(F i).map_smulₛₗ] }
  refine ⟨T,ht,?_⟩
  intro y hy; apply LinearMap.ext; intro p; obtain ⟨i,p,rfl⟩ := P.covered hs hp p; exact (hy _ _).trans (ht i p).symm

def unionAdj (a : Axis) (H : S.RealSpin) (he : P.Orientation H) :
    S.Union →ₛₗ[starRingEnd ℂ] S.Union := (P.uniqueLift hs hp
      (fun n => (S.pin n).comp (S.adj H n a)) (by
        intro d e h p; simp only [LinearMap.comp_apply,Table.adj,he.realInc, he.mirrorInc,P.stays hs hp])).exists.choose

theorem through_adjoint (a) (H : S.RealSpin) (he : P.Orientation H) (d) (v : S.Field d) :
    P.unionAdj hs hp a H he (S.pin d v) = S.pin d (S.adj H d a v) := by
  unfold unionAdj
  exact (P.uniqueLift hs hp (fun n => (S.pin n).comp (S.adj H n a)) (by
    intro i j h p; simp only [LinearMap.comp_apply,Table.adj,he.realInc, he.mirrorInc,P.stays hs hp])).exists.choose_spec d v

theorem unit_same (H : S.Basic) {d e : ℕ} : S.pin d (S.unit d)=S.pin e (S.unit e) := by
  rw [← P.stays hs hp (le_max_left d e) (S.unit d), ← P.stays hs hp (le_max_right d e) (S.unit e), P.fixs hp H, P.fixs hp H]
end DiffPlan
end YM
