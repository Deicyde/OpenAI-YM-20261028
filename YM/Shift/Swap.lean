import YM.Shift.Sol


/-!
# Germ criterion for exchanging adjacent pair. Protects SAME partial heights

Partial distributions with fixed spectators, tied adjacent gap eta0, all Xi
variables. Need holomorphic germs near S spacelike open so cannot overlap by
adiabatic argument alone. Here both contours touch every point, uniqueness
from joint AnalyticOnNhd. Need `Held` tested partial boundary readouts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Boundary
open Filter Set Function Distribution MeasureTheory Mink Probe Metric
open scoped Topology ENNReal InnerProductSpace ContDiff
variable {G : Gauge} {L : Register G} {S : Table L} {n : ℕ}

structure NearPair (n : ℕ) where
  i : Fin n
  j : Fin n
  next : i.val+1=j.val

namespace NearPair
variable (P : NearPair n)

def s := Equiv.swap P.i P.j

def switch : Points n ≃ₗᵢ[ℝ] Points n where
  toFun x := points fun i => x (P.s i)
  invFun x := points fun i => x (P.s i)
  left_inv x := by ext1; simp [s]
  right_inv x := by ext1; simp [s]
  map_smul' _ _ := rfl
  map_add' _ _ := rfl
  norm_map' p := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    change ‖points _‖^2=_
    rw [PiLp.norm_sq_eq_of_L2 _ (points _), PiLp.norm_sq_eq_of_L2 _ p]; exact Equiv.sum_comp P.s fun i => ‖p i‖^2
@[simp] lemma switch_at x i : P.switch x i=x (P.s i) := rfl


def name (p : Full n) := glow (P.switch (reality p)) (P.switch (shade p))
lemma name_name p : P.name (P.name p)=p := by
  unfold name
  have h q : P.switch (P.switch q) = q := P.switch.symm_apply_apply q
  rw [re_glow,im_glow,h,h,valley]

def gap : Set (Points n) := {x| x P.j-x P.i ∈ spacelike}
lemma open_gap : IsOpen P.gap := open_spacelike.preimage (show Continuous (fun x : Points n => x P.j - x P.i) from by fun_prop)

/-- strict spectator gap, pure time only; P isolated by construction. -/
def spectator (t : Heights n) : Prop := t P.i=t P.j ∧ (∀ i j : Fin n,i<j→ i ≠ P.i ∨ j≠P.j → t i<t j)

/-- Both reached from this partial boundary. -/
structure Fleck (y : Heights n) : Prop where
  willing : P.spectator y
  here : dawn y∈shores n
  there : P.switch (dawn y)∈shores n
  first (x : Points n) : glow x (dawn y) ∈ closure (tube n)
  second (x : Points n) : glow x (dawn y) ∈ closure (P.name ⁻¹' tube n)
end NearPair

variable {U V : Set (Full n)}
/-- Germ sheet, valid on THIS size, anchored on that order's tube. -/
structure Pane (F : Full n → ℂ) (U : Set (Full n)) (x : Full n) where
  extendF : Full n→ℂ
  doc : AnalyticAt ℂ extendF x
  fits : extendF =ᶠ[𝓝[U] x] F

namespace Pane
variable {F G' : Full n → ℂ}

lemma revive {x : Full n} (A : Pane F U x) : ∃ r>0, AnalyticOnNhd ℂ A.extendF (ball x r) ∧ EqOn A.extendF F (ball x r∩U) := by
  obtain ⟨p,hp,h⟩ := (nhdsWithin_basis_open _ U).mem_iff.mp A.fits
  obtain ⟨K,hk,hA⟩ := Metric.mem_nhds_iff.mp (inter_mem (hp.2.mem_nhds hp.1) A.doc.eventually_analyticAt)
  exact ⟨K,hk,fun y hy => (hA hy).2,fun _ w => h ⟨(hA w.1).1,w.2⟩⟩

lemma agree (he : IsOpen U) {x : Full n} (h : x ∈ closure U) (A B : Pane F U x) :
    A.extendF =ᶠ[𝓝 x] B.extendF := by
  obtain ⟨r,hr,hA,hB⟩ := A.revive
  obtain ⟨s,hs,hC,hD⟩ := B.revive
  let t := min r s
  have ht : 0 < t := lt_min hr hs
  have hx := ball_subset_ball (x := x) (min_le_left r s)
  have hz := ball_subset_ball (x := x) (min_le_right r s)
  obtain ⟨w,hw⟩ := mem_closure_iff.mp h (ball x t) Metric.isOpen_ball (mem_ball_self ht)
  have hW := (hA.mono hx).eqOn_of_preconnected_of_eventuallyEq
    (hC.mono hz) (convex_ball x t).isPreconnected hw.1 (show A.extendF =ᶠ[𝓝 w] B.extendF from ?_)
  · filter_upwards [ball_mem_nhds x ht] with i h using hW h
  filter_upwards [(Metric.isOpen_ball.inter he).mem_nhds hw] with u hu
  exact (hB ⟨hx hu.1,hu.2⟩).trans (hD ⟨hz hu.1,hu.2⟩).symm

/-- Overlap sanity. -/
lemma arrive (he : IsOpen U) {x : Full n} (A : Pane F U x) {p : Set (Full n)} (hP : IsOpen p)
    (hp : AnalyticOnNhd ℂ A.extendF p) (hv : EqOn A.extendF F (p∩U)) (i : Full n) (hI : i∈p) (hQ : i∈closure U)
    (B : Pane F U i) : A.extendF =ᶠ[𝓝 i] B.extendF :=
    agree he hQ (⟨A.extendF,hp _ hI,(Eventually.filter_mono inf_le_left (hP.mem_nhds hI)).mp
      (Eventually.mono self_mem_nhdsWithin (fun _ hu hx => hv ⟨hx,hu⟩))⟩ : Pane F U i) B

lemma propagate {Y : Type*} [TopologicalSpace Y] [PreconnectedSpace Y] (he : IsOpen U) (hk : IsOpen V)
    (q : Y → Full n) (c : Continuous q) (hq : ∀ i, q i ∈ closure U ∩ closure V) (p : ∀ i, Pane F U (q i))
    (w : ∀ i, Pane G' V (q i)) (a b : Y) :
    ((p a).extendF =ᶠ[𝓝 (q a)] (w a).extendF) ↔ ((p b).extendF =ᶠ[𝓝 (q b)] (w b).extendF) := by
  let T := {i : Y | (p i).extendF =ᶠ[𝓝 (q i)] (w i).extendF}
  have h (x : Y) : ∀ᶠ i in 𝓝 x, x∈T ↔ i∈T := by
    obtain ⟨r,hr,hA,hB⟩ := (p x).revive
    obtain ⟨s,hs,hC,hD⟩ := (w x).revive
    let t := min r s
    have ht := ball_subset_ball (x:=q x) (min_le_left r s)
    have hv := ball_subset_ball (x:=q x) (min_le_right r s)
    filter_upwards [(c.tendsto x).eventually (ball_mem_nhds (q x) (show 0 < t from lt_min hr hs))] with i hi
    have hX : q i∈ball (q x) t := hi
    have ha := (p x).arrive he isOpen_ball hA hB (q i) (ht hX) (hq i).1 (p i)
    have hh := (w x).arrive hk isOpen_ball hC hD (q i) (hv hX) (hq i).2 (w i)
    have H : q x∈ball (q x) t := mem_ball_self (lt_min hr hs)
    constructor
    · intro hx
      have hw := (hA.mono ht).eqOn_of_preconnected_of_eventuallyEq
        (hC.mono hv) (convex_ball _ t).isPreconnected H hx
      exact ha.symm.trans (EventuallyEq.trans (Eventually.mono (isOpen_ball.mem_nhds hX) (fun _ j => hw j)) hh)
    intro hX'
    have hw := (hA.mono ht).eqOn_of_preconnected_of_eventuallyEq
        (hC.mono hv) (convex_ball _ t).isPreconnected hX (ha.trans (EventuallyEq.trans hX' hh.symm))
    exact Eventually.mono (isOpen_ball.mem_nhds H) fun _ i => hw i
  have he : IsClopen T :=
    ⟨isOpen_compl_iff.1 <| isOpen_iff_mem_nhds.mpr (fun x hx => (h x).mono (fun i hp => fun hI => hx (hp.2 hI))),
        isOpen_iff_mem_nhds.mpr (fun x hx => (h x).mono (fun i hp => hp.1 hx))⟩
  change a ∈ T ↔ b∈T
  rcases isClopen_iff.mp he with e|e <;> simp [e]
end Pane
end YM.Boundary
