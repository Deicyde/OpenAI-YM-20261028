import YM.Next.UV_STRESS.Tensor
import YM.Next.UV_STRESS.Ward
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Current
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Persistence

/-!
# Countably compatible but *separate* shell legs actually suffice for the Grades

Even don't need know J sign at any one Leg. Use the one-dimensional real
current-divergence kernel result of UV_STRESS along the weak curve. Needs
its free prerequisites. Not asserting arbitrary nonzero tensors agree
from quotient-rank estimates or something. Return one exact unnormalized
I.J (no ad hoc scaling between d's), with one comparator path. No claim of
canonical form of the *renormalized* energy on Final beyond Tab.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.Grade
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb Org Spec Lattice Wilson Cells
  Next.Extract Next.UVStress Push.Common Work.A01
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} {V : DiffPlan S} {H : S.Hierarchy}
variable {d D : ℕ}



/-- Buy some actual nonzero conserved current Leg on our hierarchy, per
observable/per use. -/
def PoweredLeg (l : Leg S) (H : S.Hierarchy) (V : DiffPlan S) (F : Extraction.Order) :=
  ∃ J : S.Stress, J ∈ KernelSpace H.spin ∧ J ≠ 0 ∧ Conserved V H.spin J ∧ ClearedLeg J l F



def ProbeOffer (F : Extraction.Order) (H : S.Hierarchy) (V : DiffPlan S) :=
    Stationed F (fun l => PoweredLeg l H V)

/-- Also useful on-demand sufficient port (before e's have been chosen,
allow even new levels of cutoffs to be selected for each m,y **on towers
of orders**). Stationed success might require further inherited refinement
at which earlier quantitative prerequisites must be preserved.
J may vary across legs. -/
def ProbeDemand (F : Extraction.Order) (H : S.Hierarchy) (V : DiffPlan S) :=
    OnDemand F fun (l : Leg S) u => ∃ (J : S.Stress) (B : Axis→Axis→C.book.Ref 4) (x : C.book.Ref l.1) (K : Rates),
      J ∈ KernelSpace H.spin ∧ J ≠ 0 ∧ Conserved V H.spin J ∧ (∀ i j,S.project 4 (B i j)=J i j) ∧
      S.project _ x=spectrum S _ l.2.2 ∧ Stationed u (wages (C:=C) l.2.1 _ B x K)

lemma ProbeDemand.persists {g} (p : ProbeDemand f H V) (h : Tails g f) : ProbeDemand g H V :=
  demand_persists p h

lemma ProbeDemand.offers (h : ProbeDemand f H V) : ProbeOffer f H V := by
  letI : Countable (Leg S) := by unfold Leg Orbits; infer_instance
  apply OnDemand.stations; intro l r
  obtain ⟨g,J,B,x,K,hJ,hj,hc,he,hf,hG⟩ := h l r
  obtain ⟨u,hu⟩ := hG.collect (fun i _ _ e p => wages_persist (C:=C) i p e)
  exact ⟨g.refine u,J,hJ,hj,hc,B,x,K,he,hf,hu⟩



/-- Ward readout mapping in a translation or rotation leg. Using the
`shell*`/`flux` equivalences in Work.A01 (literal **minus** integrated ν
field with the specified center offset, not a choice of surface sign).
`U` is the centered translation/rotation *before* applying the actual
centering shift to x. -/
private def enters (J : S.Stress) (d D : ℕ) (U : E4 → E4)
    (L : S.Field d →ₗ[ℂ] S.Field D) (v : S.Field d) : Prop :=
  ∀ (n : ℕ) (q : Fin n → S.Tag) (x : Points (n+1)), x∈conf _ →
    ∀ χ, Window x χ → flux J χ (fun y => U (y-x 0)) x q v = frontRead q x D (L v)

private lemma on_all {J : S.Stress} {U : E4→E4} {L : S.Field d →ₗ[ℂ] S.Field D} (h : S.Hierarchy)
    (hp : ∀ i : Axis, Continuous (fun y => U y i)) (p : ∀ i, enters J d D U L (spectrum S d i)) :
    ∀ v : S.Field d, enters J d D U L v := by
  intro v n q x hx χ hχ
  let l := chargeField h.smooth J x hx hχ (fun y => U (y-x 0))
    (fun i : Axis => (hp i).comp (continuous_id.sub continuous_const)) q d
  have he : l=(frontRead q x D).comp L := (spectrum S d).ext fun i => p i n q x hx χ hχ
  exact LinearMap.congr_fun he v

/-- This is the reduction from paying for the continuum of all v's. No
need to show that one quantification over their bases suffices *in the
shell estimates*. After evaluating the estimates, equality of actual
flux **linear maps** on the hierarchy suffices, even for rotation, to
produce StressLaws -- still uses the very same nonzero centered J throughout.
-/
lemma charges (hC : C.Makes) (hs : CellHyp C f) (ho : f.PointLimits C S) (H : S.Hierarchy)
    (h : V.Derivatives S) (J : S.Stress) (hj : Conserved V H.spin J) (p : Legs f J) :
    ∃ (B : Parts S) (Y : SpinRows S), StressLaws S J B Y := by
  have hB (d) (i : Orbits S d) : ShellBound f (d+1) 3 (spectrum S d i) J := p ⟨d,false,i⟩
  choose X hX using fun d (i : Orbits S d) (b : Axis) => annular_field hC hs ho H h hj (spectrum S d i)
    (fun _ => basis b) (fun _ => contDiff_const) (killing_const _) 0 (fun _ _ _ => by simp) (d+1) (hB d i)
  let B (d : ℕ) (b : Axis) := (spectrum S d).constr ℂ fun i => X d i b
  have ht (d : ℕ) (b : Axis) : ∀ v, enters J d _ (fun _ => basis b) (B d b) v := on_all H (fun _ => continuous_const) (by
    intro i n q x hx χ hχ
    rw [front_eval,(show B d b (spectrum S d i)=_ from (spectrum S d).constr_basis ..)]
    exact hX d i b _ q x hx _ hχ)
  have hY (d) (i : Orbits S d) : ShellBound f d 4 (spectrum S d i) J := p ⟨d,true,i⟩
  have hv (k : Ortho.Skew) (y : E4) (r : ℝ) : orbital k 0 (r • y)=r^1 • orbital k 0 y := by
    simp only [orbital,M4.move,sub_zero,map_smul,pow_one]
  choose Y hY using fun d (i : Orbits S d) k => annular_field hC hs ho H h hj (spectrum S d i) (orbital k 0)
    (smooth_orbital k 0) (killing_orbital k 0) 1 (fun y r _ => hv k y r) d (hY d i)
  let A (d : ℕ) (k : Ortho.Skew) := (spectrum S d).constr ℂ fun i => Y d i k
  have hw (d : ℕ) (k : Ortho.Skew) : ∀ v, enters J d d (orbital k 0) (A d k) v :=
    on_all H (fun i => (smooth_orbital k 0 i).continuous) (by
      intro i n q x hx χ hχ
      rw [front_eval,show A d k (spectrum S d i)=Y d i k from (spectrum S d).constr_basis ..]
      exact hY d i k _ q x hx χ hχ)
  have ha {n : ℕ} q k d v (x : Points (n+1)) (hx : x∈conf _) χ (hz : Window x χ) :
      frontRead q x d (A d k v) = chargeAngular H.smooth J x hx hz q v k := by
    rw [← hw d k v _ _ _ hx _ hz]; unfold orbital chargeAngular; simp; rfl
  let ψ (d : ℕ) : Ortho.Skew →ₗ[ℝ] (S.Field d →ₗ[ℂ] S.Field d) := {
    toFun := A d, map_add' := ?_, map_smul' := ?_ }
  · refine ⟨B,ψ,fun {n} {x} hx q {χ} hχ b d v => ?_, fun {n} {x} hx q {χ} hχ k d v => ?_⟩
    · rw [← flux_translation,← front_eval]
      exact ht d b v _ q x hx χ hχ
    rw [← flux_spin, ← front_eval]; exact (ha q k d v x hx χ hχ).symm
  · intro k l; apply LinearMap.ext; intro v; apply S.field_ext H.laws.toSymmetric; intro n q x hx
    obtain ⟨χ,hχ⟩ := exists_window x hx
    rw [← front_eval,← front_eval,LinearMap.add_apply,map_add]; simp only [ha _ _ _ _ _ hx χ hχ,map_add]
  intro r k; apply LinearMap.ext; intro v; apply S.field_ext H.laws.toSymmetric; intro n q x hx
  obtain ⟨χ,hχ⟩ := exists_window x hx
  rw [← front_eval,← front_eval,RingHom.id_apply,show (r • A d k) v=r • A d k v from rfl,
    show frontRead q x d (r • A d k v) = r • frontRead q x d (A d k v) from
    ((frontRead q x d).restrictScalars ℝ).map_smul .., ha q k d v x hx χ hχ, ha q (r • k) d v x hx χ hχ,map_smul]

end YM.UVNext.Grade
