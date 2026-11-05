import YM.Extra.WEAK_SCALING_ACTLAW.Normalize
import YM.Work.A01.Mirror

/-!
# Criteria for a common normalized nonzero choice on the IR stress line

Remove the actual scalar expectation preserving **the local laws at all words**
(translation and centered angular shell, no surface term premise). Pre alone
without physical nontriviality is NOT enough for this ActLaw route. Give
also a finite matrix certificate at four/five sufficient on the free comparator
(E conserved-line calculation; requires separate classification and kernel
computations on the actual colored/invariant quotient).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.WeakScaling
open Set Filter Function MeasureTheory Analysis Table Ward Org Climb
open scoped Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {L : Register G} {S : Table L} {W : DiffPlan S} {n d : ℕ}

def scalarPart (J : S.Stress) : S.Stress := fun a b => Work.A15.front (n:=0) 0 Fin.elim0 4 (J a b) • S.unit 4
def centered (J : S.Stress) : S.Stress := J - scalarPart J

private lemma at0 : (0:Points 1) ∈ conf _ := fun _ _ _ => Subsingleton.elim _ _
private lemma full (v : S.Tag) : (fun _ : Fin 1 => v) = Fin.cons v Fin.elim0 := funext (Fin.cases rfl (fun j => j.elim0))

lemma unit_mean (H : S.Hierarchy) : Work.A15.front (n:=0) 0 Fin.elim0 d (S.unit d) = 1 := by
  rw [Work.A15.front_apply,S.at_unit H.laws at0]
  exact H.laws.trivial (fun i => ⟨_,S.representative _ (Fin.elim0 (α:=S.Tag) i).2⟩) _

lemma centered_mean (H : S.Hierarchy) (J : S.Stress) : Centered (centered J) := by
  intro a b
  unfold centered scalarPart; simp [map_sub,unit_mean H]

lemma centered_type (H : S.Hierarchy) (J : S.Stress) (hs : ∀ a b, J a b = J b a)
    (hc : ∀ a b, S.conj H.spin 4 (J a b)=J a b) (ht : RawTensor H.spin J) :
    (∀ a b, centered J a b=centered J b a) ∧ (∀ a b, S.conj H.spin 4 (centered J a b)=centered J a b) ∧ RawTensor H.spin (centered J) := by
  let F := Work.A15.front (n:=0) (S:=S) 0 Fin.elim0 4
  have hr (v : S.Field 4) : F (S.conj H.spin 4 v) = star (F v) := by
    dsimp only [F]; simp_rw [Work.A15.front_apply, ← full]
    exact Work.A01.real_eval H.laws.toSymmetric H.spin at0 (fun _ => (⟨4,v⟩ : S.Tag))
  have hm (s : Signed) (v : S.Field 4) : F (S.mirror H.spin _ s v) = F v := by
    have he := Work.A01.mirror_eval H.laws.toSymmetric H.spin at0 (fun _ => (⟨4,v⟩:S.Tag)) s
    rw [show Points.move s.ortho (0:Points 1) = 0 by ext1 i; exact s.ortho.motion.map_zero] at he
    dsimp only [F]; simp_rw [Work.A15.front_apply, ← full]; exact he
  have he (a b) : centered J a b=J a b-F (J a b) • S.unit 4 := rfl
  refine ⟨fun a b => ?_,fun a b => ?_, ?_⟩
  · rw [he, hs a b, he]
  · rw [he,map_sub,hc, map_smulₛₗ,S.conj_unit]
    change J a b - star (F (J a b)) • S.unit 4 = _
    rw [← hr,hc]
  intro s a b
  rw [he,map_sub,map_smul,S.mirror_unit,← hm s,ht]
  simp_rw [map_sum, map_smul,he, smul_sub,Finset.sum_sub_distrib, Finset.sum_smul,smul_assoc]









lemma flux_nontrivial (H : S.Hierarchy) (J : S.Stress) {p : Parts S} {Y : SpinRows S} (h : StressLaws S J p Y) (hp : p ≠ 0) : J ≠ 0 := by
  rintro rfl; apply hp
  funext d b; apply LinearMap.ext; intro v
  apply S.field_ext H.laws.toSymmetric; intro n q x hx
  obtain ⟨χ,hχ⟩ := Work.A01.exists_window x hx
  rw [← h.translation hx q hχ b d v,← Work.A15.translationFlux_apply hx hχ H.smooth,map_zero, ← Work.A15.front_apply]
  exact (map_zero (Work.A15.front x q (d+1))).symm

lemma free_nonzero {T : Lighthouse L} (H : (Bel L).Hierarchy) (ht : T.Goes L H.spin) : T.J ≠ 0 := by
  apply flux_nontrivial H T.J ht.delta
  intro h; apply ht.born; ext1 b; ext1 v
  exact (smul_eq_zero.mp (congrArg (fun f : Parts (Bel L) => f 4 b v) h)).resolve_left T.hκ

/-- E stress divergence matrix on the FREE quotient (not an abstract toy
certificate with unrelated nulls). Here A,B,C stand for U₁,U₂,U₃ in E
(diagonal incident-pair sum each edge once, diagonal nonincident i<j sum,
and off-diagonal cross sum). The tuple at (1,-1,2) is **twice** the indicated
stress. a,b stand for E A,B five-vector families. Spanning and the two
independent columns' detection on the exact free quotient still to prove;
no comparison to Yang–Mills derivatives is assumed for this test. -/
def div (W : DiffPlan S) (B : S.Stress) (b : Axis) := ∑ a : Axis, W.deriv 4 a (B a b)
lemma matrix_line (T : Lighthouse L) (h : (Bel L).RealSpin) (A B C : (Bel L).Stress)
    (spans : ∀ P : (Bel L).Stress, (∀ a b, P a b = P b a) → (∀ a b, (Bel L).conj h 4 (P a b)=P a b) →
      RawTensor h P → Centered P → ∃ x y z : ℝ, P = x • A + y • B + z • C)
    (a b : Axis → (Bel L).Field 5) (hA : div T.W A = (2:ℝ) • a) (hB : div T.W B = (2:ℝ) • b) (hC : div T.W C = b-a)
    (he : LinearIndependent ℝ ![a,b]) {τ : ℝ} (ht : τ ≠ 0) (hJ : T.J = τ • (A - B + (2:ℝ) • C)) : Line T h := by
  intro P ⟨hs,hr,hd⟩ hP hZ
  obtain ⟨x,y,z,rfl⟩ := spans P hs hr hP hZ
  have hu (f : ℝ) (X : (Bel L).Stress) (i j : Axis) := ((T.W.deriv 4 i).restrictScalars ℝ).map_smul f (X i j)
  have hv : (2*x-z) • a + (2*y+z) • b = 0 := by
    have h (f : ℝ) (X : (Bel L).Stress) (i j : Axis) : T.W.deriv 4 i (f • X i j) = f • T.W.deriv 4 i (X i j) := hu f X i j
    have hh : (x • div T.W A + y • div T.W B + z • div T.W C) = 0 := by
      funext j; specialize hd j
      simp_rw [Pi.add_apply,Pi.smul_apply,map_add,h,Finset.sum_add_distrib, ← Finset.smul_sum] at hd; exact hd
    rw [hA,hB,hC,smul_sub,smul_smul,smul_smul,mul_comm x,mul_comm y] at hh
    rw [sub_smul,add_smul,← hh]; abel
  obtain ⟨hx,hy⟩ := LinearIndependent.pair_iff.mp he _ _ hv
  rw [show y = -x by linarith, show z = x*2 by linarith]
  refine ⟨x/τ,?_⟩
  rw [hJ,smul_smul,div_mul_cancel₀ _ ht,smul_add,smul_sub,smul_smul, neg_smul, sub_eq_add_neg]
end YM.Extra.WeakScaling
