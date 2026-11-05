import YM.Analysis.Polydisc
import YM.Bid.Grow

/-! # Boundary word nulls are already Euclidean label nulls under the C26 inputs -/

set_option autoImplicit false
noncomputable section
namespace YM.Work.C26
open Set Filter Function Distribution Boundary
open scoped Topology

variable {G : Gauge} {L : Register G} {S T : Table L} {n : ℕ}

lemma expect_cast (U : Surface S) (b : Sentence S) (v : Fin n → Letter S)
    (h : n = b.length) (H : ∀ i, b.get (Fin.cast h i) = v i) :
    U.expect b = U.W n (fun i => (v i).1) (Joint.materialize n (fun i => (v i).2)) := by
  subst n
  have : b.get = v := funext H
  subst v
  rfl

/-- Test in the slot even after reordering (where it need no longer be the head). -/
lemma marker_on_joint (density : Bid.C25) (U : Surface S) (v : Fin n → S.Union)
    (i : Fin n) (hi : U.Marker (v i)) : U.W n v = 0 := by
  have h1 (f : Fin n → Test4) : U.W n v (Joint.materialize n f) = 0 := by
    let q : Fin n → Letter S := fun i => (v i, f i)
    obtain ⟨a,b,h⟩ := List.append_of_mem (List.mem_ofFn.mpr ⟨i,rfl⟩ : q i ∈ List.ofFn q)
    have e := expect_cast U (List.ofFn q) q (by simp) (by simp)
    change U.expect (List.ofFn q) = U.W n v (Joint.materialize n f) at e
    rw [← e,h]; exact hi a b (f i)
  have e : Submodule.span ℂ (range (Joint.materialize n)) ≤ LinearMap.ker (U.W n v).toLinearMap := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f,rfl⟩
    exact h1 f
  have H := Submodule.topologicalClosure_minimal _ e (U.W n v).isClosed_ker
  rw [density n] at H
  ext1 f
  exact H (Submodule.mem_top)

lemma strict_zero {D : ∀ n, Blanket n} {U : Surface S} {B : Waves S} {F : U.Aurora D}
    (hB : B.Region T) (hF : F.FullBody B) (hs : T.Symmetric) (hr : T.respects S)
    (v : Fin n → L.Token)
    (h : U.W n (fun i => S.pin (v i).1 (S.project _ (v i).2)) = 0)
    (p : Points n) (hp : StrictMono (fun i => time (p i))) : T.read p v = 0 := by
  rw [← B.root_raw hs hr hB v p hp]
  let z := place (trace p) (0 : Heights n)
  have e := Surface.Aurora.lower F hF _ _ z hp h
  have e1 : trace z = trace p := by ext1 i; simp [z, trace, place]
  have e2 : shift z (fun i => time (p i)) = (fun i => ↑(time (p i))*Complex.I) := by
    ext1 i; simp [shift, z, place]
  rwa [Waves.restricted,e1,e2] at e

/-- For a class of labeled words closed under permutation it suffices to reason in
strict temporal order; ties on Conf follow by continuity *after sorting*. -/
lemma read_zero (hs : T.Hierarchy) (v : Fin n → L.Token) (p : Points n) (hp : p ∈ conf n)
    (h : ∀ (r : Equiv.Perm (Fin n)) (q : Points n), StrictMono (fun i => time (q i)) →
        T.read q (v ∘ r) = 0) : T.read p v = 0 := by
  let r := Tuple.sort (fun i : Fin n => time (p i))
  let q := Points.rearrange r p
  let y (i : Fin n) := time (q i)
  have H : y ∈ sunrise n := Tuple.monotone_sort (fun i : Fin n => time (p i))
  haveI := awaits H
  rw [← hs.laws.same r hp]
  have hc : Continuous (place (trace q)) := by
    unfold place points
    simp_rw [show position = _ from funext fun x => funext fun t => (Mink.combine_at x t).symm]
    fun_prop
  have hy : place (trace q) y = q := by ext1; simp [place, trace, y]
  have hx := ((T.smooth_read hs.smooth (v ∘ r)).continuousOn q (Points.rearrange_in r hp)).continuousAt
    ((conf_open n).mem_nhds (Points.rearrange_in r hp))
  apply tendsto_nhds_unique (f := fun z => T.read (place (trace q) z) (v ∘ r))
    (hx.tendsto.comp ((hy ▸ hc.tendsto y).mono_left (nhdsWithin_le_nhds (s := east n))))
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (h r _ (by simpa only [place, points_apply, time_position] using (show StrictMono z from hz))).symm

theorem answer : YM.Bid.C26 := by
  intro density G L S T W D U B F hn ht hs hw _ hB hF x hx
  have hr : T.respects S := fun d => (hn d).symm.le
  obtain ⟨d,z,rfl⟩ := W.covered hs.laws.toSymmetric hw x
  obtain ⟨w,rfl⟩ := S.onto d z
  suffices e : S.project d w = 0 by rw [e,map_zero]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [← hn, T.criterion]
  intro n b p hp
  refine read_zero ht _ p hp fun r q hq => strict_zero hB hF ht.laws.toSymmetric hr _ ?_ q hq
  apply marker_on_joint density U _ (r.symm 0)
  let v := Fin.cons (α := fun _ => L.Token) ⟨d,w⟩ b
  let P := fun i => U.Marker (S.pin (v i).1 (S.project _ (v i).2))
  change P (r (r.symm 0))
  rw [r.apply_symm_apply]
  exact hx

end YM.Work.C26
