import YM.Extra.SOURCE_HISTORIES.LocalDebt
import YM.Planned.ATOM_REGULAR_ESTIMATE.Geometry
import YM.Planned.ATOM_REGULAR_ESTIMATE.Sampled
import YM.Push.LOCAL_SPLITTING.Raw
import YM.Push.LOCAL_SPLITTING.Transport


/-!
Restore indicator misses into the given forced alphabet using `Local`'s
construction. Keep explicit the raw bill, stencil, orientation price. No
assumption even of coherent choices of coordinates here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels Extra.Histories Push.Local Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {n m : Side} {G : Gauge} {d : ℕ}

/-! ### General reassembly/covariance lemmas -/
namespace Build
variable {F : Labels.Frame G d} {o : Site m} {M : Raw F m} {X : ℕ → Support m} {A : Hol G} {T : SectionData F}
    {R : Rep G m} {Y : Support m} {i : ℕ} {a b v σ C Λ δ w : ℝ}






variable {P : Coefficient F m}





end Build

namespace RollingMark
lemma mem_inspected (X : Support n) (x : Site n) : x∈inspected X ↔ x∈X ∨ ∃ p : Face (Per n), ¬ Disjoint X (touched p) ∧ x∈touched p := by
  simp only [inspected,Finset.mem_union, Finset.mem_biUnion,Finset.mem_univ,true_and]; apply or_congr_right; apply exists_congr; intro i
  by_cases he : Disjoint X (touched i) <;> simp [he]

lemma stamp_read (X : Support n) (s : Signed) (b : Site n) : inspected (X.image (affine s b)) = (inspected X).image (affine s b) := by
  let f := affine s b; let p := Face.send s b
  have hi : Injective f := (turnSites s b).injective
  have h (z) : touched (p z)=(touched z).image f := Work.H03.touched_send s b z
  have he (i) : Disjoint (X.image f) (touched (p i)) ↔ Disjoint X (touched i) := by rw [h]; exact Finset.disjoint_image hi
  have hp : Surjective p := Finite.injective_iff_surjective.mp (Face.injective_send s b)
  ext x; rw [mem_inspected]; constructor
  · rintro (hx|⟨z,hx,hb⟩)
    · obtain ⟨x,hm,rfl⟩ := Finset.mem_image.mp hx; exact Finset.mem_image_of_mem _ ((mem_inspected X x).2 (.inl hm))
    obtain ⟨y,rfl⟩ := hp z
    rw [h] at hb
    obtain ⟨x,hm,rfl⟩ := Finset.mem_image.mp hb
    have Hx : ¬ Disjoint X (touched y) := mt (he y).2 hx
    exact Finset.mem_image_of_mem (affine s b) ((mem_inspected X x).2 (.inr ⟨y,Hx,hm⟩))
  intro hx; obtain ⟨x,hm,rfl⟩ := Finset.mem_image.mp hx
  obtain hx|⟨z,hx,hb⟩ := (mem_inspected X x).1 hm
  · exact .inl (Finset.mem_image_of_mem _ hx)
  exact .inr ⟨p z, mt (he z).1 hx, (h z).symm ▸ Finset.mem_image_of_mem (affine s b) hb⟩

lemma stamp (X : Support n) (q : Ratio m n) (h : Odd q.count.val) (s : Signed) (b : Site m) :
    positions q (X.image (affine s (q.embed b))) = (positions q X).image (affine s b) := by
  unfold positions; rw [stamp_read,Finset.image_image,Finset.image_image]; congr 1
  ext1 x; exact parent_affine q h s b x

/-- Stronger support-motion for regular-input. No modifying the projection
promise carried to next application. -/
def Full {F : Labels.Frame G d} (T : SectionData F) (H : History G) (N p m : ℕ) (A : Hol G)
    (f : Config G (H.S.side (m+1) p) → ℂ) (c t : ℝ) (Y : Support (H.S.side (m+1) p)) :=
    let R := H.rep N p m; let S := H.levels.clock.op m p
    ∃ X : F.Coeff, ∀ y : Motion, F.coeffSize (Motion.patch F y X - Motion.patch F y 0) ≤ c ∧
      ∃ P : Coefficient F (H.S.side m p), P.x=Motion.patch F y X ∧ P.Format 0 A R ∧
        P.remBound 0 R (Real.sqrt (H.levels.clock.forcedAllowance m)) t ∧
          P.density 0 T R = Motion.dance y (blast H N p m d f) ∧
            let Z := positions S.ratio (Y.image (affine y.1 0))
            (∀ i, Z ⊆ P.support i) ∧ ∀ i, P.forced i ≠ 0 → Z ⊆ Push.Local.patch R.activities i

lemma Full.paid {F : Labels.Frame G d} {T : SectionData F} {H : History G} {N p m : ℕ} {A : Hol G} {c t : ℝ}
    {f : Config G (H.S.side (m+1) p) → ℂ} {X} (h : Full T H N p m A f c t X) : PaidAtom T H N p m A f 0 c t := by
  obtain ⟨v,hv⟩ := h; refine ⟨v,fun z => ?_⟩
  obtain ⟨h,P,hx,ht,hT,he,-⟩ := hv z; exact ⟨h,P,hx,ht,hT,he⟩
end RollingMark
open RollingMark


end YM.Planned.AtomRegular
