import YM.Work.G06.Formula
import YM.Work.G06.Pose



/-!
# G06: turn Cumuli into an equivariant polynomial section

Keep H, F and the projections through d fixed, do not infer orientation
or projection covariance from proximity estimates. Use Reynolds averaging
and realize the result again on transported curvature slots with the same
lower degree. The returned single stencil sees ALL of those paths.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.G06
open Lattice Labels RG Wilson Source Bid
open scoped Topology Matrix.Norms.Frobenius BigOperators

lemma enclose {n : ℕ} (V : Fin n → Slot) : ∃ r : ℕ, ∀ i, (V i).stencil ⊆ box r := by
  let size := fun x : Cover => Finset.univ.sup fun i : Axis => (x i).natAbs
  let W := Finset.univ.biUnion fun i => (V i).stencil
  refine ⟨W.sup size,fun i x hx => box_test.mpr ?_⟩
  have he : x ∈ W := Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hx⟩
  have hl (j : Axis) : (x j).natAbs ≤ W.sup size :=
    (show (x j).natAbs ≤ size x from Finset.le_sup (f:=fun i => (x i).natAbs) (Finset.mem_univ j)).trans
      (Finset.le_sup (f:=size) he)
  constructor <;> intro j <;> specialize hl j <;> omega

theorem realize (G : Gauge) {n : ℕ} (V : Fin n → Slot) (S : Finset Cover)
    (h : ∀ i,(V i).stencil ⊆ S) :
    ∃ E : Pose G n →ₐ[ℂ] Formula G S, ∀ U : CoverConfig G, ∀ P,
        MvPolynomial.aeval (entry U) (E P) = lumin P (mapped V U) := by
  have he (i : Fin n × G.ColorIndex) := entryPoly_slot (V i.1) (h i.1) i.2
  unfold EntryPoly at he
  choose C hC using he
  refine ⟨MvPolynomial.aeval C,fun U P => ?_⟩
  have hE : (MvPolynomial.aeval (R:=ℂ) (entry U)).comp (MvPolynomial.aeval C) =
      MvPolynomial.aeval (fun i : Fin n × G.ColorIndex => (mapped V U i.1 i.2 : ℂ)) := by
    ext i; simp only [AlgHom.comp_apply,MvPolynomial.aeval_X]; exact hC i U
  exact DFunLike.congr_fun hE P

theorem answer : YM.Bid.G06 := by
  intro G H d F m B hS hP
  obtain ⟨P,hP⟩ := hP
  obtain ⟨n,V,Q,hQ,hv⟩ := common_pose B P hP
  obtain ⟨r,hr⟩ := enclose V
  obtain ⟨E,hE⟩ := realize G V (box r) hr
  let A : SectionData F := ⟨box r,E.toLinearMap.comp Q⟩
  have he (c : F.Coeff) : A.evaluate c = averaged B P c := by
    rw [hQ]; funext U
    exact hE U (Q c)
  refine ⟨A, ?_, ?_⟩
  · exact ⟨center_box r,box_covariant r,fun c => by rw [he]; exact averaged_gauge B P hP c,
      by rw [he]; exact averaged_unit B P hP,
      fun s c U => by rw [he,he]; exact averaged_Hpart B P s c U,
      fun c U => by rw [he,he]; exact averaged_bar B P hP c U,
      fun c => by rw [he]; exact averaged_projects B P hS hP c⟩
  intro i
  exact ⟨n,V,hr,Q (Pi.single i 1), (he _).trans (hQ _),hv i⟩
end YM.Work.G06
