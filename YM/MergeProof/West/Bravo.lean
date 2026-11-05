import YM.MergeProof.West.Blanca
import YM.Push.LOOP_COEFFICIENT.Block.Tickets
-- following YM.Next.UV_STRESS.Shell with `tenet`
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Acme
open Filter Function Set MeasureTheory Analysis Extraction Table Ward Climb Work.A01
open YM.Next.UVStress
open scoped Topology ContDiff BigOperators
variable {G : Gauge}{n d D : ℕ}
section ground
variable {C : Family G} {S : Table C.book} {F : Extraction.Order} {V : DiffPlan S}
private lemma raised (k : ℕ) {v : Fin (n+1)→Lattice.Cover} (h : Extraction.Order.grid C k v∈generic _)
    (q : Fin n → S.Tag) : ∃ (x : Points (n+1)) (s : E4) (p : Fin n → C.book.Token) (z : Fin n → Lattice.Cover),
      x = Extraction.Order.grid C k (Fin.cons 0 z) ∧ x∈generic _ ∧ Points.across s x=Extraction.Order.grid C k v ∧
      (S.classTokens ∘ p=q) := by
  let s := C.S.gridPoint k (v 0)
  let z i := v (Fin.succ i)-v 0
  let x := Extraction.Order.grid C k (Fin.cons (α:=fun _ => Lattice.Cover) 0 z)
  have hx : x=Points.across (-s) (Extraction.Order.grid C k v) := by
    ext1 i
    refine Fin.cases ?_ (fun j => ?_) i
    · ext a; simp [s,x,Extraction.Order.grid,Schedule.gridPoint]
    ext a; simp [s,z,x,Extraction.Order.grid,Schedule.gridPoint,mul_sub]; ring
  refine ⟨x,s,(expose ∘ q),z,rfl,hx.symm ▸ Extraction.Order.nearGeneric (-s) h,?_,?_⟩
  · rw [hx]; ext i; simp
  exact funext fun i => Ward.sends_back _

-- finite values in the image of the same evaluation. No nonzero label
-- cap assumption. No integral dummy representative off chosen Window.
private theorem obtainable {ι Y : Type*} [Fintype ι] [AddCommGroup Y] [Module ℂ Y]
    (R : Y →ₗ[ℂ] (ι → ℂ)) (p : ι → ℂ)
    (h : ∀ g : ι→ℂ,(∀ v : Y, (∑ i, g i*R v i)=0) → (∑ i, g i*p i)=0) :
    ∃ v, R v=p := by
  classical
  suffices he : p∈LinearMap.range R from he
  by_contra H
  let S := LinearMap.range R
  have he : S.mkQ p≠0 := fun hv => H ((Submodule.Quotient.mk_eq_zero _).mp hv)
  obtain ⟨f,hf⟩ := Module.Projective.exists_dual_ne_zero ℂ he
  let L := f.comp S.mkQ
  let g (i : ι) := L (Pi.single i 1)
  have hh (w : ι → ℂ) : L w= ∑ i, g i * w i := by
    have he : w= ∑ i : ι, w i • Pi.single i 1 := by
      funext j; simp [Pi.single_apply,apply_ite]
    conv_lhs => rw [he]
    rw [map_sum]; apply Finset.sum_congr rfl; intro i _; simp [mul_comm,g]
  apply hf
  change L p=0
  rw [hh]; apply h g
  intro v; rw [← hh]; unfold L; rw [LinearMap.comp_apply, show S.mkQ _=0 from
    (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self ..),map_zero]

-- Flux coverage at all x.
theorem annular_fieldA (hC : C.Makes) (hq : Cells.CellHyp C F) (ho : F.PointLimits C S)
    (H : S.Hierarchy) (h : V.Derivatives S) {J : S.Stress} (hc : Conserved V H.spin J) (v : S.Field d)
    (U : E4→E4) (hw : ∀ i : Axis,ContDiff ℝ ∞ (fun y => U y i)) (hl : killing U) (p : ℕ)
    (hg : ∀ y (r : ℝ),0<r → U (r • y)=r^p • U y)
    (D : ℕ) (hh : D+(3+p)=d+4) (HA:Aroma C) :
    ∃ B : S.Field D, ∀ (n : ℕ) (q : Fin n→S.Tag) (x : Points (n+1)), x∈conf _ →
      ∀ χ, Window x χ → flux J χ (fun y => U (y-x 0)) x q v=disc (Fin.cons ⟨D,B⟩ q) x := by
  classical
  choose W hW using fun I : Watch C => exists_window I.held I.distinct
  let A (I : Watch C) := flux J (W I) U I.held (S.classTokens ∘ I.q) v
  have hs (I : Finset (Watch C)) : ∃ B : S.Field D,∀ y∈I,A y=y.tester S D B := by
    let Z := LinearMap.pi (fun y : I => y.val.tester S D)
    obtain ⟨B,hB⟩ := obtainable Z (fun y : I => A y.val) (fun g hx => tenet hC hq ho H h hc v U hw hl p hg D hh HA
      (fun y : I => y.val) g hx (fun y : I => W y.val) (fun y => hW _))
    exact ⟨B,fun y hy => (congr_fun hB (⟨y,hy⟩:I)).symm⟩
  obtain ⟨T,hT⟩ := Work.A04.finite_faithful _ (observes H D)
  obtain ⟨B,hB⟩ := hs T
  have hv (I : Watch C) (χ : E4 → ℝ) (hh : Window I.held χ) :
      flux J χ U I.held (S.classTokens ∘ I.q) v = I.tester S D B := by
    obtain ⟨b,hb⟩ := hs (insert I T)
    have ht : b=B := hT (funext (fun y : T => (hb y.val (Finset.mem_insert_of_mem y.property)).symm.trans (hB y y.property)))
    exact (unchanged_flux H h hc v U hw hl _ I.distinct hh (hW I) _).trans (ht ▸ hb I (Finset.mem_insert_self ..))
  refine ⟨B,fun n q x hx χ hχ => ?_⟩
  refine tendsto_nhds_unique_of_frequently_eq (continuous_flux H hx hχ U (fun i => (hw i).continuous) J q v)
    (cont_disc H (Fin.cons ⟨D,B⟩ q) hx).continuousAt ?_
  refine (((meets_grid C x).and_eventually (valid_nearby hx hχ)).mono ?_)
  rintro y ⟨⟨hp,k,w,rfl⟩,_,hz⟩
  obtain ⟨_,s,u,z,rfl,hp',hu,rfl⟩ := raised (C:=C) k hp q
  let I : Watch C := ⟨n,k,z,u,hp'⟩
  rw [← hu] at hz ⊢
  change flux J χ (fun y => U (y - Points.across s I.held 0)) (Points.across s I.held) (S.classTokens ∘ u) v =
    disc _ (Points.across s I.held)
  rw [moves_flux H I.distinct s U J _ v (show Window (Points.across s I.held) χ from hz),
    slide_disc H I.held s I.distinct,show (fun y => U (y-I.held 0)) = U from funext fun y => by rw [I.origin,sub_zero]]
  exact (hv I _ (moves_window s hz)).trans (Watch.test_known _ _)
end ground
end YM.MergeProof.Acme
