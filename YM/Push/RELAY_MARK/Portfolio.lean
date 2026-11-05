import YM.Push.RELAY_MARK.Automorphism

/-!
# At RAuthors, primary equation section [no estimate assumed]

The stencil can be chosen once for each d, also before L. When
instantiating further producer obligations for this route, they must
buy/ref/tune using these actual sections. They are bona fide candidate
sections for `Family`, not definitions of an approximation pipeline.
In particular our theorem `Portfolio.build` asks NO input feasible
calendar/pushing/provisional marked estimates/Wilson extraction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function Set MeasureTheory Labels Wilson Source Lattice RG Bid
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {H : Hol G} {d : ℕ} {F : Switch G d}

section Bind

/-- Realize a whole list of powered functions using one stencil in the required Frame/Budget. -/
private lemma columns (B : Frame G d) (Y : Label G d →ₗ[ℂ] Pre G) (h : ∀ i:B.Index,
    Y (B.basis i) ∈ powered G (B.grades i).2) :
    ∃ T : SectionData B, pop T ∧ 0∈T.stencil ∧ (∀ s:Signed,T.stencil.image s.act=T.stencil) ∧
      ∀ p, T.evaluate (B.coords p)=Y p := by
  classical
  choose m V Q hq he using fun i : B.Index => powered_pose (h i)
  choose r hr using fun i => Work.G06.enclose (V i)
  let c := Finset.univ.sup r
  have ht i b : (V i b).stencil ⊆ box c := le_trans (hr i b) (by
    intro a ha
    obtain ⟨h0,h1⟩ := box_test.mp ha
    have hh : r i ≤ c := Finset.le_sup (f:=r) (Finset.mem_univ i)
    exact box_test.mpr ⟨fun j=>by specialize h0 j; omega,fun j=>by specialize h1 j; omega⟩)
  choose E hE using fun i=> Work.G06.realize G (V i) (box c) (ht i)
  let x := B.basis.constr ℂ (fun i=>E i (Q i))
  let T : SectionData B := ⟨box c,x ∘ₗ B.coords.symm.toLinearMap⟩
  let L : Label G d →ₗ[ℂ] Pre G := ((T.eval_linear).mk' _).comp B.coords.toLinearMap
  have hl i : T.evaluate (B.coords (B.basis i)) = Y (B.basis i) := by
    rw [he i]; funext U
    change MvPolynomial.aeval (Source.entry U) (x (B.coords.symm (B.coords _))) = _
    rw [LinearEquiv.symm_apply_apply B.coords (B.basis i), show x (B.basis i)=_ from Module.Basis.constr_basis ..]
    exact hE i U (Q i)
  refine ⟨T,fun i => ?_,center_box _, fun s => box_covariant c s,fun p=> LinearMap.congr_fun (show L=Y from B.basis.ext hl) p⟩
  exact ⟨m i,V i,ht i,Q i,by rw [← B.coords_basis,hl,he i]; rfl,hq i⟩

/-- A single-section option. `weave` is the regrading from actual
polynomial data needed to put the equation label into this SectionData.
Ortho here only on the signed subgroup. No demand elsewhere. -/
structure Portfolio {B : Frame G d} (H : Hol G) (T : SectionData B)
    (weave : Label G d ≃ₗ[ℂ] Label G d) : Prop where
  valid : T.Sound H
  pays : pop T
  currency (k P : ℕ) : ∃ A : ℝ, Credit T k P A -- to be applied in the schedule; no claim what values used
  inter (s : Signed) p : weave (theta s p)=theta s (weave p)
  truly p : weave (realBar p) = realBar (weave p)
  rank (p : Label G d) : p∈Maxwell.equationIdeal G d → Micro (T.evaluate (B.coords (weave p)))

lemma weaveBuild (h : Imprint H d F) (B : Labels.Frame G d) :
    ∃ T : SectionData B, Portfolio H T (twist h.toCampaign) ∧
      ∀ p, T.evaluate (B.coords (twist h.toCampaign p))=reel F p := by
  let R := twist h.toCampaign
  let Y := reel F ∘ₗ R.symm.toLinearMap
  have hp (i : B.Index) : Y (B.basis i)∈powered G (B.grades i).2 := cost_reel h.toCampaign
    (R.symm (B.basis i)) _ (inverse_tier h.toCampaign (B.basis i) _ (rise_sector _ (B.pure i)))
  obtain ⟨T,he,hx,hS,hp'⟩ := columns B Y hp
  have hl : T.Sound H := by
    refine ⟨hx,hS,?_, ?_,?_,?_,?_⟩
    · intro c
      obtain ⟨x,rfl⟩ := B.coords.surjective c
      rw [hp']; exact reel_gauge h.toCampaign _
    · rw [← B.coords_unit, hp']; change reel F (R.symm (unit G d))=1
      rw [show R.symm (unit G d)=unit G d from R.symm_apply_eq.mpr (twist_unit _).symm]; exact reel_unit h.toCampaign
    · intro s c U
      obtain ⟨p,h0⟩ := B.coords.surjective c; subst c
      rw [Frame.act_coords,hp',hp']
      change reel F (R.symm p) (pull _ _ _)=reel F (R.symm (theta s p)) U
      have hr : R.symm (theta s p)=theta s (R.symm p) := R.symm_apply_eq.mpr (by
        change _=twist _ (theta _ _); rw [twist_orient h]; change _=theta s (R (R.symm p)); rw [LinearEquiv.apply_symm_apply])
      rw [hr,reel_orient h]; rfl
    · intro c U; obtain ⟨p,h0⟩ := B.coords.surjective c; subst c
      rw [← show B.coords (realBar p)=star (B.coords p) from funext fun i => ?_,hp',hp']
      · change reel F (R.symm (realBar p)) U=star (reel F (R.symm p) U)
        have hr : R.symm (realBar p)=realBar (R.symm p) := R.symm_apply_eq.mpr (by
          change _=twist _ (realBar _); rw [twist_real h]; change _=realBar (R (R.symm p)); rw [LinearEquiv.apply_symm_apply])
        rw [hr,reel_real h]; rfl
      have hv := B.conj_basis (B.coords p) i; rw [LinearEquiv.symm_apply_apply] at hv; exact hv
    intro c; obtain ⟨p,h0⟩ := B.coords.surjective c; subst c; rw [hp',LinearEquiv.symm_apply_apply]
    have hl : Forms H d (Y p) (R (R.symm p)).val := form_reel h.toCampaign _
    rw [R.apply_symm_apply] at hl; exact (Forms.seats _ _).1 hl
  refine ⟨T,⟨hl,he, Work.G07.answer G H d B T hl he, twist_orient h, twist_real h,?_⟩,?_⟩
  · intro p hv
    rw [hp']; change Micro (reel F (R.symm (R p)))
    rw [LinearEquiv.symm_apply_apply]; exact paid_reel h.toCampaign p hv
  intro p; rw [hp']
  change reel F (R.symm (R p)) = _; rw [R.symm_apply_apply]

/-- Unconditional production of the same section and weave for all later costs at d.
Not asking for any further hypotheses on G or on chosen basis/coordinates. -/
theorem Portfolio.build (H : Hol G) (B : Labels.Frame G d) :
    ∃ (T : SectionData B), ∃ R, Portfolio H T R := by
  obtain ⟨F,h⟩ := unsym H d
  obtain ⟨T,hp,hp'⟩ := weaveBuild (impression h) B
  exact ⟨T,_,hp⟩
end Bind
end YM.Push.Mark
