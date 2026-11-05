import YM.MergeProof.Eureka
set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function Set Filter Labels Lattice Bid
open Extraction Extraction.Lease Next.Extract Dash
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {C : Family G} {F : Extraction.Order} {d : ℕ} {R : Weave G} {b : Presentation C}
    {S : Table C.book} {D : Bin S} {Z : ∀ d : ℕ, ℕ→ CoordMap C d}

open YM.MergeProof
variable {X : ∀ d,RelayDifference.Cutoffs→ (C.label d≃ₗ[ℂ] C.label d)}
lemma drumroll (h:Scotia C R X b) (ht : Projected b F D Z) (d : ℕ) :
    ∃ L : Label G d ≃ₗ[ℂ] C.label d, (∀ p, p∈Maxwell.equationIdeal G d ↔ L p∈LinearMap.ker (D d).trueP.toLinearMap) ∧
      (∀ p,L (realBar p)=star (L p)) ∧ ∀ p s,L (theta s p)=(C.labels.level d).act s.ortho (L p) := by
  let W := C.labels.level d
  let T := (D d).trueP
  let A := (D d).step
  have ha := ht.approaches d
  change Tendsto A F.fuse (𝓝 T) at ha
  have hw':= (RelayDifference.cutoff_grows F).eventually (h.turns d); have hg : ∀ᶠ i in F.fuse, Symmetry W (A i) := by
    filter_upwards [hw'] with i hi; dsimp only [W,A]; rw [ht.same]; exact hi i.2|>.2.2
  have hw (x : W.Coeff) : Tendsto (fun i=> A i x) F.fuse (𝓝 (T x)) := Dash.arcing ha tendsto_const_nhds
  have hp : Symmetry W T := by
    constructor
    · intro s x
      let g := travelH W s
      exact tendsto_nhds_unique_of_eventuallyEq (hw (g x)) (g.continuous.continuousAt.tendsto.comp (hw x)) (hg.mono fun i hi=> hi.signed s x)
    intro x
    exact tendsto_nhds_unique_of_eventuallyEq (hw (star x)) (hw x |>.star) (hg.mono fun i hi=> hi.real_ x)
  let Yx (i) := T * A i + (1-T)*(1-A i)
  have h0 : T*T=T := by
    apply ContinuousLinearMap.ext; exact (D d).final
  have hu : Tendsto Yx F.fuse (𝓝 1) := by
    have hh := (tendsto_const_nhds (x:=T)|>.mul ha).add
      ((tendsto_const_nhds (x:=(1-T))|>.mul (tendsto_const_nhds (x:=1)|>.sub ha)))
    rw [show T*T+(1-T)*(1-T)=1 by rw [sub_mul,one_mul,mul_sub,h0,mul_one]; abel] at hh
    exact hh
  obtain ⟨⟨N,p⟩,hs,hN,H⟩ := ((hu.eventually (Units.isOpen.mem_nhds (x:=1) (isUnit_one ))).and (hw'.and hg)).exists
  let i := (N,p)
  have hz : IsUnit (Yx i) := hs
  obtain ⟨Y,hY⟩ := Spin.unit_shape (Yx i) hz
  have he (x) : Y x = T (A i x) + ((x-A i x)-T (x-A i x)) := by
    have hv (x) : Y x= Yx i x := LinearMap.congr_fun hY x
    simp [hv,Yx]
  refine ⟨(bindP C R d N p (X d (N,p))).trans Y, fun q=>?_,fun q=>?_,fun q s=>?_⟩
  · suffices hh : A i= b.step d i by
      have hl (x) : Y (A i x)=T (Y x) := by
        have hr x : A i (A i x)=A i x := (D d).projection ..
        have hc x : T (T x)=T x := (D d).final _
        rw [he,he,hr,sub_self,map_zero, sub_self,add_zero,map_add,hc]
        simp only [map_sub,hc,sub_self,add_zero]
      let L := bindP C R d N p (X d (N,p))
      change q∈Maxwell.equationIdeal G d ↔ T (Y (L q))=0
      rw [← hl, map_eq_zero_iff _ Y.injective,hh]
      change _↔ _∈LinearMap.ker _
      rw [(h.step d N p).ker]
      exact ⟨fun he=> ⟨_,he,rfl⟩,fun h=>by
        obtain ⟨x,hx,h⟩ := h; exact L.injective h ▸ hx⟩
    rw [show A = _ from ht.same d]
  · have ht : ∀ x,Y (star x) = star (Y x) := fun x=>by
      simp only [he,hp.real_,(show Symmetry W (A i) from H).real_,← star_sub, ← star_add] -- Y after
    simp only [LinearEquiv.trans_apply,(hN p).1, ht]
  · let V := travelH W s
    have ht (x) : Y (V x) = V (Y x) := by
      rw [he,he]; simp only [(show ∀ x,A i (V x)=_ from fun _=> H.signed s _),hp.signed]
      simp only [i,V,map_sub,map_add,hp.signed]
    simp only [LinearEquiv.trans_apply, (hN p).2.1]; exact ht _

-- Apply at exactly the post-ties normalized base. Needs FREE comparison assumptions,
-- not assuming any rank agreement with interacting S.
theorem thrush (h:Scotia C R X b) (ht : Projected b F D Z)
    {M : ℕ→Table C.book} {T} {W} (H : Base C F S M D T W)
    (hf : (Maxwell.freeTable C.labels).RealSpin) (hp : ∀ d, Maxwell.residual G d=⊥) : Maxwell.Ranks T H.kernel.spin := by
  classical
  refine ⟨hf,fun d=>?_⟩
  let Y := Maxwell.freeTable C.labels
  let B := C.labels.level d
  obtain ⟨L,hL,hb',hv⟩ := drumroll h ht d
  let V : C.label d≃ₗ[ℂ] C.label d := L.symm.trans B.coords
  have he (p) : L p∈T.null d ↔ (B.coords p) ∈ Y.null d := by
    rw [H.null d,← hL]
    constructor
    · intro hk; apply (Maxwell.projectionExact ..).1; rw [hp]
      rw [Submodule.mem_bot]; apply Subtype.ext
      change Maxwell.observable G d ((C.labels.level d).coords.symm (B.coords p))=0
      rw [B.coords.symm_apply_apply]; exact LinearMap.mem_ker.mp hk
    intro hk; have H := (Maxwell.projectionExact ..).2 hk
    rw [hp,Submodule.mem_bot] at H
    apply LinearMap.mem_ker.mpr
    have hh : Maxwell.observable G d ((C.labels.level d).coords.symm (B.coords p))=0 := congr_arg Subtype.val H
    rw [B.coords.symm_apply_apply] at hh; exact hh
  have hp (p) : p∈T.null d ↔ V p∈ Y.null d := by
    obtain ⟨x,rfl⟩ := L.surjective p; rw [show V (L x)=B.coords x from by simp [V]]; exact he x
  have ho : (T.null d).map V.toLinearMap=Y.null d := by
    refine le_antisymm (fun x hx=>?_) (fun x hx=>?_)
    · obtain ⟨p,hp',he⟩ := hx; subst x; exact (hp p).1 hp'
    have hb := hp (V.symm x); rw [V.apply_symm_apply] at hb
    exact ⟨V.symm x,hb.2 hx,V.apply_symm_apply _⟩
  let Q : T.Field d≃ₗ[ℂ]Y.Field d := Submodule.Quotient.equiv _ _ V ho
  have hg x : Q (T.project d x)=Y.project d (V x) := rfl
  have hu p : V (L p)=B.coords p := by simp [V]
  refine ⟨Q,fun x=>?_,fun s x=>?_⟩
  · obtain ⟨x,rfl⟩ := T.onto d x
    obtain ⟨p,rfl⟩ := L.surjective x
    change Q (T.project d (star (L p)))=Y.conj hf d _
    rw [hg,hg,Y.conj_project,hu,←hb',hu]
    refine congr_arg _ ?_; funext i
    have ht := B.conj_basis (B.coords p) i; rw [B.coords.symm_apply_apply] at ht; exact ht
  obtain ⟨x,rfl⟩ := T.onto d x
  obtain ⟨p,rfl⟩ := L.surjective x
  change Q (T.project d (B.act s.ortho (L p)))=Y.mirror hf d _ _
  rw [hg,hg, ← hv,hu,hu]
  exact congr_arg (Y.project d) (Eq.symm (B.act_coords ..))
end YM.Push.Mark
