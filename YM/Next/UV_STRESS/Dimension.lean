import YM.Next.UV_STRESS.Focus
import YM.Next.UV_STRESS.Tensor

/-!
# Transfer of stress rank on the actual observable quotients

Only the Maxwell case is assumed. Don't simply conjugate the center condition:
physical expectation is not the free functional in these bases! We pass
from one centered space to the other by recentering.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Set Function Filter MeasureTheory Analysis Table Ward Climb Extraction
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {L M : Register G} {S : Table L} {T : Table M}
section Recenter

structure Coherent (H : S.RealSpin) (a : T.RealSpin) (d : ℕ) (U : S.Field d ≃ₗ[ℂ] T.Field d) : Prop where
  stars v : U (S.conj H _ v)=T.conj a _ (U v)
  signed i v : U (S.mirror H _ i v)=T.mirror a _ i (U v)

lemma flips {H : S.RealSpin} {h : T.RealSpin} {d U} (hp : Coherent H h d U) : Coherent h H d U.symm := by
  constructor
  · intro v; obtain ⟨v,rfl⟩ := U.surjective v; simp [← hp.stars]
  intro i v; obtain ⟨v,rfl⟩ := U.surjective v; simp [← hp.signed]

def transformed (U : S.Field 4 ≃ₗ[ℂ] T.Field 4) : S.Stress →ₗ[ℝ] T.Stress where
  toFun B i j := U (B i j)
  map_add' _ _ := funext fun _ => funext fun _ => U.map_add ..
  map_smul' _ _ := funext fun _ => funext fun _ => (U.toLinearMap.restrictScalars ℝ).map_smul ..

lemma transformed_mem {U : S.Field 4 ≃ₗ[ℂ] T.Field 4} {H : S.RealSpin} {h : T.RealSpin}
    (hp : Coherent H h 4 U) {v : S.Stress} (hv : v∈SymSpace H) : transformed U v∈SymSpace h := by
  obtain ⟨A,B,P⟩ := sym_mem.mp hv
  refine sym_mem.mpr ⟨fun i j => congr_arg U (A i j), fun i j => by
    change T.conj _ _ (U _)=U _; rw [← hp.stars,B],?_⟩
  intro i t s
  change T.mirror _ _ i (U _)=∑ b, ∑ j : Axis,_ • U (v b j)
  rw [← hp.signed,P]; simp only [map_sum,map_smul]

def reCenter (T : Table M) : T.Stress →ₗ[ℝ] T.Stress where
  toFun B i j := centering T _ (B i j)
  map_add' _ _ := funext fun _ => funext fun _ => (centering T _).map_add ..
  map_smul' _ _ := funext fun _ => funext fun _ => ((centering T _).restrictScalars ℝ).map_smul ..

lemma enters (H : S.Hierarchy) (v : S.Stress) (h : v∈SymSpace H.spin) : reCenter S v ∈ KernelSpace H.spin := by
  obtain ⟨A,B,P⟩ := sym_mem.mp h
  refine kernel_mem.mpr ⟨sym_mem.mpr ⟨fun i j => congr_arg (centering S 4) (A i j),fun i j => ?_,?_⟩,
    fun i j => centers_field H.laws _⟩
  · exact (conj_center H _).trans (congr_arg (centering S 4) (B i j))
  intro i t s
  change S.mirror _ _ i (centering S _ (v t s))=∑ b, ∑ j : Axis,_ • centering S _ (v b j)
  rw [mirror_center H,P]; simp only [map_sum,map_smul]

lemma locks {H : S.RealSpin} {B : S.Stress} (h : B∈KernelSpace H) : reCenter S B=B := by
  funext i j
  change centering S _ _ = _
  rw [value_center,(kernel_mem.mp h).2]; simp

variable (H : S.Hierarchy) (a : T.Hierarchy)

def sending {U : S.Field 4 ≃ₗ[ℂ] T.Field 4} (h : Coherent H.spin a.spin 4 U) :
    ↑(KernelSpace H.spin)→ₗ[ℝ] ↑(KernelSpace a.spin) :=
  ((reCenter T).comp ((transformed U).comp (KernelSpace _).subtype)).codRestrict _ (fun v =>
    enters a _ (transformed_mem h (kernel_mem.mp v.property).1))

lemma embrace {U : S.Field 4 ≃ₗ[ℂ] T.Field 4} (h : Coherent H.spin a.spin 4 U) (hu : U (S.unit 4)=T.unit 4)
    (v : KernelSpace H.spin) : sending a H (flips h) (sending H a h v)=v := by
  apply Subtype.ext; funext i j
  change centering S _ (U.symm (centering T _ (U _))) = _
  rw [value_center (U _), map_sub, U.symm_apply_apply, map_sub, map_smul, ← hu, U.symm_apply_apply,
    map_smul,const_out H.laws, smul_zero,sub_zero]
  exact congr_fun (congr_fun (locks v.property) i) j

def centerEquiv {U : S.Field 4 ≃ₗ[ℂ] T.Field 4} (h : Coherent H.spin a.spin 4 U) (hu : U (S.unit 4)=T.unit 4) :
    ↑(KernelSpace H.spin) ≃ₗ[ℝ] ↑(KernelSpace a.spin) :=
  { sending H a h with
    invFun := sending a H (flips h)
    left_inv := embrace H a h hu
    right_inv := embrace a H (flips h) (hu ▸ U.symm_apply_apply (S.unit 4)) }

def rolling {H : S.RealSpin} {a : T.RealSpin} {U : S.Field 5 ≃ₗ[ℂ] T.Field 5} (h : Coherent H a 5 U) :
    ↑(Vectors H) →ₗ[ℝ] ↑(Vectors a) where
  toFun B := by
    refine ⟨fun i => U (B.val i),?_⟩
    obtain ⟨p,q⟩ := B.property
    constructor
    · exact fun i => (h.stars _).symm.trans (congr_arg U (p i))
    intro i j; rw [← h.signed,q]; simp only [map_sum,map_smul]
  map_add' _ _ := Subtype.ext (funext fun _ => U.map_add ..)
  map_smul' _ _ := Subtype.ext (funext fun _ => ((U.toLinearMap).restrictScalars ℝ).map_smul ..)

def moves {H : S.RealSpin} {a : T.RealSpin} {U : S.Field 5 ≃ₗ[ℂ] T.Field 5} (h : Coherent H a 5 U) :
    ↑(Vectors H) ≃ₗ[ℝ] ↑(Vectors a) :=
  { rolling h with
    invFun := rolling (flips h)
    left_inv := fun v => Subtype.ext (funext fun i => U.symm_apply_apply (v.val i))
    right_inv := fun v => Subtype.ext (funext fun i => U.apply_symm_apply (v.val i)) }
end Recenter

section ThroughFour
variable {C : Family G} {S : Table C.book} {W : DiffPlan S} {V : DiffPlan (Bel C.book)} {X : Scaling S}
variable (H : S.Hierarchy) (a : (Bel C.book).Hierarchy) (ho : W.Orientation H.spin)

private def chart (k : ℕ) (h : Coherent a.spin H.spin 4 (X.U k 4)) (h' : Coherent a.spin H.spin 5 (X.U k 5))
    (hh : X.U k 4 ((Bel C.book).unit 4)=S.unit 4) :
    ↑(KernelSpace a.spin) →ₗ[ℝ] ↑(Vectors a.spin) :=
  (moves h').symm.toLinearMap.comp
    ((X.r k • currentDiv W H.spin ho).comp (centerEquiv a H h hh).toLinearMap)

private lemma chart_reads (k : ℕ) (h : Coherent a.spin H.spin 4 (X.U k 4)) (h' : Coherent a.spin H.spin 5 (X.U k 5))
    (hh : X.U k 4 ((Bel C.book).unit 4)=S.unit 4) (hw : W.Derivatives S) (v : KernelSpace a.spin) (i : Axis) :
    (chart H a ho k h h' hh v).val i= ∑ j, tiltScale X W k 4 j (v.val j i) := by
  apply (X.U k 5).injective
  change X.U k 5 ((X.U k 5).symm (X.r k • (∑ j, W.deriv 4 j (centering S _ (X.U k 4 (v.val j i))))))=_
  rw [LinearEquiv.apply_symm_apply, map_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _; rw [value_center,map_sub,map_smul,W.unit_drop H.laws hw H.smooth]; simp only [smul_zero,sub_zero]
  change _=X.U k 5 (X.r k • (X.carry k (leaves W.deriv 4 j) (v.val j i)))
  have he (t : (Bel C.book).Field 5) : X.U k 5 (X.r k • t)= X.r k • X.U k 5 t :=
    ((X.U k 5).toLinearMap.restrictScalars ℝ).map_smul ..
  rw [he,X.carries_f]; rfl

private theorem stays_onto {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (f : ℕ → E→ₗ[ℝ] Y) (F : E→ₗ[ℝ] Y) (he : Surjective F) (h : ∀ x, Tendsto (fun k => f k x) atTop (𝓝 (F x))) :
    ∀ᶠ k in atTop, Surjective (f k) := by
  classical
  obtain ⟨g,hg⟩ := F.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr he)
  let B k := (f k).comp g
  have hv (v : Y) : Tendsto (fun i => B i v) atTop (𝓝 v) := by
    have ht := h (g v); rw [show F (g v)=v from LinearMap.congr_fun hg v] at ht; exact ht
  let b := Module.finBasis ℝ Y
  let I := Fin (Module.finrank ℝ Y)
  let L : (I → Y) →ₗ[ℝ] Y→L[ℝ] Y := LinearMap.toContinuousLinearMap.toLinearMap.comp (b.constr ℝ).toLinearMap
  have hR (f : Y→ₗ[ℝ] Y) : L (fun i => f (b i)) = LinearMap.toContinuousLinearMap f := by
    apply ContinuousLinearMap.coe_injective; exact b.ext fun i => b.constr_basis ..
  let W0 := LinearMap.toContinuousLinearMap (LinearMap.id : Y→ₗ[ℝ] Y)
  have ht : Tendsto (fun k => LinearMap.toContinuousLinearMap (B k)) atTop (𝓝 W0) := by
    dsimp only [W0]
    simp_rw [← hR]
    exact L.continuous_of_finiteDimensional.continuousAt.tendsto.comp
      (tendsto_pi_nhds.mpr (show ∀ i : I, Tendsto (fun k => (fun j : I => B k (b j)) i) atTop
        (𝓝 ((fun j : I => b j) i)) from fun i => hv _))
  filter_upwards [ht.eventually (ContinuousLinearMap.isOpen_injective.mem_nhds (show Injective W0 from injective_id))] with k hk
  intro y; obtain ⟨x,hx⟩ := (LinearMap.injective_iff_surjective.mp (show Injective (B k) from hk)) y; exact ⟨g x,hx⟩

/-- Free prerequisite. Producer Maxwell must realize it with T.J in the
chosen normalization (both signs allowed *there*, not varying later).
On the actual `Bel` fields: no dimensions in an unconstrained jet API. -/
structure FreeDiv (T : Lighthouse C.book) (h : (Bel C.book).Hierarchy) (p : T.W.Orientation h.spin) : Prop where
  onto : Surjective (currentDiv T.W h.spin p)
  one : Module.finrank ℝ (LinearMap.ker (currentDiv T.W h.spin p)) = 1
  enters : T.J ∈ KernelSpace h.spin
  origin : Conserved T.W h.spin T.J
  sign : T.J ≠ 0

lemma vector_coherence {d : ℕ} (ht : Stable H.spin a.spin W V X) :
    ∀ᶠ k in atTop, Coherent a.spin H.spin d (X.U k d) :=
  (ht.hsym d).mono fun _ hk => ⟨hk.2,hk.1⟩

/-- Actual physical full rank (onto) and one-dimensional stress line. -/
theorem differential_rank (T : Lighthouse C.book) (p : T.W.Orientation a.spin)
    (hf : FreeDiv T a p) (hw : W.Derivatives S) (hh : T.W.Derivatives (Bel C.book))
    (X : Scaling S) (hz : Approaches (path X) (isoPanel X)) (ht : Stable H.spin a.spin W T.W X) :
    Surjective (currentDiv W H.spin ho) ∧ Module.finrank ℝ (LinearMap.ker (currentDiv W H.spin ho))=1 := by
  classical
  let T₀ := currentDiv T.W a.spin p
  have ha : ∀ᶠ k in atTop, Coherent a.spin H.spin 4 (X.U k 4) ∧ Coherent a.spin H.spin 5 (X.U k 5) ∧
      X.U k 4 ((Bel C.book).unit 4)=S.unit 4 := (vector_coherence H a ht).and ((vector_coherence H a ht).and (ht.units 4))
  let Z (k : ℕ) : ↑(KernelSpace a.spin)→ₗ[ℝ] ↑(Vectors a.spin) :=
    if Hk : Coherent a.spin H.spin 4 (X.U k 4) ∧ Coherent a.spin H.spin 5 (X.U k 5) ∧
      X.U k 4 ((Bel C.book).unit 4)=S.unit 4 then chart H a ho k Hk.1 Hk.2.1 Hk.2.2 else 0
  have he (v : KernelSpace a.spin) (i : Axis) : Tendsto (fun k => (Z k v).val i) atTop (𝓝 ((T₀ v).val i)) := by
    have he (j : Axis) := Dash.arcing (bend_limit H hw a hh X 4 j hz) (tendsto_const_nhds (x:=v.val j i))
    refine Tendsto.congr' (f₁:=fun k => ∑ j, tiltScale X W k 4 j (v.val j i)) ?_ (tendsto_finsetSum _ (fun j _ => he j))
    filter_upwards [ha] with k hk; unfold Z; rw [dif_pos hk,chart_reads H a ho k _ _ _ hw]
  have hs := stays_onto (E:=KernelSpace a.spin) (Y:=Vectors a.spin) Z T₀ hf.onto (fun x => tendsto_subtype_rng.mpr (tendsto_pi_nhds.mpr (he x)))
  obtain ⟨k,hk,hz⟩ := (ha.and hs).exists
  unfold Z at hz; rw [dif_pos hk] at hz
  let Y := centerEquiv a H hk.1 hk.2.2; let Q := moves hk.2.1
  have hp : 0<X.r k := X.positive k
  have hr : Surjective (currentDiv W H.spin ho) := by
    intro y
    obtain ⟨i,hi⟩ := hz (Q.symm (X.r k • y))
    change Q.symm (X.r k • currentDiv W H.spin ho (Y i))=Q.symm _ at hi
    exact ⟨Y i,smul_right_injective _ hp.ne' (Q.symm.injective hi)⟩
  refine ⟨hr,?_⟩
  have hb := LinearMap.finrank_range_add_finrank_ker T₀
  have hl := LinearMap.finrank_range_add_finrank_ker (currentDiv W H.spin ho)
  rw [LinearMap.range_eq_top.mpr hf.onto,finrank_top,hf.one,Y.finrank_eq,Q.finrank_eq] at hb
  rw [LinearMap.range_eq_top.mpr hr,finrank_top] at hl
  omega
end ThroughFour
end YM.Next.UVStress
