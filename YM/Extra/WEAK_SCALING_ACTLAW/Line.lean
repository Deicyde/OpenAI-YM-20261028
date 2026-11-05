import YM.Extra.WEAK_SCALING_ACTLAW.Criteria
import YM.Next.BOUNDARY.Alias

/-!
# Birth and identification of the physical stress line (conditional)

Lower rank via the two H tensor types on the *normalized* free and
physical systems at four and five, with exact transport between their real
forms except for a possible scalar loss BEFORE mean removal. Upper rank via
fixed finite-dimensional matrices of the free expectations and divergence
along one weak comparison (no flux inputs). This does not construct local
flux maps on the kernel. The free-space dimension inequalities and Line
remain explicit free hypotheses; see also `matrix_line`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.WeakScaling
open Function Set Filter MeasureTheory Table Climb Ward Org
open scoped Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {L : Register G} {S : Table L}

def tensors (H : S.RealSpin) : Submodule ℝ S.Stress where
  carrier := {J | (∀ a b, J a b=J b a) ∧ (∀ a b, S.conj H 4 (J a b)=J a b) ∧ RawTensor H J}
  zero_mem' := by simp [RawTensor]
  add_mem' {x y} := by
    rintro ⟨hx,hr,ht⟩ ⟨hy,hs,hu⟩
    refine ⟨fun a b => congrArg₂ (fun x y : S.Field 4 => x+y) (hx a b) (hy a b),fun a b => ?_,fun s a b => ?_⟩
    · simp [hr a b,hs a b]
    · rw [Pi.add_apply,Pi.add_apply,map_add,ht,hu]; simp [smul_add,Finset.sum_add_distrib]
  smul_mem' c x := by
    rintro ⟨hx,hr,ht⟩
    refine ⟨fun a b => congrArg (fun v : S.Field 4 => c • v) (hx a b),fun a b => ?_,fun s a b => ?_⟩
    · change S.conj H 4 (c • x a b)=c • x a b
      rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smulₛₗ,RCLike.conj_ofReal,hr]
    · change S.mirror H _ s (c • x a b)=_
      rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul,ht]; simp only [Finset.smul_sum,Pi.smul_apply,
        RCLike.real_smul_eq_coe_smul (K:=ℂ)]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => smul_comm ..

def vacuum (S : Table L) : S.Stress →ₗ[ℝ] (Axis → Axis → ℂ) := LinearMap.pi fun a => LinearMap.pi fun b =>
  ((Work.A15.front (n:=0) 0 Fin.elim0 4).restrictScalars ℝ).comp ((LinearMap.proj (φ:=fun _ : Axis => S.Field 4) b).comp (LinearMap.proj (φ:=fun _ : Axis => Axis → S.Field 4) a))

def meanFree (H : S.RealSpin) : Submodule ℝ S.Stress := tensors H ⊓ LinearMap.ker (vacuum S)

def polar (H : S.RealSpin) : Submodule ℝ (Axis → S.Field 5) where
  carrier := {v | (∀ b, S.conj H 5 (v b)=v b) ∧ ∀ k b, S.mirror H 5 k (v b)=
      ((Work.A01.eps k b:ℝ):ℂ) • v (k.perm b)}
  zero_mem' := by simp
  add_mem' {x y} := by rintro ⟨hx,hr⟩ ⟨hy,hs⟩; simp [hx,hr,hy,hs,smul_add]
  smul_mem' c x := by
    rintro ⟨hx,hr⟩
    simp only [mem_setOf_eq,Pi.smul_apply,RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smulₛₗ,RCLike.conj_ofReal,
      hx,hr, RingHom.id_apply]; exact ⟨fun _ => trivial,fun _ _ => smul_comm ..⟩

-- Actual finite divergence and its restricted range.
def sourceDiv (V : DiffPlan S) : S.Stress →ₗ[ℝ] (Axis → S.Field 5) := LinearMap.pi fun b =>
    ∑ a : Axis, ((V.deriv 4 a).restrictScalars ℝ).comp ((LinearMap.proj (φ:=fun _ : Axis => S.Field 4) b).comp (LinearMap.proj (φ:=fun _ : Axis => Axis → S.Field 4) a))
lemma source_apply (V : DiffPlan S) (J : S.Stress) : sourceDiv V J = div V J := by ext1 b; simp [sourceDiv, div]

lemma polar_div {V : DiffPlan S} {H : S.RealSpin} (he : V.Orientation H) {J : S.Stress} (h : J ∈ tensors H) :
    sourceDiv V J ∈ polar H := by
  rw [source_apply]
  obtain ⟨_,hr,ht⟩ := h
  constructor
  · simp [div,he.realDer,hr]
  intro k b
  unfold div
  rw [_root_.map_sum, Finset.smul_sum]
  conv_rhs => rw [← Equiv.sum_comp k.perm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [he.mirrorDer,Work.A01.tensor_column ht, Work.A01.eps_column,map_smul, Complex.ofReal_mul,
    smul_smul, ← mul_assoc,← Complex.ofReal_mul, Work.A01.eps_self]
  simp

def cutDiv (V : DiffPlan S) {H : S.RealSpin} (he : V.Orientation H) := LinearMap.codRestrict (polar H)
    ((sourceDiv V).domRestrict (meanFree H)) (fun x => polar_div he x.property.1)

variable {C : Family G} {S : Table C.book} {V : DiffPlan S}

-- For existence it suffices to get a one-way injection at each type,
-- in opposite directions. Use expectation on the actual side for this U.
lemma input_size (H : S.Hierarchy) (h : (Free C).Hierarchy) (U : YM.Spin.change S 4)
    (he : YM.Spin.realH H.spin h.spin U) (hq : U ((Free C).unit 4)=S.unit 4) :
    Module.finrank ℝ (meanFree h.spin) ≤ Module.finrank ℝ (meanFree H.spin) := by
  let z : (Axis → Axis → ℂ) →ₗ[ℂ] S.Stress := LinearMap.pi fun i => LinearMap.pi fun j =>
    ((LinearMap.id (R:=ℂ) (M:=ℂ)).smulRight (S.unit 4)).comp ((LinearMap.proj (φ:=fun _ : Axis => ℂ) j).comp
      (LinearMap.proj (φ:=fun _ : Axis => Axis → ℂ) i))
  let f : S.Stress →ₗ[ℝ] S.Stress := LinearMap.id - (z.restrictScalars ℝ).comp (vacuum S)
  have hf (x) : f x = centered x := rfl
  let g : (Free C).Stress →ₗ[ℝ] S.Stress := LinearMap.pi fun i => LinearMap.pi fun j =>
    (U.toLinearMap.restrictScalars ℝ).comp ((LinearMap.proj (φ:=fun _ : Axis => (Free C).Field 4) j).comp (LinearMap.proj (φ:=fun _ : Axis => Axis → (Free C).Field 4) i))
  have hg (x) i j : g x i j = U (x i j) := rfl
  have hw (x) (hx : x ∈ tensors h.spin) : g x ∈ tensors H.spin := by
    obtain ⟨hs,hr,ht⟩ := hx
    refine ⟨fun a b => congrArg U (hs a b),fun a b => ?_,fun s a b => ?_⟩
    · rw [hg, ← he.2,hr]
    rw [hg,← he.1,ht]; simp [hg]
  have hv (x : (Free C).Stress) (hX : x∈meanFree h.spin) : f (g x) ∈ meanFree H.spin := by
    obtain ⟨hs,hr,ht⟩ := hw x hX.1
    rw [hf]
    exact ⟨centered_type H (g x) hs hr ht,funext fun i => funext fun j => centered_mean H (g x) i j⟩
  let l := LinearMap.codRestrict (meanFree H.spin) ((f.comp g).domRestrict (meanFree h.spin)) (fun x => hv x.val x.property)
  refine LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp ((LinearMap.ker_eq_bot' (f:=l)).mpr ?_))
  intro x hx; apply Subtype.ext
  change x.val=0
  funext a b
  have hs := congrArg (fun v : meanFree H.spin => v.val a b) hx
  let z := (vacuum S (g x.val) a b)
  have ht := (show vacuum (Free C) x.val = 0 from x.property.2)
  have hz := congrFun (congrFun ht a) b
  have h0 : x.val a b=z • (Free C).unit 4 := U.injective (by rw [map_smul,hq]; exact sub_eq_zero.mp hs)
  change Work.A15.front 0 Fin.elim0 4 (x.val a b) = (0:ℂ) at hz
  rw [h0,map_smul,unit_mean h,smul_eq_mul,mul_one] at hz
  rw [h0,hz,zero_smul]; rfl

lemma output_size (H : S.RealSpin) (h : (Free C).RealSpin) (U : YM.Spin.change S 5) (he : YM.Spin.realH H h U) :
    Module.finrank ℝ (polar H) ≤ Module.finrank ℝ (polar h) := by
  let l : (Axis → S.Field 5) →ₗ[ℝ] Axis → (Free C).Field 5 := LinearMap.pi fun b =>
    (U.symm.toLinearMap.restrictScalars ℝ).comp (LinearMap.proj b)
  have hx (x) b : U (l x b)=x b := U.apply_symm_apply _
  have hv (x) (hp : x ∈ polar H) : l x ∈ polar h := by
    obtain ⟨hr,hs⟩ := hp
    constructor
    · exact fun b => U.injective (by rw [he.2,hx,hr])
    exact fun s b => U.injective (by rw [he.1,map_smul,hx,hx,hs])
  let u := LinearMap.codRestrict (polar h) (l.domRestrict (polar H)) (fun x => hv x.val x.property)
  refine LinearMap.finrank_le_finrank_of_injective (f:=u) fun x y he => Subtype.ext ?_
  funext b
  rw [← hx x b, ← hx y b]; exact congrArg (fun z : polar h => U (z.val b)) he

/-- Nonzero symmetric conserved tensor with scalar expectation removed.
From just one finite curve with exact alignment at four & five and the stated
free type dimension bound. No surjectivity of a rescaled matrix assumed. -/
lemma stress_birth (H : S.Hierarchy) (h : (Free C).Hierarchy) {W : DiffPlan (Free C)}
    {M D : ℕ} {Q : ℝ} (b : Curve V W H.spin h.spin M D Q) (hd : 4 < D)
    (he : V.Orientation H.spin) (hs : Module.finrank ℝ (polar h.spin) < Module.finrank ℝ (meanFree h.spin)) :
    ∃ J : S.Stress, J ≠ 0 ∧ Centered J ∧ Conserved V H.spin J ∧ RawTensor H.spin J := by
  obtain ⟨k,hk⟩ := b.graded.exists
  have ho := hk.1 5 hd
  have hi := hk.1 4 hd.le
  have h₁ := input_size H h (b.X k 4) ⟨hi.1,hi.2.1⟩ hi.2.2
  have h₂ := output_size H.spin h.spin (b.X k 5) ⟨ho.1,ho.2.1⟩
  have hh : ¬ Injective (cutDiv V he) := fun h => (LinearMap.finrank_le_finrank_of_injective h).not_gt (lt_of_le_of_lt h₂ (hs.trans_le h₁))
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot'] at hh
  push Not at hh
  obtain ⟨x,hx,h⟩ := hh
  obtain ⟨⟨hr,ht,hc⟩,hq⟩ := x.property
  have hw := congrArg Subtype.val hx
  change sourceDiv V x.val = 0 at hw
  rw [source_apply] at hw
  exact ⟨x,fun e => h (Subtype.ext e),fun i j => congrFun (congrFun (show vacuum S x.val = 0 from hq) i) j,⟨hr,ht,congrFun hw⟩,hc⟩

private lemma fit {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    (f : ℕ → A →ₗ[ℝ] B) (g : A →ₗ[ℝ] B) (h : ∀ x, Tendsto (fun k => f k x) atTop (𝓝 (g x))) :
    Tendsto (fun k => (f k).toContinuousLinearMap) atTop (𝓝 g.toContinuousLinearMap) := by
  let b := Module.finBasis ℝ A
  let F : (A →L[ℝ] B) →ₗ[ℝ] (Fin (Module.finrank ℝ A) → B) := LinearMap.pi fun i => (ContinuousLinearMap.apply ℝ B (b i)).toLinearMap
  refine norm_fit F ?_ (tendsto_pi_nhds.mpr (fun i => h (b i)))
  intro x y he
  exact ContinuousLinearMap.coe_injective (show x.toLinearMap=y.toLinearMap from b.ext (congrFun he))

namespace Curve
variable {W : MaxwellData C} {M D : ℕ} {Q : ℝ} {h : S.RealSpin} (b : Curve V W.T.W h W.hT.spin M D Q)

include b

/-- Actual physical line is at most one-dimensional: compare the kernel of
the augmented divergence (including the physical one-insertion entries) on
the full real symmetric tensor space via *one* Witness at the same table.
Even if the map of free tensors isn't mean preserving at k, it is injective
from the augmented rows here, so any two centered exact stresses compare.
-/
lemma only_line (hQ : 0 < Q) (hd : 4 < D) (hn : 1 ≤ M) (H : S.Hierarchy) (hw : V.Derivatives S)
    (hl : Line W.T W.hT.spin) {J P : S.Stress} (hJ : Conserved V h J) (hJ' : RawTensor h J) (hJ₀ : Centered J)
    (hP : Conserved V h P) (hP' : RawTensor h P) (hP₀ : Centered P) (he : J ≠ 0) : ∃ c : ℝ, P = c • J := by
  obtain ⟨ℓ,hℓ⟩ := Module.Projective.exists_dual_ne_zero ℝ (free_nonzero W.hT W.lit)
  let L := tensors W.hT.spin
  let Y := Free C
  let f k : (Axis → S.Field 5) →ₗ[ℝ] Axis → Y.Field 5 := LinearMap.pi fun a =>
    ((b.X k 5).symm.toLinearMap.restrictScalars ℝ).comp (LinearMap.proj a)
  let X k : L →ₗ[ℝ] S.Stress := LinearMap.pi fun i => LinearMap.pi fun j => ((b.X k 4).toLinearMap.restrictScalars ℝ).comp
    (((LinearMap.proj (φ:=fun _ : Axis => (Free C).Field 4) j).comp (LinearMap.proj (φ:=fun _ : Axis => Axis → (Free C).Field 4) i)).domRestrict L)
  let l := ℓ.domRestrict L
  let A k := (((f k |>.comp (b.r k • sourceDiv V)).prod (vacuum S)).comp (X k)).prod l
  let B := (((sourceDiv W.T.W).prod (vacuum Y)).domRestrict L).prod l
  have hB : Injective (LinearMap.toContinuousLinearMap B) := by
    apply (LinearMap.ker_eq_bot (f:=B)).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    obtain ⟨h₁,h₂,h₃⟩ := x.property
    have hD := congrArg (fun v : ((Axis → Y.Field 5) × (Axis → Axis → ℂ)) × ℝ => v.1.1) hx
    change sourceDiv W.T.W x.val = 0 at hD
    rw [source_apply] at hD
    obtain ⟨c,hc⟩ := hl x.val ⟨h₁,h₂,congrFun hD⟩ h₃ (fun a b => congrArg (fun v => v.1.2 a b) hx)
    have hc' := congrArg Prod.snd hx; change ℓ x.val=0 at hc'
    rw [hc,map_smul,smul_eq_mul,mul_eq_zero] at hc'
    rw [hc'.resolve_right hℓ,zero_smul] at hc; exact Subtype.ext hc
  have hb : Tendsto (fun k => LinearMap.toContinuousLinearMap (A k)) atTop (𝓝 (LinearMap.toContinuousLinearMap B)) := by
    refine fit (A:=↥L) (B:=((Axis → Y.Field 5) × (Axis → Axis → ℂ)) × ℝ) A B ?_; intro x; apply Tendsto.prodMk_nhds _ tendsto_const_nhds
    apply Tendsto.prodMk_nhds
    · refine tendsto_pi_nhds.mpr fun c => ?_
      change Tendsto (fun k => (b.X k 5).symm (b.r k • (sourceDiv V (X k x)) c)) _ (𝓝 ((sourceDiv W.T.W x.val) c))
      simp_rw [source_apply,div, Finset.smul_sum,map_sum]; exact tendsto_finsetSum _ fun a _ => b.deriv 4 hd a _
    refine tendsto_pi_nhds.mpr fun a => tendsto_pi_nhds.mpr fun c => ?_
    change Tendsto (fun k => Work.A15.front (S:=S) 0 Fin.elim0 4 (b.X k 4 (x.val a c))) atTop (𝓝 (Work.A15.front (S:=Y) 0 Fin.elim0 4 (x.val a c)))
    let v := Fin.cons (α:=fun _ : Fin (0+1) => Y.Tag) ⟨4,x.val a c⟩ Fin.elim0
    have ht := b.read_limit H hw hQ hn v (d:=4) (Fin.cases le_rfl (fun j => j.elim0)) hd id tendsto_id (0:Points 1)
      ⟨by simpa,fun i j he => False.elim (he (Subsingleton.elim _ _))⟩ (fun _ => 0) tendsto_const_nhds
    have hh k : b.read v k 0 = Work.A15.front 0 Fin.elim0 4 (b.X k 4 (x.val a c)) := by
      rw [Curve.read,readMap,smul_zero,Work.A15.front_apply]; change S.useAt S _ _=_; congr 1
      funext i; exact Fin.cases rfl (fun j => j.elim0) i
    rw [Work.A15.front_apply]; simpa only [hh] using! ht
  obtain ⟨k,hk,hg⟩ := ((hb.eventually ((ContinuousLinearMap.isOpen_injective (𝕜:=ℝ) (E:=↥L) (F:=((Axis → Y.Field 5) × (Axis → Axis → ℂ)) × ℝ)).mem_nhds (show LinearMap.toContinuousLinearMap B ∈ {u : L →L[ℝ] ((Axis → Y.Field 5) × (Axis → Axis → ℂ)) × ℝ | Injective u} from hB))).and b.graded).exists
  have hk : Injective (A k) := hk
  let U := b.X k 4
  obtain ⟨H₁,H₂,_⟩ := hg.1 4 hd.le
  have back (j : S.Stress) (hj : Conserved V h j) (ht : RawTensor h j) (h₀ : Centered j) :
      ∃ u : L, X k u = j ∧ A k u = (0,l u) := by
    let u (a c : Axis) := U.symm (j a c)
    have hu : u ∈ L := by
      refine ⟨fun a b => congrArg U.symm (hj.symmetric a b), fun a b => U.injective ?_,fun g a b => U.injective ?_⟩
      · exact (H₂ _).trans (by change S.conj h 4 (U (U.symm (j a b))) = U (U.symm (j a b)); rw [LinearEquiv.apply_symm_apply,hj.real])
      have hh := H₁ g (u a b); change U _ = S.mirror h 4 g (U (u a b)) at hh
      rw [hh]; simp only [map_sum,map_smul,u,LinearEquiv.apply_symm_apply,ht g a b]
    have hz : X k ⟨u,hu⟩ = j := funext fun a => funext fun b => U.apply_symm_apply _
    have hh' : sourceDiv V j = 0 := (source_apply ..).trans (funext hj.divergence)
    have h' : vacuum S j = 0 := funext fun a => funext (h₀ a)
    exact ⟨_,hz,Prod.ext (show (f k (b.r k • sourceDiv V (X k ⟨u,hu⟩)),vacuum S (X k ⟨u,hu⟩)) = 0 by rw [hz,hh',h',smul_zero,map_zero]; rfl) rfl⟩
  obtain ⟨u,hu,hu'⟩ := back J hJ hJ' hJ₀; obtain ⟨v,hv,hv'⟩ := back P hP hP' hP₀
  have hl : l u ≠ 0 := fun h => he (hu.symm.trans (by rw [show u=0 from hk ((hu'.trans (by simp [h])).trans (A k).map_zero.symm),map_zero]))
  refine ⟨l v / l u,hv.symm.trans <| (congrArg (X k) (hk ?_)).trans ((X k).map_smul .. |>.trans (by rw [hu]))⟩
  rw [hv',map_smul,hu']; exact Prod.ext (smul_zero ..).symm (div_mul_cancel₀ _ hl).symm
end Curve
end YM.Extra.WeakScaling
