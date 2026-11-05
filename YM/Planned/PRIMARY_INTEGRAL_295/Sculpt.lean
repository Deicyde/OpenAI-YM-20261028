import YM.Next.FREE_KERNELS.Amend
import YM.Planned.PRIMARY_INTEGRAL_295.Molecules
import YM.Planned.PRIMARY_INTEGRAL_295.Radical
import YM.Planned.PRIMARY_INTEGRAL_295.Twines


/-!
σ-family real θ, primitive input formula in G.El before applying any
$\phi$ endpoint gauge transformation.

Physical gauge on G torus.

Buried
calculation contingent on those stamps tying to actual density; true F3SO
replica/root/etc supplying the stamp separate.

Not an isolated expectation
hypothesis using committed matrix.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Porous
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Labels Lattice RG Wilson Source Source.Drops Oval Nimbuses Dunes Place Emits Ripple Purse Twines
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius NNReal ENNReal
variable {E Θ : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {I : Θ → Type} [Fintype Θ] [∀ i, Fintype (I i)]
variable {G : Gauge} {S : Finset Cover} {k l d : ℕ} {t ξ s M δ : ℝ} {F : Labels.Frame G d} {L n n' : Side}

-- soft sum across all tested normalization degrees without rescaling p factors.
def vessel (B : Roof S G) (F : Labels.Frame G d) (k : ℕ) (M : ℝ) := 1+∑ i:F.Index,flask B k (F.grades i).2 M
lemma vessel_ge (B : Roof S G) (F : Labels.Frame G d) (k:ℕ) (h:1≤M) : 1≤vessel B F k M :=
    le_add_of_nonneg_right (Finset.sum_nonneg fun i _=> zero_le_one.trans (flask_ge _ _ (F.grades i).2 h))
lemma solvent (B : Roof S G) (F : Labels.Frame G d) (k:ℕ) (i:F.Index) (h:1≤M) :
    flask B k (F.grades i).2 M ≤ vessel B F k M := (Finset.single_le_sum (f:=fun i=>flask B k (F.grades i).2 M)
      (fun i _=> zero_le_one.trans (flask_ge _ _ (F.grades i).2 h)) (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)

-- Preserve all clocks from h. Bind same indexing.
variable {X : E→Dev S G} (B : Roof S G)
variable (V : ∀ i,Stand (I i) E S G) (φ : Θ→ℝ≥0)

abbrev Scene (I : Θ→Type) := Σ i, Sky (I i)
private lemma delta (hφ : ∑ i,φ i=1) (f : Θ→ℝ) (δ:ℝ) (h : ∀ i, ‖f i-1‖ ≤ δ) :
    ‖(∑ i,(φ i:ℝ) • f i)-1‖≤δ := by
  classical
  have he (c:ℝ): ∑ i,(φ i:ℝ)*c=c:=by rw [← Finset.sum_mul,← NNReal.coe_sum,hφ,NNReal.coe_one,one_mul]
  have H : (∑ i,(φ i:ℝ) • f i)-1=∑ i,(φ i:ℝ)*(f i-1) := by simp only [smul_eq_mul,mul_sub,Finset.sum_sub_distrib,he]
  rw [H,← he δ]; apply (norm_sum_le ..).trans (Finset.sum_le_sum (fun i _=>?_))
  rw [norm_mul,Real.norm_of_nonneg (φ i).coe_nonneg]; exact mul_le_mul_of_nonneg_left (h i) (φ i).coe_nonneg

-- Gate Clock's single marginal on σ-space.
lemma ringtones (hφ : ∑ i, φ i=1) (hc : ∀ i, (V i).Calls B X t ξ s k M) (l:ℕ) (hd : (t+ξ+s)*flask B k l M ≤ δ) :
    let M:=M
    Emits.Clock (dial (fun i:Θ=> stdGaussian (Sky (I i))) φ) k l X
       (fun a:Scene I=> (V a.1).skyW B ξ t a.2) (fun a=> (V a.1).rho a.2) 0 t 1
       (fun a=> ore B k M t ξ s a.2) δ := by
  classical
  intro p
  let μ (i:Θ):=stdGaussian (Sky (I i)); let R(a : Scene I) := (V a.1).rho a.2
  have he i:=(V i).shoot_clock B (hc i) l
  refine ⟨along μ φ (fun i=> (he i).cores), along μ φ (fun i=> (he i).carries), ?_,?_,?_⟩
  · by_cases hh : Nonempty Θ
    · exact (he (Classical.arbitrary _)).rates.trans hd
    letI:IsEmpty Θ:=⟨fun i=>hh ⟨i⟩⟩; simp at hφ
  · let f (x:Scene I) := Purse.due (R x) 0 k (l+k) (ore B k M t ξ s x.2)
    have hi i : Integrable (f∘Sigma.mk i) (μ i) := (he i).charge.1
    exact ⟨bust μ φ f hi,weighed μ φ hφ f hi (fun i=> (he i).charge.2.trans hd)⟩
  let f (x:Scene I) := R x 0
  have hi i : Integrable (f∘Sigma.mk i) (μ i):=(he i).pay.1
  refine ⟨bust μ φ f hi,?_⟩
  change ‖(∫ x:Scene I,f x∂dial μ φ)-1‖ ≤ δ; rw [blend μ φ f hi]; exact delta φ hφ _ δ (fun i=> (he i).pay.2.trans hd)

section
variable (T : SectionData F) {A : Hol G} (hT : T.Sound A)
variable (Y : F.Index→Config G n→ℂ) (path:E→Config G n)

-- External rare/threshold assumption: true torus U reconstructed
-- from selected/no-hole θ, Z and queries adjoined as CurvedData. Receipt
-- refers to actual marginal `stdGaussian` **AFTER** composing with V.square,
-- so if another Gaussian implementation used must show exact transport. Seek
-- primitive U in torus coords with no φ and return any gauges coherently
-- extendable on the torus support. Common stamps ∀ x in cover, path. No
-- assuming q-model prototype for evaluation.
structure Profile (V : ∀ i,Stand (I i) E T.stencil G) (φ : Θ→ℝ≥0) (U : ∀ i, E → Sky (I i) → Config G n') (L : Side) (t ξ : ℝ) : Prop where
  grades : ∑ i,φ i=1
  runs i : i≠0 → Y i ∘ path =ᶠ[𝓝 0] (L.val:ℝ)^d • (fun y=> ∑ j:Θ,(φ j:ℝ) • (
        ∫ z:Sky (I j), (V j).rho z y • ((t^(F.grades i).2)⁻¹ •
          T.places (Place.copy F i) 0 (U j y ((V j).square y z))) ∂stdGaussian (Sky (I j))))
  charts (i : Θ) : ∀ᶠ y : E in 𝓝 0, ∀ z : Sky (I i), (V i).rho z y≠0 →
      ∃ g : Site n'→G.El, ∀ a:Spot T.stencil,
        expandAt (0:Site n') (gauge g (U i y ((V i).square y z))) (placeEdge a)=tent (t • (V i).bed ξ z y) a

variable [FiniteDimensional ℝ E]

include hT
set_option maxHeartbeats 800000 in
/-- Boot Protocol analytically. Full coarse Torus path cost if true.
Γ transition paid through Curtain Clock receipts. -/
theorem hold (V : ∀ i,Stand (I i) E T.stencil G) (φ : Θ→ℝ≥0) (U : ∀ i, E → Sky (I i) → Config G n')
    {X : E→Dev T.stencil G} {D : ℝ} (B : Roof T.stencil G) (h : Profile T Y path V φ U L t ξ)
    (hc : ∀ i, (V i).Calls B X t ξ s k M) (hD : 1 ≤ D) (hK : (t+ξ+s)*vessel B F k M ≤ δ) (hp : 1≤M) :
    Radical.Gate T L Y path X t k D δ := by
  classical
  let μ (i:Θ) := stdGaussian (Sky (I i))
  let f (a : Scene I) := (V a.1).skyW B ξ t a.2
  let r (a : Scene I) := (V a.1).rho a.2
  haveI : Nonempty Θ := by
    by_contra hh
    letI:IsEmpty Θ:=⟨fun i=>hh ⟨i⟩⟩; have h1:=h.grades; simp at h1
  have hh:=hc (Classical.arbitrary Θ)
  have ht:=hh.rate.1; have hj:=hh.noise.1; have hs:=hh.error.1
  refine ⟨Scene I,_,dial μ φ,f,r,fun x=> ore B k M t ξ s x.2,?_ ,fun i hi=>?_⟩
  · exact Eventually.of_forall (fun z=> ((hc z.1).cover _).1.1)
  intro l X'
  have hv : ∀ i':Θ, Regales (X' ∘ Sigma.mk i') (μ i') k 0 := fun i' => (V i').clocks B (hc i') _ (column_smooth T i) l
  refine ⟨Emits.Clock.radius (ringtones B V φ h.grades hc l ?_) hD, Twines.more μ φ hv, ?_⟩
  · exact (mul_le_mul_of_nonneg_left (solvent B F k i hp) (by positivity)).trans hK
  apply (h.runs i hi).trans
  choose S hS H using hv
  have hb (i) := (V i).tent_whenever B (hc i)
  filter_upwards [eventually_all.mpr h.charts,eventually_all.mpr hb,eventually_all.mpr (fun i=> (H i).room.mem_nhds (hS i))] with y hx he hz
  let a(z:Scene I):=X' z y
  suffices H: (∑ j:Θ,(φ j:ℝ) • (∫ z:Sky (I j), (V j).rho z y • ((t^l)⁻¹ •
          T.places (Place.copy F i) (0:Site n') (U j y ((V j).square y z))) ∂μ j)) =
        (∫ z:Scene I,a z∂dial μ φ) from congr_arg ((L.val:ℝ)^d • ·) H
  have hu (i : Θ) : Integrable (a ∘ Sigma.mk i) (μ i) := by
    have ht := (H i).serves (hz i) (Nat.zero_le k)
    let L := (continuousMultilinearCurryFin0 ℝ E ℂ).toContinuousLinearEquiv.toContinuousLinearMap
    exact L.integrable_comp ht
  rw [Twines.blend _ _ a hu]; refine Finset.sum_congr rfl fun j _=> congr_arg _ (integral_congr_ae ?_)
  apply Eventually.of_forall; intro z
  change (V j).rho z y • _=(V j).rho z y • ((t^l)⁻¹ • Place.column T i (t • _))
  by_cases hp : (V j).rho z y ≠ 0; swap; · simp [not_ne_iff.mp hp]
  obtain ⟨g,hg⟩:= hx j z hp
  let v:=t • (V j).bed ξ z y; let u:=U j y ((V j).square y z)
  have hj : ∀ i, G.lieExp (B.stitch v i) = tent v i := (B.supported v (he j z
    (le_of_not_gt (fun hi=> hp (((hc j).cover _).2.2 hi))))).1
  apply congr_arg ((V j).rho z y • ·); apply congr_arg ((t^l)⁻¹ • ·)
  change T.places (copy F i) 0 u = Place.column T i (t • t⁻¹ • B.stitch v)
  rw [smul_inv_smul₀ ht.ne',← T.placed_invariant hT 0 (copy F i) g u]
  apply T.cylinder_local (copy F i); intro a hA hB
  let b : Spot T.stencil:=⟨(⟨a.1,hA⟩,a.2),hB⟩
  exact (hg b).trans ((hj b).symm.trans (pore_site (B.stitch v) b).symm)
end
end YM.Planned.PrimaryIntegral295.Porous
