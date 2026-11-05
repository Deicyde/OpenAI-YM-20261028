import YM.AnalyticNext.CUBIC_MATCH.Region.Placement
import YM.Next.BOUNDARY.Coordinates
import YM.Next.EXTRACTION.Tails
import YM.Next.FREE_KERNELS.Amend
import YM.Next.SCHEDULE.Blocks
import YM.Next.SCHEDULE.Post



set_option warningAsError false

/-!
# The scaling pays for path phases

Coarse units width θ, fine lengths in the true cover EVEN for long winding
paths. Read at a native fine offset v at cost a coarse phase at
most `exp (θ * (4 + size v / L))` for positioning (length ℓ1). Evaluate using actual real counting
stencils. Signed channels below pay also at most two shifted endpoints in
this expression. No clipping, every torus. Scale receipt tests translations,
cover wraps and first differences simultaneously across tori.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch
open Function Filter Lattice Laurent RG Wilson Precision Exterior Tree Tensor Bid Bloch Matrix
open Next.Free Work.F08
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {k : ℕ} {μ : Type*} {η θ C B : ℝ} {n L : Side}

/-- `μ`, the small parameter. -/
def tilt (L : Side) := (L.val:ℝ)⁻¹
lemma tilt_pos : 0 < tilt L := by unfold tilt; positivity


/-- Real overshoot a step in `reachOf` pays translating the local read. -/
def phaseCost (L : Side) (θ : ℝ) (s : ℕ) := Real.exp (θ*tilt L*s)
lemma phase_pos (L : Side) (θ : ℝ) (s : ℕ) : 0 < phaseCost L θ s := Real.exp_pos _
lemma phase_mono (hp : 0≤θ) {L : Side} {x y : ℕ} (h : x ≤ y) : phaseCost L θ x ≤ phaseCost L θ y :=
  Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast h) (mul_nonneg hp tilt_pos.le))


lemma phase_length (L : Side) (θ : ℝ) (s : ℕ) : phaseCost L θ (s*L.val)=Real.exp (θ*s) := by
  unfold phaseCost tilt; congr 1; push_cast; field_simp





lemma size_unit (a : Axis) : size (step a:Cover)=1 := by
  unfold size; rw [Finset.sum_eq_single a]
  · simp
  · intro j _ h; simp [h]
  simp
lemma size_reverse_step (a : Axis) : size (-(step a):Cover)=1 := by rw [size_neg,size_unit]
lemma size_native (s : Step) : size (s.vec:Cover)=1 := by unfold Step.vec; split <;> simp only [size_unit,size_reverse_step]



variable {c f : μ → Side}

/-- Have same block parity across these real tori. In top case c=f
and one residue; doesn't make a StepData at L=1. -/
def between (h : ∀ i : μ,(f i).val=(c i).val*L.val) (p : μ) : Ratio (c p) (f p) := ⟨L,h p⟩

abbrev ShiftRoot (c f : μ → Side) := ∀ p, Site (c p) → Site (f p)

/-- Fine link-scale profiles paid at rate θ. Anchor relative to (c p) site i.
`root` in application embeds that site, modulo orientation rotation. -/
structure ScaleRead (c f : μ → Side) (L : Side) (root : ShiftRoot c f) (V : ∀ p, Dir G (c p) → Dir G (f p)) (θ C : ℝ) : Prop where
  rate : 0<θ
  fee : 0≤C
  link (v : Cover) (j : TypeFace 1) : LocalRep c 1 θ (C*tilt L*phaseCost L θ (size v))
    (fun p i a => V p a (wrap (f p) v+root p i,j))
  gain (v : Cover) (w : Axis) (j : TypeFace 1) : LocalRep c 1 θ (C*tilt L^2*phaseCost L θ (size v))
    (fun p i a => V p a ((wrap (f p) v+root p i)+step w,j) - V p a (wrap (f p) v+root p i,j))

lemma one_address (he : 0<θ) (x : TypeFace 1) : LocalRep c 1 θ (Fintype.card G.ColorIndex:ℝ) (fun p i (a : Dir G (c p)) => a (i,x)) := by
  let b := EuclideanSpace.basisFun G.ColorIndex ℝ
  let f (k : G.ColorIndex) : SiteRead G c G.Color := fun p i a => a (i,x) k • b k
  have h (k) : LocalRep c 1 θ 1 (f k) := by
    let u := tapEquivOne G (0,x,k)
    let K := fun a => if a=u then b k else 0
    refine ⟨he,zero_le_one,K,fun i => ?_,fun p t a => ?_⟩
    · by_cases hi : i=u
      · rw [hi]; simp only [K,u,if_true,b,OrthonormalBasis.norm_eq_one,reaches_one]; simp [wanes,size]
      rw [show K i=0 from if_neg hi,norm_zero,one_mul]; exact (wanes_pos ..).le
    unfold receive; rw [tsum_eq_single u]; swap; · intro y hy; rw [show K y=0 from if_neg hy,smul_zero]
    simp only [K,if_true,verse,Fin.prod_univ_succ,Finset.univ_eq_empty,Finset.prod_empty,mul_one]; unfold toneOf
    change _ = a (wrap (c p) 0+t,x) k • b k; rw [map_zero,zero_add]
  have hh := LocalRep.allFin he h
  rw [mul_one] at hh; exact hh.fits fun p i v => (show ∑ k,f k p i v=_ from b.sum_repr _)




end YM.CubicMatch
