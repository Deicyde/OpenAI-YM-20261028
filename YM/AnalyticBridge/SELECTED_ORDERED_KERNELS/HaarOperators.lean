import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.AuthorizedLoans
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Currency

/-!
Will NOT give logarithm/Jacobian/likelihood or dominated differentiation
of the Haar-coordinate density from this theorem alone. (Same bona fide
μ & C, bounds on the velocities etc are needed in that task.) Here C_I
is an actual marginal of the endpoint SectorChange Gaussian, not an
entry of a full inverse mistaken for an inverse of a marginal. Prices can
be used also with held Haar args; require an extent R to get an unweighted
ℓ²-operator bound. Derivatives are true ordered derivatives normalized on
coarse V by an output BudgetPoint's order-growth convention; after delay
of both thresholds. No dropping components of `tape`. No assuming a scene
schedule already supplies this request, or `Baking`/`Iteration` data or
extending their estimates to non-real flags. Includes non-small V with the
correct sector data (not a displacement neighborhood uniform across L).
-/
set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.Sector
open Lattice Wilson RG Precision Exterior Tree Function Filter Topology Next.SectorChange Set WardBin.Lies
  YM.Pressure YM.Pressure.Stores FreeResolvent Affine TestD Window Mark Matrix Rows Schur Wisps
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {H : Tube G S} {T : Forest S.ratio} {r s M N Y d δ g x Y' : ℝ}
  {q n : ℕ} {A : Stores S} {k : S.Choices} {V : Config G c}
  {ι : Type} [Fintype ι] [DecidableEq ι]

def eddy (H : Tube G S) (x : ℝ) (A : Stores S) (T : Forest S.ratio) (k : S.Choices) (e : ι → In (G:=G) x A T) : Config G c → Matrix ι ι ℝ :=
  limitTo (covariance H x A T k) e

lemma eddy_is (e : ι → In (G:=G) x A T) : marginal H x A T k e 0 = fun V => (eddy H x A T k e V)⁻¹ := resolver_zero _

def covFee (G : Gauge) (q j : ℕ) (M r Y : ℝ) := surcharge G j * (Y*count q M Y r)
def invFee (G : Gauge) (q j : ℕ) (M r Y g Y' : ℝ) := surcharge G j * cost q (Y*count q M Y r) Y' g 0 j

abbrev kernelTax (G : Gauge) (q j P R : ℕ) (d t K : ℝ) := tender G j P (narrow q d/2) t K * ((1+(R:ℝ))^P)^j

structure KernelOp (q : ℕ) (t d : ℝ) (a : ι → Site c) (m : ℕ → ℝ) (F : Config G c → Matrix ι ι ℝ) (V : Config G c) : Prop where
  smooth : WardBin.Lies.Germ q (euclid F) V
  ordered_price (l : List (Directions G c)) : l.length ≤ q → ∀ (p : BudgetPoint) (o : Site c) (R : ℕ), p.threshold ≤ 2*t →
    (∀ B ∈ l, p.dirBound o B) → (∀ i, separation (a i) o ≤ R) →
    ‖leftDerivs (euclid F) l V‖ ≤ kernelTax G q l.length p.power R d t (m l.length)

structure MarginalInputs (H : Tube G S) (x : ℝ) (A : Stores S) (T : Forest S.ratio) (k : S.Choices) (V : Config G c)
    (q : ℕ) (d M δ r Y g Y' : ℝ) : Prop where
  scale : temp x ≤ 2 * fiery G x S.patch.L
  priced : Loans H x A T k V q M d r Y δ g Y'
  ops {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι → In (G:=G) x A T) : Injective e →
    let t := fiery G x S.patch.L
    let F := eddy H x A T k e
    FreeResolvent.Gap (F V) g ∧ FreeResolvent.Gap (F V)⁻¹ (g/(1+covFee G q 0 M r Y)^2) ∧
      KernelOp q t d (front A T ∘ e) (fun j => covFee G q j M r Y) F V ∧
      KernelOp q t δ (front A T ∘ e) (fun j => invFee G q j M r Y g Y') (marginal H x A T k e 0) V

lemma kernelOp_of {F : Config G c → Matrix ι ι ℝ} {a : ι → Site c} {m : ℕ→ℝ} {t γ : ℝ} (h : Book (native c) a a Prod.fst q (narrow q d) γ m F V)
    (hd : 0 < d) (hg : 0 ≤ γ) : KernelOp q t d a m F V := by
  refine ⟨?_, fun l hl p o R he hB hr => h.operator l hl he (narrow_pos q hd) hB hg R hr⟩
  exact ((Matrix.toEuclideanCLM (n:=ι) (𝕜:=ℝ)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.contDiff.contDiffAt.comp _ h.smooth : _)

lemma buys_inputs (hg : 0 < g) (hA : Ground H x A T k V s N r g) (h : Loans H x A T k V q M d r Y δ g Y')
    (hV : temp x ≤ 2 * fiery G x S.patch.L) : MarginalInputs H x A T k V q d M δ r Y g Y' := by
  refine ⟨hV,h,?_⟩
  intro ι _ _ e he t F
  have hF := h.C.part he
  have hI := h.slices e he 0 le_rfl
  have hd := h.d_pos; have hδ := h.δ_pos
  have hG := hA.cloud_gap.submatrix e he; have ht := hF.nonneg 0 (Nat.zero_le _)
  exact ⟨hG, op_gap hG hg (by unfold covFee; linarith only [ht]) ((pours_op hF.zeroth (by positivity)).trans (by unfold covFee; linarith)),
    kernelOp_of hF hd (by positivity),kernelOp_of hI hδ (by positivity)⟩

theorem haar_operators (G : Gauge) (P : Patch) (Pt : Teller G) (hp : P.Branches Pt.bind G) (q : ℕ) :
    ∃ r g d M Y δ Y' : ℝ, 0<r ∧ 0<g ∧ 0<d ∧ 0<δ ∧ 0≤M ∧ 0≤Y ∧ 0≤Y' ∧ ∀ᶠ x in atTop, ∀ {c f : Side} (S : StepData c f) (H : Tube G S), S.patch=P →
    100*(1+radiusB x) ≤ c.val → Pt.Funds S H → ∀ (A : Stores S) (T : Forest S.ratio) (k:S.Choices) (V : Config G c), A.flags=RG.flags (temp x) V →
    MarginalInputs H x A T k V q d M δ r Y g Y' := by
  obtain ⟨s,N,r,g,hs,hN,hr,hg,h⟩ := Selected.authorized_loans G P Pt hp
  obtain ⟨t,K,ht,hK,hq⟩ := h q
  have p := plan (q:=q) (lt_min ht hs) (hN.trans (le_max_left N K)) hr P G
  have p' := plan (q:=q) p.pos (mul_nonneg p.vol (count_nn p)) hg P G
  refine ⟨r,g,_,_,_,_,_,hr,hg,p.pos,p'.pos,p.m,p.vol,p'.vol,?_⟩
  filter_upwards [hq,Work.E07.temp_coarse_le G P.L] with x hx hy
  intro c f S H hS hR hT A T k V hV; obtain ⟨h,-,h'⟩ := hx S H hS hR hT A T k V hV
  unfold Query at h'; rw [hS] at h'
  exact buys_inputs hg h h' (hS ▸ hy)
end YM.SelectedOrderedKernels.Sector
