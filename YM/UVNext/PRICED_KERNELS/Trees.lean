import YM.Push.PRICE_COMPILER.Authors
import YM.UVNext.PRICED_KERNELS.Echo
import YM.UVNext.PRICED_KERNELS.Strolling



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Pre-L actual tree corrected stationary rows

Use Annuity at fixed-root, including integralLink
along ANY forest's walk choices. No correction arrays yet. Repaired towers on
Permit, but go even to any periodic test of those at the right ratio. The price
in L^-1 of A0 means can afford BOTH tree hikes and fixRoot against it without
changing width and without unbounded cost in realized output (same within-stage
ask). No payment via decreases of width on each invocation. These are statements
about the actual matrix rows. Orientation & path-lift tags elsewhere; paths are
read HERE literally on the torus step/hike. All per-period claims include tree
angles. Does not license changing any subsequent nonlinear forecasts post-L.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PricedKernels
open Filter Set Function Lattice RG Precision Pressure Laurent Exterior Bloch Matrix Tree
open Push.PriceCompiler
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {c f : Side} {S : StepData c f}

/-- Optional separate geometry check: use parent estimate on all sides. -/
lemma embed_parent (g : Ratio c f) (x : Site f) : (separation x (g.embed (g.parent x)):ℝ) ≤ g.count.val := by
  have hx := Next.Free.scaled_dist g x (g.parent x)
  have hL := (show 0<(g.count.val:ℝ) from Nat.cast_pos.mpr g.count.property)
  simpa using (div_le_iff₀ hL).mp hx

section straight
variable (S : StepData c f) (s : ℝ) (hs : 0 ≤ s)

/-- Factorization of straighten. Use `form` physical index `vac` selectors
actual duplicated for every fine start, storing the hike suppliers and fixRoot.
-/
def rootAt (g : Ratio c f) : Matrix (Body 0 f) (Body 0 c) ℝ := LinearMap.toMatrix'
    (LinearMap.pi fun i : Body 0 f => LinearMap.proj (R:=ℝ) (φ:=fun _ => ℝ) (g.parent i.1,vac))

def hiker (F : Forest S.ratio) : Matrix (Body 0 f) (Body 1 f) ℝ := LinearMap.toMatrix'
    (LinearMap.pi fun i : Body 0 f => integralLink i.1 (F.hike i.1))

lemma factor_tree (F : Forest S.ratio) (A : Matrix (Body 1 f) (Body 1 c) ℝ) :
    straighten S F A=(hiker S F-rootAt S.ratio*fixRoot S)*A := by
  -- applying to arbitrary v
  apply Matrix.toLin'.injective
  apply LinearMap.ext; intro v; funext i
  change (straighten S F A *ᵥ v) i = (((hiker S F-rootAt S.ratio * fixRoot S)*A)*ᵥ v) i
  simp only [books,← Matrix.mulVec_mulVec,Matrix.sub_mulVec, hiker,rootAt,LinearMap.toMatrix'_mulVec]; rfl

include hs
lemma rootAt_paid : Annuity (site f _) (parent S.ratio _) (rootAt S.ratio) (tollFine S s) (Real.exp s) := by
  apply Annuity.earned; intro i v hv
  rw [rootAt, LinearMap.toMatrix'_mulVec]; change |v _| ≤ _
  have he := hv (S.ratio.parent i.1,vac)
  refine he.trans (Real.exp_monotone ?_)
  have hx := embed_parent S.ratio i.1
  let L := (S.patch.L.val:ℝ)
  have hL : 0 < L := Nat.cast_pos.mpr S.patch.L.property
  calc
    _ ≤ s/L*L := mul_le_mul_of_nonneg_left hx (div_nonneg hs hL.le)
    _ ≤ s := (div_mul_cancel₀ _ hL.ne').le

lemma hiker_paid (F : Forest S.ratio) : Annuity (site f _) (site f _) (hiker S F) (tollFine S s) (4*S.patch.L.val*Real.exp (4*s)) := by
  let L := (S.patch.L.val:ℝ)
  have hL : 0<L := Nat.cast_pos.mpr S.patch.L.property
  apply Annuity.earned; intro i v hv
  rw [hiker, LinearMap.toMatrix'_mulVec]
  have he := walk_receipt (tollFine S s) (div_nonneg hs hL.le) v i.1 hv i.1 (F.hike i.1)
  have hh{y : Site f} : ((F.hike y).length:ℝ) ≤ 4*L := by
    unfold L; exact_mod_cast (show (F.hike y).length≤4*S.patch.L.val from (F.hike_lower y).trans (F.bound y))
  have hx : tollFine S s*(0+((F.hike i.1).length:ℝ)) ≤ 4*s := by rw [zero_add]; calc
      _ ≤ s/L*(4*L) := mul_le_mul_of_nonneg_left hh (div_nonneg hs hL.le)
      _ ≤ _ := (show s/L*(4*L)=_ by field_simp).le
  refine he.trans (mul_le_mul hh (Real.exp_monotone ?_) (Real.exp_pos _).le (by positivity))
  simpa using hx

/-- Reserve for gradients; `delta_budget` already at *any* positive
fixed width in Laurent coordinates. -/
def dC (k : ℕ) (t : ℝ) := Fintype.card (TypeFace k)*(Next.Free.delta_budget k t).choose
omit hs in
lemma dC_nonneg (k : ℕ) (s : ℝ) : 0 ≤ dC k s := by unfold dC; have := (Next.Free.delta_budget k s).choose_spec.1; positivity

omit hs in
lemma delta_paid (n : Side) (k : ℕ) (s : ℝ) (h : 0 ≤ s) : Annuity (site n _) (site n _) (d k n) s (dC k s) :=
    Annuity.paid_site ((Next.Free.delta_budget k s).choose_spec.2) h n
lemma delta_fine (k : ℕ) : Annuity (site f _) (site f _) (d k f) (tollFine S s) (dC k s) := by
  refine (delta_paid f k s hs).cut ?_ le_rfl
  exact div_le_self hs (Nat.one_le_cast.mpr S.patch.L.property)


def hikeC (J : ℕ) (s : ℝ) := 4*Real.exp (4*s)+Real.exp s * (2*stepC J s)
omit hs in
lemma hikeC_pos (J : ℕ) (s : ℝ) : 0<hikeC J s := by unfold hikeC; have := stepC_pos J s; positivity

lemma straight_price (F : Forest S.ratio) (A : Matrix (Body 1 f) (Body 1 c) ℝ) (C : ℝ) (hC : 0 ≤ C)
    (he : Annuity (site f _) (parent S.ratio _) A (tollFine S s) (C/S.patch.L.val)) :
    Annuity (site f _) (parent S.ratio _) (straighten S F A) (tollFine S s) (hikeC S.patch.J s*C) := by
  have hh := stepC_pos S.patch.J s
  have hL := (show 0<(S.patch.L.val:ℝ) from Nat.cast_pos.mpr S.patch.L.property)
  have ht : 0 ≤ tollFine S s := div_nonneg hs hL.le
  rw [factor_tree]
  apply (((hiker_paid S s hs F).minus ((rootAt_paid S s hs).times (fix_price S s hs) ht (by positivity))).times he ht
    (div_nonneg hC hL.le)).cut le_rfl
  unfold hikeC; exact le_of_eq (by field_simp)
lemma extract_price (F : Forest S.ratio) (A : Matrix (Body 1 f) (Body 1 c) ℝ) (C : ℝ) (hC : 0 ≤ C)
    (he : Annuity (site f _) (parent S.ratio _) A (tollFine S s) (C/S.patch.L.val)) :
    Annuity (site f _) (parent S.ratio _) (extracted S F A) (tollFine S s) ((1+dC 0 s*hikeC S.patch.J s)*C) := by
  have hh : 0 ≤ hikeC S.patch.J s*C := mul_nonneg (hikeC_pos ..).le hC
  have hl : (1:ℝ) ≤ S.patch.L.val := Nat.one_le_cast.mpr S.patch.L.property
  have ht : 0 ≤ tollFine S s := div_nonneg hs (by linarith)
  apply ( (he.cut le_rfl (div_le_self hC hl)).plus ((delta_fine S s hs 0).times (straight_price S s hs F A C hC he) ht hh)).cut le_rfl
  exact le_of_eq (by ring)


end straight
end YM.UVNext.PricedKernels
