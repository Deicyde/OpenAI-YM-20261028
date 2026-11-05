import YM.Next.EXTRACTION.Tails
import YM.Push.STATIONARY_UNIFORM.HessCost
import YM.Push.STATIONARY_UNIFORM.ImplicitRadius
import YM.Push.STATIONARY_UNIFORM.ScoreBounds



/-!
# A pre-L budget for actual implicit paths (RScene/RLoops)

Works on *any* continuing PathData with the Bounds ticket; does not assume
that Planting, Horizon/cross formulas give a consistent continuing choice of
Taylor arrays on BLOCK OUTPUT (separate hard problem). Doesn't even assume the
Fourier metric/ell identification. Use S-energy identities directly.

Main export `Before.graph`.

Input (besides the automatically buyable `Before`
pricing data): curvature PathData.Bounds and the usual kernel patch criteria
at this step.

`Before.full_pack` for joint analyticity, exponential tensor
and Hessian/inverse bounds on the same domains independent of all torus
volumes.

Every radius is real.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Lattice Wilson RG Precision Tree Pressure Gauge Exterior Bid
open Work.F03 Work.F04 Matrix
open Filter Function Set Metric
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} (B : Forest S.ratio) (t : S.Choices)
variable {μ C Z D Λ : ℝ} {n : ℕ} {R : PathData G} {p : Clip}
variable {x : Positions (Primary c G)} {v : Positions (Key B G)}

lemma paint_meet (x : Positions (Primary c G)) (v : Positions (Key B G)) :
    paint B G (meetVar x v)=(tint G _ x,tint G _ v) := by
  unfold paint meetVar; rw [ContinuousLinearEquiv.trans_apply,(partSpace ..).apply_symm_apply]; rfl

lemma written (x : Positions (Primary c G)) (v : Positions (Key B G)) (p : Clip) (R : PathData G) :
    priced B t p R (meetVar x v) = tested B t p R (tint G _ x) (tint G _ v) := by unfold priced; rw [Function.comp_apply,paint_meet]; rfl

lemma view_exact : (HasFDerivAt (priced B t p R ∘ meetVar x) (0:Positions (Key B G) →L[ℝ] ℝ) v) ↔
    HasFDerivAt (tested B t p R (tint G _ x)) (0 : AxisChart G B →L[ℝ] ℝ) (tint G _ v) := by
  let L := tint G B.Free
  let F := tested B t p R (tint G _ x)
  have he : priced B t p R ∘ meetVar x = F ∘ L := funext fun y => written ..
  rw [he]; change _ ↔ HasFDerivAt F _ (L v); constructor
  · intro h
    have hL : L.symm (L v)=v := L.symm_apply_apply v
    have hh := (show HasFDerivAt (F ∘ L) (0:Positions _ →L[ℝ] ℝ) (L.symm (L v)) from hL.symm ▸ h).comp
      (L v) L.symm.hasFDerivAt
    simpa [Function.comp_def] using hh
  intro h; simpa using h.comp v L.hasFDerivAt

lemma glyph (i : Key B G) : tint G _ (bolt i) = frame B i := by
  funext j
  ext k
  change bolt i (j,k) = (frame B i j) k
  by_cases he : j=i.1
  · subst j; simp [bolt,frame, EuclideanSpace.basisFun_apply, Pi.single_apply,Prod.ext_iff]
  have hi : (j,k) ≠ i := fun h => he (congr_arg Prod.fst h)
  simp [bolt,frame, hi,he]

/- constants via translation then `jets_linear` as before -/
lemma on_slice {ι τ : Type} [Fintype ι] [Fintype τ] {f : Positions (ι ⊕ τ) → ℝ} {x : Positions ι} {v : Positions τ} (k : ℕ)
    (hf : ContDiffAt ℝ ω f (meetVar x v)) :
    iteratedFDeriv ℝ k (fun y => f (meetVar x y)) v =
      (iteratedFDeriv ℝ k f (meetVar x v)).compContinuousLinearMap (fun _ => lowerCol) := by
  let A := meetVar x v
  let L := f ∘ meetVar x
  let Q (y) := f (A+y)
  have h : ContDiffAt ℝ ω Q 0 :=
    (show ContDiffAt ℝ ω f (A+(0:Positions (ι⊕τ))) by rw [add_zero]; exact hf).comp (f:=fun y => A+y) 0 (contDiffAt_const.add contDiffAt_id)
  have he := Next.Foundations.jets_linear (k:=k) (Uniform.lowerCol (τ:=τ)) (h.of_le le_top)
  rw [show iteratedFDeriv ℝ k Q 0=iteratedFDeriv ℝ k f A from by unfold Q; rw [iteratedFDeriv_comp_add_left, add_zero]] at he
  have ht : Q ∘ lowerCol = fun y => L (v+y) := by
    funext y; change f (meetVar x v+meetVar (0:Positions ι) y)=f (meetVar x (v+y)); unfold meetVar
    rw [← map_add,Prod.mk_add_mk,add_zero]
  rwa [ht,iteratedFDeriv_comp_add_left,add_zero] at he

lemma block_congr (he : ContDiffAt ℝ ω (priced B t p R) (meetVar x v)) :
    block (priced B t p R) (meetVar x v)=hessian B t p R (tint G _ x) (tint G _ v) := by
  ext i j
  let L := tint G B.Free; let F := priced B t p R; let A := meetVar x v
  let P := tested B t p R (tint G _ x)
  have ht : P ∘ L = fun y => F (meetVar x y) := funext fun y => (written ..).symm
  have hP : ContDiffAt ℝ ω P (L v) := by
    have hi : ContDiffAt ℝ ω (P ∘ L) v := by
      rw [ht]; refine he.comp (f:=meetVar x) v ?_
      exact ((partSpace (Primary c G) (Key B G)).symm.contDiff.contDiffAt).comp (f:=fun q => (x,q)) v (contDiffAt_const.prodMk contDiffAt_id)
    have hj : ContDiffAt ℝ ω (P ∘ L) (L.symm (L v)) := by simpa using hi
    have hk : ContDiffAt ℝ ω ((P ∘ L) ∘ L.symm) (L v) := hj.comp _ L.symm.contDiff.contDiffAt
    simpa [Function.comp_def] using hk
  have hh : iteratedFDeriv ℝ 2 (P ∘ L) v ![bolt i, bolt j]=hessian B t p R (tint G _ x) (tint G _ v) i j := by
    change iteratedFDeriv ℝ 2 (P ∘ L.toContinuousLinearMap) v _ = _
    rw [iter_lin_at (L:=L.toContinuousLinearMap) (hP.of_le le_top),ContinuousMultilinearMap.compContinuousLinearMap_apply]
    change iteratedFDeriv ℝ 2 P (L v) _=iteratedFDeriv ℝ 2 P (L v) _
    congr 1
    funext k; fin_cases k <;> exact glyph ..
  rw [← hh, ht,on_slice (f:=F) 2 he,ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hz := (block_hermitian he).apply i j
  rw [star_trivial] at hz
  rw [← hz]; unfold block entry; rw [Matrix.of_apply]; congr 1
  funext k; fin_cases k <;> exact (lower_bolt ..).symm

lemma block_charge (hb : R.Bounds p μ C Λ) (h : Larger (G:=G) S) (hg : Harness G S.patch.J S.kernel Z D) :
    Charge (block (priced B t p R) 0) (zeroGap S.patch S.kernel p Z D) := by
  intro v
  let L := paint B G; let F := priced B t p R; let x : Positions (Primary c G) := 0
  let H := uncurry (tested B t p R)
  have hP : ContDiffAt ℝ ω H 0 := (price_identity B t hb h.1).1
  have he : ContDiffAt ℝ ω H (L 0) := by rw [map_zero]; exact hP
  let J := lowerCol (ι:=Primary c G) (τ:=Key B G)
  have hk := iter_lin_at (L:=L.toContinuousLinearMap) (k:=2) (he.of_le le_top)
  have hh : iteratedFDeriv ℝ 2 F 0 ![J v,J v] =
      iteratedFDeriv ℝ 2 (tested B t p R 0) 0 ![tint G _ v,tint G _ v] := by
    rw [Work.F01.vertical_hessian B t (h:=fun t => (price_identity B t hb h.1).1)]
    change iteratedFDeriv ℝ 2 (H ∘ L.toContinuousLinearMap) 0 _=iteratedFDeriv ℝ 2 H _ _
    rw [hk,ContinuousMultilinearMap.compContinuousLinearMap_apply,map_zero]; congr 1
    have hp : L (J v)=(0,tint G _ v) := by
      change paint B G (meetVar x v)=_; rw [paint_meet]; simp only [x,map_zero]
    funext k; fin_cases k <;> exact hp
  let A := (fderiv ℝ (fderiv ℝ F) 0)
  have hv : v ⬝ᵥ (block F 0 *ᵥ v)=iteratedFDeriv ℝ 2 F 0 ![J v,J v] := by
    rw [iteratedFDeriv_two_apply]; change _ = A (J v) (J v)
    change _ = ((A (J v)).comp J) v
    rw [by_row]; unfold mulVec dotProduct; refine Finset.sum_congr rfl fun i _ => congr_arg (v i * ·) ?_
    let T := ((ContinuousLinearMap.apply ℝ ℝ (J (bolt i))).comp (A.comp J))
    change _= T v
    rw [by_row]; apply Finset.sum_congr rfl; intro j _
    rw [show T (bolt j)=block F 0 i j from ?_]; exact mul_comm ..
    rw [block,of_apply,entry]; unfold T; simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply]
    rw [show J (bolt j)=_ from lower_bolt j, show J (bolt i)=_ from lower_bolt i,iteratedFDeriv_two_apply]; rfl
  rw [show v ⬝ᵥ _ = _ from hv,hh,← vertical_count B v]; exact symbolic_gap B hb h hg t _

/-- Fix without knowing L, period, or the paths. -/
structure Before (G : Gauge) (μ C : ℝ) (j : ℕ) (Q : KernelChoices) (n : ℕ) where
  n_ok : 3≤n
  lc : ℝ
  Z : ℝ
  X : ℝ
  W : ℝ
  δ : ℝ
  D : ℝ
  r : ℝ
  c₁ : ℝ
  c₂ : ℝ
  exp : ExpReceipt G (n+1) lc
  labels : PaintSupply G (n+1) Z
  paid : SquarePay G n Z μ C X
  log : LogReceipt G D δ
  focus : FocusReceipt G n W r
  shell : Harness G j Q c₁ c₂

lemma pre_order (G : Gauge) (μ C : ℝ) (j : ℕ) (Q : KernelChoices) (hn : 3≤n) : Nonempty (Before G μ C j Q n) := by
  obtain ⟨lc',_,h⟩ := exp_receipt G (n+1)
  obtain ⟨Z,hZ⟩ := paint_supply G (n+1)
  obtain ⟨X,hX⟩ := square_pay G n Z μ C
  obtain ⟨W,r,_,hw⟩ := focus_receipt G n
  obtain ⟨D,δ,H⟩ := log_receipt G
  obtain ⟨u,v,hu⟩ := link_charge G j Q
  exact ⟨hn,lc',Z,X,W,δ,D,r,u,v,h,hZ,hX,H,hw,hu⟩

/-- Reification of the radii/costs to be purchased for explicit radius lemmas. -/
structure ChartPrices where
  value : ℝ -- H,cubic,quartic,...
  initial : ℝ -- open, full branch and equality-of-tests radius
  width : ℝ -- exponential rate on entries (per fine site, not coarse strip)
  gap : ℝ -- flat gap
  coords : ℕ -- per site

namespace ChartPrices
variable (V : ChartPrices)
def safety := reserveH V.coords V.value V.width V.initial V.gap
def zone := reserveV V.coords V.value V.width V.initial V.gap
def horizon := reserveX V.coords V.value V.width V.initial V.gap
def rate := tiltWidth V.coords (V.gap/2) V.width V.value
def inverse := inversePrice V.coords V.value V.width V.gap
end ChartPrices

namespace Before
variable {j : ℕ} {Q : KernelChoices} (A : Before G μ C j Q n)

def tables (p : Clip) (P : Patch) : ChartPrices where
  value := allCost G n A.Z A.X μ C A.lc A.W p P Q
  initial := paidRadius G n A.Z A.lc A.D A.δ A.r P Q
  width := weaker n (entryWidth n P.L μ)
  gap := zeroGap P Q p A.c₁ A.c₂
  coords := townCost G

lemma receipt (hp : R.Bounds p μ C Λ) (hK : Larger (G:=G) S) (hj : S.patch.J=j) (ht : S.kernel=Q) :
    let Y := A.tables p S.patch
    Receipt (address B G) Y.width n Y.coords Y.value Y.initial Y.gap (priced B t p R) ∧
      ∀ x∈ball 0 Y.initial, ∀ u, priced B u p R x=priced B t p R x := by
  subst j; subst Q
  obtain ⟨he,H⟩ := paid_ball B t hp hK.1 (le_trans (by norm_num) A.n_ok) A.labels A.paid A.exp A.log A.focus
  refine ⟨⟨town B,zeroGap_pos ..,he,?_,?_,A.n_ok,fun v hv => ⟨(H v hv).1,(H v hv).2.1⟩,block_charge B t hp hK A.shell,?_⟩,fun x hx u => ((H x hx).2.2 u).symm⟩
  · have hw := width_positive hp.width n S.patch.L; unfold tables weaker; dsimp only; positivity
  · unfold tables allCost; dsimp only; positivity
  funext i
  unfold priced Slope entry
  have ha := paint B G |>.contDiff.contDiffAt (n:=ω) (x:=0)
  obtain ⟨hh,_,h0,_⟩ := price_identity B t hp hK.1
  rw [iteratedFDeriv_one_apply, fderiv_comp _ _ (ha.differentiableAt (by simp)), map_zero,h0]
  · rfl
  rw [map_zero]; exact hh.differentiableAt (by simp)

/-- `address ∘ inr` is fine location of actual `Key`. All operator/kernels in ordinary counting
coordinates; seal along both rows and columns. Do NOT pay the whole value
of the score in a volume-independent sup→scalar norm. -/
lemma full_pack (hp : R.Bounds p μ C Λ) (hK : Larger (G:=G) S) (hj : S.patch.J=j) (ht : S.kernel=Q) :
    let Y := A.tables p S.patch
    PriceGap B p R Y.gap ∧
    0<Y.gap ∧ 0<Y.width ∧ 0<Y.initial ∧ 0<Y.value ∧ 0<Y.safety ∧ 0<Y.rate ∧
    (∀ v∈ball 0 Y.initial, ContDiffAt ℝ ω (priced B t p R) v ∧ Scatter (address B G) Y.width n (priced B t p R) v Y.value) ∧
    ∀ x : Positions (Primary c G), ∀ v : Positions (Key B G), meetVar x v ∈ closedBall 0 Y.safety →
      let L := hessian B t p R (tint G _ x) (tint G _ v)
      let l := address B G ∘ Sum.inr
      L.IsHermitian ∧ 0<L.det ∧ Charge L (Y.gap/2) ∧ Sealed l Y.width L Y.value ∧ Sealed l Y.rate L⁻¹ (Y.gap/2/2)⁻¹ ∧
      (∀ v, ‖(L⁻¹ *ᵥ v)‖ ≤ Y.inverse*‖v‖) ∧
      (∀ v : Positions (Key B G), (∑ i, ((L⁻¹ *ᵥ v) i)^2) ≤ (Y.gap/2)⁻¹^2 * ∑ i, v i^2) := by
  subst j; subst Q
  have hr := (A.receipt B t hp hK rfl rfl).1
  refine ⟨symbolic_gap B hp hK A.shell,hr.pos_m,hr.pos_a,hr.pos_r,hr.pos_C,hr.reserveH_pos,
    tiltWidth_pos _ (half_pos hr.pos_m) hr.pos_a hr.pos_C.le,hr.born,?_⟩
  intro x v hv
  have h := hr.born _ (closedBall_subset_ball hr.reserveH_lt hv)
  have hh := block_congr B t h.1
  dsimp only
  -- keep Decidable norms at predictions
  rw [← hh]
  obtain ⟨hD,he,hc⟩ := hr.priced_inverse (meetVar x v) hv
  have hg := hr.snaps _ hv
  exact ⟨block_hermitian h.1,hD,hg,block_rows h.2 (le_trans (by norm_num) A.n_ok),he,hc,hg.energy_inverse (half_pos hr.pos_m) (isUnit_iff_ne_zero.mpr hD.ne')⟩

/-- The critical function on the *actual* spaces. Sup on individual
real physical color entries (`tint.symm`) for both of these radii. `tint_inv_le`
thus ensures every TypeFace/color-vector-sup input in that same ball fits too.
Reuse THIS branch; no uniqueness promised outside zone. -/
def Service (p : Clip) (R : PathData G) (g : In G c → AxisChart G B) :=
    let Y := A.tables p S.patch
    0 < Y.horizon ∧ Y.horizon ≤ Y.zone ∧ 0 < Y.zone ∧ Y.zone ≤ Y.safety ∧ Y.safety < Y.initial ∧
      Critical B p R g ∧ ∀ x : In G c, (tint G _).symm x ∈ ball 0 Y.horizon →
        ContDiffAt ℝ ω g x ∧ ‖(tint G _).symm (g x)‖ ≤ Y.zone/2 ∧
        ∀ t : S.Choices, ∀ q : AxisChart G B, (tint G _).symm q ∈ closedBall 0 Y.zone →
          (HasFDerivAt (tested B t p R x) (0 : AxisChart G B →L[ℝ] ℝ) q ↔ q=g x)

lemma graph (hp : R.Bounds p μ C Λ) (hK : Larger (G:=G) S) (hj : S.patch.J=j) (ht : S.kernel=Q) :
    ∃ g, A.Service B p R g := by
  let Y := A.tables p S.patch
  let R₁ := Y.horizon; let R₂ := Y.zone
  let t : S.Choices := Classical.arbitrary _
  obtain ⟨hF,H⟩ := A.receipt B t hp hK hj ht
  obtain ⟨g,hg,h⟩ := hF.throughout
  let L := tint G (Body 1 c); let Z := tint G B.Free
  let f := Z ∘ g ∘ L.symm
  let s := ball (0:Positions (Primary c G)) R₁
  let T := closedBall (0:Positions (Key B G)) R₂
  have hR : 0 < R₂ := hF.reserveV_pos
  have hz : 0 < R₁ := hF.reserveX_pos
  have hs : L.symm (0:In G c)∈s := by rw [map_zero]; exact mem_ball_self hz
  have h₀ : f 0=0 := by simp [f,hg]
  have h₁ (x : In G c) (hx : L.symm x∈s) : ContDiffAt ℝ ω f x := Z.contDiff.contDiffAt.comp x
    (((h _ hx).1).comp x L.symm.contDiff.contDiffAt)
  have h₂ (x : In G c) (hx : L.symm x∈s) : ‖Z.symm (f x)‖ ≤ R₂/2 := by unfold f; simp only [Function.comp_apply, Z.symm_apply_apply]; exact (h _ hx).2.1
  have h₃ (x : In G c) (hx : L.symm x∈s) (u : S.Choices) (q : AxisChart G B) (hq : Z.symm q ∈ T) :
      HasFDerivAt (tested B u p R x) (0 : AxisChart G B →L[ℝ] ℝ) q ↔ q=f x := by
    let y := L.symm x; let v := Z.symm q
    have he : HasFDerivAt (𝕜:=ℝ) (tested B u p R x) 0 q ↔ HasFDerivAt (priced B u p R ∘ meetVar y) (0:Positions _→L[ℝ] ℝ) v := by
      have he := view_exact (p:=p) (R:=R) (x:=y) (v:=v) B u
      change _ ↔ HasFDerivAt (tested B u p R (L y)) _ (Z v) at he
      simpa only [y,v,L.apply_symm_apply,Z.apply_symm_apply] using! he.symm
    rw [he]
    have hf : meetVar y v ∈ ball 0 Y.initial := closedBall_subset_ball
      ((show Y.zone ≤ Y.safety from min_le_left ..).trans_lt hF.reserveH_lt) (Receipt.holds (K:=Y.coords) (m:=Y.gap) hx hq)
    have heq : priced B u p R ∘ meetVar y =ᶠ[𝓝 v] priced B t p R ∘ meetVar y := by
      filter_upwards [(meet_derivative y v).continuousAt.tendsto.eventually (isOpen_ball.mem_nhds hf)] with b hb
      exact H _ hb u
    refine (show HasFDerivAt (priced B u p R ∘ meetVar y) _ _ ↔ HasFDerivAt (priced B t p R ∘ meetVar y) _ _ from
      ⟨fun h => h.congr_of_eventuallyEq heq.symm, fun h => h.congr_of_eventuallyEq heq⟩).trans
      (((h y hx).2.2 v hq).trans ?_)
    change Z.symm q=g y ↔ q=Z (g y)
    rw [ContinuousLinearEquiv.symm_apply_eq]
  refine ⟨f,hz,min_le_left ..,hR,min_le_left ..,hF.reserveH_lt,⟨h₀,h₁ _ hs,fun t => ?_⟩,
    fun x hx => ⟨h₁ x hx,h₂ x hx,h₃ x hx⟩⟩
  refine ⟨(price_identity B t hp hK.1).1,?_⟩
  filter_upwards [L.symm.continuous.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds hs)] with x hx
  apply (h₃ x hx t (f x) ?_).2 rfl
  change Z.symm _∈closedBall _ _; simpa using (h₂ x hx).trans (half_lt_self hR).le
end Before
end YM.Push.Uniform
