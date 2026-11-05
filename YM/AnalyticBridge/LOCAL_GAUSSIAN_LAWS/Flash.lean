import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Curving
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.HeadSwitch
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.NearDelay
import YM.Extra.ITERATION_NO_LOSS.Continuity




/-!
# Releasing curvature prices on a remotely cleared patch

Addresses can be recut anywhere by expenditure of the exp part (but
NOT assuming the cut after is H-covariant). Same H/T/path and F/tag
in every exchange. Gap premises delivered side-by-side from real
Funds on actual flags. Menu works with arbitrary temperatures at that
step, after the cost of THIS passage; final chartConsumer will delay
hatted schedules if needed--not asserting this of every old wait.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws.Remote
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Motion Rows Push.SectorMeasure Presented Pressure.Stores Gaussian Tree Wisps Bid
open Assembly Current FreeResolvent
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G : Gauge} {c f : Side}

/-- On this gait supplies comparison to *uncut* Pcond for all tested
$d_1$ covariance entries from the *actual sector* at the chosen
V gauge. This identifies the centered Gaussian *matrices* once
using the licenses (Gauged.stays proves exact relation of the ordered
and sym kernels to those before applying z globally; NOT simply identity
on these charged fibers). Free clocks here apply even to all periods,
including main comparison to flat (we don't use a finite other patch's
Gram). No assumptions that the mean is near the free mean. No Z/J
here. Compare against the curled law of the provided common free
data--actual conditional expression even when successive Beds agree.
$η$ priced *for both prescribed fields and all U*, simultaneous, x
is the actual step parameter. -/
theorem released (G : Gauge) (P : Patch) (Pt : Teller G) (hp : P.Branches Pt.bind G) (s C : ℝ) (hs : 0<s) (hC : 0≤C) :
    ∃ Y η K σ E : ℝ, 0<Y ∧ 0<η ∧ 0<K ∧ 0<σ ∧ 0<E ∧ ∀ᶠ x : ℝ in atTop,
    120 ≤ radiusB x ∧ ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Pt.Funds S T →
    Larger (G:=G) S → 100*(1+radiusB x) ≤ c.val → ∀ Λ, T.up.Bounds T.high s C Λ →
    ∀ (U : Stores S) (o : Site c), Clears U x o (radiusB x) → ∀ V : Config G c, U.flags=RG.flags (temp x) V →
    ∃ z : Site c→G.El, (∀ i : Bond c, separation o i.1≤radiusB x → G.chord (Lattice.gauge z V i)≤clearanceFare x) ∧ Remote.paid S (replica S.ratio (Lattice.gauge z V)) o (radiusB x) (clearanceFare x) ∧ ∀ (F : Forest S.ratio) (g : Geometry) (k : S.Choices),
    let W Q := pane (sectorW G S x U F g) (Rows.gram T x Q k (shots S x) U F) 0
    let u := bareStores S
    let B := pane (sectorW G S x u F g) (Rows.gram T x 1 k (shots S x) u F) 0
    let Q := Lattice.gauge z V
    (∀ i j : In x U F (G:=G), separation o (front U F j) ≤ radiusB x/2+1 → |W Q i j-B (official U F i) (official U F j)|≤x^(-(1/4):ℝ)) ∧
    ∀ (H L : Bed) (τ : Towers S.patch.L) (a m N M : ℝ) (p : Clip), 0<a → 0<m →
    Floor H T.high f a M → Floor L p c m N → Attached H T.up → Towers.Diagonal S H L τ → Sworn H f G →
      let X := opened G S x u F (bare_is_Clear S x F)
      let ideal := tensor G (fConditional S H L τ)
      FreeResolvent.Gap (treeMatrix G S F H.metric) η ∧ FreePrice (native c) (theta S.ratio F) (treeMatrix G S F H.metric) (B.submatrix X X) σ K (K*Real.exp (-E*radiusB x)) Y ∧
      ∃ A : ℝ, A=(curlTariff G P 0)^2*(K+1) ∧ ∀ i j : tileP (G:=G) (f:=f),
        separation o (seat S 2 i) ≤ radiusB x/2 → separation o (seat S 2 j) ≤ radiusB x/2 →
        |rainbow U F x (W Q) i j-ideal i j| ≤ A*x^(-(1/4):ℝ) := by
  let K:=Pt.bind; let p:=Pt.top.clip
  obtain ⟨A,δ,hA,hδ,H⟩ := chip_repair G P K p C hp hC
  obtain ⟨w,η,B,r,t,hw,hB,hr,ht,hη,he⟩ := freeHead G P K p hs hC
  obtain ⟨Ω,hΩ,hh⟩ := Next.SectorChange.Gap.not_flat G P Pt hp
  obtain ⟨D,hD,hM⟩ := Next.SectorChange.Gap.stood G P Pt
  have HB : 0<B := zero_lt_one.trans_le hB
  refine ⟨r,η,B,w,t,hr,hη,HB,hw,ht,?_⟩
  filter_upwards [he,hh,Work.E01.radiusB_tendsto.eventually_ge_atTop 200,small_span P,
    fares G P A hA (η:=Ω) (H:=D) hΩ hD hδ,Extra.Iteration.Scales.first t (1/4) ht] with x he hh hX hv hyd heB
  let d := radiusB x
  have hX : 200≤d := hX
  have h0 : d/2+1+boxCharge x+span P x+span P x≤d := by unfold boxCharge; unfold d at hX ⊢; omega
  refine ⟨by omega,?_⟩
  intro c f S T hP hp' hS hV Λ hT U o hu V hx
  have hK : S.kernel=K := hp'.knobs
  have hL : T.high = p := hp'.high
  obtain ⟨z,he',hz⟩ := axial S U V o hu hV hx
  refine ⟨z,he',hz,fun F g k => ?_⟩
  intro W u B' Q
  have h : FreeResolvent.Gap (Rows.gram T x Q k (shots S x) U F) Ω := ⟨hh S T hP hV hp' U F k Q (by rw [hx]; simp [Q])⟩
  have hW : FreeResolvent.Gap (Rows.gram T x (1:Config G c) k (shots S x) u F) D := ⟨hM S T hP (by rw [← hP]; exact hS.2.1) (by omega) hp' x u F k⟩
  rw [hL] at hT
  let M:= x^(-(1/4):ℝ)
  have hV (i j : In (G:=G) x U F) (hj : separation o (front U F j) ≤ d/2+1) : |W Q i j-B' (official U F i) (official U F j)|≤ M := by
    apply (H _ hyd.1 hyd.2.1 S hP hK T _ _ hL hT x o d _ (by omega) hz k U F g Ω D 0 hΩ hD le_rfl hu h hW i j (by omega)).trans
    rw [census_clock,hP]; exact hyd.2.2
  refine ⟨hV, fun H L τ a m N M' p' ha hm hH hL' ht' hJ hsw => ?_⟩
  intro X Z
  rw [← hL] at hT
  obtain ⟨g₀,hH'⟩ := he.2 S T hP hK hS hL Λ (hL ▸ hT) F k u g (bare_is_Clear S x F) H ht' (hL ▸ hH.roots) hsw
  let w' := B*Real.exp (-t*d); have hw' : 0≤w' := by unfold w'; positivity
  have hm' : 0 ≤ M := (Real.exp_pos _).le.trans heB
  refine ⟨g₀,hH', (curlTariff G P 0)^2*(B+1),rfl,fun i j hi hj => ?_⟩
  have H0 := curlize U F x o d (d/2) hu (by omega) (W Q) B' M hm' hV i j hi hj
  let F0:=plane (G:=G) S F
  let R:=treeInverse G S F H.metric 0
  let I:=mirror (B'.submatrix X X)
  let Y := F0*I*F0.transpose; have HZ : Z=F0*R*F0.transpose := (cutHead S F H hS hH ha τ hL' hm hJ).symm
  let v:=curlTariff G S.patch 0
  have hl : (native c).Schur (seat S 2 (G:=G)) (seat S 2 (G:=G)) 0 (v*w'*v) (Y-Z) := by
    rw [HZ]; unfold Y; rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    apply plane_bill _ _ _ le_rfl hw'
    have hr : R=(treeMatrix G S F H.metric)⁻¹ := by unfold R treeInverse resolve; rw [zero_smul,add_zero]
    rw [hr]
    exact hH'.cov.mono hw.le le_rfl
  have hx : |Y i j-Z i j| ≤ v*w'*v := by simpa only [Cost.weight_zero,one_mul, Matrix.sub_apply] using hl.rows.weighted i j
  let W0 := rainbow U F x (W Q)
  change |W0 i j - _| ≤ _
  rw [show W0 i j-Z i j=(W0 i j-Y i j)+(Y i j-Z i j) by ring]
  apply (abs_add_le ..).trans ((add_le_add H0 hx).trans ?_)
  change v^2*M+v*w'*v ≤ _
  have hg : w' ≤ B*M := mul_le_mul_of_nonneg_left heB HB.le
  rw [← hP]
  calc
    _ = v^2*(M+w') := by ring
    _ ≤ v^2*(M+B*M) := by gcongr
    _ = _ := by unfold v M; ring
end YM.AnalyticBridge.LocalGaussianLaws.Remote
