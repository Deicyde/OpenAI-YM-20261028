import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Panels
import YM.Push.FREE_RESOLVENT.Atlas
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Chosen

/-!
# Nonlinear V jets at the prescription of Gaussian sector change

No deleting rows even when forming an inverse only in a panel. Costs on the
actual covariance `fog` (including positive lower bounds) not inferred from
formal A alone without estimating the actual sizes about these SAME windows.

Parameter identification:
  V is a true coarse configuration, `A.flags` is the complete stored
  `RG.flags (temp x)` for V; x is coarse hatted beta used in this step
  and determines all these cuts (`radiusB x`). Sector holds this *one*
  allocation record's fields fixed, in particular *all* costs, flags,
  aisles, k/tag choices, F forest/trunks, x and Tube. D and Fog don't depend
  on the values of Y (full frozen Haar links). Prices even in a uniform
  real sup-coordinate neighborhood of each such V, where the derivatives
  are on the UNMASKED functions of B, even if off `actualFlags`. No Legendre or
  logarithmic changes of field measure in these estimates. The `assembly`
  theorem doesn't even require the particular Directed data.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.SectorAffine

open Filter Function Set Lattice Wilson RG Precision Pressure Tree Exterior
open YM.Next.Fluctuations YM.Next.SectorChange
open YM.Next.SectorChange.Rows YM.Next.SectorChange.Wisps YM.Next.SectorChange.Schur
open YM.Push.Uniform (bolt)
open YM.FreeResolvent (Mark Bundle native)
open YM.FreeResolvent.TestD Matrix
open scoped Topology ContDiff BigOperators InnerProductSpace Classical Matrix.Norms.Frobenius

variable {G : Gauge} {P : Patch} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S} {x σ η d M : ℝ}

abbrev pickedPi (A : Stores S) (F : Forest S.ratio) (T : Tube G S) (x : ℝ)
    (V : Config G c) (k : S.Choices) (u : ℝ) (B : PriceCoords G c) :=
  panelPi (panels A F) (profileGram T x V A F k B) u
abbrev pickedDeficit (A : Stores S) (F : Forest S.ratio) (T : Tube G S) (x : ℝ)
    (V : Config G c) (k : S.Choices) (u : ℝ) (B : PriceCoords G c) :=
  panelError (panels A F) (profileGram T x V A F k B) u
abbrev pickedCov (A : Stores S) (F : Forest S.ratio) (T : Tube G S) (x : ℝ)
    (V : Config G c) (k : S.Choices) (B : PriceCoords G c) := fog A F T x (field V B) k

lemma picked_sym (A : Stores S) (F : Forest S.ratio) (T : Tube G S) (x : ℝ)
    (V : Config G c) (k : S.Choices) (B : PriceCoords G c) :
    let P := pickedPi A F T x V k 0 B
    pickedCov A F T x V k B = (1/2:ℝ) • (P + P.transpose) := by
  unfold pickedCov pickedPi fog clouded panelPi profileGram
  simp only [zero_smul,add_zero]

lemma shift_zero {ι : Type} [Fintype ι] [DecidableEq ι] {E : Type} [NormedAddCommGroup E] (Q : E → Matrix ι ι ℝ) :
    action Q 0 = fun x => (Q x)⁻¹ := by
  funext x
  change (Q x + (0:ℝ) • 1)⁻¹ = _
  simp only [zero_smul,add_zero]

lemma assembled_price {k : ℕ} {A : Stores S} {t : S.Choices} {B : PriceCoords G c} {V : Config G c}
    (hp : Polar B (Wisps.front A F) (Wisps.front A F) (pickedPi A F T x V t 0) k d M) :
    Polar B (Wisps.front A F) (Wisps.front A F) (pickedCov A F T x V t) k d M := by
  have he := (hp.one_add hp.transpose).scale (1/2:ℝ)
  rw [show pickedCov A F T x V t=_ from funext (picked_sym A F T x V t)]
  rw [abs_of_nonneg (by norm_num), show (1/2:ℝ)*(M+M)=M from by ring] at he
  exact he

lemma assembled_error {k : ℕ} {A : Stores S} {t : S.Choices} {B : PriceCoords G c} {V : Config G c}
    (hp : Polar B (Wisps.front A F) (Wisps.front A F)
      (pickedPi A F T x V t 0-action (profileGram T x V A F t) 0) k d M) :
    Polar B (Wisps.front A F) (Wisps.front A F)
      (pickedCov A F T x V t-action (profileGram T x V A F t) 0) k d M := by
  have he := (hp.one_add hp.transpose).scale (1/2:ℝ)
  rw [abs_of_nonneg (by norm_num), show (1/2:ℝ)*(M+M)=M from by ring] at he
  refine he.glue (Eventually.of_forall (fun y => ?_))
  simp only [Pi.sub_apply,shift_zero,picked_sym]
  let Q := profileGram T x V A F t y
  let W := pickedPi A F T x V t 0 y
  have h : Q.IsSymm := by unfold Q profileGram Rows.gram Matrix.IsSymm; rw [Matrix.transpose_mul,Matrix.transpose_transpose]
  change (1/2:ℝ) • ((W-Q⁻¹)+(W-Q⁻¹)ᵀ)=(1/2:ℝ) • (W+Wᵀ)-Q⁻¹
  rw [Matrix.transpose_sub,h.inv.eq]
  ext i j
  simp only [Matrix.transpose_apply,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply, smul_eq_mul]; ring

/-- `η` for Q, `lower` for actual C. n arbitrary finite. Every `Polar`
contains neighborhood smoothness `ContDiffAt` and absolute row and column
budgets per component, with exponential position bills
*in each external V location*, in addition to kernel decay between output and
input indices. `v` is the decay rate in the exponentially small errors. Use
at `d,v,η,lower>0` as purchased below; `drain u=(1+u)⁻¹`. -/
structure KernelJets (n : ℕ) (d v η lower M : ℝ) (A : Stores S) (F : Forest S.ratio)
    (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices) (B : PriceCoords G c) : Prop where
  moveAnalytic : ContDiffAt ℝ ω (profileD T x V A F k) B
  moves : Polar B (Wisps.down S) (Wisps.front A F) (profileD T x V A F k) n d M
  gramJets : Polar B (Wisps.front A F) (Wisps.front A F) (profileGram T x V A F k) n d M
  cJets : Polar B (Wisps.front A F) (Wisps.front A F) (pickedCov A F T x V k) n d M
  solvency : YM.FreeResolvent.Gap (profileGram T x V A F k B) η
  covSanction : YM.FreeResolvent.Gap (pickedCov A F T x V k B) lower
  covPosDef : (pickedCov A F T x V k B).PosDef
  principalJets (I : Set (Rows.In x A F (G:=G))) :
    ∀ u : ℝ, 0≤u → ResolventJets (Wisps.front A F ∘ (Subtype.val : I → _)) B n d M u
      (action (limitTo (profileGram T x V A F k) (Subtype.val : I → _)) u)
  globalJets : ∀ u : ℝ, 0≤u → ResolventJets (Wisps.front A F) B n d M u
    (action (profileGram T x V A F k) u)
  windowJets : ∀ u : ℝ, 0≤u → ResolventJets (Wisps.front A F) B n d M u (pickedPi A F T x V k u)
  deficitJets : ∀ u : ℝ, 0≤u → Polar B (Wisps.front A F) (Wisps.front A F) (pickedDeficit A F T x V k u)
    n d (M*Real.exp (-v*radiusB x)*drain u)
  closenessJets : ∀ u : ℝ, 0≤u → Polar B (Wisps.front A F) (Wisps.front A F)
    (pickedPi A F T x V k u-action (profileGram T x V A F k) u) n d
    (M*Real.exp (-v*radiusB x)*drain u^2)

namespace KernelJets
variable {k : ℕ} {v l : ℝ} {V : Config G c} {A : Stores S} {B : PriceCoords G c} {t : S.Choices}

lemma costs (H : KernelJets k d v η l M A F T x V t B) {M' d' : ℝ} (hm : M≤M') (hd : d' ≤ d) :
    KernelJets k d' v η l M' A F T x V t B :=
  { moveAnalytic := H.moveAnalytic
    moves := thin H.moves le_rfl hd hm
    gramJets := thin H.gramJets le_rfl hd hm
    cJets := thin H.cJets le_rfl hd hm
    solvency := H.solvency
    covSanction := H.covSanction
    covPosDef := H.covPosDef
    principalJets := fun I u hu => (H.principalJets I u hu).weaker le_rfl hm hd hu
    globalJets := fun u hu => (H.globalJets u hu).weaker le_rfl hm hd hu
    windowJets := fun u hu => (H.windowJets u hu).weaker le_rfl hm hd hu
    deficitJets := fun u hu => thin (H.deficitJets u hu) le_rfl hd (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le) (drain_pos hu).le)
    closenessJets := fun u hu => thin (H.closenessJets u hu) le_rfl hd (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le) (sq_nonneg _)) }

lemma covarianceJets (H : KernelJets k d v η l M A F T x V t B) :
    Polar B (Wisps.front A F) (Wisps.front A F)
      (pickedCov A F T x V t - fun y => (profileGram T x V A F t y)⁻¹) k d
      (M*Real.exp (-v*radiusB x)) := by
  have hx := H.closenessJets 0 le_rfl
  simp only [show drain 0=1 by simp [drain],one_pow,mul_one] at hx
  rw [← shift_zero]; exact assembled_error hx
end KernelJets


/-- Actual selected-sector source object with all inverses and prices.
Use `KernelJets` projections with the existential positive prices.
Threshold imposed uniformly. No purchase of a real Directed or claim of
physical realizability of the S,N labels. -/
theorem assembly (G : Gauge) (P : Patch) (Pt : Teller G) (hk : P.Branches Pt.bind G) (n : ℕ) :
    ∃ r d v η l M : ℝ, 0<r ∧ 0<d ∧ 0<v ∧ 0<η ∧ 0<l ∧ 0<M ∧
    ∀ᶠ x : ℝ in atTop, 120 ≤ radiusB x ∧ ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P →
    100*(1+radiusB x) ≤ c.val → Pt.Funds S T → ∀ (A : Stores S) (F : Forest S.ratio) (V : Config G c),
    A.flags=RG.flags (temp x) V → ∀ (k : S.Choices) (B : PriceCoords G c), ‖B‖≤r →
      KernelJets n d v η l M A F T x V k B := by
  obtain ⟨r,s,M,η,hr,hs,hM,hη,H⟩ := precision G P Pt hk n
  let d := room s M η n
  have hd : 0<d := (room_grid hs hM.le hη n).1
  let W := priceFiber P G d
  have hW : 0<W := priceFiber_pos ..
  have hp : Price s M η d 1 W 1 n := ⟨hη,hM.le,hs,rfl,le_rfl,hW.le,zero_le_one,le_rfl⟩
  have hc := room_small hp
  let M₀ := meter n n M 1 (rise W η); have hm₀ : 0 ≤ M₀ := hp.meter_abs
  let M₁ := FreeResolvent.tagPrice 1 n M (W*M₀); have hm₁ : 0 ≤ M₁ := by unfold M₁ FreeResolvent.tagPrice; positivity
  let M₂ := FreeResolvent.tagPrice 1 n M₀ M₁; have hm₂ : 0 ≤ M₂ := by unfold M₂ FreeResolvent.tagPrice; positivity
  let C := M+M₀+W*M₀+M₁+M₂; have hW₀ : 0 ≤ W*M₀ := mul_nonneg hW.le hm₀
  have he : M ≤ C := by unfold C; linarith only [hW₀,hm₀,hm₁,hm₂]
  have he₀ : M₀ ≤ C := by unfold C; linarith only [hW₀,hM,hm₁,hm₂]
  have heW : W*M₀ ≤ C := by unfold C; linarith only [hm₀,hM,hm₁,hm₂]
  have he₁ : M₁ ≤ C := by unfold C; linarith only [hm₀,hM,hW₀,hm₂]
  have he₂ : M₂ ≤ C := by unfold C; linarith only [hm₀,hM,hW₀,hm₁]
  obtain ⟨e₁,e₂,g,-,-,hl,hg⟩ := Schur.windows hs hη hM.le (priceFiber P G) (fun _ => (priceFiber_pos ..).le)
  have ht : Tendsto (fun x => radiusB x / 60) atTop atTop := by
    refine Filter.tendsto_atTop.mpr fun i => ?_
    filter_upwards [YM.Work.E01.radiusB_tendsto.eventually_ge_atTop (60*i)] with x hx; omega
  let v := d/120; have hv : 0<v := by unfold v; positivity
  refine ⟨r,d,v,η,g,C,hr,hd,hv,hη,hl,hM.trans_le he,?_⟩
  filter_upwards [ht.eventually hg,H,YM.Work.E01.radiusB_tendsto.eventually_ge_atTop 120] with x hy hx hz
  refine ⟨hz,?_⟩
  intro c f S T hP hs' hT A F V hA k B hB
  obtain ⟨ha,hD,_,hQ,hw,-⟩ := hx S T hP hs' hT A F V hA k B hB
  let a := Wisps.front A F (G:=G) (x:=x)
  have ha' : Revenue a (priceFiber P G) := by
    intro d hd i
    rw [← hP]; exact (fiber_volume S G hd A F x).1.bound i
  let Q := profileGram T x V A F k
  let R := radiusB x/60
  let t := panels (G:=G) (x:=x) A F
  have hb : Bars t a R := boards A F G hz
  have hs : (native c).Volume a d W := ⟨ha' d hd⟩
  obtain ⟨_,hv',hp'⟩ := hy a (Q B) t ha' (priced_pour (polar_schur hQ) hM.le) (by
      unfold Q profileGram Rows.gram Matrix.IsSymm; rw [transpose_mul,transpose_transpose]) (funded_gap hw) hb
  have h (u : ℝ) (hu : 0 ≤ u) := panel_price hb hu hQ hp hs hw
  have hu (u : ℝ) (hu : 0 ≤ u) := ((h u hu).1).weaker (Nat.le_refl n) heW (show d ≤ d from le_rfl) hu
  let L := Real.exp (-((n+1:ℕ):ℝ)*d*R)
  let Y := Real.exp (-v*radiusB x)
  have hr : L ≤ Y := by
    have hN : radiusB x ≤ 120*R := by unfold R; omega
    have hj : (radiusB x:ℝ) ≤ 120*(R:ℝ) := by exact_mod_cast hN
    apply Real.exp_monotone
    unfold v; push_cast
    nlinarith only [mul_le_mul_of_nonneg_left hj hd.le,
      mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hd.le) (Nat.cast_nonneg R)]
  refine { moveAnalytic := ha, moves := thin hD le_rfl hc he, gramJets := thin hQ le_rfl hc he,
           solvency := hw, cJets := assembled_price ?_, covSanction := fund_gap hv', covPosDef := hp',
           principalJets := fun I u hj => (cost_window hj hQ hp hs hw (Subtype.val : I → _) Subtype.val_injective).weaker le_rfl he₀ le_rfl hj,
           globalJets := fun u hj => (cost_full hj hQ hp hs hw).weaker le_rfl he₀ le_rfl hj,
           windowJets := hu, deficitJets := fun u hj => ?_, closenessJets := fun u hj => ?_ }
  · have hf := (hu 0 le_rfl).polar (hM.le.trans he) le_rfl
    rw [show drain 0=1 by simp [drain],mul_one] at hf; exact hf
  · refine thin (h u hj).2.1 le_rfl le_rfl (mul_le_mul_of_nonneg_right ?_ (drain_pos hj).le)
    exact mul_le_mul he₁ hr (Real.exp_pos _).le (hM.le.trans he)
  refine thin (h u hj).2.2 le_rfl le_rfl (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
  exact mul_le_mul he₂ hr (Real.exp_pos _).le (hM.le.trans he)
end YM.AnalyticBridge.SectorAffine
