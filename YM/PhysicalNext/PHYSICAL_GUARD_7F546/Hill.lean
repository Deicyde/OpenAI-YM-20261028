import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Hop
import YM.Extra.ITERATION_NO_LOSS.Radius
import YM.PhysicalNext.PHYSICAL_GUARD_7F546.Reads


/-!
# Purchase the weighted price on exactly the physical hill

Keep the `Teller.Funds` and both sides' actual bounds and compatibility.
Replay the purchase from `Local.hill` retaining more of the receipts. In
particular don't call two independent theorems choosing v. After the one
choice of z,v, BOTH actual covariances have uniform (x-independent) entry
bounds, and the same v pays the standardized mean on all tested coordinates.
Keep also the original Workshop likelihood/contrast conclusion.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PhysicalGuard7f546
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Motion Rows Push.SectorMeasure Presented Pressure.Stores Gaussian Tree Wisps Bid
open YM.AnalyticBridge.LocalGaussianLaws Assembly Current FreeResolvent Remote Lift Extra.Iteration.Scales MeasureTheory Density Local
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {x R U : ℝ} {A : Stores S} {T : Tube G S}
    {H : Bed} {o : Site c} {V : Config G c}

/-- Expend *at* these physical data. `z` gauge, `v` log extension.
Freeze both before any probe. The release even lets us freeze before F.
Calls to the polynomial estimates on this price still pay for the degree
and number of read coordinates (not their distinct sites). All fine and
coarse data of the constructions are retained, not clipped e.g. to the
size of the read set.
-/
def WeightedAt (x R U : ℝ) {S : StepData c f} (A : Stores S) (T : Tube G S) (H : Bed)
    (o : Site c) (V : Config G c) (z : Site c → G.El) (v : Dir G c) : Prop :=
    let V' := Lattice.gauge z V
    A.flags = RG.flags (temp x) V' ∧
    (∀ i : Bond c, separation o i.1 ≤ radiusB x → G.chord (V' i) ≤ clearanceFare x) ∧
    Remote.paid S (replica S.ratio V') o (radiusB x) (clearanceFare x) ∧
    (AgreeNear id o (radiusB x) V' (represent v) ∧ ‖v‖ ≤ R * clearanceFare x) ∧
    ∀ (F : Forest S.ratio),
    let J := treeInverse G S F H.metric 0
    let b := portrait_head T F v
    J.PosDef ∧ ∀ (k : S.Choices) (q : Chi) (d : ℝ) (s : Geometry) (Y : LinkArray G (Frozen A x F)),
      let a := portrait T A F k x V' s q d Y
      let Q := palette T A F k x V' s
      Q.PosDef ∧ ∀ (I : Type) [Fintype I] [DecidableEq I] (e : I ↪ In x A F (G:=G)),
        lives I F A o (radiusB x/4) e → ∀ β : ℝ, 0 < β → β ≤ 3*x →
          let g := coupling β
          let l := e.trans (loadLink A F x)
          ReadPrice Q J a b g e l x U ∧
          -- keep the exact bounded-test consumer (and its log price in ReadPrice)
          ∀ (f : (I → ℝ) → ℝ) (W : ℝ), Measurable f → (∀ y, |f y| ≤ W) →
            let C := Q.submatrix e e
            let B := J.submatrix l l
            let u := g⁻¹ • (b ∘ l - a ∘ e)
            let X := ∫ z, f ((a + g • z) ∘ e) ∂cloud Q
            X = (∫ z, Density.replace C B u z * f (b ∘ l + g • z) ∂cloud B) ∧
              |X - (∫ z, f ((b + g • z) ∘ l) ∂cloud J)| ≤ W * x^(-(1/16):ℝ)

theorem WeightedAt.keeps {z v} (h : WeightedAt x R U A T H o V z v) : Workshop x R A T H o V := by
  intro F
  obtain ⟨-, -, -, h, H'⟩ := h
  refine ⟨z,v,h,?_⟩
  intro J b
  obtain ⟨hj,hF⟩ := H' F
  refine ⟨hj, fun k q d s Y => ?_⟩
  intro a Q
  obtain ⟨hp,he⟩ := hF k q d s Y
  refine ⟨hp, fun I _ _ e hi β hβ hl => ?_⟩
  obtain ⟨hc,hg⟩ := he I e hi β hβ hl
  intro g N P l C B u
  refine ⟨fun y => ?_,fun L W hL hW => hg L W hL hW⟩
  rw [show u = -displacement a b g e l from (against ..).symm]
  exact hc.paid.workshopLog y

set_option maxHeartbeats 600000 in
/-- The x threshold is chosen before S/period/the actual beds etc. as
in `Local.hill`. Thus can in particular take this after fixing K, D
and any price bounds in the calling family. Constant entry bounds (not
`room x`) purchased in the same order, enabling uniform absolute moments.
There is no hidden dependence on a previous choice of F, gauge, flags,
frozen Y, etc. -/
theorem purchase (G : Gauge) (P : Patch) (Pt : Teller G) (hp : P.Branches Pt.bind G) :
    ∃ R U : ℝ, 1 ≤ R ∧ 1 ≤ U ∧ ∀ᶠ x in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Pt.Funds S T →
    ∀ (H L : Bed) (a m D V : ℝ), 0<a → 0<m → Floor H T.high f a V → Floor L T.low c m D →
      Attached H T.up → Attached L T.down → Sworn H f G → Sworn L c G →
      Towers.Diagonal S H L T.R → Towers.Roll S H L T.R T.high T.low →
      Larger (G:=G) S → 100*(1+radiusB x)≤c.val →
    ∀ (A : Stores S) (o : Site c), Clears A x o (radiusB x) →
      ∀ V : Config G c, A.flags=RG.flags (temp x) V →
      ∃ z v, WeightedAt x R U A T H o V z v := by
  obtain ⟨Y,η,K,σ,E,hY,hη,hK,hσ,hE,H⟩ := Remote.released G P Pt hp
    Pt.top.width Pt.top.paths Pt.top.width_pos Pt.top.paths_pos.le
  obtain ⟨p,s,M,C,E',g1,hp',hs,hM,hC,hE',hg1,H'⟩ := AnalyticBridge.LocalGaussianLaws.quote G P Pt hp
  obtain ⟨R,hR,hZ⟩ := Lift.mean_shot G P Pt hp
  let q := η/(K+1)^2
  have hq : 0<q := by unfold q; positivity
  let U := max C η⁻¹
  have hU : 1 ≤ U := hC.trans (le_max_left ..)
  refine ⟨R, U, hR, hU, ?_⟩
  filter_upwards [hZ, H', H, Local.limited G P (show 0≤(1:ℝ) from zero_le_one),
    Local.limited G P (zero_le_one.trans hC), Local.limited G P (inv_pos.mpr hg1).le,
    Local.limited G P (inv_pos.mpr hq).le, Local.limited G P (inv_pos.mpr hη).le,
    Extra.Iteration.Scales.first E (1/4) hE, powers (1+K) (by positivity)]
    with x hv hQ hx hA hC0 he1 hκ h₃ he0 hek
  let T0 := room x
  let B₀ := x^(-(1/4):ℝ)
  let t := x^(-(1/8):ℝ)
  obtain ⟨hx0,hx1,hA',huβ,hg⟩ := hek
  have hx_one : 1 ≤ x := by linarith
  have he : 0<x := by linarith
  have hx2 : 0≤B₀ := by unfold B₀; positivity
  have hT0 : 0≤t := by unfold t; positivity
  intro c f S T hP hh H₁ H₂ lo m N M0 hu hm hH hH' hw ht HV HW Hc Hr hS hT A o hV V hb
  obtain ⟨D,W,hD,hW⟩ := hh.feeds
  rw [← hh.high] at hD
  obtain ⟨z,HZ,HW',h_cov⟩ := hx.2 S T hP hh hS hT D hD A o hV V hb
  let V' := Lattice.gauge z V
  have hB : A.flags=RG.flags (temp x) V' := by unfold V'; rw [gauge_flags,hb]
  obtain ⟨v,hv',he_mean⟩ := hv S T hP ⟨hh,H₁,H₂,lo,M0,m,N,hH,hH',hw,ht,HV,HW,Hc,Hr⟩ hT A o hV
    V' hB HZ HW'
  refine ⟨z,v,hB,HZ,HW',hv',?_⟩
  intro F J b
  let Q0 := treeMatrix G S F H₁.metric
  have hX : FreeResolvent.Gap Q0 (treeFare G S.patch S.kernel lo) :=
    tree_gap S F _ hS hu ⟨fun i => (hH.uniform.1 i).1⟩
  have hHQ : Q0.PosDef := by
    refine gap_positive (Matrix.IsSymm.submatrix ?_ _) hX (treeFare_pos G S.patch S.kernel hu)
    exact FreeResolvent.full_symmetric _ hH.symmetric.1
  have h_inv : J=Q0⁻¹ := by unfold J treeInverse resolve; rw [zero_smul,add_zero]
  have hj : J.PosDef := h_inv.symm ▸ hHQ.inv
  refine ⟨hj, fun k χ d u y => ?_⟩
  intro a X
  obtain ⟨Hi,Hc'⟩ := hQ.2 S T hP hT hh A F k V' hB
  have hL : Closes (native c) (front A F) (Rows.gram T x V' k (shots S x) A F)
      (sectorW G S x A F u) s M p C (E' * Real.exp (-s * radiusB x)) g1 := by
    cases u
    · exact Hi
    · exact Hc'
  obtain ⟨Ha,HY⟩ := h_cov F u k
  let A' := bareStores S
  let r := opened G S x A' F (bare_is_Clear S x F)
  let ν := panoramic T A' F k x 1 u
  obtain ⟨hk,hF,_⟩ := HY H₁ H₂ T.R lo m N M0 T.low hu hm hH hH' hw Hc HV
  have Hflat : (native c).Schur (theta S.ratio F) (theta S.ratio F) σ (K * Real.exp (-E * radiusB x))
      (mirror (ν.submatrix r r)-J) := by erw [h_inv]; exact hF.cov
  have hXpos : X.PosDef := hL.cloud
  -- HERE in the two genuine, full covariances
  have hCurv (i j : In x A F (G:=G)) : |X i j| ≤ C :=
    Local.entry (show (native c).Schur (front A F) (front A F) _ _ X from hL.compares.1) hs.le i j
  have hR0 : FreeResolvent.Gap J q := by
    rw [h_inv]
    exact flipped_gap hη hk hK.le (hF.pays.mono hσ.le le_rfl)
  have he_inv : ∀ i j, |J i j| ≤ η⁻¹ := by
    rw [h_inv]
    exact hk.point hη (Q0.mul_nonsing_inv (hk.unit_det hη))
  refine ⟨hXpos, fun I H1 H2 e₀ hi β hβ hI => ?_⟩
  intro g l
  let n : ℝ := Fintype.card I
  have hC1 (k : ℝ) (h : 0≤k) (HP : slotCount G S (radiusB x/4)*k ≤ T0) : n*k ≤ T0 :=
    (mul_le_mul_of_nonneg_right (reach o (D:=radiusB x/4) e₀ hi) h).trans HP
  have hc : n ≤ T0 := by simpa using hC1 1 zero_le_one (hA S hP)
  obtain ⟨h_work,Hwork⟩ := hA' n (Nat.cast_nonneg _) hc
  have hw (i : I) : |g⁻¹*(b (l i)-a (e₀ i))| ≤ t := by
    obtain ⟨HX,HK⟩ := he_mean F k χ d y (e₀ i) (hi i) u
    rw [← HX] at HK
    rw [abs_mul,abs_of_nonneg (inv_pos.mpr (coupling_pos hβ)).le,abs_sub_comm]
    exact (mul_le_mul_of_nonneg_left
      (show |a (e₀ i)-b (l i)| ≤ x^(-(7/8):ℝ) from HK)
      (inv_pos.mpr (coupling_pos hβ)).le).trans (hg β hβ hI)
  -- license the bounded Workshop / log price with these *same* choices
  let C' := X.submatrix e₀ e₀
  let B' := J.submatrix l l
  let pos := front A F ∘ (e₀:I → In x A F (G:=G))
  have hPrices :
      let u' := (native c).Schur pos pos 0 T0
      u' C' ∧ u' C'⁻¹ ∧ u' B' ∧ u' B'⁻¹ ∧ (native c).Schur pos pos 0 t (C'-B') := by
    intro u'
    obtain ⟨-,hQ,hN⟩ := affordable (D:=native c) e₀ hg1 hL.gap_cov (zero_le_one.trans hx1)
      hXpos hCurv (zero_le_one.trans hC) pos (hC1 C (zero_le_one.trans hC) (hC0 S hP))
      (hC1 g1⁻¹ (inv_pos.mpr hg1).le (he1 S hP))
    obtain ⟨-,hQ0,hN0⟩ := affordable (D:=native c) l hq hR0 (zero_le_one.trans hx1)
      hj he_inv (inv_pos.mpr hη).le pos (hC1 η⁻¹ (inv_pos.mpr hη).le (h₃ S hP))
      (hC1 q⁻¹ (inv_pos.mpr hq).le (hκ S hP))
    refine ⟨hQ,hN,hQ0,hN0,cheaply (mul_nonneg (by positivity : 0≤1+K) hx2) ?_ h_work⟩
    intro i j
    let Y' := mirror (ν.submatrix r r)
    let M' := panoramic T A F k x V' u
    let i' := l i
    let j' := l j
    have hp1 : |X (e₀ i) (e₀ j)-Y' i' j'| ≤ B₀ := by
      have hi' (p o' : I) : |M' (e₀ p) (e₀ o')-ν (r (l p)) (r (l o'))| ≤ B₀ :=
        Ha _ _ ((hi o').trans (by omega))
      change |(1/2:ℝ)*(M' (e₀ i) (e₀ j)+M' (e₀ j) (e₀ i))-1/2*(ν (r i') (r j')+ν (r j') (r i'))| ≤ _
      apply Eq.trans_le _ (half_keep (hi' i j) (hi' j i)); congr 1; unfold i' j'; ring
    have hp2 : |Y' i' j'-J i' j'| ≤ K*B₀ := (Local.entry Hflat hσ.le i' j').trans
      (mul_le_mul_of_nonneg_left he0 hK.le)
    change |X (e₀ i) (e₀ j)-J i' j'| ≤ _
    rw [show X (e₀ i) (e₀ j)-J i' j'=X (e₀ i) (e₀ j)-Y' i' j'+(Y' i' j'-J i' j') by ring]
    exact (abs_add_le ..).trans ((add_le_add hp1 hp2).trans_eq (by ring))
  have hsBill := Local.stress X J a b g (coupling_pos hβ).ne' e₀ l hXpos hj
    hT0 hx1 huβ hw pos hPrices Hwork
  -- now retain the flat uniform bound as well for polynomial uses
  refine ⟨⟨hXpos, hj, coupling_pos hβ, hx_one, hU, hXpos.submatrix e₀.injective,
    hj.submatrix l.injective, fun i j => (hCurv _ _).trans (le_max_left ..),
    fun i j => (he_inv _ _).trans (le_max_right ..), ?_, ?_⟩, fun f C hf hm => hsBill.2 f hf C hm⟩
  · intro i
    have he : |(-displacement a b g e₀ l) i| ≤ t := by rw [against]; exact hw i
    rwa [Pi.neg_apply, abs_neg] at he
  intro w P
  rw [against]
  exact hsBill.1 w

end YM.PhysicalNext.PhysicalGuard7f546
