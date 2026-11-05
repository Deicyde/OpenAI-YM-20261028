import YM.Next.UV_STRESS.Foundation
import YM.Extra.WEAK_SCALING_ACTLAW.Orientation
import YM.UVNext.FREE_STRESS_CERTIFICATE.Choose

/-!
Leading-order actual supplier towards the X-space comparison. One common
positive length sequence going to zero, with exact filtration maps
and independent, separated Wick predictions; no coupling-power error.
`meter` at the raw stress still uses a scale factor; remove it with Ward
and finite-dimensional tensor tests below. This is not a tree/loop diagram
correlation assertion by itself.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Pert
open Function Filter Climb Org Next.UVStress Spec Table Ward
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {C : Family G} {S : Table C.book} {F : Extraction.Order} {W : DiffPlan S}
    {M : MaxwellData C} {I : IR (C:=C) S} {X : Scaling S}

structure Supplier (F : Extraction.Order) (W : DiffPlan S) (M : MaxwellData C) (I : IR (C:=C) S)
    (X : Scaling S) : Prop where
  uv : UV C F S W M I
  ider : W.Inclusions S
  deriv : W.Derivatives S
  nonzero : I.J≠0
  raw : I.J∈KernelSpace uv.basis.kernel.spin
  line : FreeDiv M.T M.hT M.lit.hers
  limit_ : Approaches (path X) (isoPanel X)
  fit : Stable uv.basis.kernel.spin M.hT.spin W M.T.W X
  meter_ : X.meter I.J M.T.J

variable (h : Supplier F W M I X)
include h

theorem all_jets (n d j : ℕ) {R : ℝ} (hR : 0<R) : X.jets n d j R :=
  comparison_jets h.uv.basis.kernel h.deriv M.hT M.lit.pales X h.limit_ n d j R hR

theorem afterTrack (n d j : ℕ) {R : ℝ} (hR : 1≤R) : ∃ k,
    Track (afterScale X k) W M.T I.J h.uv.basis.kernel.spin M.hT.spin n d j R :=
  focused_track h.uv.basis.kernel h.deriv M.hT M.T M.lit.pales X h.limit_ h.fit I.J h.meter_ n d j R hR

theorem watches {α : Type*} {l : Filter α} (v : Scaling S → ℕ → α)
    (hv : ∀ k j, v (afterScale X k) j = v X (j+k))
    (hw : Bid.Watches I.J M.T h.uv.basis.kernel.spin M.hT.spin W (fun Y => Tendsto (v Y) atTop l)) :
    Tendsto (v X) atTop l := by
  obtain ⟨d,n,j,R,hR,e⟩ := hw.ask
  obtain ⟨k, hk⟩ := afterTrack h n d j hR
  refine (tendsto_add_atTop_iff_nat k).1 ?_
  exact (e _ d n j R le_rfl le_rfl le_rfl le_rfl hk).congr (hv k)

theorem for_derivative (d : ℕ) : Bid.ConLap X W.deriv d M.T.W.deriv X.r :=
  watches h _ (fun _ _ => rfl) (Work.A04.answer h.uv.basis.kernel W h.ider h.deriv M I.J d)

theorem for_angular (d j) : Tendsto (fun i => (X.xi i)⁻¹ • (Spin.transport I.Y (X.U i d) j)) atTop
    (𝓝 (M.T.κ • Spin.leaf M.T.K.lie d j)) := by
  obtain ⟨d0,N,m,R,hR,e⟩ := (Work.A05.answer h.uv.basis.kernel W h.ider h.deriv M I.J d I.p I.Y h.uv.planet).ask
  obtain ⟨k, hk⟩ := afterTrack h N d0 m hR
  exact (tendsto_add_atTop_iff_nat k).mp ((e _ _ _ _ R le_rfl le_rfl le_rfl le_rfl hk).2 j)

theorem ratio {c : ℝ} (hc : leaves I.p 4 = c • leaves W.deriv 4) :
    c≠0 ∧ Tendsto (fun i => c / X.xi i) atTop (𝓝 M.T.κ) := by
  have hlim := watches h (l:=𝓝 M.T.κ) _ (fun _ _ => rfl)
    (Extra.WeakScaling.tracks_ratio M h.uv.basis.kernel h.ider h.deriv h.uv.planet hc)
  exact ⟨fun e => M.T.hκ (tendsto_nhds_unique (by simp only [e,zero_div] at hlim; exact hlim) tendsto_const_nhds),hlim⟩

theorem one_line : Module.finrank ℝ (LinearMap.ker (currentDiv W h.uv.basis.kernel.spin h.uv.aligned))=1 :=
  (differential_rank (ho:=h.uv.aligned) h.uv.basis.kernel M.hT M.T M.lit.hers h.line h.deriv M.lit.pales X
    h.limit_ h.fit).2

theorem centered_charges {J : S.Stress} (hc : Conserved W h.uv.basis.kernel.spin J)
    {Y : SpinRows S} (he : StressLaws S J W.deriv Y) : StressLaws S (reCenter S J) W.deriv Y := by
  let down (i j : Axis) := -expectation S 4 (J i j)
  have hid : reCenter S J = J + UVNext.FreeStress.fossil down := by
    funext i j
    change centering S 4 _ = J i j + down i j • _
    rw [value_center]; simp [down,sub_eq_add_neg]
  rw [hid]
  exact UVNext.FreeStress.add_unit h.uv.basis.kernel he down (fun i j => by dsimp [down]; rw [hc.symmetric])

theorem centered_line {J : S.Stress} (hc : Conserved W h.uv.basis.kernel.spin J)
    (ht : RawTensor h.uv.basis.kernel.spin J) {Y : SpinRows S} (he : StressLaws S J W.deriv Y) :
    ∃ c : ℝ, c • reCenter S J = I.J ∧ c≠0 ∧ leaves I.p 4 = c • leaves W.deriv 4 ∧
      Tendsto (fun i => c/X.xi i) atTop (𝓝 M.T.κ) := by
  let V : KernelSpace h.uv.basis.kernel.spin := ⟨reCenter S J,
    enters h.uv.basis.kernel _ (sym_mem.mpr ⟨hc.symmetric,hc.real,ht⟩)⟩
  have hV : currentDiv W h.uv.basis.kernel.spin h.uv.aligned V=0 := by
    apply (linear_cons _ _ _ _).2
    obtain ⟨e1,e2,e3⟩ := sym_mem.mp (kernel_mem.mp V.property).1
    refine ⟨e1,e2,fun j => ?_⟩
    change ∑ a, W.deriv 4 a (centering S 4 _) = 0
    have hd := W.unit_drop h.uv.basis.kernel.laws h.deriv h.uv.basis.kernel.smooth 4
    simp_rw [value_center,map_sub,map_smul,hd,smul_zero,sub_zero,hc.divergence j]
  let u : LinearMap.ker _ := ⟨V,hV⟩
  let v : LinearMap.ker (currentDiv W h.uv.basis.kernel.spin h.uv.aligned) :=
    ⟨⟨I.J,h.raw⟩,(linear_cons ..).2 h.uv.planet.tensor⟩
  have hn : reCenter S J≠0 := Extra.WeakScaling.flux_nontrivial h.uv.basis.kernel _ (centered_charges h hc he) (fun hw => ?_)
  · have hu : u≠0 := fun h => hn (congrArg (fun x : LinearMap.ker _ => x.val.val) h)
    obtain ⟨c,hc'⟩ := (finrank_eq_one_iff_of_nonzero' _ hu).mp (one_line h) v
    have hk : c • reCenter S J=I.J := congrArg (fun x : LinearMap.ker _ => x.val.val) hc'
    have he' := UVNext.FreeStress.scale_stress h.uv.basis.kernel (centered_charges h hc he) c
    have hsizes d : I.p d = (c • W.deriv) d := by
      have he' : StressLaws S I.J (c • W.deriv) (c • Y) := by rw [← hk]; exact he'
      funext a; apply LinearMap.ext; intro B; apply S.field_ext h.uv.basis.kernel.laws.toSymmetric; intro n q x hx
      obtain ⟨χ,hχ⟩ := Work.A01.exists_window x hx
      exact (h.uv.planet.raw.translation hx q hχ a d B).symm.trans (he'.translation hx q hχ a d B)
    have h4 : leaves I.p 4=c • leaves W.deriv 4 := by
      ext1 i; ext1 B; change I.p 4 i B=_; rw [hsizes]; rfl
    exact ⟨c,hk,(ratio h h4).1,h4,(ratio h h4).2⟩
  exfalso
  apply M.lit.born
  have hh := for_derivative h 4
  refine tendsto_nhds_unique hh ?_
  rw [hw, show leaves (S:=S) 0 4=0 from rfl]; simp
  exact tendsto_const_nhds.congr (fun k => (show (X.r k) • (0 : Climb.Vector 4 (Bel C.book)) = 0 from funext (fun j => ContinuousLinearMap.ext (fun v => show X.r k • ((0 : (Bel C.book).Field 4 →L[ℂ] (Bel C.book).Field (4+1)) v) = _ from smul_zero _))).symm)

theorem meter_physical {J : S.Stress} (hc : Conserved W h.uv.basis.kernel.spin J)
    (ht : RawTensor h.uv.basis.kernel.spin J) {Y : SpinRows S} (he : StressLaws S J W.deriv Y) (a b : Axis) :
    Tendsto (fun k => (X.U k 4).symm ((↑(X.r k ^ 4 : ℝ):ℂ) • J a b)) atTop
      (𝓝 ((M.T.κ)⁻¹ • M.T.J a b)) := by
  obtain ⟨c,hc',hC,_,hv⟩ := centered_line h hc ht he
  have ht' : Tendsto (fun k => (X.U k 4).symm ((↑(X.r k^4 : ℝ):ℂ) • reCenter S J a b)) atTop
      (𝓝 ((M.T.κ)⁻¹ • M.T.J a b)) := by
    refine ((hv.inv₀ M.T.hκ).smul (h.meter_ a b)).congr ?_; intro k
    rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),← LinearEquiv.map_smul,← hc',Pi.smul_apply,Pi.smul_apply,
      RCLike.real_smul_eq_coe_smul (K:=ℂ) c,smul_smul,smul_smul]
    congr 2
    push_cast; field_simp [hC,(X.sign k).ne']; rfl
  have hu : Tendsto (fun k => X.r k^4 * (1:ℝ)) atTop (𝓝 0) := by simpa using X.drips.pow 4
  let t := expectation S 4 (J a b)
  have ht := ((Complex.continuous_ofReal.continuousAt.tendsto.comp hu).mul_const t).smul_const ((Bel C.book).unit 4)
  rw [Function.comp_def, Complex.ofReal_zero,zero_mul,zero_smul] at ht
  have heq : J a b = reCenter S J a b + t • S.unit 4 := by
    change _ = centering _ _ _ + _; rw [value_center]; exact (sub_add_cancel _ _).symm
  have ht' := ht'.add ht; rw [add_zero] at ht'; refine ht'.congr' ((h.fit.units 4).mono ?_)
  intro k hk
  rw [heq]
  dsimp
  rw [smul_add,map_add,← hk]
  congr 1
  simp only [mul_one]
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul,map_smul,LinearEquiv.symm_apply_apply] 
  exact (smul_smul ..).symm

end YM.Pert
