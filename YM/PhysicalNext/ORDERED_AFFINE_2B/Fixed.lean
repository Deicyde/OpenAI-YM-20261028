import YM.Extra.MULTISOURCE_BOUNDS.Corrections
import YM.Extra.MULTISOURCE_BOUNDS.Trajectory
import YM.Extra.MULTISOURCE_TRAJECTORIES.Trials
import YM.Extra.SOURCE_HISTORIES.Issue
import YM.Extra.SOURCE_HISTORIES.Offsets
import YM.Extra.WILSON_STARTUP.Copies
import YM.Next.MAXWELL.Det
import YM.PhysicalNext.ORDERED_AFFINE_2B.Quote
import YM.Push.COMMON_WITNESSES.Fields
import YM.Push.CUTOFF_PROJECTORS.Bank
/-!
# The fixed-sector estimate: affine maps, center of the endpoint-window
# Gaussian substitution, and corrections

All quotes on the indicated SAME branch data, even as V incremented.
`b=Dᵀ F0`. `rest` below gets real covariance-error income (from
SA.Offset.Shift, differential consequences of principal window
identities); merely proving bounds on A, μ and b separately would not
establish this result. The shift is by **transpose** of the panel Pi, not
by its symmetrization C, both from the same gram. C-precision estimates
retained together for use in E Frco. This is a statement on the part of
the step existing after these post-L delays. Not new assumptions about
any not-yet-built trajectories. ; endpoint-window convention as in pinned SC.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B
open Function Filter Set Lattice Wilson RG Pressure Precision Exterior Tree
open Next Next.Fluctuations Next.SectorChange
open Push.SectorMeasure Matrix
open AnalyticBridge.SectorAffine
open scoped Topology ContDiff InnerProductSpace BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f}
namespace Fixed
section reads
variable (T : Tube G S) (x : ℝ) (A : Stores S) (F : Forest S.ratio) (k : S.Choices)
variable (V : Config G c)

abbrev D := Rows.move T x V k (shots S x) A F
abbrev precision := Rows.gram T x V k (shots S x) A F
abbrev covariance := fog A F T x V k

abbrev mismatch := (Fixed.covariance T x A F k V)⁻¹-precision T x A F k V
abbrev distortion := precision T x A F k V * Fixed.covariance T x A F k V - 1

variable (q : Chi) (d : ℝ) (Y : LinkArray G (Frozen A x F))
-- all of these marked at V LAST
abbrev zeroRow : Config G c → Prices G (Slots S) := fun U => Offset.f0 T x A F k U q d Y
abbrev forceB := Offset.b T x k A F q d Y
abbrev mean := Offset.mean T x k A F q d Y
abbrev rest := Offset.residual T x k A F q d Y

def tip : Config G c → Prices G (Slots S) := fun U =>
    D T x A F k U *ᵥ mean T x A F k q d Y U + zeroRow T x A F k q d Y U

/-- Priced by individual row (consumer sums ONLY when needed; not a
claim that a single total across the torus has a period-independent
estimate). Sign and divisor for Frco, not the masked `Rows.residual` in
the rest of sleeves. -/
def debit (g : ℝ) : Config G c → Prices G (Slots S) := fun U i => -(tip T x A F k q d Y U i)^2/(2*g^2)

abbrev eta (g : ℝ) : Config G c → Prices G (Active A x F) := fun U => -g⁻¹ • (rest T x A F k q d Y U)
end reads

variable {T : Tube G S} {x : ℝ} {A : Stores S} {F : Forest S.ratio}
    {k : S.Choices} {V : Config G c} {ε d d' s α M C a L : ℝ} {n : ℕ} {q : Chi}

/-- UNTIL reading at a V with correct flag data, these functions
of V (`Offset` maps) are smooth-extension prescriptions only. At
that base V, include the equality with all Rows APIs, for all Y. -/
def Agrees (T : Tube G S) (x : ℝ) (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (q : Chi) (ε : ℝ) (V : Config G c) :=
    ∀ Y : LinkArray G (Frozen A x F),
      let W := shots S x
      let μ := mean T x A F k q ε Y V
      zeroRow T x A F k q ε Y V = Rows.source T x V k W A F q ε Y ∧
      forceB T x A F k q ε Y V=Rows.blame T x V k W A F q ε Y ∧
      μ = meanLog A F T x V k q ε Y ∧
      tip T x A F k q ε Y V=Rows.direct T x V k W A F q ε Y μ ∧
      ∀ g : ℝ, (∑ i, debit T x A F k q ε Y g V i) = -Rows.guide T x V k W A F q ε Y μ/g^2 ∧
        eta T x A F k q ε Y g V = Rows.eta T x V k W A F q ε Y μ g

lemma fromShift (h : Offset.Shift n x d s ε M T F A V k q) : Agrees T x A F k q ε V := by
  intro Y W μ
  have he := congr_fun h.okay Y; obtain ⟨hb,hm,hη⟩ := Offset.reads_actual _ _ _ _ _ _ _ Y V he
  have hi : tip T x A F k q ε Y V=Rows.direct T x V k W A F q ε Y μ := by
    unfold Rows.direct tip zeroRow W; rw [he]
  refine ⟨he,hb,hm,hi,fun g=> ⟨?_,(hη g).symm⟩⟩
  unfold debit Rows.guide; rw [hi]; simp_rw [← Finset.sum_div]; rw [dotProduct]
  simp_rw [pow_two,Finset.sum_neg_distrib]; ring

-- Note: "μ bound" here p/o polynomial costs are retrieved by
-- Quote.authenticated. Matrix estimates for the SAME data, t⁰ at base
-- then positive normalized orders j priced with t' ^ j.
structure Fees (T : Tube G S) (x : ℝ) (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (q : Chi) (ε : ℝ)
    (V : Config G c) (n : ℕ) (s d M : ℝ) : Prop where
  real_price : Agrees T x A F k q ε V
  pd_A : (precision T x A F k V).PosDef
  pd_C : (Fixed.covariance T x A F k V).PosDef
  matrices :
    let a := Wisps.front A F (G:=G) (x:=x)
    let m := orderedCost G 1 M
    let z := M*Real.exp (-s*radiusB x)
    SelectedOrderedKernels.Book (FreeResolvent.native c) (Wisps.down S) a Prod.fst n (SelectedOrderedKernels.narrow n d) d m (D T x A F k) V ∧
    SelectedOrderedKernels.Book (FreeResolvent.native c) a a Prod.fst n (SelectedOrderedKernels.narrow n d) d m (precision T x A F k) V ∧
    SelectedOrderedKernels.Book (FreeResolvent.native c) a a Prod.fst n (SelectedOrderedKernels.narrow n d) d m (Fixed.covariance T x A F k) V ∧
    SelectedOrderedKernels.Book (FreeResolvent.native c) a a Prod.fst n (SelectedOrderedKernels.narrow n d) d (orderedCost G 1 z) (distortion T x A F k) V ∧
    SelectedOrderedKernels.Book (FreeResolvent.native c) a a Prod.fst n (SelectedOrderedKernels.narrow n d) d (orderedCost G 1 z) (mismatch T x A F k) V
  quotes (Y : LinkArray G (Frozen A x F)) :
    let a := Wisps.front A F (G:=G) (x:=x); let t := temp x
    let d' := SelectedOrderedKernels.narrow n d; let j := M*fiery G x S.patch.L; let z := j*Real.exp (-s*radiusB x)
    BundleQuote n (Wisps.down S) d' (orderedCost G t j) (zeroRow T x A F k q ε Y) V ∧
    BundleQuote n a d' (orderedCost G t j) (forceB T x A F k q ε Y) V ∧
    BundleQuote n a d' (orderedCost G t j) (mean T x A F k q ε Y) V ∧
    BundleQuote n a d' (orderedCost G t z) (rest T x A F k q ε Y) V ∧
    BundleQuote n (Wisps.down S) d' (orderedCost G t j) (tip T x A F k q ε Y) V ∧
    ∀ g : ℝ, 0 < g →
    BundleQuote n (Wisps.down S) d' (orderedCost G t (2^n*(j/g)^2/2)) (debit T x A F k q ε Y g) V ∧
    BundleQuote n a d' (orderedCost G t (z/g)) (eta T x A F k q ε Y g) V

lemma apply_at (he : Estimate n d' s a L C A F T x V k 0) (h : Offset.Shift n x d s ε M T F A V k q)
    (ha : 0<a) (hL : 0<L) (ht : 0<temp x) (ht' : temp x≤1)
    (hm : 0≤M) (hc : 0≤C) (hr : 0<α) (hr' : α + n*α ≤ d') (hv : α ≤ d) :
    Fees T x A F k q ε V n s α (1+M+C+2^n*(M*C)) := by
  let t := fiery G x S.patch.L; have ht0 : 0≤t := temp_nonneg _
  let c := 1+M+C+2^n*(M*C); let u := 2^(n:ℕ)*(M*C); have hu : 0≤u := by unfold u; positivity
  have hs : M ≤ c := by change M ≤ 1+M+C+u; linarith
  have hμ : C ≤ c := by change C ≤ 1+M+C+u; linarith
  have hj : u*t+M*t ≤ c*t := by
    rw [←add_mul]; apply mul_le_mul_of_nonneg_right _ ht0; change _ ≤ 1+M+C+u; linarith
  have hy : α≤d' := (le_add_of_nonneg_right (show 0 ≤ ↑n*α by positivity)).trans hr'
  obtain ⟨hQ,hG⟩ := he.toKernelJets.price_bounds (hr.le.trans hy) ha hL
  have heQ := hQ.pos; have heC := hG.pos
  rw [profileGram,AnalyticBridge.SectorAffine.field_zero] at heQ
  rw [pickedCov,AnalyticBridge.SectorAffine.field_zero] at heC
  let e := Real.exp (-s*radiusB x); have hx : 0≤ e := (Real.exp_pos _).le
  refine ⟨fromShift h,heQ,heC,?_,?_⟩
  · intro i m z; have hspare := mul_le_mul_of_nonneg_right hμ hx; have hf := hc.trans hμ
    exact ⟨matrix_submits (A:=D T x A F k) (V:=V) hr hf (thin he.moves le_rfl hy hμ),
      matrix_submits (A:=precision T x A F k) (V:=V) hr hf (thin he.gramJets le_rfl hy hμ),
      matrix_submits (A:=Fixed.covariance T x A F k) (V:=V) hr hf (thin he.cJets le_rfl hy hμ),
      matrix_submits (A:=distortion T x A F k) (V:=V) hr (mul_nonneg hf hx) (thin he.sJets le_rfl hy hspare),
      matrix_submits (A:=mismatch T x A F k) (V:=V) hr (mul_nonneg hf hx) (thin he.inverseGapJets le_rfl hy hspare)⟩
  intro Y a' r d'' j z
  have hf := Offset.Parcel.mono (h.corners Y) hv le_rfl
  obtain ⟨hb,hμ,hw⟩ := h.steps Y
  let a₀ := Wisps.down S (G:=G)
  have hμ' := Offset.Parcel.mono hμ hv le_rfl
  have hcost := mul_le_mul_of_nonneg_right hs ht0
  have hw' : Offset.Parcel 0 a' α n (scaled r (rest T x A F k q ε Y) V) z := Offset.Parcel.mono hw hv
    (mul_le_mul_of_nonneg_right hcost hx)
  have hZ := Offset.Parcel.mono hf le_rfl hcost
  have hDl : Offset.Parcel 0 a₀ α n (scaled r (tip T x A F k q ε Y) V) j := by
    have hh := hμ'.deliver (mul_nonneg hm ht0) (Offset.polar_compress he.moves ht.le ht') hc hr.le hy
      ((le_add_of_nonneg_left hr.le).trans hr')
    have hk := Offset.Parcel.add hh hf
    apply Offset.Parcel.mono hk le_rfl
    apply le_trans _ hj; exact le_of_eq (by unfold u t; ring)
  refine ⟨submits_bundle hZ hr ht ht',
    submits_bundle (Offset.Parcel.mono hb hv hcost) hr ht ht',submits_bundle (hμ'.mono le_rfl hcost) hr ht ht',
    submits_bundle hw' hr ht ht',submits_bundle hDl hr ht ht',fun g hg => ?_⟩
  -- price debit pointwise squares in the scaled chart BEFORE chaining to Lie jets
  constructor
  · intro i; apply submits _ hr ht ht'
    let L := ContinuousLinearMap.mul ℝ ℝ
    have h1 := Offset.Point.multiply (n:=n) L (ContinuousLinearMap.opNorm_mul_le ℝ ℝ) (hDl i) (hDl i)
    have h2 := h1.scale (- (2*g^2)⁻¹)
    -- simplify scalar action
    unfold scaled at *
    convert h2 using 1
    · ext y; unfold debit r; simp [L]; ring
    · rw [abs_neg,abs_of_nonneg (by positivity : 0≤ (2*g^2)⁻¹)]; ring
  · intro i; apply submits _ hr ht ht'
    have hg' := (hw' i).scale (-g⁻¹)
    rw [abs_neg,abs_of_nonneg (inv_pos.mpr hg).le,mul_comm,←div_eq_mul_inv] at hg'; exact hg'


/-- Standalone physical supplier on the post-L family, for all correct
flag tables and every record even if no U realizes the remaining
tests. ε is chosen as B * the fine threshold (B *constant* here, not
the growing radiusB); see the combined purchase later which uses the
same cost choice in ActualScalar's plate. No coordinates/gains for global
hard indicators claimed.
-/
theorem pricing (G : Gauge) (P : Patch) (Pt : Teller G) (hP : P.Branches Pt.bind G) (B : ℝ) (hB : 0<B) (q : Chi) (n : ℕ) :
    ∃ s d M : ℝ, 0<s ∧ 0<d ∧ 0<M ∧ ∀ᶠ x : ℝ in atTop, 120 ≤ radiusB x ∧ 0<temp x ∧ temp x ≤ 1 ∧
      temp x ≤ 2*fiery G x P.L ∧ ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P →
        100*(1+radiusB x) ≤ c.val → Pt.Funds S T → ∀ (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (V : Config G c),
        V∈ eligible A G x → Fees T x A F k q (B*fiery G x S.patch.L) V n s d M := by
  obtain ⟨r,d,d',s,M,N,a,L,hr,hd,hd',hs,hM,hN,ha,hL,h⟩ := Offset.prices G P Pt B hB q n hP
  let u := min d (d'/(1+(n:ℝ))); have hu : 0<u := lt_min hd (div_pos hd' (by positivity))
  have hv : u+(n:ℝ)*u ≤ d' := by
    have ht : u*(1+(n:ℝ)) ≤ d' := (le_div_iff₀ (by positivity : (0:ℝ) < 1 + (n:ℝ))).mp (min_le_right d _)
    linarith only [ht]
  refine ⟨s,u,1+M+N+2^n*(M*N),hs,hu,by positivity,?_⟩
  filter_upwards [h,monitors G P.L] with x hx hh
  refine ⟨hx.1,hh.1,hh.2.1,hh.2.2,fun S T hp hR hT A F k V hk => ?_⟩
  obtain ⟨he,h⟩ := hx.2 S T hp hR hT A F V hk k
  exact apply_at (he 0 (by simpa using hr.le)) h ha hL hh.1 hh.2.1 hM.le hN.le hu hv (min_le_left ..)

end Fixed
end YM.PhysicalNext.OrderedAffine2B
