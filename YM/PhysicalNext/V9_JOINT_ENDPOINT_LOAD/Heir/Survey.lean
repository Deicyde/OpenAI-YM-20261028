import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Abroad
import YM.Planned.ATOM_REGULAR_ESTIMATE.CrossEffect
import YM.Progress.STATIONARY_SCENES.Frames

/-!
# Bare predictor model in whole Direction normalization

No sector-replacement or cost of a likelihood asserted; source term used is
Offset's smooth extension. Pane inverse and selection are of the ENDPOINT
system. This price requires a globally small link chart and a *completely
bare* sector, initially only on a comparison torus. Next test local reads
and buy a separate first-order improvement and actual V anchor comparisons.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Lattice Wilson Pressure Precision RG Tree Matrix Next.SectorChange
    Next.SectorChange.Rows Schur Wisps AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
    AnalyticBridge.SectorAffine.Offset FreeResolvent.TestD Exterior Push.SectorMeasure
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {n m : ℕ}

abbrev clear (S : StepData c f) (x : ℝ) (F : Forest S.ratio) := Active (bareStores S) x F
abbrev bareD (T : Tube G S) (x : ℝ) (F : Forest S.ratio) (k : S.Choices) := profileD T x (1:Config G c) (bareStores S) F k
abbrev barePi (T : Tube G S) (x : ℝ) (F : Forest S.ratio) (k : S.Choices) := pickedPi (bareStores S) F T x (1:Config G c) k 0
abbrev pencil (T : Tube G S) (F : Forest S.ratio) (x : ℝ) (k : S.Choices) (u : PriceCoords G c) := (bareD T x F k u).transpose *ᵥ ink T F x k u
def school (T : Tube G S) (F : Forest S.ratio) (x : ℝ) (k : S.Choices) (u : PriceCoords G c) : Prices G (clear S x F) :=
  -(barePi T x F k u).transpose *ᵥ pencil T F x k u

section equality
variable {P : Teller G} (hT : P.Funds S T) (F : Forest S.ratio) (x : ℝ) (k : S.Choices) (q : Chi) (d : ℝ)
    (Y : LinkArray G (Frozen (bareStores S) x F)) (u : PriceCoords G c)
include hT in
lemma school_eq : school T F x k u = Offset.mean T x k (bareStores S) F q d Y (field 1 u) := by
  let U := field 1 u
  have he : Rows.input x (bareStores S) F (autoShell q d U Y)=0 := by
    funext i; unfold Rows.input; split
    next hi => rw [dif_neg (notChilled S F x _)]; rfl
    rfl
  obtain ⟨a,b,hh,-⟩ := hT.feeds
  have hv : bump T x U k (0: Directions G f)=0 := by
    rw [show (0:Directions G f)=(0:ℝ) • (0:Directions G f) from (zero_smul ..).symm, Rows.bump_smul _ _ _ _ hh,zero_smul]
  unfold Offset.mean Offset.b Offset.f0
  rw [he,hv,add_zero]; unfold school barePi pickedPi panelPi; rw [zero_smul,add_zero]
end equality

section excursion
variable {I J : Type} [Fintype I] [Fintype J] {B : PriceCoords G c} {a : I → Site c} {b : J → Site c}
    {d σ v η l K M : ℝ} {k : S.Choices}
private lemma polar_shift {Q : PriceCoords G c → Matrix I J ℝ} (h : Polar B a b Q n d K) : Polar (G:=G) 0 a b (fun y => Q (B+y)) n d K := by
  refine ⟨(show ContDiffAt ℝ n Q (B+0) by rw [add_zero]; exact h.smooth).comp (f:=fun y => B+y) 0 (contDiffAt_const.add contDiffAt_id),fun t ht => ?_⟩
  unfold jet; rw [iteratedFDeriv_comp_add_left,add_zero]; exact h.bound t ht
private lemma shift_pay (F : Forest S.ratio) (x : ℝ) (u : PriceCoords G c) (hd : 0 ≤ d) (hs : d ≤ σ) (ht : n*d ≤ σ) (hM : 0 ≤ M)
    (hK : 0 ≤ K) (h : KernelJets n σ v η l M (bareStores S) F T x (1:Config G c) k u)
    (hp : Parcel 0 (down S) d n (fun y => ink T F x k (u+y)) K) :
    Parcel 0 (front (bareStores S) F) d n (fun y => school T F x k (u+y)) (2^n*( (2^n*(K*M)) * M)) := by
  have hPi := (h.windowJets 0 le_rfl).polar hM le_rfl
  rw [show drain 0=1 by simp [drain],mul_one] at hPi
  let U := bareStores S
  have ht := hp.deliver hK (polar_shift h.moves.transpose) hM hd hs ht
  have hP := ht.deliver (by positivity : 0≤(2:ℝ)^n*(K*M)) (polar_shift hPi.transpose) hM hd hs (show (n:ℝ)*d ≤ σ from ‹_›)
  exact hP.nonnegated.glue (Eventually.of_forall fun y => (neg_mulVec (pencil T F x k (u+y)) ((barePi T x F k (u+y)).transpose)).symm)

lemma reader_norm (u : Directions G c) : ‖reader G c u‖ ≤ ‖u‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
  exact fun i => (PiLp.norm_apply_le (u i.1) _).trans (norm_le_pi_norm ..)

omit [Fintype J] in
private lemma debit (y : Directions G c) {Q : PriceCoords G c → I → ℝ} (u : Directions G c → I → ℝ) (hd : 0<d) (hQ : u = Q ∘ reader G c)
    (h : Parcel 0 a d n (fun z => Q (reader G c y + z)) K) (hK : 0 ≤ K) :
    Through n u y (activation G n 0 d*K) := by
  let H z := Q (reader G c y+z)
  have ht := Parcel.activated_scale (H:=H) (by simpa using! h : Parcel 0 a d n (fun z : PriceCoords G c => H ((1:ℝ) • z)) K) hd zero_lt_one 0 hK
  have he z : u (y+z)=(H ∘ reader G c) z := by simp [H,hQ]
  have hS : ContDiffAt ℝ n u y := by
    have hv : u=(fun z => u (y+z)) ∘ (fun z => z-y) := by ext z; simp only [Function.comp_apply]; rw [add_sub_cancel]
    nth_rw 1 [hv,funext he]; exact (sub_self y |>.symm ▸ ht.1).comp (f:=fun z => z-y) y (contDiffAt_id.sub contDiffAt_const)
  refine ⟨hS,fun i hi => ?_⟩
  have hp : iteratedFDeriv ℝ i u y=iteratedFDeriv ℝ i (H ∘ reader G c) 0 := by
    rw [← funext he,iteratedFDeriv_comp_add_left,add_zero]
  rw [hp]; have h0 := mul_nonneg (zero_le_one.trans (activation_one G n 0 hd)) hK
  refine Planned.AtomRegular.op_le_of_unit h0 (fun v hv => (pi_norm_le_iff_of_nonneg h0).mpr fun j => ?_)
  let Z := List.ofFn v
  have ha : Afford 1 0 (0 : Site c) Z := by
    unfold Afford Z; rw [List.forall_mem_ofFn_iff]; intro i j; simp [FreeResolvent.Mark.hill]; exact (norm_le_pi_norm ..).trans (hv _)
  have hj := ht.2 0 Z (List.length_ofFn.trans_le hi) ha j
  simpa only [Z, Real.norm_eq_abs,FreeResolvent.Stars.list_result,FreeResolvent.Mark.hill,pow_zero, one_pow, inv_one,one_mul, id_comp] using hj
end excursion

def forecast (T : Tube G S) (x : ℝ) (F : Forest S.ratio) (k : S.Choices) : Directions G c → Prices G (clear S x F) := school T F x k ∘ reader G c

theorem survey (G : Gauge) (P : Patch) (Pt : Teller G) (hP : P.Branches Pt.bind G) (n : ℕ) :
    ∃ r M : ℝ, 0<r ∧ 0<M ∧ ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Pt.Funds S T →
      100*(1+radiusB x) ≤ c.val → ∀ (F : Forest S.ratio) (k : S.Choices) (u : Directions G c), ‖u‖ ≤ r → Through n (forecast T x F k) u M := by
  obtain ⟨r,d,K,hr,hd,hK,h⟩ := abroad G P Pt hP n
  obtain ⟨r',s,v,η,l,M,hr',hs,-,-,-,hM,H⟩ := assembly G P Pt hP n
  let t := min d (s/(n+1:ℕ)); have ht : 0<t := lt_min hd (by positivity)
  have hS : t+(n:ℝ)*t ≤ s := by
    have he := mul_le_mul_of_nonneg_right (min_le_right d (s/((n+1:ℕ):ℝ))) (show (0:ℝ) ≤ (n+1:ℕ) by positivity)
    rw [div_mul_cancel₀ _ (show ((n+1:ℕ):ℝ)≠0 by positivity)] at he
    change t*((n+1:ℕ):ℝ) ≤ _ at he; push_cast at he; linarith only [he]
  let X := (2:ℝ)^n*((2^n*(K*M))*M)
  have hX : 0 < X := by unfold X; positivity
  refine ⟨min r r',activation G n 0 t*X,lt_min hr hr',mul_pos (zero_lt_one.trans_le (activation_one G n 0 ht)) hX,?_⟩
  filter_upwards [h,H] with x h H c f S T hs' hF hp F k u hu
  have hu' := (reader_norm u).trans hu
  have hq := H.2 S T hs' hp hF (bareStores S) F 1 (noFlags ..).symm k _ (hu'.trans (min_le_right ..))
  exact debit u (forecast T x F k) ht rfl (shift_pay F x _ ht.le ((le_add_of_nonneg_right (show 0≤(n:ℝ)*t by positivity)).trans hS)
    ((le_add_of_nonneg_left ht.le).trans hS) hM.le hK.le hq ((h S T hs' hF hp F k _ (hu'.trans (min_le_left ..))).mono (min_le_left ..) le_rfl)) hX.le
end YM.PhysicalNext.JointLoad.Heir
