import YM.Further.FREE_COVARIANCE_KP.KP.Petals
import YM.Next.RANK.Radian.Signed
import YM.PhysicalNext.RANK_COVARIANCE_ATLAS.Fourier

/-!
# Window estimate on the ACTUAL stamp

No statement about derivatives of the discrete P array at non-chosen
volumes. The interpolant already reads exact Periodic P; here charge
all required derivatives in FREQUENCY (punctured) and heat gap, with
one λ=2π conversion including stencils/volume convention. Allows prices
at every smoothing stage j consistently pre-L.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.RankCovariance
open Function Lattice Laurent Bloch Exterior Matrix RG
open Further.FreeCovariance.KP
open Next.Rank Next.Rank.Atlas Next.Rank.Radian Next.Rank.Beamer Next.Rank.CellsInt
open scoped Topology BigOperators ComplexConjugate Classical InnerProductSpace ContDiff

variable {n : Side} {G : Gauge} {α Ω η : ℝ}

/-- Gaussian parameter in *this* chart. -/
def chartHeat := circleRate^2
lemma chartHeat_pos : 0<chartHeat := sq_pos_of_pos circle_pos

-- make the PA/positive-face reading in the two imported APIs explicit.
-- analogue of KP's (private) `corner`, no cochain quotient endpoints.
private lemma wedge_front (a : PA) (q : Axis → ℂ) (v : X1→ℂ) :
    (wedge 1 q *ᵥ v) (plaquette a) = q a.val.1 * v (coord a.val.2)-q a.val.2 * v (coord a.val.1) := by
  let b := a.val.1; let d := a.val.2; have hb : b<d := a.property
  let F := plaquette a
  have hh : F.val={b,d} := rfl
  unfold wedge; rw [Matrix.sum_mulVec]; simp_rw [Matrix.smul_mulVec]; rw [Finset.sum_apply]
  change ∑ i, q i * ((left ℂ 1 i)*ᵥv) F=_
  rw [← Finset.sum_subset (Finset.subset_univ ({b,d}:Finset Axis)),Finset.sum_insert (by simp [hb.ne]), Finset.sum_singleton]
  · have hs : b∈F.val := hh ▸ Finset.mem_insert_self ..
    have ht : d∈F.val := by simp [hh]
    have hb' : remove b F hs=coord d := by ext i; by_cases he:i=b <;> simp [coord,remove,hh,he,hb.ne]
    have hd' : remove d F ht=coord b := by ext i; by_cases he:i=d <;> simp [coord,remove,hh,he,hb.ne']
    simp_rw [eliminate]; rw [dif_pos hs,dif_pos ht,hb',hd']
    rw [parity,parity,pre,pre]; simp [hh,Finset.filter_insert,Finset.filter_singleton,hb,hb.not_gt]; rfl
  intro i _ h; rw [eliminate,dif_neg (show i∉F.val from hh ▸ h),mul_zero]

private lemma turn_scales (x : E4) (i : Axis) : turned (circleRate • x) i=chirp i x := by
  rw [turned_at,chirp]; change Complex.I*((↑(circleRate*x i):ℂ))=_
  unfold circleRate; push_cast; ring

private lemma thermal_scale (x : E4) : liturgy chartHeat x = (spine (circleRate • x))⁻¹ * breeze 1 (circleRate • x) := by
  unfold liturgy spine
  rw [show breeze 1 (circleRate • x)=major chartHeat x from ?_,norm_smul,Real.norm_of_nonneg circle_pos.le,mul_pow,Complex.ofReal_mul]
  · have hp : Maxwell.normal=(circleRate^2)⁻¹ := by unfold Maxwell.normal circleRate; ring
    rw [hp,Complex.ofReal_inv, _root_.mul_inv_rev,div_eq_mul_inv]; ring
  unfold breeze Further.FreeCovariance.KP.polar chartHeat major; congr 2; rw [norm_smul,Real.norm_of_nonneg circle_pos.le,mul_pow]; ring

lemma heat_window (D L : Degree G) (h : D.paint=L.paint) (x : E4):
    HeatP chartHeat (origin D) (origin L) x = breeze 1 (circleRate • x) * pearls [] [] (circleRate • x) (plaquette D.a) (plaquette L.a) := by
  let a:= D.a; let b:= L.a; let p:=circleRate • x; let i:=a.val.1; let j:=a.val.2; let k:=b.val.1; let l:=b.val.2
  let T:= wedge 1 (turned p); let Z:=turned p
  have he : (T*Tᴴ) (plaquette a) (plaquette b)= Z i * star (T (plaquette b) (coord j))- Z j * star (T (plaquette b) (coord i)):= wedge_front a _ (fun z=> Tᴴ z (plaquette b))
  have hx (g : Axis) : T (plaquette b) (coord g)=Z k*(if l=g then 1 else 0)-Z l*(if k=g then 1 else 0):= by
    have hz:= wedge_front b (turned p) (Pi.single (coord g) 1); simpa only [mulVec_single_one,Pi.single_apply,coord_iff,Matrix.col, Matrix.transpose_apply] using hz
  unfold HeatP paints; rw [if_pos (show (origin D).paint=(origin L).paint from h)]
  have hu : raypath (origin D) (origin L)=[] := by simp [raypath,origin]
  simp only [hu,List.nil_append,show (origin L).degree=0 from rfl,pow_zero,one_smul,pearls,bill,List.map_nil,List.prod_nil,star_one]
  unfold pearl; rw [Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul]; unfold feather
  let A (u v : Axis) := press [u,v] (liturgy chartHeat) x
  have ht u v : A u v=Z u*(Z v*( (spine p)⁻¹*breeze 1 p)) := by
    unfold A Z p; rw [turn_scales,turn_scales,← thermal_scale]; rfl
  have hb (g t : Axis) (f : E4→ℂ) : (if g=t then f else 0) x=(if g=t then 1 else 0)*f x := by split <;> simp [*]
  simp only [Pi.sub_apply,hb]
  change (((if k=j then 1 else 0)*A i l - (if l=j then 1 else 0)*A i k)-((if k=i then 1 else 0)*A j l-(if l=i then 1 else 0)*A j k)) = breeze 1 p * ((spine p)⁻¹ *(T*Tᴴ) (plaquette a) (plaquette b))
  have hm (u : Axis) : star (Z u)= -Z u := by simp [Z,turned_at]
  have hq (g t : Axis) : star (if g=t then (1:ℂ) else 0) = (if g=t then 1 else 0) := by split_ifs <;> simp
  rw [he,hx,hx,ht,ht,ht,ht]; simp only [star_sub,star_mul,hm,hq]; ring

section bounds
open Set MeasureTheory
variable {ι : Type*} {f : ι → E4 → ℂ} {j : ℕ}
private lemma radial_scale (H : Further.FreeCovariance.KP.Weight whole (j:ℤ) f) (n : ℕ) (R : ℝ) :
    ∃ c : ℝ, ∀ i, Cast (fun z=>f i (circleRate • z)) n j R c := by
  let a:=circleRate; have ha : 0<a:=circle_pos
  let L:=a • ContinuousLinearMap.id ℝ E4
  have ho : L ⁻¹' whole.look=whole.look:= by ext z; simp [L,whole,ha.ne']
  have ht : MapsTo L whole.look whole.look := fun x hx=> (show x ∈ L ⁻¹' whole.look by rwa [ho])
  choose B hB hb using H.quotes
  let q (k:ℕ) := B k * a^j; let c := ∑ k ∈ Finset.range (n+1), q k
  have he (k) : 0≤q k := mul_nonneg (hB _) (pow_nonneg ha.le _)
  refine ⟨c,fun i=>⟨Finset.sum_nonneg fun k _=>he k,?_,?_⟩⟩
  · exact (H.smooth i|>.of_le (WithTop.coe_le_coe.mpr le_top)).comp L.contDiff.contDiffOn ht
  intro k hk z hZ _
  have hs : (↑k:ℕ∞ω)≤ ∞:=WithTop.coe_le_coe.mpr le_top
  have hx:= L.iteratedFDerivWithin_comp_right (H.smooth i) whole.ok.uniqueDiffOn (by rw [ho];exact whole.ok.uniqueDiffOn) (by rw [ho];exact hZ : z∈L ⁻¹' whole.look) hs
  rw [ho, Further.FreeCovariance.KP.Weight.within_price _ _ (show z∈whole from hZ),Further.FreeCovariance.KP.Weight.within_price _ _ (show L z∈whole from ht hZ)] at hx
  rw [show (iteratedFDeriv ℝ k (f i) (L z)).compContinuousLinearMap _ = (a^k:ℝ) • iteratedFDeriv ℝ k (f i) (L z) from ?_] at hx; swap
  · ext v; change iteratedFDeriv ℝ k (f i) (L z) (fun i=> a • v i) = a^k • _
    simpa using (ContinuousMultilinearMap.map_smul_univ (iteratedFDeriv ℝ k (f i) (L z)) (fun _ => a) v)
  have hh : ‖L z‖=a*‖z‖:= by simp [L,norm_smul,abs_of_pos ha]
  have hv : 0<‖z‖:= norm_pos_iff.mpr hZ
  change ‖iteratedFDeriv ℝ k (f i∘ L) z‖ * ‖z‖^k ≤ _
  rw [hx,norm_smul,Real.norm_of_nonneg (pow_nonneg ha.le _)]
  calc
    _ ≤ a^k * (B k* ‖L z‖^((j:ℤ)-k)) * ‖z‖^k := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hv.le _); apply mul_le_mul_of_nonneg_left _ (pow_nonneg ha.le _); exact hb k i _ (ht hZ)
    _ = q k * ‖z‖^j := by rw [hh,zpow_sub₀ (mul_pos ha hv).ne',zpow_natCast,zpow_natCast,mul_pow,mul_pow]; unfold q; field_simp
    _ ≤ _:= mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _=> he i) (Finset.mem_range_succ_iff.mpr hk)) (pow_nonneg hv.le _)

private lemma charter_price (ha : 0<α) (he : 0<η) (Ω : ℝ) (n : ℕ) (a b : TypeFace 2) :
    ∃ c : ℝ, 0≤c ∧ ∀ i : Firm α Ω η,
      Cast (kernelChart i a b) n 0 2 c ∧ Cast (fun x => ivory [] [] i (circleRate • x) a b) n 1 1 c := by
  obtain ⟨c,H⟩ := radial_scale (j:=0) (house_pay [] [] ha (Ω:=Ω) he a b) n 2
  obtain ⟨q,K⟩ := radial_scale (j:=1) (ivory_goes [] [] ha (Ω:=Ω) he a b) n 1
  refine ⟨max 0 (max q c),le_max_left ..,fun i=> ⟨(H i).coin ?_, (K i).coin ?_⟩⟩
  · exact (le_max_right ..).trans (le_max_right ..)
  exact (le_max_left ..).trans (le_max_right ..)

theorem window_prices (ha : 0 < α) (he : 0 < η) (Ω : ℝ) (n : ℕ) : ∃ C : ℝ, 0≤C ∧
    ∀ (f : Firm α Ω η) {G : Gauge} (a b : Degree G), Radian.Window (coloredChart f a b) 2 C n chartHeat a b := by
  choose c hc hh using charter_price ha he Ω n
  let q := ∑ a,∑ b,c a b
  have hq : 0≤q:=Finset.sum_nonneg fun _ _=> Finset.sum_nonneg fun _ _=> hc _ _
  refine ⟨q,hq,fun f G a b=> ?_⟩
  have hr (i j):c i j ≤ q:= (Finset.single_le_sum (fun k _=>hc i k) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun i _=> Finset.sum_nonneg fun j _=>hc i j) (Finset.mem_univ i))
  unfold coloredChart; split
  · rename_i H; let u:=plaquette a.a; let v:=plaquette b.a; obtain ⟨hU,hV⟩:= hh u v f
    have hF: Cast (kernelChart f u v) n 0 2 q:= hU.coin (hr u v)
    refine ⟨hq,chart_small f u v,?_,measurable_of_continuousOn_compl_singleton 0 hF.hills.continuousOn, hF,?_⟩
    · unfold kernelChart; rw [smul_zero,room_none,norm_zero]; exact hq
    rw [show kernelChart f u v - HeatP chartHeat (origin a) (origin b) = (fun x => ivory [] [] f (circleRate • x) u v) from funext fun x=> by unfold ivory; rw [Pi.sub_apply,heat_window a b H]; rfl]
    exact hV.coin (hr u v)
  rename_i H
  have he (j : ℕ) (y:ℝ) : Cast (0:E4→ℂ) n j y q := ⟨hq,contDiffOn_const,fun i _ z _ _=>by simp; positivity⟩
  refine ⟨hq,fun x _=>rfl,norm_zero (E:=ℂ)|>.trans_le hq,measurable_const,he 0 _,?_⟩
  unfold HeatP paints; rw [if_neg (show (origin a).paint≠(origin b).paint from H),sub_self]; exact he 1 1
end bounds
end YM.PhysicalNext.RankCovariance
