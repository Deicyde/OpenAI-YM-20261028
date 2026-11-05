import YM.Next.RANK.Radian.TK
import YM.PhysicalNext.RANK_COVARIANCE_ATLAS.Atlas


/-!
# Finite Fourier stamp

Bridge E Kper fundamental-cube smoothed cut to stencils in Rank. Smooth
partition is in FREQUENCY, on the chart cover (KP). Compose in exactly
+2πi convention. This does not change the torus coefficients: full sum on
all aliases in the room, including even-side endpoints. The partition avoids
having to assert smoothness across the other reciprocal copies of the pole.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.RankCovariance
open Function Lattice Laurent Bloch Exterior Matrix RG
open Further.FreeCovariance.KP
open Next.Rank Next.Rank.Atlas Next.Rank.Radian Next.Rank.Beamer Next.Rank.CellsInt
open scoped Topology BigOperators ComplexConjugate Classical InnerProductSpace

variable {n : Side} {G : Gauge} {α Ω η : ℝ}

-- conversion from unit-frequency chart to radian chart. carry 2π exactly

def circleRate : ℝ := 2*Real.pi
lemma circle_pos : 0<circleRate := by unfold circleRate; positivity
lemma song_wave (x y : E4) : song x (circleRate • y) = wave x y := by
  rw [wave,Real.fourierChar_apply]
  unfold song; rw [london_at]; congr 1
  simp only [real_inner_smul_right,inner_neg_right,neg_neg]; rw [real_inner_comm x]
  rw [circleRate]; push_cast; ring

lemma shift_rate (n : Side) (x : Cover) : circleRate • Radian.addr n x = lit n x := by
  unfold circleRate Radian.addr lit; rw [smul_smul]; change _= (2 * Real.pi / _) • _; rw [div_eq_mul_inv]; rfl

/-- Plain unspecialized multiplier, full scalar pair. -/
def kernelChart (f : Firm α Ω η) (a b : TypeFace 2) (x : E4) :=
    rebus [] [] f (circleRate • x) a b

/-- Chart aperture (E units). -/
lemma chart_small (f : Firm α Ω η) (a b : TypeFace 2) : eventP 2 (kernelChart f a b) := by
  intro x hx; unfold kernelChart rebus; rw [house_off,zero_smul]; rfl
  intro h; let p:=circleRate • x
  have hr : ‖p‖ ≤ 2*mural := by
    apply le_of_sq_le_sq _ (by have := fearless.1; linarith)
    rw [PiLp.norm_sq_eq_of_L2]; calc
      _ ≤ ∑ _ : Axis,mural^2 := Finset.sum_le_sum fun i _=> pow_le_pow_left₀ (norm_nonneg _) (h i) _
      _ = _ := by simp; ring
  unfold p at hr; rw [norm_smul,Real.norm_of_nonneg circle_pos.le] at hr
  have he := mul_lt_mul_of_pos_left hx circle_pos; push_cast at he
  unfold circleRate mural at *; linarith [Real.pi_pos]

-- Since the smooth `house` partition is zero elsewhere, a Finset room
-- gathers all pav copies. Retains `x` arbitrary integer lift, not only
-- cyclic representatives or outside origin.
lemma chart_reads (n : Side) (x : Cover) (f : Firm α Ω η) (a b : TypeFace 2) :
    stepsP (kernelChart f a b) n 2 (mapZ x) = rock n f a b x := by
  let Y (j : Cover):= wave (mapZ x) (addr n j)* kernelChart f a b (addr n j)
  let X (j : Cover):= song (rcast x) (lit n j) * rebus [] [] f (lit n j) a b
  have hz (i):Y i=X i := by unfold Y X kernelChart; rw [← shift_rate, song_wave]; rfl
  let R:= Radian.room n 2
  let W:= Finset.univ.image (pav n)
  have hW : (∑ j∈R,Y j)=(∑ i : Site n × St, X (pav n i)) := by
    have ht : (∑ i : Site n × St, X (pav n i))=(∑ j∈ W,Y j) := by
      unfold W; rw [Finset.sum_image]; simp_rw [hz]; exact (pav_sep n).injOn
    rw [ht]
    have hu (j:Cover) (h : j∉W) : Y j=0 := by
      rw [hz]; unfold X rebus
      have hx : house (lit n j)=0 := by
        by_contra hx
        obtain ⟨i,rfl⟩ := roof_hit j hx
        exact h (Finset.mem_image_of_mem _ (Finset.mem_univ _))
      rw [hx]; simp
    have hr (j : Cover) (h : j ∉ R) : Y j=0 := by
      unfold Y; rw [chart_small f a b _ (lt_of_not_ge fun hx=> h (addressBW _ _ hx)),mul_zero]
    calc
      _ = ∑ i∈R∪W, Y i := Finset.sum_subset Finset.subset_union_left (fun i _ hi=> hr i hi)
      _ = _ := (Finset.sum_subset Finset.subset_union_right (fun i _ hi=> hu i hi)).symm
  rw [stepsP]; unfold scansP; rw [Further.FreeCovariance.KP.rock,covering]; change _ • (∑ j ∈ R,Y j) = (tally:ℂ) * _
  rw [hW]; simp only [Complex.real_smul]
  rw [← mul_assoc]; congr 1
  unfold tally leap height; have hπ := Real.pi_ne_zero; have h:= side_ne n; push_cast; field_simp

def coloredChart (f : Firm α Ω η) (a b : Degree G) : E4→ℂ := if a.paint=b.paint then kernelChart f (plaquette a.a) (plaquette b.a) else 0

lemma colored_reads (A : Levels G) (N k p) (f : Firm α Ω η)
    (ha : 0<α) (he : 0<η) (hf : f.row=Next.Free.pink A.clock.kernel.penalty (Next.Free.location A N k))
    (x y u v : Cover) (a b : Degree G) :
    ((stamp A N p).κ k).cov (body x (u,a.a,a.paint)) (body y (v,b.a,b.paint))=
      stepsP (coloredChart f a b) (A.S.side k p) 2 (captured x y u v) := by
  rw [lift_lag]; unfold coloredChart
  split; swap
  · simp [stepsP,scansP]
  symm; unfold captured; rw [chart_reads,Episode.bridge A.clock.kernel.penalty A.clock.kernel.penalty_pos (A.clock.adm k) ha he _ f hf]
end YM.PhysicalNext.RankCovariance
