import YM.Planned.PRIMARY_INTEGRAL_295.East
import YM.Planned.PRIMARY_INTEGRAL_295.Tones


/-!
# E Jloer, the predicted *normalized* comparison jets at the identity

For the separated finite Probe list at the stencil, reads actual
log-link tests on the torus; in comparison use full cover row acting on
polynomial jets only. Charges before-L from Record and Carrier. Exponential
tail comparison to true mean/log Hessian at t>0 requires additional payment
for each chart, not included here.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Postcards
open Function Filter Set Metric Labels Lattice RG Place Carrier Source Source.Drops Bloch Precision Next.Free
open Film
open Push.Local (Probe runProbe)
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {d j t : ℕ} {L : Side}

def forecast (S : Finset Cover) (p : Probe G d) (K : Lines L) (c f : ℝ) (x : ℝ) : Dev S G :=
    f⁻¹ • trace S K (WardBin.engineered x (trunk d (c • p.1)))

lemma forecast_truth (S : Finset Cover) (p : Probe G d) (K : Lines L) (c f : ℝ) (hk : Whole K) :
    ContDiff ℝ ω (forecast S p K c f) := by
  exact ((trace_smooth (G:=G) hk S d).comp (WardBin.eng_cont ..)).const_smul (f⁻¹)
@[simp] lemma forecast_zero (S : Finset Cover) (p : Probe G d) (K : Lines L) (c f : ℝ) : forecast S p K c f 0=0 := by
  unfold forecast
  have he : WardBin.engineered (0:ℝ) (trunk d (c • p.1))=0 := by funext i; simp [WardBin.engineered_at]
  rw [he,trace_root,smul_zero]

/-- Convolution cost, can call after expansion at the finite actual
snap vectors in p, no opNorm changes from period. -/
private lemma toneAt (S : Finset Cover) (k : ℝ) (hk : 0 < k) (hj : 4 ≤ j) (ht : 4 ≤ t) (n : ℕ) (hn : n ≤ d) (v : Fin n → Snap G d) :
    ∃ C:ℝ,0≤C ∧ ∀ P : Flight j t, ‖iteratedFDeriv ℝ n (trace S (linesOf P k) (G:=G) (d:=d)) 0 v‖ ≤ C := by
  classical
  obtain ⟨A,hA,hX⟩:=mail_cap G d n
  let s:=d*n
  let g (x : Cover) (a : Axis) := iteratedFDeriv ℝ n (lane (G:=G) (d:=d) (seat x) a) 0 v
  let M:=A*∏ j, ‖v j‖; have hM : 0≤M := by unfold M; positivity
  have hf : Carries g s M := by
    refine ⟨hM,fun x a=>?_⟩
    apply ((iteratedFDeriv ℝ n (lane (G:=G) (d:=d) (seat x) a) 0).le_opNorm v).trans
    exact (mul_le_mul_of_nonneg_right (hX _ _) (by positivity)).trans_eq (mul_right_comm ..)
  obtain ⟨σ,D,hσ,hD,H⟩ := priced k hk hj ht
  let B:=4*M*widthCost σ s*D; let u (p : Spot S) := liftCost s (first p).val
  have hu (p : Spot S) : 0≤u p := liftCost_pos ..
  have he := Finset.sum_nonneg (s:=Finset.univ) (fun i _=>hu i)
  have hw:=widthCost_ge hσ s; have hB:0≤B:=by unfold B; positivity
  refine ⟨B*∑ p,u p,mul_nonneg hB he,fun P=>(pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i=>?_⟩
  rw [trace_mail (stored P k hk ht) hn]
  let C:=D/(P.L.val:ℝ)
  have hp := unitStep_pos P.L
  have hh : (linesOf P k).strip σ C := by simpa [C, advanceC] using H P [] (by simp)
  have hx := (field_cost hσ (show 0≤C by unfold C; positivity) hh s hf).2 (first i).val (beam i)
  apply hx.trans
  change 4*M*widthCost σ s*C*u i ≤ _
  have hC : C≤D := div_le_self hD.le (Nat.one_le_cast.mpr P.L.property)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hC (by positivity)) (Finset.single_le_sum (fun i _=> hu i) (Finset.mem_univ i)) (hu i) hB

lemma replicate (S : Finset Cover) (p : Probe G d) (π k : ℝ) (hπ : 1≤π) (hk : 0 < k) (hj : 4 ≤ j) (ht : 4 ≤ t) (n : ℕ) (hn : n ≤ p.2.val) :
    ∃ C : ℝ,0≤C ∧ ∀ (P : Flight j t) (c f : ℝ), PPX.Blend π f c → ‖iteratedFDeriv ℝ n (forecast S p (linesOf P k) c f) 0‖ ≤ C := by
  classical
  cases n with
  | zero => exact ⟨0,le_rfl,fun P c f h=> by simp⟩
  | succ r =>
    let n:=r+1
    let g (x : ℝ) := WardBin.engineered x (trunk d p.1)
    let H (P : Flight j t) := trace S (linesOf P k) (G:=G) (d:=d)
    have hg : ContDiff ℝ ω g := WardBin.eng_cont ..
    have hz : g 0=0 := by funext i; unfold g; simp [WardBin.engineered_at]
    let v (b : OrderedFinpartition n) (i : Fin b.length) : Snap G d := iteratedDeriv (b.partSize i) g 0
    choose D hD HD using fun b : OrderedFinpartition n => toneAt S k hk hj ht b.length
      (b.length_le.trans (hn.trans (Nat.le_of_lt_succ p.2.isLt))) (v b)
    have hK:= Finset.sum_nonneg (s:=Finset.univ) (fun i _=> hD i)
    refine ⟨∑ b : OrderedFinpartition n,π*D b, Finset.sum_nonneg (fun i _=>by have := hD i; positivity),fun P c f hf=>?_⟩
    have ha := hf.fine; have hb:=hf.coarse
    have hF : forecast S p (linesOf P k) c f = f⁻¹ • (H P ∘ (c • g)) := by
      funext x
      change f⁻¹ • H P (WardBin.engineered x (trunk d (c • p.1)))=f⁻¹ • H P (c • g x)
      unfold g; rw [← map_smul]; rfl
    have hG : ContDiff ℝ ω (c • g) := contDiff_const.smul hg
    have ht' : ContDiff ℝ ω (H P) := trace_smooth (stored P k hk ht) ..
    rw [hF, norm_iteratedFDeriv_eq_norm_iteratedDeriv];
    change ‖iteratedFDeriv ℝ n (f⁻¹ • (H P ∘ (c • g))) 0 (fun _=>1)‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply ((ht'.comp hG).contDiffAt.of_le le_top), smul_apply,
      Cases.compReads ht'.contDiffAt hG.contDiffAt le_top, Finset.smul_sum]; apply (norm_sum_le ..).trans
    apply Finset.sum_le_sum; intro b _
    let m:=b.length
    have hm : 0<m := b.length_pos (Nat.succ_pos r)
    unfold Cases.caseRead
    simp only [Pi.smul_apply,hz,smul_zero,iteratedFDeriv_const_smul_apply (hg.contDiffAt.of_le le_top),smul_apply]
    let u := iteratedFDeriv ℝ b.length (H P) (0:Snap G d)
    change ‖f⁻¹ • u (fun i => c • v b i)‖ ≤ _
    have HE := u.map_smul_univ (fun _=> c) (v b)
    rw [HE,smul_smul,norm_smul,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
      Real.norm_of_nonneg (by positivity)]
    have hc : f⁻¹*c^m≤π := calc
      f⁻¹ * c^m ≤ f⁻¹*c := mul_le_mul_of_nonneg_left (by simpa using pow_le_pow_of_le_one hb.le hf.covers hm) (by positivity)
      _ ≤ π := (by rw [mul_comm,← div_eq_mul_inv]; exact hf.accounted)
    exact mul_le_mul hc (HD b P) (norm_nonneg _) (by positivity)

-- `revealed` same map when applied at probes with present normalized account.
theorem measured {F : Labels.Frame G d} {H : Hol G} (T : SectionData F) (h : T.Sound H) (b : Bid.pop T)
    (P : Flight j t) (k π c f : ℝ) (hk : 0<k) (ht : 4≤t) (hd : d≤j) (hp : PPX.Blend π f c) (p : Probe G d) (a : F.Index) :
    let Z := PPX.Seal.donne T h hk ht b P hd hp
    runProbe F p (Z.leads P.L (copy F a)) = (P.L.val:ℝ)^d •
      iteratedDeriv p.2.val (Tones.tint T a f ∘ forecast T.stencil p (linesOf P k) c f) 0 := by
  intro Z; unfold Z; rw [PPX.Seal.revealed T h hk ht b P hd hp a p]
  let g (x:ℝ):=trace T.stencil (linesOf P k) (WardBin.engineered x (trunk d (c • p.1)))
  let l := (F.grades a).2
  have hv := hp.fine.ne'
  have he : Tones.tint T a f ∘ forecast T.stencil p (linesOf P k) c f = (f^l)⁻¹ • (Place.column T a ∘ g) := by
    funext x; change (f^l)⁻¹ • column T a (f • f⁻¹ • g x)=_; rw [smul_smul, mul_inv_cancel₀ hv, one_smul]; rfl
  have hh : ContDiff ℝ ω (Place.column T a ∘ g) := (column_smooth ..).comp ((trace_smooth (stored P k hk ht) ..).comp (WardBin.eng_cont ..))
  rw [he,iteratedDeriv_const_smul (hh.contDiffAt.of_le le_top), smul_smul, Complex.real_smul]
  push_cast; rfl
end YM.Planned.PrimaryIntegral295.Postcards
