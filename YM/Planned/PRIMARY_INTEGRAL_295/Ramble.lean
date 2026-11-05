import YM.Planned.PRIMARY_INTEGRAL_295.Bazaars
import YM.Planned.PRIMARY_INTEGRAL_295.Postcards

/-!
# Probe repayment on the actual cover rows

Use normalized b=.../t.

At input probe path
`testLinks d 0`, unmasked stencil germs are Cover polynomial; perform
exact derivative alignment with `Postcards.forecast` AT ALL physical
anchors thought of on one cover.

Error charge for differing b cut/torus
wrap (Γ etc) forthcoming, not in this identity.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Ramble
open Function Filter Set Metric Labels Lattice RG Wilson Source Source.Drops
open Place Streets Bazaars Postcards PPX Carrier Precision Exterior Bloch Next.Free
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
open Push.Local (Probe)
variable {d k l n j : ℕ} {G : Gauge} (Z : Probe G d) {T : Finset Cover} {L : Side}

-- errors need moment expansion on ALL coarse cover coordinates, including
-- where `scripts` never promotes an actual sample U edge log.
def panel (b c : ℝ) := c • WardBin.engineered b (trunk d Z.1)
lemma panel_paid (c:ℝ) : ContDiff ℝ ω fun x:ℝ=> panel Z x c := (WardBin.eng_cont ..).const_smul c
lemma paid_origin (c:ℝ) : panel Z 0 c = 0 := by unfold panel; ext1 i; simp [WardBin.engineered_at]
lemma panels (x c:ℝ) : panel Z x c = WardBin.engineered x (trunk d (c • Z.1)) := by
    unfold panel; rw [← map_smul]; rfl

def script (t c : ℝ) (x : Cover) (i:Axis) (y:ℝ) := t⁻¹ • Film.lane (seat x) i (panel Z y c)
def lamina (n:ℕ) (t c:ℝ) : Window G.Color := fun x i=> iteratedDeriv n (script Z t c x i) 0

lemma script_smooth (c t : ℝ) (x : Cover) (i:Axis) : ContDiffAt ℝ ω (script Z t c x i) 0 := by
  have he : ContDiffAt ℝ ω (Film.lane (seat x) i) (panel Z 0 c) := by simp only [paid_origin]; exact Film.lane_smooth _ _
  exact (he.comp (f:=fun y=> panel Z y c) 0 (panel_paid Z c).contDiffAt).const_smul _

-- reconciliation scales STEP, not arbitrary polarizations; use even with
-- zero theta roots as formal only, spend positive.
lemma script_truth (H : Hol G) (a : Edge Cover) (t c : ℝ) (x : ℝ) :
    script Z t c a.1 a.2 x=t⁻¹ • G.plog (G.mat (H.links d (c • Z.1) x a)) := by
  rw [script,Film.lane_truth H a,panels,show H.links d (c • Z.1) x=_ from ?_]
  exact (scales H _ x)

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma scaleLines (A : Lines L) (b : ℝ) (f : Window E) : applyLine A (b • f)=b • applyLine A f := by
  ext1 x; ext i; unfold applyLine stream; simp only [Pi.smul_apply,Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _=>?_; rw [← tsum_const_smul'']; exact tsum_congr fun i=>smul_comm ..

lemma sumIt {ι : Type*} (U : Finset ι) (f : ι → Window E) (n : ℕ) (c : ι → ℝ) (h : ∀ i ∈ U, Carries (f i) n (c i))
    (A : Lines L) (hh : Whole A) : Carries (∑ i∈U,f i) n (∑ i∈U,c i) ∧
    applyLine A (∑ i∈U,f i)=∑ i∈U,applyLine A (f i) := by
  classical
  induction U using Finset.induction_on with
  | empty =>
    constructor
    · simp only [Finset.sum_empty]; exact ⟨le_rfl,fun _ _=>by simp⟩
    ext1 x; ext1 i; simp [applyLine,stream]
  | insert i u hi ih =>
    have ht:=h i (by simp)
    obtain ⟨hg,hf⟩:=ih (fun i' hi'=>h _ (Finset.mem_insert_of_mem hi'))
    rw [Finset.sum_insert hi,Finset.sum_insert hi,Finset.sum_insert hi]; constructor
    · refine ⟨add_nonneg ht.1 hg.1,fun x i'=>?_⟩
      rw [add_mul]; exact (norm_add_le ((f i) x i') ((∑ i∈u,f i) x i')).trans (add_le_add (ht.2 _ _) (hg.2 _ _))
    rw [addLine hh _ _ ht hg,hf]
end

-- pointwise vector of each ordered partition derivative with its own
-- factorial/account. `f` here Faa coefficient, not total Taylor.
private def grains (t c:ℝ) (b : OrderedFinpartition n) : Window G.Color := fun x i=> t⁻¹ •
    Cases.caseRead b (Film.lane (G:=G) (d:=d) (seat x) i) (fun x=> panel Z x c) 0 (fun _=>1)

private lemma surveyed (π : ℝ) (hπ : 1≤π) (b : OrderedFinpartition n) : ∃ D:ℝ,0 ≤ D ∧
    ∀ (c t : ℝ), Blend π t c → Carries (grains Z t c b) (d*n) D := by
  classical
  set m:=b.length
  let g x := WardBin.engineered x (trunk d Z.1)
  have hg : ContDiff ℝ ω g := WardBin.eng_cont ..
  let v(i:Fin m) := iteratedDeriv (b.partSize i) g 0
  let p := (∏ i,‖v i‖); have hp:0≤p:=by unfold p; positivity
  obtain ⟨C,hC,H⟩:= Film.mail_cap G d m
  refine ⟨π*C*p,by positivity,fun c t hc=>⟨by positivity,fun x i=>?_⟩⟩
  let V:= Film.lane (seat x) i (G:=G) (d:=d)
  let W := iteratedFDeriv ℝ m V 0
  have hy(j:ℕ) : iteratedFDeriv ℝ j (fun x=>panel Z x c) 0=c • iteratedFDeriv ℝ j g 0 := iteratedFDeriv_const_smul_apply (a:=c) (hg.contDiffAt.of_le le_top)
  unfold grains Cases.caseRead; simp only [paid_origin]; simp_rw [hy,smul_apply]
  change ‖t⁻¹ • W (fun j => c • v j)‖ ≤ _
  by_cases hm : m=0
  · have hv (a : Fin m→Snap G d) : W a=0 := by unfold W; revert a; rw [hm]; intro a; simp [V,Film.lane_root]
    rw [hv,smul_zero,norm_zero]; have he:=liftCost_pos (d*n) x; positivity
  have ht:=hc.fine; have hcp:=hc.coarse; have he := W.map_smul_univ (fun _=>c) v
  rw [he,Finset.prod_const,Finset.card_univ,Fintype.card_fin,smul_smul,norm_smul,Real.norm_of_nonneg (by positivity)]
  have hr : t⁻¹*c^m ≤ π := (mul_le_mul_of_nonneg_left (show c^m ≤ c by simpa using pow_le_pow_of_le_one hcp.le hc.covers (Nat.one_le_iff_ne_zero.mpr hm)) (by positivity)).trans
    ((by rw [mul_comm, ← div_eq_mul_inv]; exact hc.accounted))
  apply (mul_le_mul hr ((W.le_opNorm _).trans (mul_le_mul_of_nonneg_right (H x i) hp)) (norm_nonneg _) (by positivity)).trans
  have h : liftCost (d*m) x≤liftCost (d*n) x := pow_le_pow_right₀ (show 1≤1+(Laurent.size x:ℝ) by simp) (Nat.mul_le_mul_left d b.length_le)
  calc
    _ = π*C*p*liftCost (d*m) x := by change π*(C*liftCost (d*m) x * p) = _; ring
    _ ≤ _ := by gcongr

private lemma together (n:ℕ) (t c:ℝ) : lamina Z n t c=∑ b:OrderedFinpartition n,grains Z t c b := by
  classical
  ext1 x; ext1 i
  let g:=fun x:ℝ=>panel Z x c
  let h : Snap G d→G.Color:=Film.lane (seat x) i
  have hg : ContDiff ℝ ω g:=panel_paid ..; have hh : ContDiffAt ℝ ω h (g 0) := by
    rw [show g 0=_ from paid_origin Z c]; exact Film.lane_smooth _ _
  rw [Finset.sum_apply,Finset.sum_apply]
  change iteratedFDeriv ℝ n (t⁻¹ • (h ∘ g)) 0 (fun _=>1)=_
  rw [iteratedFDeriv_const_smul_apply ((hh.comp 0 hg.contDiffAt).of_le le_top), smul_apply, Cases.compReads hh hg.contDiffAt le_top,Finset.smul_sum]
  rfl

/-- All cover points of the hol logarithm jets are usable. -/
lemma gathered (π : ℝ) (hπ:1≤π) (n:ℕ) : ∃ C : ℝ, 0≤C ∧ ∀ c t,
    Blend π t c → Carries (lamina Z n t c) (d*n) C ∧ ∀ (T:Finset Cover) {L} (W:Lines L), n≤d → Whole W →
      iteratedDeriv n (forecast T Z W c t) 0 = Units.inView T (applyLine W (lamina Z n t c)) := by
  classical
  choose C hC H using fun b:OrderedFinpartition n=>surveyed Z π hπ b
  refine ⟨∑ b,C b,Finset.sum_nonneg (fun i _=>hC i),fun c t ht=>?_⟩; rw [together]
  constructor
  · -- use direct norm sum to avoid a Whole context
    refine ⟨Finset.sum_nonneg fun i _=>hC i,fun x i=>?_⟩; rw [Finset.sum_apply,Finset.sum_apply,Finset.sum_mul]
    exact (norm_sum_le ..).trans (Finset.sum_le_sum fun b _=> (H b c t ht).2 x i)
  intro T L W hn hW
  let g : Snap G d → Dev T G := Film.trace T W
  let a:ℝ→Snap G d:=fun x=> panel Z x c
  have hg:ContDiff ℝ ω g:= Film.trace_smooth hW T d; have ha:=panel_paid Z c
  rw [show forecast T Z W c t=t⁻¹ • (g ∘ a) from funext fun x=>by simp only [forecast,a,g,panels,Pi.smul_apply,Function.comp_apply]]
  change iteratedFDeriv ℝ n (t⁻¹ • (g∘a)) 0 (fun _=>1)=_
  rw [iteratedFDeriv_const_smul_apply ((hg.comp ha).contDiffAt.of_le le_top),smul_apply,Cases.compReads hg.contDiffAt ha.contDiffAt le_top,Finset.smul_sum]
  rw [(sumIt Finset.univ (grains Z t c) (d*n) C (fun i _=> H _ c t ht) W hW).2]
  funext i; rw [Finset.sum_apply]; unfold Units.inView; rw [Finset.sum_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl; intro b _; unfold grains Cases.caseRead; simp only [paid_origin,Pi.smul_apply]
  unfold g; let v (i:Fin b.length):Snap G d:=iteratedDeriv (b.partSize i) a 0
  change t⁻¹ • (iteratedFDeriv ℝ b.length (Film.trace T W (G:=G) (d:=d)) 0 v) i = _
  rw [Film.trace_mail hW (b.length_le.trans hn)]
  exact congr_fun (congr_fun (scaleLines W t⁻¹ (fun x i=> iteratedFDeriv ℝ b.length (Film.lane (seat x) i) 0 v)).symm _) _
end YM.Planned.PrimaryIntegral295.Ramble
