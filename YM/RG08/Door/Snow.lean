import YM.RG08.Door.Miles
/-!
# per-coefficient summit. Conservative defaults off announced tails
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Door
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Matrix
open scoped BigOperators Topology Real
variable {X:Chain}{G:Gauge}{E e r d τ D j t i k m l n s :ℕ}{R θ C w:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}
open Wings Summit
variable {I:Type}{u:I→Windows}
section pricing
variable {α β : Type}[NormedAddCommGroup β]
lemma tinted {V:ℕ→Quire.Rooted β α r}{U:Quire.Rooted β α r}(h:Tendsto V atTop (𝓝 U))(hh:∀ᶠ v in atTop,Quire.Lit (V v) w C) : Quire.Lit U w C := by
  have he := tendsto_pi_nhds.mpr (fun i=>(tendsto_pi_nhds.mp h i).norm)
  apply (show Quire.Lit U w C from ?_); unfold Quire.Lit Quire.Ink
  simpa only [Charge,norm_norm] using charge_stop (U:=fun i=>‖U i‖) (F:=fun j i=> ‖V j i‖) (w:=ling w) (fun _=> (ling_pos _ _).le) he (hh.mono (fun i hi=> by simpa only [Quire.Lit, Quire.Ink,Charge,norm_norm] using hi))
variable [CompleteSpace β]
lemma knit {U : ℕ→ℕ→ Quire.Rooted β α r}{σ:ℕ→ℝ}(hp: ∀ i,0<σ i)(h:Twill (menu X) (chop X (1/4)) (fun i:Wings u n=> U i.N i.i) (fun i=> U i.M i.i) (fun i=> σ i.i)) :
    Twill (menu X) (chop X (1/4)) (fun i:Wings u n=> U i.N i.i) (fun i=>apex (fun N=> U N i.i)) (fun i=> σ i.i) := by
  obtain ⟨B,⟨C,p,hC,H⟩,HT⟩:= h.one.serves; obtain ⟨V,⟨D,q,hD,hZ⟩,hg⟩:=h.goes.serves
  have hv (i: Wings u n)(N)(hN:i.i+n≤N) (M) (hM:N≤M): Quire.Lit (U N i.i-U M i.i) (σ i.i) (D*menu X i^q * gain X.S (1/4) i.i N) := Ink.raise (hg {i with N:=N,cut:=hN,M:=M,side:=hM}) (mul_le_mul_of_nonneg_right (hZ _|>.2) (gain_pos ..).le)
  have he (i:Wings u n) : Tendsto (fun N=> U N i.i) atTop (𝓝 (apex (fun N=>U N i.i))) := by
    have hz k: CauchySeq (fun N=> U N i.i k) := by
      apply Metric.cauchySeq_iff'.mpr; intro ε hE
      obtain ⟨N,hN,ht⟩:= ((eventually_ge_atTop (i.i+n)).and ((tendsto_gain X.S (v:=1/4) (by norm_num) i.i|>.const_mul (D*menu X i^q)).eventually (gt_mem_nhds (by simpa only [mul_zero])))).exists
      refine ⟨N,fun j hj=> ?_⟩; rw [dist_comm,dist_eq_norm_sub]; exact ((le_mul_of_one_le_left (norm_nonneg _) (ling_one (hp _).le k)).trans (budget_single (hv i N hN j hj) _)).trans_lt ht
    choose A hA using fun k=> cauchySeq_tendsto_of_complete (hz k); exact apex_win ⟨A,tendsto_pi_nhds.mpr hA⟩
  constructor; exact h.one
  · refine ⟨_,(Weighed.constant (menu X) hC).times (Weighed.power (menu X) (sh X) p),fun i=>?_⟩
    rw [Pi.mul_apply,Pi.pow_apply,Pi.one_apply,mul_one]; exact tinted (he i) ((eventually_ge_atTop (i.i+n)).mono fun N hN=> Ink.raise (HT {i with N:=N,cut:=hN,M:=N,side:=le_refl N}) (by rw [Pi.one_apply,mul_one]; exact (H _).2))
  refine ⟨_,(Weighed.constant (menu X) hD).times (Weighed.power (menu X) (sh X) q),fun i=>?_⟩
  rw [Pi.mul_apply,Pi.pow_apply]; exact tinted (tendsto_const_nhds.sub (he i)) ((eventually_ge_atTop _).mono (hv i i.N i.cut))
-- scalar leases have same limits
lemma pine {B:ℕ→ℕ→ℝ} (h:Lease (menu X) (chop X (1/4)) (fun i:Wings u n=> B i.N i.i) (fun i=> B i.M i.i)): Lease (menu X) (chop X (1/4)) (fun i:Wings u n=> B i.N i.i) (fun i=> apex (fun N=> B N i.i)) := by
  obtain ⟨A,⟨D,q,hD,H⟩,hv⟩:= h.asset
  have he (i:Wings u n)(N)(hN:i.i+n≤N) (M)(hM:N≤M) : ‖B N i.i-B M i.i‖≤ D*menu X i^q*gain X.S (1/4) i.i N:= (hv {i with N:=N,M:=M,side:=hM,cut:=hN}).trans (mul_le_mul_of_nonneg_right (H _|>.2) (gain_pos ..).le)
  have ht(i:Wings u n): Tendsto (fun N=> B N i.i) atTop (𝓝 (apex fun N=>B N i.i)) := by
    refine apex_win (cauchySeq_tendsto_of_complete ?_); apply Metric.cauchySeq_iff'.mpr; intro ε hE
    obtain ⟨N,hN,hv⟩:= ((eventually_ge_atTop (i.i+n)).and ((tendsto_gain X.S (v:=1/4) (by norm_num) i.i|>.const_mul (D*menu X i^q)).eventually (gt_mem_nhds (by simpa only [mul_zero])))).exists
    refine ⟨N,fun j hj=>?_⟩; rw [dist_comm,dist_eq_norm_sub]; exact (he i N hN _ hj).trans_lt hv
  constructor; exact h.has
  · obtain ⟨C,p,hC,hP⟩:= h.has; exact ⟨C,p,hC,fun i=>⟨norm_nonneg _, le_of_tendsto (ht i|>.norm) ((eventually_ge_atTop _).mono (fun N (hp:i.i+n≤N)=> (hP {i with N:=N,M:=N,side:=le_rfl,cut:=hp}).2))⟩⟩
  refine ⟨_,(Weighed.constant (menu X) hD).times (Weighed.power (menu X) (sh X) q),fun i=>?_⟩
  rw [Pi.mul_apply,Pi.pow_apply]; exact le_of_tendsto ((tendsto_const_nhds.sub (ht i)).norm) ((eventually_ge_atTop _).mono (he i i.N i.cut))
end pricing
-- actual Apex independent of auxiliary widths & E. Signatures.
section
variable (ν D' X H Ω h hD)
def zPlay (i : ℕ) : ReadsU F D R:= fun b k r=>apex (fun N=> stepboard X ν D' H Ω (d.le_succ.trans hD) h N i b k r)
def wPlay (i : ℕ) : ReadsU F D R:= fun b k r=>apex (fun N=> uprise (dance X ν D' N i) (stepboard X ν D' H Ω (d.le_succ.trans hD) h N (i+1)) b k r)
def glowSig (i:ℕ): Session (Letter F):= Matrix.of fun j k=> PowerSeries.mk (fun n=>apex (fun N=> hot (dice X ν D' H Ω (d.le_succ.trans hD) h N i) n j k))
def puffSig (i:ℕ): Session (Letter F):= Matrix.of fun j k=> PowerSeries.mk (fun n=>apex (fun N=> hot (dice X ν D' H Ω (d.le_succ.trans hD) h N i)⁻¹ n j k))
end
variable (he:Tights T S ν D' u)
include he
local notation "Ξ" => Xe (u:=u) T ν D'
local notation "♣" => Te (u:=u) T ν D'
local notation "Υ" => Ye (u:=u) X ν D' T
local notation "Ⓨ" => menu X
local notation "Δ" => chop X (1/4)
local notation "◆" => (zPlay X Ω ν D' H h hD)
lemma frozenY (hk:e≤E)(b:Letter F)(r): Twill Ⓨ Δ (fun i=> Υ i b e r) (fun i=>◆ i.i b e r) (fun i=> ώ T i.i) :=
   knit (U:= fun N i=> stepboard X ν D' H Ω _ h N i b e r) (σ:=ώ T) (fun _=> T.pos _) (yellow he hk b r)
lemma frozenX (hk:e≤E)(b:Letter F)(r): Twill Ⓨ Δ (fun i=> Ξ i b e r) (fun i=> wPlay X Ω ν D' H h hD i.i b e r) (fun i=> ώ T i.i) :=
   knit (U:=fun N i=> uprise (dance X ν D' N i) (stepboard X ν D' H Ω _ h N (i+1)) b e r) (σ:=ώ T) (fun _=>T.pos _) (xml he hk b r)
lemma frozenT (hk:e≤E) : Lying Ⓨ Δ (fun i=> hot (♣ i) e) (fun i=>hot (glowSig X Ω ν D' H h hD i.i) e) := by
  intro i j; have hx:= pine (B:=fun N k=> hot (dice X ν D' H Ω (d.le_succ.trans hD) h N k) e i j) (interlace he hk i j)
  simp_rw [glowSig,hot_node,Matrix.of_apply,PowerSeries.coeff_mk]; exact hx
lemma frozenB (hk:e≤E) : Lying Ⓨ Δ (fun i=> hot (♣ i)⁻¹ e) (fun i=>hot (puffSig X Ω ν D' H h hD i.i) e) := by
  intro i j; have hx:= pine (B:=fun N k=> hot (dice X ν D' H Ω (d.le_succ.trans hD) h N k)⁻¹ e i j) (cashOut he hk i j)
  simp_rw [puffSig,hot_node,Matrix.of_apply,PowerSeries.coeff_mk]; exact hx
end YM.RG08.Door
