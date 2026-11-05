import YM.RemainderComparison.Gaussian.Anchor
import YM.RemainderComparison.Gaussian.Lift

/-!
 # Analytic path/pack/test vertices from their stencil jets.

 `braces` BEFORE applying b^{-m}; can traverse even profile boundary. One
 uses the chart of the `T` output, in particular evaluations at distant z
 at b ≠ 0 unrestricted are not needed. Use AP for every core amplitude
 model H; Budget uses same `p,U,v` and μ independent of cutoff version.
 Keep exterior accounting and real `Life` tests separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Germ
open Matrix Filter Function Metric Set ProbabilityTheory MeasureTheory Finset
open Lattice RG Push.AbsoluteSums ConnectedActivityE6 Trace
open Coat PhysicalNext.Repeat Lantern Poll Blaze Brush
open scoped Topology BigOperators Classical NNReal ENNReal ContDiff
variable {G : Gauge} {L : Side} {p q : ℝ → ℝ}
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {E F H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {n j r m k : ℕ} {v u D d C A b : ℝ} {W : E × Poll.Body ι→F}
    {Q : E→Matrix ι ι ℝ} {ϕ ψ : E×Poll.Body ι→ ℝ} {ρ : E→ Poll.Body ι}
local notation "ℰ" => ℝ×E
local notation "Ξ" => Poll.Body ι

def usage (ρ : E→Poll.Body ι) (z : Poll.Body ι) (x : ℝ×E) : E × Poll.Body ι := Lantern.visit ρ z 1 (kite x)
def braces (W : E×Poll.Body ι→F) (ρ : E→Poll.Body ι) (j : ℕ) (D v u A : ℝ) : Prop:=
    ∀ x∈patch E v u,∀ z : Poll.Body ι,‖z‖ ≤ D → Brush j A 1 W (usage ρ z x)
def baggage (W : E×Poll.Body ι→F) (ρ : E→Poll.Body ι) (x : ℰ) (z:Ξ):= W (usage ρ z x)
def canopy' (j:ℕ) (D u C:ℝ):= Lantern.clump j (wind j u + wind j u) (spanE C D)
def vest (j:ℕ) (D u A C:ℝ):= Lantern.clump j (canopy' j D u C) A
local notation "₴" => vest
variable [FiniteDimensional ℝ E] [CompleteSpace F] [SecondCountableTopology F]
variable (h : Golf ϕ ψ ρ Q k D d d C)
include h
omit [FiniteDimensional ℝ E] in
lemma arrangement {q:ℝ×E} (hp : j≤k) (hv:v≤d) (ht:v*u≤d) (hx:q∈patch E v u) {z:Poll.Body ι} (hz:‖z‖ ≤ D) :
    Brush j (canopy' j D u C) 1 (usage ρ z) q:= by
  let p:= kite q; have hh: p∈patch E d d:= kite_moves hv ht hx
  have hq := (patch_test ..).1 hh
  exact composite ((aileron (v:=v) (hv.trans h.small) hx).2) (Lantern.camp ρ (t:=1) (by simp) (max_le (hq.1.le.trans h.small) (hq.2.le.trans h.small)) ((h.curve p.2 hq.2).smaller (by omega)) hz)
omit [FiniteDimensional ℝ E] [CompleteSpace F] in
lemma plank (hp : j≤k) (hz:0<v) (hv : v ≤ d) (ht : v*u ≤ d) (hu:0<u) (he : braces W ρ j D v u A) : Picture (baggage W ρ) D v u j (₴ j D u A C) := by
  have hx x (hx:x∈patch E v u) z (hz:‖z‖≤D): Brush j (₴ j D u A C) 1 (fun i=> W (usage ρ z i)) x:= composite (arrangement h hp hv ht hx hz) (he x hx z hz)
  let s:=closedBall (0:Ξ) D
  refine ⟨(hx (0,0) (show _∈patch E v u from ⟨mem_ball_self hz,mem_ball_self hu⟩) 0 (by simpa using h.off)).nonneg,fun x hx=> ?_,hx⟩
  let f (z:Ξ):=W (usage ρ z x)
  have hf:ContinuousOn f s := fun z hz=> by
    apply ContinuousAt.continuousWithinAt; exact (he _ hx z (mem_closedBall_zero_iff.mp hz)).smooth.continuousAt.comp (f:=fun i=>usage ρ i x) (show ContinuousAt (fun i=>usage ρ i x) z by unfold usage Lantern.visit; fun_prop)
  borelize F
  change StronglyMeasurable (s.indicator f)
  apply Measurable.stronglyMeasurable; apply measurable_of_restrict_of_restrict_compl (s:=s) measurableSet_closedBall
  · rw [show s.restrict (s.indicator f)=s.restrict f from funext fun i=> indicator_of_mem i.2 _]
    exact (continuousOn_iff_continuous_restrict.mp hf).measurable
  rw [show sᶜ.restrict (s.indicator f)=(fun _=>0) from funext fun i=> indicator_of_notMem i.2 _]
  exact measurable_const
-- expand at center only to enlarge moment cutoff. Need ball-continuity in all leg paths.
omit [FiniteDimensional ℝ E] [CompleteSpace F] [SecondCountableTopology F] in
lemma extra {u:ℝ} (hu:0<u) {c:ℝ} (hc:0<c) (he : Brush j A 1 W (0,ρ 0)) (R:ℝ) (hR : 0 ≤ R): ∃ v : ℝ, 0<v ∧ v ≤ c ∧ v*u ≤ c ∧ braces W ρ j R v u (A+1) := by
  obtain ⟨e,he',hE⟩:= Metric.mem_nhds_iff.mp (Trace.nearby he (lt_add_one A))
  obtain ⟨u',hu',hU⟩:= Metric.mem_nhds_iff.mp ((h.curve _ (show ‖(0:E)‖ < d from norm_zero.trans_lt h.pos)).smooth.continuousAt (ball_mem_nhds (ρ 0) (half_pos he')))
  let m:= min u' (min e c); have hm:0 < m:=lt_min hu' (lt_min he' hc)
  obtain ⟨v,hv,hK,hp⟩:= tiny_apron hm hu; let v':=min v (e/2/(1+R)); have hd: v'≤v := min_le_left ..
  have hb : v'*u ≤ c:= (mul_le_mul_of_nonneg_right hd hu.le).trans (hp.trans ((min_le_right ..).trans (min_le_right ..)))
  refine ⟨v',lt_min hv (by positivity), hd.trans (hK.trans ((min_le_right ..).trans (min_le_right ..))),hb,fun x hx z hz=> ?_⟩
  apply hE; have hs := (patch_test ..).1 hx
  let p:=kite x; have he : ‖p.2‖ < m:= (patch_test ..|>.1 (kite_moves hK hp (patch_mono hd le_rfl hx))).2
  rw [mem_ball_iff_norm]; unfold usage Lantern.visit; rw [one_smul]; change max ‖p.2-0‖ ‖ρ p.2+p.1 • z-ρ 0‖< e
  rw [sub_zero]; refine max_lt (he.trans_le ((min_le_right ..).trans (min_le_left ..))) ?_
  have ht: ‖ρ p.2-ρ 0‖<e/2:= mem_ball_iff_norm.mp (hU (mem_ball_zero_iff.mpr (he.trans_le (min_le_left ..))))
  have hf : ‖p.1 • z‖ ≤ e/2:= by
    have hu' : 0≤v':=(norm_nonneg _).trans hs.1.le
    rw [norm_smul]; exact (mul_le_mul hs.1.le (hz.trans (le_add_of_nonneg_left zero_le_one)) (norm_nonneg _) hu').trans ((le_div_iff₀ (by positivity : 0 < 1+R)).1 (min_le_right ..))
  rw [show ρ p.2+p.1 • z-ρ 0=(ρ p.2-ρ 0)+(p.1 • z) by abel]
  exact ((norm_add_le ..).trans_lt (add_lt_add_of_lt_of_le ht hf)).trans_le (add_halves _).le
omit h [FiniteDimensional ℝ E] [DecidableEq ι] in
lemma prolonged (hc: 0≤C) (hA:0≤A) (hu: 0≤u) (z:Ξ) : ₴ j ‖z‖ u A C ≤ ₴ j 1 u A C*vat j z := by
  let H:ℝ:= wind j u+wind j u; have hx:0 ≤ H:= by unfold H wind; positivity
  let c:= 1+‖z‖; have hz:1 ≤ c:= le_add_of_nonneg_right (norm_nonneg _)
  have hp: canopy' j ‖z‖ u C ≤ canopy' j 1 u C*c:= clump_ext _ _ hx (by unfold spanE; unfold c; nlinarith only [mul_nonneg hc (norm_nonneg z),norm_nonneg z])
  unfold vest; apply (le_trans (b:= Lantern.clump j (canopy' j 1 u C*c) A) _ (clump_stairs hz _ hA j))
  · unfold Lantern.clump; have h : 0≤ canopy' j ‖z‖ u C:= by unfold canopy' Lantern.clump spanE wind; positivity
    gcongr
  unfold canopy' Lantern.clump spanE wind; positivity
omit [FiniteDimensional ℝ E] [CompleteSpace F] in
lemma credit (hp : j≤k) (hz:0<v) (hv : v ≤ d) (ht : v*u ≤ d) (hu:0<u) (he : braces W ρ j D v u A) : Cloud (baggage W ρ) D v u j j (₴ j D u A C + ₴ j 1 u (A+1) (C+1)) := by
  have hc : (0,(0:E))∈patch E v u:= ⟨mem_ball_self hz,mem_ball_self hu⟩
  have hN: usage ρ (0:Ξ) (0,0)=(0,ρ 0):= by simp [usage,Lantern.visit,kite]
  have hW := he _ hc 0 (norm_zero.trans_le h.off)
  rw [hN] at hW; have hp':0≤A:= hW.nonneg
  have hC:0≤C:=(h.curve _ (show ‖(0:E)‖<d from norm_zero.trans_lt h.pos)).nonneg
  have hh (R:ℝ) (hR : 0≤ R) : ∃ v'>0, Picture (baggage W ρ) R v' u j (₴ j R u (A+1) (C+1)) := by
    obtain ⟨c,hc,H⟩:= larger h hR; obtain ⟨v',hv,hX,hT,hZ⟩:= extra h hu hc hW R hR; exact ⟨v',hv,plank H hp hv hX hT hu hZ⟩
  have hg := plank h hp hz hv ht hu he
  obtain ⟨b₁, - , hξ⟩:= hh 1 zero_le_one
  refine ⟨hg.mend le_rfl le_rfl le_rfl (le_add_of_nonneg_right hξ.expense),fun y hy z=> ?_,fun R hR=> let ⟨b,hb,hM⟩:= hh R hR; ⟨b,hb,_,hM⟩⟩
  obtain ⟨b,hb,H⟩:= hh ‖z‖ (norm_nonneg z)
  refine (H.budget (0,y) (show _ ∈patch E b u from ⟨mem_ball_self hb,mem_ball_zero_iff.mpr hy⟩) z le_rfl).climb ?_ le_rfl
  apply (prolonged (by positivity : 0≤C+1) (by positivity : 0 ≤ A+1) hu.le z).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hg.expense) (vat_nonneg _ _))

lemma scored (hp : j + m ≤ k) (hz:0<v) (hv : v ≤ d) (ht : v*u ≤ d) (hu:0<u) (he : braces W ρ (j+m) D v u A) (hr : ρ 0=0) (hn : cleared W m 0) :
    let n:= j+m; let Z := ₴ n D u A C+₴ n 1 u (A+1) (C+1)
    let p:= promote (baggage W ρ) m r
    Cloud p D v u j n ((3^j)^r*(Z+1)*3^j) ∧ ∀ a∈patch E v u, ∀ z,a.1≠0→ ‖z‖≤D →
      p a z=a.1^r • (a.1^m)⁻¹ • W (usage ρ z a) := by
  intro n Z p'; have H := credit h hp hz hv ht hu he
  refine ⟨promoted H (hv.trans h.small) r,fun x hx z he' hQ=> ?_⟩
  have hb : ((0:ℝ),x.2)∈patch E v u:= ⟨mem_ball_self hz,hx.2⟩
  have hg : usage ρ z (0,x.2)=0:= by unfold usage Lantern.visit kite; simp [hr]
  exact receipt H.toPicture hx he' hQ (chart_cleared W hn (show ContDiffAt ℝ m W 0 from hg ▸ ((he _ hb _ hQ).smaller (show m≤ j+m from Nat.le_add_left ..)).smooth) _ _ hg ((arrangement h (show m≤ k by omega) hv ht hb hQ).smooth))
end YM.RemainderComparison.Germ
