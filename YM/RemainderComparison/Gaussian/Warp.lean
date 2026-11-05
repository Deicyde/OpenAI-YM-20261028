import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lantern.Predict
import YM.RemainderComparison.Gaussian.Album

/-!
 # Stationary analytic jet budget on the common chart.

 Variable `b` extends here through zero on the reference chart only.
 At zero insertion, unrestricted Z growth proven here from the same
 P.Gram station, NOT an assumption that the interacting integrand
 at actual b is bounded on unrestricted Z's. Determinants in `grace`
 use real Hermitian covariance. Pre-kernel factor left unevaluated.
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
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n j : ℕ} {v u D d x e c C A B : ℝ} {Q : E → Matrix ι ι ℝ} {ρ : E→Body ι} {ϕ ψ:E×Body ι→ℝ}
local notation "ℰ" => ℝ×E
local notation "Ξ" => Poll.Body ι

def kite (x:ℰ): ℰ:= (x.1,x.1 • x.2)
lemma kite_moves {x:ℰ} (hv :v ≤ B) (hp:v*u ≤ B) (ha:x∈patch E v u) : kite x∈patch E B B:= by
  have h :=(patch_test ..).1 ha
  refine (patch_test ..).2 ⟨h.1.trans_le hv,?_⟩
  unfold kite; dsimp only; rw [norm_smul]
  exact lt_of_lt_of_le (mul_lt_mul' h.1.le h.2 (norm_nonneg _) (patch_zero ha).1) hp -- edit

def wind (j : ℕ) (u : ℝ) := 1*(1+u)*3^j
lemma aileron {x : ℰ} (hv : v ≤ 1) (hp:x∈patch E v u) :
    Brush j (wind j u) 1 (Prod.snd ∘ kite) x ∧ Brush j (wind j u+wind j u) 1 kite x := by
  obtain ⟨hy,hx⟩:= (patch_test ..).1 hp
  have he:= Trace.left_age (j:=j) (hy.le.trans hv)
  have hk : 0≤ u:=(norm_nonneg _).trans hx.le
  have hh : Brush j (1+u) 1 (fun x:ℰ=> x.2) x:= Brush.linearB (ContinuousLinearMap.snd ℝ ℝ E) (u:=1+u) (d:=1) (by change ‖x.2‖≤_; exact hx.le.trans (le_add_of_nonneg_left zero_le_one)) (by rw [mul_one]; exact le_trans (ContinuousLinearMap.norm_snd_le ..) (le_add_of_nonneg_right hk)) zero_le_one
  have h := Trace.paint he hh
  refine ⟨h,(he.climb (show (1:ℝ)≤wind j u from ?_) le_rfl).pair h⟩
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le le_rfl (le_add_of_nonneg_right hk)) (one_le_pow₀ (by norm_num))
lemma tiny_apron (hc : 0<A) (hu : 0<u): ∃ B:ℝ, 0<B ∧ B ≤ A ∧ B*u ≤ A := by
  refine ⟨min A (A/u),lt_min hc (div_pos hc hu),min_le_left .., (le_div_iff₀ hu).1 (min_le_right ..)⟩

section extend
variable (h : Golf ϕ ψ ρ Q j D d d C)
include h
lemma larger {M : ℝ} (hp : 0≤M) : ∃ c:ℝ, 0<c ∧ Golf ϕ ψ ρ Q j M c c (C+1) := by
  have hd : ‖(0:E)‖ < d:= by rw [norm_zero]; exact h.pos
  obtain ⟨hx,hX⟩:= h.color 0 0 (0,(0:E)) (show ‖(0:Ξ)‖ ≤ D from (norm_zero).trans_le h.off) (by simp) (show ‖(0:ℝ)‖<d from norm_zero.trans_lt h.pos') hd
  rw [show Lantern.visit ρ 0 0 (0,0)= (0,ρ 0) from (by simp [Lantern.visit])] at hx hX
  obtain ⟨e,he,hE⟩:=Metric.mem_nhds_iff.mp ((Trace.nearby hx (lt_add_one C)).and (Trace.nearby hX (lt_add_one C)))
  obtain ⟨q,hq,hQ⟩:=Metric.mem_nhds_iff.mp ((h.curve _ hd).smooth.continuousAt.eventually (ball_mem_nhds (ρ 0) (half_pos he)))
  let m:= min (min d e) q; let c:= min m (e / 2 / (1+M))
  have ht: 0 < c:= lt_min (lt_min (lt_min h.pos he) hq) (by positivity)
  have hl : c ≤ min d e:= (min_le_left ..).trans (min_le_left ..); have hs : c ≤ d:=hl.trans (min_le_left ..); have hN: C ≤ C+1:= by linarith
  refine ⟨c,ht,ht,ht,hs.trans h.small,hs.trans h.small,hp,fun x hx=> (h.curve _ (hx.trans_le hs)).climb hN le_rfl,fun z t y hz hi hy hZ=> ?_,fun x hx=> h.station x (hx.trans_le hs),fun x hx=> ⟨(h.gram x (hx.trans_le hs)).1, ((h.gram x (hx.trans_le hs)).2).climb hN le_rfl⟩⟩
  apply hE; unfold Lantern.visit; rw [mem_ball_iff_norm]; change max ‖y.2-0‖ ‖ρ y.2+t • y.1 • z-ρ 0‖ < e
  rw [sub_zero]; refine max_lt (hZ.trans_le (hl.trans (min_le_right ..))) ?_
  have ht:‖ρ y.2-ρ 0‖ < e/2:= mem_ball_iff_norm.mp (hQ (mem_ball_zero_iff.mpr (hZ.trans_le ((min_le_left ..).trans (min_le_right ..)))))
  have hx : ‖t • y.1 • z‖ ≤ e/2:= by
    rw [norm_smul,Real.norm_of_nonneg hi.1]; apply (mul_le_of_le_one_left (norm_nonneg _) hi.2).trans
    rw [norm_smul]; exact (mul_le_mul hy.le (hz.trans (le_add_of_nonneg_left zero_le_one)) (norm_nonneg _) (by linarith only [norm_nonneg y.1,hy])).trans ((le_div_iff₀ (by positivity : 0 < 1+M)).1 (min_le_right ..))
  rw [show ρ y.2+t • y.1 • z-ρ 0=ρ y.2-ρ 0+t • y.1 • z by abel]
  exact ((norm_add_le ..).trans_lt (add_lt_add_of_lt_of_le ht hx)).trans_le (le_of_eq (add_halves e))
end extend

-- keep explicit orders in Bucket estimate for POLY projection
lemma clump_ext (j:ℕ) (a : ℝ) (hp : 0 ≤ B) (he : A ≤ C*a) : Lantern.clump j B A ≤ Lantern.clump j B C*a := by
  unfold Lantern.clump
  rw [mul_right_comm (((Nat.factorial j):ℝ)*C),mul_assoc ((Nat.factorial j:ℝ)) C a]; gcongr
lemma widening (hf: 1 ≤ e) (h:0 ≤ d) (hp:d ≤ e) (he : 0 ≤ C) :
    fee j C d ≤ fee j C 1 * e^(j+2):= by
  let b:= spanE C 1; let p:= spanE C d
  have hx : 0≤b := by unfold b spanE; positivity
  have hy : p≤b*e:= by
    unfold p b spanE; nlinarith only [hp,hf,mul_le_mul_of_nonneg_left hf he]
  have hz : 0 ≤ clump j b C:= by unfold clump; positivity
  have ht : clump j p C ≤ clump j b C * e^j := by
    have hh : 0≤p:=by unfold p spanE; positivity
    refine le_trans (b:=clump j (b*e) C) ?_ (clump_stairs hf hx he j)
    unfold clump; gcongr
  have he' : acrossE j C d ≤ acrossE j C 1*e^(j+2):= by
    unfold acrossE
    refine le_trans (b:= e*(e*(clump j b C* e^j))) ?_ (le_of_eq ?_)
    · have hp':0 ≤ clump j (spanE C d) C:= by unfold clump spanE; positivity
      gcongr -- edit
    unfold b; ring
  unfold fee; rw [add_mul,add_mul,add_mul,add_mul,add_mul]
  have hh := ht.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hf (Nat.le_add_right j 2)) hz)
  exact add_le_add (add_le_add (by have h := le_mul_of_one_le_right he (one_le_pow₀ hf (n:=j+2)); linarith) (by linarith)) (by unfold b p at *; linarith)

def coloring (ϕ ψ:E×Body ι→ℝ) (ρ : E→Body ι) (Q:E→Matrix ι ι ℝ) (x:ℝ×E) (z:Body ι) := grace ϕ ψ ρ Q z (kite x)
local notation "₣" => coloring ϕ ψ ρ Q

def canopy (j:ℕ) (D u C:ℝ) := Lantern.clump j (wind j u+ wind j u) (fee j C D)
variable [FiniteDimensional ℝ E]
variable (h : Lantern.Golf ϕ ψ ρ Q j D d d C) (hv : v ≤ d) (ha : v*u ≤ d) (hu : 0<u)
include h hv ha hu
lemma framing : Picture ₣ D v u j (canopy j D u C):= by
  let s:= closedBall (0:Ξ) D
  have hf x (hx:x∈patch E v u):= (patch_test ..).1 (kite_moves hv ha hx)
  have hd := h.off; have hp : 0≤C:= (h.curve _ (show ‖(0:E)‖<d from norm_zero.trans_lt h.pos)).nonneg
  refine ⟨by unfold canopy fee acrossE spanE Lantern.clump wind; positivity, fun x hx=> ?_,fun y hy z hz=> composite ((aileron (j:=j) (hv.trans h.small) hy).2) (compel D h (hf _ hy).2 (hf _ hy).1 hz)⟩
  let f z:= coloring ϕ ψ ρ Q x z
  have hp : ContinuousOn f s:= gallon D h (hf x hx).2 (hf x hx).1
  apply Measurable.stronglyMeasurable
  apply measurable_of_restrict_of_restrict_compl (s:=s) measurableSet_closedBall
  · rw [show s.restrict (s.indicator f)=s.restrict f from funext fun i=> indicator_of_mem i.2 _]
    exact (continuousOn_iff_continuous_restrict.mp hp).measurable
  rw [show sᶜ.restrict (s.indicator f)=(fun _=>0) from funext fun i=> indicator_of_notMem i.2 _]
  exact measurable_const

lemma far_closure : Cloud ₣ D v u j (j+2) (canopy j D u C+canopy j 1 u (C+1)) := by
  have hp:= framing h hv ha hu; have hC:0≤C:= (h.curve _ (show ‖(0:E)‖ < d from norm_zero.trans_lt h.pos)).nonneg
  have he:0≤canopy j 1 u (C+1):= by unfold canopy fee acrossE spanE Lantern.clump wind; positivity
  refine ⟨hp.mend le_rfl le_rfl le_rfl (le_add_of_nonneg_right he), fun x hx z=>?_,fun R hR=>?_⟩
  · obtain ⟨d',hd,hD⟩:= larger h (norm_nonneg z); obtain ⟨ε,hε,hv,hp'⟩:= tiny_apron hd hu
    have hh := framing hD hv hp' hu |>.budget (0,x) (show _∈patch E ε u from (patch_test ..).2 ⟨norm_zero.trans_lt hε,hx⟩) z le_rfl
    apply hh.climb _ le_rfl; have hb:1 ≤ 1+‖z‖:= le_add_of_nonneg_right (norm_nonneg _)
    refine le_trans (b:=canopy j 1 u (C+1) * vat (j+2) z) (clump_ext _ _ ?_ (widening hb (norm_nonneg _) (le_add_of_nonneg_left zero_le_one) (by positivity : 0 ≤ C+1))) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hp.expense) (vat_nonneg ..))
    unfold wind; positivity
  obtain ⟨d',hd,hD⟩:= larger h hR; obtain ⟨ε,hε,hv,hp⟩:= tiny_apron hd hu; exact ⟨_,hε,_,framing hD hv hp hu⟩
end YM.RemainderComparison.Germ
