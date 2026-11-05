import YM.Next.RANK.LineBox
import YM.Next.RANK.Peaks
import YM.Next.RANK.SolveRay



/-!
# Quantify discrepancy using weighted radial reads for SHORT and long H

Local extractors from old mask, on the true cubical origin. Long terms included in Taylor
bill but not with any `.PiVanish`. Functions along different real tests need not agree away
from the germ once supports and thresholds enter. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Spindle
open Lattice RG Wilson Source Labels Source.Drops Configuration Beamer Normal Rise Asymptotics Filter Set Function MvPolynomial MeasureTheory
open scoped Classical Matrix.Norms.Frobenius Topology ContDiff BigOperators

variable {G : Gauge} {n : Side} {o : Site n} {D R d : ℕ} (H : Hol G)


def south (o : Site n) (A : Snap G d) (t s : ℝ) := H.testLinks d o (expand d (t • A)) s

def spots {o : Site n} (h : 2*(R+1)<n.val) (p : RG.BudgetPoint) (A : Snap G d) (r : ℝ) : Space G o R := fun x => domain H R (register h x) A p.threshold r

lemma spots_read {o : Site n} (h : 2*(R+1)<n.val) (p : RG.BudgetPoint) (A : Snap G d) (r : ℝ) (x : Dim o R) :
    spots H h p A r x = wired p.threshold o R (south H o A p.threshold r) x := by
  unfold spots domain
  rw [Pi.smul_apply, comp_apply,Pi.smul_apply, ← flash_smul]
  unfold south wired; rw [feeling H _ _ r o h x]; unfold bore rock; rw [comp_apply,show H.links d _ r= _ from Source.Drops.scales ..]; rfl

lemma spots_cost {o : Site n} (h : 2*(R+1)<n.val) (p : RG.BudgetPoint) (A : Snap G d) (r : ℕ) :
    ContDiffAt ℝ r (spots (o:=o) H h p A) 0 ∧ spots (o:=o) H h p A 0=0 := by
  obtain ⟨C,v,hv,Hs⟩ := exact_turn H A r
  exact ⟨contDiffAt_pi.mpr (fun i => (Hs _ _ p.threshold_pos p.threshold_le (register h i)).1),funext fun i=> (Hs _ _ p.threshold_pos p.threshold_le (register h i)).2.2.1⟩

lemma spot_green {o : Site n} (h : 2*(R+1)<n.val) (p : RG.BudgetPoint) (A : Snap G d) : ∀ᶠ r : ℝ in 𝓝 0,
    Agrees (patch R o) (net p o R (spots H h p A r)) (spine (south H o A p.threshold r) o) := by
  let P r:= south H o A p.threshold r
  let W r:= spine (P r) o
  have hz (i : Dim o R) (r : ℝ) : G.mat (W r i.val)= rock H d R (register h i) (p.threshold • flash A r) := by
    unfold W P south; rw [feeling H _ _ r o h i, show H.links d _ r= _ from Source.Drops.scales .., ← flash_smul]; rfl
  have hh (i : Dim o R) : ∀ᶠ r : ℝ in 𝓝 0, G.lieExp (p.threshold • (spots H h p A r i)) = W r i.val := by
    have hi := shots H d 1
    let v (r : ℝ) := W r i.val
    -- derive Tendsto to 1 of mat from path representations G02.
    have he : AnalyticAt ℝ (rock H d R (register h i)) 0 := by
      let x:= register h i
      let e:= x.val
      -- simplify path product
      have hp : rock H d R x=fun y=> G.mat (travel (H.links d (expand d y) 1) 0 (paths e.1++[posDir e.2]++ Lattice.reverse (paths (e.1+step e.2)))) := by
        funext s; symm; rw [travel_append,travel_append,stops,stop_append, stops,travel,travel,mul_one,
          show stop (e.1:Cover) [posDir e.2]=e.1+step e.2 from rfl]; have hr := travel_reverse (x:=0) (paths (e.1+step e.2)) (H.links d (expand d s) 1); rw [stops] at hr; rw [hr]; rfl
      rw [hp]; exact (Work.G02.walkGerm H d _ _).1
    have hk (t : ℝ) : Tendsto (fun r => flash (t • A) r) (𝓝 0) (𝓝 0) := by simpa using (flashDiff (n:=1) (t•A)).continuous.tendsto 0
    have hg : Tendsto v (𝓝 0) (𝓝 1) := by
      apply ((G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.isInducing.tendsto_nhds_iff).2
      change Tendsto (fun r => G.mat (W r i.val)) _ _
      simp_rw [hz,G.mat_one,← flash_smul]
      simpa only [unroll] using! he.continuousAt.tendsto.comp (hk p.threshold)
    filter_upwards [hg.eventually G.plog_right] with r hr
    rw [spots_read, wired, smul_smul,mul_inv_cancel₀ p.threshold_pos.ne',one_smul]; exact hr
  filter_upwards [eventually_all.mpr hh] with r ha
  intro e he ht; let i:Dim o R:= ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ e,he,ht⟩⟩
  exact (net_in p _ i).trans (ha i)

-- at a physical support. Weighted error from polynomial vTest. No projecting H long.

def snips {o : Site n} (h : 2*(R+1)<n.val) (p : RG.BudgetPoint) (A : Snap G d) (x : links G o R) (r : ℝ) := (↑(scan (spots H h p A r) x):ℂ)
def tacks {o : Site n} (h : 2*(R+1)<n.val) (A : Snap G d) (x : links G o R) (r : ℝ) := ((probeLine H R (register h x.1) A r x.2):ℂ)

-- norm price
lemma shades (A : Snap G d) (m D : ℕ) :
    ∃ C : ℝ,∃ L : ℕ,0≤C ∧ ∀ (b : ℕ) (n : Side) (o : Site n) (h : 2*(b+1)<n.val) (p : RG.BudgetPoint),
      (∀ i,ContDiffAt ℝ m (snips (o:=o) H h p A i) 0) ∧ (∀ i,ContDiffAt ℝ m (tacks (o:=o) H h A i) 0) ∧
        ∀ (P : poly (links G o b)), totalDegree P≤ D →
          let c := coin P*C*(1+(b:ℝ))^L
          ‖evaluate_ray (walked (tacks H h A) P) m‖≤ c ∧
          ‖evaluate_ray (walked (snips H h p A) P) m-evaluate_ray (walked (tacks H h A) P) m‖≤ c*p.threshold := by
  obtain ⟨C,L,hc,HC⟩ := speech H A m
  obtain ⟨K,hK,HK⟩ := poetry m D
  refine ⟨(m+1:ℝ)*K*C^D,L*D,by positivity,fun b n o h p=>?_⟩
  have he (i : links G o b) := HC b p.threshold p.threshold_pos p.threshold_le (register h i.1) i.2
  let U:= snips (o:=o) H h p A
  let V:= tacks (o:=o) H h A
  let a:=1+(b:ℝ); have hv : 1 ≤ a := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hC : 1≤C*a^L := one_le_mul_of_one_le_of_one_le hc (one_le_pow₀ hv)
  refine ⟨fun i => (he i).1,fun i=> (he i).2.1,fun P hp=>?_⟩
  obtain ⟨hh,hv,ht⟩ := HK (links G o b) U V (C*a^L) p.threshold hC p.threshold_pos.le {
    east i := ⟨(he i).1,fun j h=> ((he i).2.2.2.2 j h).1⟩, west i := ⟨(he i).2.1,fun j h=> ((he i).2.2.2.2 j h).2.1⟩
    bar i := ⟨(by change ContDiffAt ℝ m (U i - V i) 0; exact ((he i).1).sub ((he i).2.1)),fun j h=> ((he i).2.2.2.2 j h).2.2⟩ } P hp
  refine ⟨(count_probe m _ hv).trans_eq ?_,?_⟩
  · unfold a; rw [mul_pow,pow_mul]; ring
  change ‖evaluate_ray (walked U P) m-evaluate_ray (walked V P) m‖≤ _
  rw [net_probe m hh.1 hv.1]; refine (count_probe m _ ht).trans_eq ?_; unfold a; rw [mul_pow,pow_mul]; ring

lemma genuine (x : Support n) (F : Config G n→ℂ) (p : RG.BudgetPoint) (a : ℂ) (T : poly (links G o R)) (S : Rules G)
    (Z : ℝ) (P : p.Regular x F) (hx : x ⊆ patch R o) (h : 2*(R+1)<n.val) (A : Snap G d) (hr : 0≤Z) (hd : d≤D) (hh : ∀ y,
      ‖y‖≤pane S→ ‖a*F (net p o R y)-text (scan y) T‖ ≤ Z* ‖y‖^(D+1)) :
    let W := walked (snips H h p A) T
    ContDiffAt ℝ d W 0 ∧ asym d ((fun r : ℝ=> a*F (south H o A p.threshold r))-W) := by
  obtain ⟨C,v,c,HC⟩ := shades H A d D
  let X:= spots (o:=o) H h p A
  intro W; obtain ⟨hf,ht⟩:= spots_cost H (o:=o) h p A 1
  have hv : Tendsto X (𝓝 0) (𝓝 0):= by rw [← show X 0=0 from ht]; exact hf.continuousAt.tendsto
  have he:= (show HasFDerivAt X _ 0 from (hf.differentiableAt one_ne_zero).hasFDerivAt).isBigO_sub
  obtain ⟨L,hL,HL⟩ := he.exists_pos
  refine ⟨walks _ _ (HC R n o h p).1 _, knock hd (error_power (Z*L^(D+1)) ?_)⟩
  filter_upwards [HL.bound,hv.eventually (Metric.ball_mem_nhds (0:Space G o R) (pane_pos S)),spot_green H (o:=o) h p A] with r hp hp' hR
  change ‖X r-X 0‖ ≤ L* ‖r-0‖ at hp; rw [show X 0=0 from ht,sub_zero,sub_zero] at hp
  let B:= south H o A p.threshold r
  change ‖a*F B-text (scan (X r)) T‖≤ _
  rw [show F B=F (net p o R (X r)) from (P.symmetry (fingers B o) B).symm.trans (P.sites _ _ (by intro i he hh; exact (hR i (hx he) (hx hh)).symm))]
  apply (hh _ (by rw [dist_zero_right] at hp'; exact le_of_lt hp')).trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hp _) hr).trans_eq ?_)
  ring
end YM.Next.Rank.Spindle
