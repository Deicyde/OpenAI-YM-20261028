import YM.Next.RANK.Allowance
import YM.Next.RANK.ParticleGate
import YM.Next.RANK.Prayer

/-!
# Supplies use frame costs; compare actual coordinates using moment estimates
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Atlas
open Lattice Wilson RG Station Set Labels Price Prayer Glimmer Rise Normal Function Filter Cells Perch  Beamer Configuration Marker Glyph Common Particle Read Exponential
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {C : Family G} {d k N p n : ℕ}

-- free entry bounded on all used x, independent of tiling and perturbations. actual normalized derivative via standard and smooth.

def pointwise (x : Points n) : Fin n × Maxwell.Slot G → Fin n × Maxwell.Slot G → ℂ := fun i j => if i.1 = j.1 then 0 else Maxwell.Wick.entry i.2 j.2 (x i.1) (x j.1)

def readsEach (G : Gauge) (d : ℕ) (i j : Fin n × KeyIn G d) :=
    let f := Normal.perSlot (fun _ : Fin n => mapper (G:=G) (d:=d))
    fun x : Points n => Finsupp.linearCombination ℂ ((Finsupp.linearCombination ℂ (pointwise x)) (f i)) (f j)

lemma lives (i j : Fin n × KeyIn G d) : ContinuousOn (readsEach G d i j) (conf n) := by
  have he (i j : Fin n × Maxwell.Slot G) : ContinuousOn (fun x : Points n => pointwise x i j) (conf n) := by
    intro x hx
    unfold pointwise; split
    · exact continuousWithinAt_const
    rename_i ht
    have hk := (Maxwell.Wick.entry_smooth (x:=(x i.1,x j.1)) i.2 j.2 ((show Function.Injective x.ofLp from hx).ne ht)).continuousAt
    exact (hk.comp (f:=fun x : Points n => (x i.1,x j.1)) (by fun_prop)).continuousWithinAt
  unfold readsEach
  simp only [Finsupp.linearCombination_apply,Finsupp.sum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply continuousOn_finsetSum _; intro k hk; refine continuousOn_const.mul (continuousOn_finsetSum _ fun z _ => continuousOn_const.mul (he z k))

lemma covered {b : ℝ} (A : Levels G) (hb : 0<b) (h : G.Simple) {x : Points n} (hx : x∈conf _)
    {a : ℝ} (ha : 0 < a) (i j : Fin n × KeyIn G d) : ∀ᶠ k in atTop, ∀ hf : Fit A b k x, ‖(currentX (Ship.fitting hf) G d).cov i j‖ ≤ (1/2)*bill a (clim A k) := by
  have he := ((lives i j) x hx).continuousAt ((conf_open n).mem_nhds hx); have hp := he.tendsto.comp (tuning A x h hb)
  have hb := ((bill_lo ha).comp (hat_rate A h)).const_mul_atTop (by norm_num : 0 < (1/2:ℝ))
  filter_upwards [hp.norm.eventually (ge_mem_nhds (lt_add_one ‖readsEach G d i j x‖)),hb.eventually_ge_atTop (‖readsEach G d i j x‖+1)] with k he ht hh
  exact (le_trans he ht)

def fraction (n k : ℕ) (s : ℝ) := bill (fuel k n/4) s

lemma clockwise (D₀ : ℕ) {b : ℝ} (A : Levels G) (h : G.Simple) (hb : 0<b) (x : Points n) (hx : x∈conf _) (d : ℕ) : ∀ᶠ k in atTop,∀ hp : Fit A b k x,
    let s:=clim A k
    Meridian (G:=G) d (Ship.fitting hp) (fraction n D₀ s) (fraction n D₀ s) (bill (-3) s) (bill (fuel D₀ n) s) (bill (-2) s) (Station.mag A b k) (lengthW s) := by
  obtain ⟨c,hc,he⟩ := sense G d; let ζ := fuel D₀ n
  have ht : 0<ζ := fuel_real D₀ n
  have hh : ζ≤1/4 := by dsimp only [ζ,fuel]; apply div_le_div_of_nonneg_left zero_le_one (by norm_num); push_cast;nlinarith
  have hec := hat_rate A h
  have hz := transports (b:=ζ) (a:=3*ζ/4) (by linarith) 2
  filter_upwards [eventually_all.mpr fun i => eventually_all.mpr fun j => covered A hb h hx ht (G:=G) (d:=d) i j,
    hec.eventually (zone_power (d-1) (a:=ζ/4) (by linarith)), ( (bill_lo (a:=ζ/4) (by linarith)).comp hec).eventually_ge_atTop c, hec.eventually hz]
    with k H1 H2 H3 H4
  intro hp s
  have hs : fraction n D₀ s=bill (ζ/4) s := rfl
  let T := fraction n D₀ s; have hT : 1 ≤ T := Glimmer.costed (ζ/4) s (by linarith)
  have hz : 1 ≤ Station.mag A b k := by rw [mag_bill]; exact Glimmer.costed _ _ hb.le
  have hB : T*T*T ≤ (1/2)*bill ζ s := by
    change 2*bill _ s ≤ bill _ s at H4
    rw [show T= _ from hs,overlap,overlap,show ζ/4 + ζ/4 + ζ/4=3*ζ/4 by ring]; linarith only [H4]
  have hC : 0<bill ζ s := Real.exp_pos _
  refine ⟨hz,zero_le_one.trans hT,zero_le_one.trans hT,(Real.exp_pos _).le,Glimmer.costed _ s ht.le, fun i => (he _).trans H3,H2,
    ?_,?_,?_,fun i j => ?_, by linarith only [hB,hC]⟩
  · apply (le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans hT) (zero_le_one.trans hT)) hT).trans; linarith only [hB,hC]
  · rw [hs, overlap, overlap]; apply billed; linarith only [hh]
  · rw [hs,overlap]; apply billed; linarith only [hh]
  change ‖_‖+T*T*T ≤ bill ζ s; linarith only [show ‖_‖≤(1/2)*bill ζ s from H1 i j hp,hB]

-- uniform over all st probes within finite frame d. Consume once at probe.
def passing (u : Fin n → C.label d) (k degree : ℕ) (b : ℝ) :=
    let Y:= C.path.levels
    let s := clim Y k; let ρ:= Station.mag Y b k
    let ply:= lengthW s
    let F:= fun i => (C.labels.level d).coords.symm (u i)
    let I:= (Subtype.val : trimV ply G → _)
    ∀ N (p : ℕ) (_ : k≤N) M T, Heating C k N p d degree M T → ∀ v : Fin n → C.label d, (∀ i : Fin n, Price.Solves C ρ d k N p T (u i) (v i)) →
      ∃ X : Spend n degree, X.B=bill (fuel degree n) s ∧ X.collision=bill (-2) s ∧ X.cost=bill (-3/2) s ∧
        Tolls X (fun _ : Fin n => features d I ρ) (fun i => M (v i)) F ρ (bill (b*d+saves C d) s) (bill (fuel degree n) s)

lemma passing_all (h : G.Simple) (hp : C.Makes) (degree : ℕ) (u : Fin n → C.label d) (b : ℝ) (hb : 0<b)
    (hw : Atlas.saves C d+3 ≤ b) : ∀ᶠ k in atTop, passing u k degree b := by
  let Y:= C.path.levels
  let F := fun i => (C.labels.level d).coords.symm (u i)
  let v := fun i => thawKey (F i)
  let A := (∑ i, Rise.coin (v i))+1
  have hh (i) : 0 ≤ coin (v i) := Rise.sign _ _ zero_le_one
  have hz : 1 ≤ A := by unfold A; linarith only [show 0 ≤ ∑ i, coin (v i) from Finset.sum_nonneg fun i _ => hh i]
  filter_upwards [eventually_all.mpr (fun i => love b hb h hp (u i)),(hat_rate Y h).eventually (shed n degree A hz), (hat_rate Y h).eventually (radiant (G:=G) (d:=d) (n:=n) degree)] with k h1 h2 h3
  obtain ⟨Q,hξ,hb₁,hP,hB,hc⟩ := h2
  intro N p hk M T H v₀ he
  let s:= clim Y k; let ρ:= mag Y b k
  have he' : 1 ≤ ρ := by unfold ρ;rw [mag_bill]; exact Glimmer.costed _ _ hb.le
  let I := (Subtype.val : trimV (lengthW s) G→ Address G)
  refine ⟨Q,hB,hP,hc, ⟨he', fun i => h1 i _ _ hk degree M T H (v₀ i) (he i), fun i => H.order _, fun i => ?_, fun _ z => ?_,Glimmer.costed _ _ (fuel_real degree n).le,fun i => ?_,?_⟩⟩
  · rw [hb₁]; exact (Finset.single_le_sum (f:=fun i => coin (v i)) (fun i _ => hh i) (Finset.mem_univ i)).trans (le_add_of_nonneg_right zero_le_one)
  · exact h3 _ I ρ he' z ((tracing _ _).mp z.property)
  · exact Perch.aligned I ρ (zero_lt_one.trans_le he') (he i) (M _) (H.test _)
  rw [hξ]; change _ ≤ _* (Station.mag Y b k)^(d+1); rw [mag_bill]; exact Glimmer.ticket degree n d (Atlas.saves C d) b hw s
end YM.Next.Rank.Atlas
