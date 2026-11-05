import YM.MergeProof.West.Cream
import YM.TraceExtension.Prom.Sway.Dol
import YM.TraceExtension.Prom.Sway.Sushi
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Tuning
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Atlas
open Lattice Wilson RG Station Set Labels Price Prayer Glimmer Rise Normal Function Filter Cells Perch  Beamer Configuration Marker Glyph Common Particle Read Exponential
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {C : Family G} {d k N p n : ℕ}

lemma coveredXSky {b : ℝ} (A : Levels G) (hb : 0<b) (h : G.Simple) {x : Points n} (hx : x∈conf _)
    {a : ℝ} (ha : 0 < a) (fκ : ℕ→ℕ) (hζ:Tendsto fκ atTop atTop)(px:ℕ → Points n) (I:ℕ→ℝ) (hD':∀ i,b ≤ I i) (zφ:Tendsto (fun i=> tested A (I i) (fκ i) (px i)) atTop (𝓝 x)) (i j : Fin n × KeyIn G d) : ∀ᶠ k in atTop, ∀ hf : FitSky A (I k) (fκ k) (px k), ‖(currentX (Ship.fittingSky hf) G d).cov i j‖ ≤ (1/2)*bill a (clim A (fκ k)) := by
  have he := ((lives i j) x hx).continuousAt ((conf_open n).mem_nhds hx); have hp := he.tendsto.comp zφ
  have hb := ((bill_lo ha).comp ((hat_rate A h).comp hζ)).const_mul_atTop (by norm_num : 0 < (1/2:ℝ))
  filter_upwards [hp.norm.eventually (ge_mem_nhds (lt_add_one ‖readsEach G d i j x‖)),hb.eventually_ge_atTop (‖readsEach G d i j x‖+1)] with k he ht hh
  exact (le_trans he ht)

lemma clockwiseXSky (D₀ : ℕ) {b : ℝ} (A : Levels G) (h : G.Simple) (hb : 0<b) (x : Points n) (hx : x∈conf _) (fκ : ℕ→ℕ) (hζ:Tendsto fκ atTop atTop)(px:ℕ → Points n) (I:ℕ→ℝ) (hD':∀ i,b ≤ I i) (zφ:Tendsto (fun i=> tested A (I i) (fκ i) (px i)) atTop (𝓝 x)) (d : ℕ) : ∀ᶠ k in atTop,∀ hp : FitSky A (I k) (fκ k) (px k),
    let s:=clim A (fκ k)
    Meridian (G:=G) d (Ship.fittingSky hp) (fraction n D₀ s) (fraction n D₀ s) (bill (-3) s) (bill (fuel D₀ n) s) (bill (-2) s) (Station.mag A (I k) (fκ k)) (lengthW s) := by
  obtain ⟨c,hc,he⟩ := sense G d; let ζ := fuel D₀ n
  have ht : 0<ζ := fuel_real D₀ n
  have hh : ζ≤1/4 := by dsimp only [ζ,fuel]; apply div_le_div_of_nonneg_left zero_le_one (by norm_num); push_cast;nlinarith
  have hec := (hat_rate A h).comp hζ
  have hz := transports (b:=ζ) (a:=3*ζ/4) (by linarith) 2
  filter_upwards [eventually_all.mpr fun i => eventually_all.mpr fun j => coveredXSky A hb h hx ht fκ hζ px I hD' zφ (G:=G) (d:=d) i j,
    hec.eventually (zone_power (d-1) (a:=ζ/4) (by linarith)), ( (bill_lo (a:=ζ/4) (by linarith)).comp hec).eventually_ge_atTop c, hec.eventually hz]
    with k H1 H2 H3 H4
  intro hp s
  have hs : fraction n D₀ s=bill (ζ/4) s := rfl
  let T := fraction n D₀ s; have hT : 1 ≤ T := Glimmer.costed (ζ/4) s (by linarith)
  have hz : 1 ≤ Station.mag A (I k) (fκ k) := by rw [mag_bill]; exact Glimmer.costed _ _ (hb.le.trans (hD' k))
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

end YM.Next.Rank.Atlas
namespace YM.Next.Rank.Prayer
open Function Set Lattice Wilson RG Normal Beamer Perch Configuration Glimmer Atlas Filter Station
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {P : Schedule} {A:Levels G} {d p k l n : ℕ}

lemma penaltyXSky (x : Points n) (hx : x∈conf n) (b : ℝ) (d : ℕ) (A : Levels G) (hB : G.Simple) (hb : 5≤ b) (fκ : ℕ→ℕ) (hζ:Tendsto fκ atTop atTop)(px:ℕ → Points n) (I:ℕ→ℝ) (hD':∀ i,b ≤ I i) (zφ:Tendsto (fun i=> tested A (I i) (fκ i) (px i)) atTop (𝓝 x)) :
    ∀ᶠ k in atTop, ∀ hp : FitSky A (I k) (fκ k) (px k), ∀ (i j : Fin n) (L S : Hub G d 0), i ≠ j →
      let T := tested A (I k) (fκ k) (px k); let r := mag A (I k) (fκ k)
      ‖amount r L.val * amount r S.val * mourn (gesture L.val) (gesture S.val) (collect d (Ship.fittingSky hp) r G i j) -
        light L.val S.val (T i) (T j)‖ ≤ bill (-4) (clim A (fκ k)) := by
  suffices H : ∀ᶠ k in atTop, ∀ (i j : Fin n) (L S : Hub G d 0), i≠j → ∀ hp : FitSky A (I k) (fκ k) (px k),
      let T := tested A (I k) (fκ k) (px k); let r := mag A (I k) (fκ k)
      ‖amount r L.val * amount r S.val * mourn (gesture L.val) (gesture S.val) (collect d (Ship.fittingSky hp) r G i j) -
        light L.val S.val (T i) (T j)‖ ≤ bill (-4) (clim A (fκ k)) from H.mono fun _ h hp i j L S hi => h i j L S hi hp
  refine eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_all.mpr fun L => eventually_all.mpr fun S => ?_
  have ht : 0 < b := by linarith
  obtain ⟨C,hc,he⟩ := fence (n:=n) L S
  let a := 1/(2:ℝ)
  have hg (v w : KeyIn G d) : ∀ᶠ k in atTop, ∀ p : FitSky A (I k) (fκ k) (px k),
      ‖(currentX (Ship.fittingSky p) G d).cov (i,v) (j,w)‖ ≤ a*bill a (clim A (fκ k)) := Atlas.coveredXSky A ht hB hx (by norm_num [a]) fκ hζ px I hD' zφ _ _
  filter_upwards [eventually_all.mpr fun v => eventually_all.mpr (hg v),((hat_rate A hB).comp hζ).eventually (transports (b:=b + -4) (show a<b + -4 by dsimp [a]; linarith) (C*a))]
    with k hv hh hi hp
  let s:= clim A (fκ k)
  intro T r
  have hr : 1 ≤ r := by dsimp only [r]; rw [mag_bill]; exact Glimmer.costed _ _ (ht.le.trans (hD' k))
  apply le_of_mul_le_mul_left _ (zero_lt_one.trans_le hr)
  refine (he T (Ship.fittingSky hp) i j hi (a*bill a s) (by unfold a bill; positivity) (fun p q => ?_) _ hr).trans ?_
  · exact (Complex.abs_re_le_norm _).trans (hv p q hp)
  change C*(a* _ ) ≤ r*_;rw [show r=_ from mag_bill A (I k) (fκ k),overlap,← mul_assoc]; exact hh.trans (billed _ (add_le_add_left (hD' k) _))
end YM.Next.Rank.Prayer
