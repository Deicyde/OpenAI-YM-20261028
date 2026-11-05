import YM.MergeProof.East.Chore
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.LiftMark
open Labels Lattice Wilson RG Normal Atlas Filter Perch Set Glimmer Price Rise Station MeasureTheory Tariffs
open scoped Topology BigOperators ContDiff Classical

variable {G : Gauge} {F : Family G} {k N p d : ℕ}

lemma terms_paySky (S : Levels G) (h : G.Simple) (F : Frame G d) (n : ℕ) (κ:ℝ)(hκ:0<κ) : ∀ᶠ k : ℕ in atTop, ∃ c, ExtraLevel S k d n F c (κ*bill (-1/2) (clim S k)) := by
  obtain ⟨c,hc⟩ := Tariffs.zone_cost F; have hp := shaded n
  have he := shade_pos n; let a:=shade n
  have hv : a*(n:ℝ) ≤ 1/4 := by dsimp only [a]; linarith only [shade_thin n,he]
  have hh1 : -1+a*((n:ℝ)+2) < -1/2 := by dsimp only [a]; linarith only [shade_thin n]
  have hh2 : -1+a*((n:ℝ)+1) < -1/2 := by dsimp only [a]; linarith only [he,shade_thin n]
  let A:= 2*((n:ℝ)+2)
  have hc' := hc.1; let K:= hat_rate S h
  filter_upwards [ K.eventually (transports' hh1 (6*c*(n:ℝ)*(2:ℝ)^n) hκ),
    K.eventually (transports' hh2 (6*c*A^n) hκ), K.eventually (transports' (show a< -1/2+1 by dsimp only [a]; linarith) (1+A^n) hκ),booth S 1 h,K.eventually (transports' (show (-1:ℝ) < -1/2 by norm_num) (6*c) hκ)] with k h1 h2 h3 hx h4
  let s:=clim S k;let B:= tin s n;let e:= bill (-1) s; let v:=S.clock.threshold k
  have hE : 0 ≤ B := zero_le_one.trans (tincost s n)
  refine ⟨c,hc,?_,?_⟩
  · have he : (n:ℝ)*(v*B)*(2*B)^n ≤ n*(e*B)*(2*B)^n := by apply mul_le_mul_of_nonneg_right _ (by positivity : 0 ≤ (2*B)^n); gcongr
    unfold annuity; change 2*c*(e+B*(n*(v*B)*(2*B)^n+e*A^n*B^n))≤ κ*bill (-1/2) s
    apply (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left (add_le_add_left he (e*A^n*B^n)) hE) e) (show 0≤2*c by positivity)).trans
    have hp : e*B^n*B*B=bill (-1+a*(n+2)) s := by
      dsimp only [B,e,tin]; rw [bills,overlap,overlap,overlap]; congr 1; unfold a; ring
    have ht : e*B^n*B=bill (-1+a*(n+1)) s := by
      dsimp only [B,e,tin]; rw [bills,overlap,overlap]; congr 1; unfold a; ring
    change 6*c*(n:ℝ)*2^n* _≤ κ*bill (-1/2) s at h1; change 6*c*A^n* _≤ κ*bill (-1/2) s at h2
    change _*bill _ s ≤ _ at h1 h2; rw [← hp] at h1; rw [← ht] at h2
    rw [mul_pow]; linarith only [h1,h2,h4]
  change B+B*(e*A^n) ≤ (κ*bill (-1/2) s)*S.clock.monitor k
  rw [fire_bill]
  apply le_trans _ (h3.trans_eq ?_); swap;
  · rw [mul_assoc,overlap]
  have ht : e ≤ 1 := by exact (billed s (by norm_num : (-1:ℝ) ≤ 0)).trans (bill_zero s).le
  change B+B*(e*A^n) ≤ (1+A^n)*B
  have hy : 0 ≤ A^n := by unfold A; positivity
  nlinarith only [mul_le_mul_of_nonneg_right ht (mul_nonneg hy hE)]

theorem kpc_plusSky (n : ℕ) (F : Family G) (h : G.Simple) (H : F.Makes) (d : ℕ) (κ:ℝ) (hκ:0<κ)(hw:κ ≤ 1) :
    ∀ᶠ k in atTop,∀ N p, k ≤ N →
      let S:= F.path.levels
      let s:= clim S k
      let B:= tin s n
      ∀ X : AtlasData G F.S p, ∀ L : Heater F k d,
        let Q := control X (k:=k) 0 (wood S k)
        (∀ i j, ‖Q.cov i j‖≤ B) → MarkedStart L Q n B (GaugeScale F k N p) (bill (-1) s) N p →
          ∃ T, LCheque k N p d n (Wick X L) T (κ*bill (-1/2) s) := by
  filter_upwards [terms_paySky F.path.levels h (F.labels.level d) n κ hκ,supports n F h H] with k H1 H2 N p hn S s B X L Q H3 H4
  obtain ⟨c,hc⟩ := H1; obtain ⟨hg,ht,H⟩ := H2 _ hn p
  exact pins_extra k N p d n X L c B (bill (-1) s) hc.coe (tincost ..) (Real.exp_pos _).le ((billed s (by norm_num : (-1:ℝ) ≤ 0)).trans (bill_zero s).le) _ (mul_le_one₀ hw (Real.exp_pos _).le ((billed _ (by norm_num : (-1/2:ℝ) ≤ 0)).trans (bill_zero _).le)) hc.numeric hc.number _ hg rfl ht H4 (H Q H3)
end YM.Next.Rank.LiftMark
