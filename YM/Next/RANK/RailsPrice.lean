import YM.Next.RANK.Rails

/-!
# Choose price at one kpc consumption. Uniform even before period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.LiftMark
open Labels Lattice Wilson RG Normal Atlas Filter Perch Set Glimmer Price Rise Station MeasureTheory Tariffs
open scoped Topology BigOperators ContDiff Classical

variable {G : Gauge} {F : Family G} {k N p d : ℕ}

def shade (n : ℕ) := 1/(4*(n+2) : ℝ)
def tin (s : ℝ) (n : ℕ) := bill (shade n) s
lemma shade_pos (n : ℕ) : 0 < shade n := by unfold shade; positivity
lemma shade_thin (n : ℕ) : shade n*(n+2) ≤ 1/4 := by unfold shade; refine le_of_eq ?_; field_simp
lemma shaded (n : ℕ) : shade n ≤ 1/4 := by
  have h := shade_thin n; have hp : shade n≥0 := (shade_pos n).le; nlinarith
lemma tincost (s : ℝ) (n : ℕ) : 1≤tin s n := Glimmer.costed _ _ (shade_pos _).le

structure Sublevel (S : Levels G) (k d n : ℕ) (F : Frame G d) (c : ℝ) : Prop where
  coe : zonal F c
  numeric : 2*c*(bill (-1) (clim S k)+tin (clim S k) n*annuity (S.budget k).threshold (tin (clim S k) n) (bill (-1) (clim S k)) n) ≤ 1
  number :
    let B:= tin (clim S k) n
    B+B*(bill (-1) (clim S k)*(2*((n:ℝ)+2))^n) ≤ S.clock.monitor k


lemma booth (S : Levels G) (a : ℝ) (hg : G.Simple) : ∀ᶠ k in atTop,
    S.clock.threshold k ≤ bill (-a) (clim S k) := by
  -- t*p^a ≤ 1
  filter_upwards [(Station.hat_rate S hg).eventually (YM.Vac.Numbers.cost (1+a) (1/2:ℝ) (by norm_num))] with k h
  let s:=clim S k; have hn := zero_lt_one.trans (S.fits.delayed k)
  have hs : bill (1+a) s ≤ Real.sqrt s := by rw [Real.sqrt_eq_rpow]; rwa [YM.Vac.Numbers.P,← Real.exp_mul] at h
  apply le_of_mul_le_mul_right _ (Real.exp_pos (boil s*a)); change _*bill a s ≤ _*bill a s
  have he : 0 < Real.sqrt s := Real.sqrt_pos.2 hn
  calc
    _ = (Real.sqrt s)⁻¹ * bill (1+a) s := by rw [← overlap,← mul_assoc]; rw [← show S.clock.monitor k=bill 1 s from fire_bill S k];rfl
    _ ≤ 1 := (mul_le_mul_of_nonneg_left hs (inv_pos.mpr he).le).trans (by rw [inv_mul_cancel₀ he.ne'])
    _ ≤ _ := by change _≤bill (-a) s * bill a s; rw [overlap,neg_add_cancel,bill_zero]

lemma terms (S : Levels G) (h : G.Simple) (F : Frame G d) (n : ℕ) : ∀ᶠ k : ℕ in atTop, ∃ c, Sublevel S k d n F c := by
  obtain ⟨c,hc⟩ := Tariffs.zone_cost F; have hp := shaded n
  have he := shade_pos n; let a:=shade n
  have hv : a*(n:ℝ) ≤ 1/4 := by dsimp only [a]; linarith only [shade_thin n,he]
  have hh1 : -1+a*((n:ℝ)+2) < 0 := by dsimp only [a]; linarith only [shade_thin n]
  have hh2 : -1+a*((n:ℝ)+1)<0 := by dsimp only [a]; linarith only [he,shade_thin n]
  let A:= 2*((n:ℝ)+2)
  have hc' := hc.1; let K:= hat_rate S h
  filter_upwards [ K.eventually (transports hh1 (6*c*(n:ℝ)*(2:ℝ)^n)),
    K.eventually (transports hh2 (6*c*A^n)), K.eventually (transports (show a<1 by dsimp only [a]; linarith) (1+A^n)),booth S 1 h,K.eventually (transports (show (-1:ℝ)<0 by norm_num) (6*c))] with k h1 h2 h3 hx h4
  let s:=clim S k;let B:= tin s n;let e:= bill (-1) s; let v:=S.clock.threshold k
  rw [bill_zero] at h1 h2
  have hE : 0 ≤ B := zero_le_one.trans (tincost s n)
  refine ⟨c,hc,?_,?_⟩
  · have he : (n:ℝ)*(v*B)*(2*B)^n ≤ n*(e*B)*(2*B)^n := by apply mul_le_mul_of_nonneg_right _ (by positivity : 0 ≤ (2*B)^n); gcongr
    unfold annuity; change 2*c*(e+B*(n*(v*B)*(2*B)^n+e*A^n*B^n))≤1
    apply (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left (add_le_add_left he (e*A^n*B^n)) hE) e) (show 0≤2*c by positivity)).trans
    have hp : e*B^n*B*B=bill (-1+a*(n+2)) s := by
      dsimp only [B,e,tin]; rw [bills,overlap,overlap,overlap]; congr 1; unfold a; ring
    have ht : e*B^n*B=bill (-1+a*(n+1)) s := by
      dsimp only [B,e,tin]; rw [bills,overlap,overlap]; congr 1; unfold a; ring
    change 6*c*(n:ℝ)*2^n* _≤1 at h1; change 6*c*A^n* _≤1 at h2
    change _*bill _ s ≤ _ at h1 h2; rw [← hp] at h1; rw [← ht] at h2
    rw [mul_pow]; linarith only [h1,h2,(show 6*c*e≤1 from (h4.trans (bill_zero _).le))]
  change B+B*(e*A^n) ≤ S.clock.monitor k
  rw [fire_bill]
  apply le_trans _ h3; have ht : e ≤ 1 := by exact (billed s (by norm_num : (-1:ℝ) ≤ 0)).trans (bill_zero s).le
  change B+B*(e*A^n) ≤ (1+A^n)*B
  have hy : 0 ≤ A^n := by unfold A; positivity
  nlinarith only [mul_le_mul_of_nonneg_right ht (mul_nonneg hy hE)]

-- band conversion from original t.
lemma supports (n : ℕ) (F : Family G) (h : G.Simple) (H : F.Makes) : ∀ᶠ k in atTop,∀ N (_ : k ≤ N) p,
    let W:= F.path.levels
    let g:= GaugeScale F k N p
    let t:= W.clock.threshold k
    let s:= clim W k
    0 < g ∧ g ≤ t ∧
      ∀ X : Normal.Symmetric (trimV (wood W k) G), (∀ i j, ‖X.cov i j‖≤ tin s n) →
        ∀ i j, ‖(opq X (↑(t/g):ℂ)).cov i j‖≤ bill (-1) s := by
  let A:= F.path.levels
  have he := shade_pos n
  filter_upwards [(hat_rate A h).eventually (transports (show shade n<1 from lt_of_le_of_lt (shaded n) (by norm_num)) 4),
    (hat_rate A h).eventually ((bill_lo (a:=1) zero_lt_one).eventually_ge_atTop 2)] with k hc hv N hx p
  intro W g t s
  let a:= A.clock.hatBeta k; let b:= F.path.β N p k; let D:= A.clock.monitor k
  have ht : b ≥ a/2 := (H.wilson.represents N p k hx).band.1
  have hg : 0 < a := zero_lt_one.trans (A.fits.delayed k); have hp : 0<b := lt_of_lt_of_le (by positivity) ht
  have hT : 0< g := inv_pos.mpr (Real.sqrt_pos.2 hp)
  have hD := (show 2 ≤ D from (show D= _ from fire_bill A k) ▸ hv)
  have hh : 0<t := (W.budget k).threshold_pos
  have hB : g ≤ 2* (Real.sqrt a)⁻¹ := by
    change (Real.sqrt b)⁻¹ ≤ _; have ht' := Real.sqrt_pos.mpr hp; have hx' := Real.sqrt_pos.mpr hg
    field_simp; nlinarith only [ht, Real.sq_sqrt hp.le,Real.sq_sqrt hg.le,hx',ht']
  have ha : g*D ≤ 2*t := calc
    _ ≤ _ := mul_le_mul_of_nonneg_right hB (show 0≤D from (Real.exp_pos _).le)
    _ = 2*t := by rw [mul_assoc];rfl
  have he' : g ≤ t := by linarith only [ha,mul_le_mul_of_nonneg_left hD hT.le]
  refine ⟨hT,he',fun X h i j => ?_⟩
  let r:=t/g; have hr : 0<r := div_pos hh hT
  change ‖((↑r:ℂ)*(↑r:ℂ))⁻¹* X.cov i j‖ ≤ bill _ s
  have hf : D ≤ 2*r := (by unfold r; field_simp; linarith only [ha])
  have hh : bill 1 s * bill (-1) s=1 := by rw [overlap,add_neg_cancel,bill_zero]
  have hy : D * bill (-1) s=1 := show _ from (show D=_ from fire_bill A k) ▸ hh
  rw [norm_mul,norm_inv,norm_mul, Complex.norm_real,Real.norm_of_nonneg hr.le, ← div_eq_inv_mul,div_le_iff₀ (mul_pos hr hr)]
  refine (h i j).trans ?_
  have hT : 4*tin s n ≤ D := (show D=bill 1 s from fire_bill A k) ▸ hc
  have hp : D*D ≤ (2*r)*(2*r) := mul_le_mul hf hf (show 0≤D by linarith) (by positivity)
  have hY : 0 < bill (-1) s := Real.exp_pos _
  nlinarith only [hT,mul_le_mul_of_nonneg_left hp hY.le,congr_arg (·*D) hy]

-- Starting-phase stamp consumption.
theorem kpc (n : ℕ) (F : Family G) (h : G.Simple) (H : F.Makes) (d : ℕ) :
    ∀ᶠ k in atTop,∀ N p, k ≤ N →
      let S:= F.path.levels
      let s:= clim S k
      let B:= tin s n
      ∀ X : AtlasData G F.S p, ∀ L : Heater F k d,
        let Q := control X (k:=k) 0 (wood S k)
        (∀ i j, ‖Q.cov i j‖≤ B) → MarkedStart L Q n B (GaugeScale F k N p) (bill (-1) s) N p →
          ∃ T, Heating F k N p d n (Wick X L) T := by
  filter_upwards [terms F.path.levels h (F.labels.level d) n,supports n F h H] with k H1 H2 N p hn S s B X L Q H3 H4
  obtain ⟨c,hc⟩ := H1; obtain ⟨hg,ht,H⟩ := H2 _ hn p
  exact pins k N p d n X L c B (bill (-1) s) hc.coe (tincost ..) (Real.exp_pos _).le ((billed s (by norm_num : (-1:ℝ) ≤ 0)).trans (bill_zero s).le) hc.numeric hc.number _ hg rfl ht H4 (H Q H3)
end YM.Next.Rank.LiftMark
