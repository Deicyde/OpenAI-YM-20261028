import YM.Next.RANK.Rails

/-!
# KPC projection lemma

Seek data from the true origin k transport. Primary polynomial seed costs before
forming Wick calibration operator, in $t/g$ weights on each independent variable.
Orientation assumptions separate: test at 0 unscaled still in invariant sector
and star lifts. Vacuum unit label covariance means B₀ unit exact. Retains reference
cost covariance through $N$. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.LiftMark
open Labels Lattice Wilson RG Normal Atlas Perch Price Beamer Configuration Glimmer Rise Filter MvPolynomial Tariffs
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {F : Family G} {k N p d n : ℕ}


structure LCheque (k N p d n:ℕ)(L: Heater F k d) (P: F.label d→ₗ[ℂ] F.label d)(κ:ℝ):Prop where
   heats : Heating F k N p d n L P
   credit (x:F.label d): let t:=awake F d k N p x;let D:=F.labels.level d;D.coeffSize (t-P x) ≤ κ*D.coeffSize t/2
   bill_ (x:F.label d) : coin (L x) ≤ κ*F.path.levels.clock.monitor k * (F.labels.level d).coeffSize (Price.awake F d k N p x)

theorem pins_extra (k N p d n : ℕ) (X : AtlasData G F.S p) (L : Heater F k d) (c B ε : ℝ) (hc : zonal (F.labels.level d) c)
    (hB : 1 ≤ B) (he : 0 ≤ ε) (hε : ε ≤ 1)
    (κ : ℝ) (hκ: κ ≤ 1) (hu : let t := F.path.levels.clock.threshold k; 2*c*(ε+B*annuity t B ε n) ≤ κ)
    (hb : B + B*(ε*(2*((n:ℝ)+2))^n) ≤ κ*F.path.levels.clock.monitor k)
    (g : ℝ) (h : 0<g) (hg : g=GaugeScale F k N p) (h' : g ≤ F.path.levels.clock.threshold k)
    (hM : MarkedStart L (control X (k:=k) 0 _) n B g ε N p)
    (hC : ∀ i j, let t:= F.path.levels.clock.threshold k; ‖(opq (control X (k:=k) 0 (wood F.path.levels k)) (↑(t/g):ℂ)).cov i j‖ ≤ ε) :
    ∃ P, LCheque k N p d n (Wick X L) P κ := by
  let F':= F.labels.level d; let H:= control X (k:=k) 0 (wood F.path.levels k)
  let t:= F.path.levels.clock.threshold k
  have ht := (show 0<t from (F.path.levels.budget k).threshold_pos); let z:= t/g
  have hz : 1 ≤ z := (le_div_iff₀ h).2 (by rwa [one_mul]); have hz' := zero_lt_one.trans_le hz
  have hx : shrink F k N p=z⁻¹ := by change _=(t/g)⁻¹; rw [inv_div,hg]; rfl
  obtain ⟨H1,H2,H3,A,D,H4⟩ := hM
  let P := (expose F').leftInverse.comp (printed (Wick X L)); let T:= F'.scaled z ∘ₗ P
  have hE := LinearMap.ker_eq_bot.mpr (exposed F')
  have hw v : expose F' (P v)= printed (Wick X L) v := by
    obtain ⟨i,h,-⟩ := H3 v; change printed (Wick X L) v= expose F' i at h; dsimp only [P, LinearMap.comp_apply]; rw [h, LinearMap.leftInverse_apply_of_inj hE]
  let Q:= opq H (↑z:ℂ)
  have hA := (F.path.levels.budget k).threshold_le
  have hY : 0 ≤ (2*((n:ℝ)+2))^n := by positivity
  let f := faceTest F d k
  let w:= key G d
  have hI v : factors (↑z:ℂ) (Wick X L v)=milk Q (factors (↑z:ℂ) (L v)) := blend_up H _ (Complex.ofReal_ne_zero.mpr hz'.ne') (L v)
  have hs v : totalDegree (factors (↑z:ℂ) (L v)) ≤ n := (factor_degree ..).trans (H2 v).1
  have hu' := hc.1; have h₀ := zero_lt_one.trans_le hB
  have Hβ : 0≤ annuity t B ε n := by unfold annuity; positivity
  have h_credit (v): let t':=awake F d k N p v; F'.coeffSize (t'-T v) ≤ κ* F'.coeffSize t'/2:=by
    intro a
    let x:= awake F d k N p v
    let q := factors (↑z:ℂ) (L v)
    have hp := H2 v; have hzv:= (stock t B ε (P:=q) (K:=Q) _ A ht hA hB D (hs v) he hε hC).2
    have ht' : expose F' (T v)= trim (exchange f (milk Q q)) w d := by
      change thawKey (F'.coords.symm (F'.scaled z (P v)))=_
      rw [weighed_in,← expose_at,hw]; change factors (↑z:ℂ) (trim (exchange _ (Wick X L v)) _ _)=_
      rw [← trim_factor, sprinkle, hI v]
    let Hx:= trim (garnish A f t q) w d
    let Hy:= trim (exchange f (milk Q q)) w d
    change F'.coeffSize (x- T v)≤ _
    let b:= F'.coeffSize x
    have h1 : coin (expose F' x-Hx) ≤ b*ε := H4 v
    have h2 : coin (Hx-Hy)≤ coin q* annuity t B ε n := by dsimp only [Hx,Hy]; rw [← trim_sub]; exact (trims 1 zero_le_one ..).trans hzv
    apply (hc.2 _).trans; rw [map_sub, ht']; change c * coin (expose F' x-Hy) ≤ _; rw [show expose F' x-Hy= expose F' x-Hx+(Hx-Hy) by abel]
    apply (mul_le_mul_of_nonneg_left (le_trans (Rise.taller _ zero_le_one ..) (add_le_add h1 (h2.trans (mul_le_mul_of_nonneg_right hp.2 Hβ)))) hc.1).trans
    have ht'' : 0≤b := Finset.sum_nonneg fun _ _ => norm_nonneg _
    change c*(b*ε+B*b* annuity t B ε n) ≤ κ*b/2
    linarith only [mul_le_mul_of_nonneg_right (show 2*c*(ε+B*annuity t B ε n)≤ κ from hu) ht'']

  have h_bill (v): coin (Wick X L v) ≤ κ*F.path.levels.clock.monitor k * (F.labels.level d).coeffSize (Price.awake F d k N p v):=by
    let j:=factors (↑z:ℂ) (L v)
    let b:= F'.coeffSize (awake F d k N p v)
    have hp := H2 v; apply (blends (Wick X L v) z hz).trans
    rw [hI]; have hx : milk Q j=j+(milk Q j-j) := by abel
    change coin (milk Q j) ≤ _
    rw [hx]; apply (Rise.taller _ zero_le_one ..).trans; have hv := bounds Q n ε hC he hε j (hs v)
    apply (add_le_add hp.2 (hv.1.trans (mul_le_mul_of_nonneg_right hp.2 (mul_nonneg he hY)))).trans; linarith only [mul_le_mul_of_nonneg_right hb (show 0 ≤ b from Finset.sum_nonneg fun _ _ => norm_nonneg _)]
  refine ⟨T, ⟨⟨?_,?_,?_,?_⟩,h_credit,h_bill⟩⟩
  · constructor
    · let u := F.refUnit d
      have hp : F'.e0= P u := by
        apply exposed F'; rw [hw u]
        change thawKey (F'.coords.symm F'.e0)=trim (exchange _ (milk _ (L u))) _ _
        rw [H1, Normal.pure,map_one, show F'.coords.symm F'.e0=Labels.unit G d by rw [← F'.coords_unit]; exact F'.coords.symm_apply_apply _]
        rw [show thawKey (unit G d)=1 from map_one _];
        ext i; rw [trim_coeff]; split_ifs with hg
        · rfl
        rw [coeff_one]; rw [if_neg]; intro H; subst i; simp at hg
      rw [show T u = F'.scaled z (P u) from rfl,← hp,F'.scaled_unit]
    · intro v; obtain ⟨i,h,hU⟩ := H3 v; have Hp : P v=i := exposed _ ((hw v).trans h)
      have Hq : P (star v)=star i := exposed _ ((hw _).trans hU)
      change F'.scaled z (P _)=star (F'.scaled z (P _)); rw [Hp,Hq]; funext j; simp
    intro v z
    apply (h_credit v).trans; have hX':0≤ F'.coeffSize (Price.awake F d k N p v):= Finset.sum_nonneg fun _ _=>norm_nonneg _
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_left hX' hκ) (by norm_num)
  · intro v; apply (h_bill v).trans
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (Real.exp_pos _).le hκ) (Finset.sum_nonneg fun _ _=>norm_nonneg _)

  · intro v; let X':= Wick X L v
    have he := ((bounds Q n ε hC he hε (factors _ (L v)) (hs v)).2)
    change totalDegree X' ≤ n
    rw [← show factors ((↑z:ℂ))⁻¹ (factors (↑z:ℂ) X')=X' from cycles _ _ (Complex.ofReal_ne_zero.mpr hz'.ne') _]
    exact (factor_degree ..).trans (by dsimp only [X']; rw [hI]; exact he)
  intro v
  rw [hx, show (F.labels.level d).scaled (z)⁻¹ (T v)= P v by
    have he := F'.scaled_inv (inv_ne_zero hz'.ne') (P v); rw [inv_inv] at he; exact he]
  unfold Perch.Verdict; rw [LiftMark.costs]
  apply congr_arg
  exact (hw v).symm
end YM.Next.Rank.LiftMark
