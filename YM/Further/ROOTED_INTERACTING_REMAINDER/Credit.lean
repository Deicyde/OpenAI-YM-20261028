import YM.Further.ROOTED_INTERACTING_REMAINDER.Fades
import YM.Further.ROOTED_INTERACTING_REMAINDER.Normalization
/-!
# Exact delay sufficiency for the intact normalized remainder

P asks for widths, loops, etc. before L. Implements a critical check:
Survey.far and .spare ARE available under that protocol, at the *same*
instances, eventually throughout x (judged under the E.B(x) torus size
qualification); not an extra LF hypothesis. Price of tails and growth
stated especially to see how much area exponent really used. Not
advertising arbitrary post-L pressure reserves.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.RootedInteractingRemainder
open Filter Function Lattice RG Wilson Pressure Pressure.Stores Pressure.Teller Next.Fluctuations
open Next.Fluctuations.Sector Push.SectorMeasure Oriented Tree SectorNext.Vacuum Precision
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {L : Side}
open Work.E09
open Vac.Numbers

local notation "Δ" => Module.finrank ℝ G.Color
-- Lower bound important for .room. Needs no stronger hypothesis on band
-- than exact half-width. Exponent 2 is `p²` and asymptotic logarithm gate
-- restores main volume as O(log p) instead of O(log β).
private lemma hat_sq {x : ℝ} (h : 0<x) : x * temp x ^ 2 = P x ^ (2:ℕ) := by
  rw [temp, mul_pow,inv_pow,Real.sq_sqrt h.le,←mul_assoc,mul_inv_cancel₀ h.ne',one_mul]
  rfl
lemma deep_monitor : Tendsto P atTop atTop := Real.tendsto_exp_atTop.comp ((tendsto_pow_atTop (n:=2) (by decide)).comp
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop))

private lemma permit (L : Side) (c : ℝ) (h : 0<c) : ∀ᶠ x : ℝ in atTop,
    let v := betaF G x L; let t := fiery G x L
    ∀ β : ℝ,v/2≤β → β≤2*v → let τ := Real.sqrt β
      (0<t ∧ t≤1 ∧ 1 ≤ τ ∧ τ⁻¹ ≤ t ∧ τ*t ≤ 2*P v ∧
        Real.exp (-c*(β*t^2))* (t⁻¹)^Δ ≤ 1) := by
  have hv := betaF_growth G L
  -- just dominate log beta by P, *not* the t⁻¹ itself; cost is single log.
  have hk : ∀ᶠ s : ℝ in atTop, Real.log s ≤ P s := by
    filter_upwards [eventually_gt_atTop 1,(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1] with s hs hz
    calc
      _ = Real.exp (Real.log (Real.log s)) := (Real.exp_log (Real.log_pos hs)).symm
      _ ≤ _ := Real.exp_monotone (by change Real.log (Real.log s) ≤ (Real.log (Real.log s))^2; change 1 ≤ Real.log (Real.log s) at hz; nlinarith only [hz]) 
  have ht : Tendsto temp atTop (𝓝 0) := by simpa only [pow_zero,one_mul] using radiusB_temp 0
  filter_upwards [hv.eventually (eventually_ge_atTop 4),hv.eventually hk,hv.eventually (ht.eventually (ge_mem_nhds zero_lt_one)),
    (deep_monitor.comp hv).eventually_ge_atTop (max 2 (Δ/c:ℝ))] with x hx he ht hD
  intro v t β hm hr τ
  have h4 : (4:ℝ) ≤ v := hx
  have ha : 1 ≤ β := by linarith only [hm,h4]
  let s := Real.sqrt v
  have hs : 1 ≤ s := Real.le_sqrt_of_sq_le (by rw [one_pow]; linarith only [h4])
  have hτ : 1 ≤ τ := Real.le_sqrt_of_sq_le (by rw [one_pow]; exact ha)
  have hs' : 0<s := zero_lt_one.trans_le hs
  have hτ' : 0<τ := zero_lt_one.trans_le hτ
  have hw : 0<t := temp_pos (show 0<v by linarith)
  let y := P v
  have hZ : 2 ≤ y := (le_max_left ..).trans hD
  have hr' : (Δ:ℝ) ≤ c*y := by
    have hu : (Δ:ℝ)/c ≤ y := (le_max_right ..).trans hD
    linarith only [(div_le_iff₀ h).mp hu]
  have hτ2 : τ^2=β := Real.sq_sqrt (by linarith)
  have hs2 : s^2=v := Real.sq_sqrt (by linarith)
  have hib : t=s⁻¹*y := rfl
  have hh : s ≤ τ*2 := by nlinarith only [hs,hτ,hs2,hτ2,hm,ha]
  have ho : τ ≤ 2*s := by nlinarith only [hs,hτ,hs2,hτ2,hr,h4]
  refine ⟨hw,ht,hτ,?_,?_,?_⟩
  · rw [hib,inv_eq_one_div τ,mul_comm,← div_eq_mul_inv,div_le_div_iff₀ hτ' hs']
    nlinarith only [hZ,hτ,hh]
  · change τ*t ≤ 2*y
    rw [hib,mul_comm s⁻¹,← div_eq_mul_inv,← mul_div_assoc,div_le_iff₀ hs']
    linarith only [mul_le_mul_of_nonneg_right ho (show 0≤y by linarith)]
  let n := Δ
  calc
    _ = Real.exp (-c*(β*t^2)+(n:ℝ)*(-Real.log t)) := by rw [Real.exp_add,Real.exp_nat_mul,Real.exp_neg,Real.exp_log hw]
    _ ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hz : -Real.log t ≤ y/2 := by
        have hp : 0≤Real.log y := Real.log_nonneg (by linarith only [hZ])
        rw [hib,Real.log_mul (by positivity : s⁻¹≠0) (by linarith : y≠0),Real.log_inv]
        have hb : Real.log s=Real.log v/2 := Real.log_sqrt (by linarith)
        change Real.log v ≤ y at he
        linarith
      have hv' : v*t^2 = y^2 := hat_sq (by linarith)
      have hh' := mul_le_mul_of_nonneg_right hm (sq_nonneg t)
      have he := mul_le_mul_of_nonneg_left hz (a:=(n:ℝ)) (by positivity)
      have hh'' := mul_le_mul_of_nonneg_right (show (n:ℝ) ≤ c*y from hr') (show 0≤y by linarith)
      linarith only [hh'',he,mul_le_mul_of_nonneg_left hh' h.le,show c*(v*t^2)=c*y^2 by rw [hv']]

private lemma wounded_small (L : Side) (C σ C' σ' : ℝ) (hC : 0<C) (hσ : 0<σ)
    (hC' : 0<C') (hσ' : 0<σ') :
    let b := fun x=>betaF G x L
    Tendsto (fun x => b x*wound σ C (fiery G x L) (till x) 1) atTop (𝓝 0) ∧
    Tendsto (fun x => b x*wound σ' C' (temp x) (till x) L.val) atTop (𝓝 0) := by
  intro b
  have he := betaF_growth G L
  have h {C σ : ℝ} {t : ℝ→ℝ} (d : ℕ) (hd : 0<d) (hC : 0<C) (hs : 0<σ) (hT : Tendsto t atTop (𝓝 0)) (h0 : ∀ x,0≤t x) :
      Tendsto (fun x => b x*wound σ C (t x) (till x) d) atTop (𝓝 0) := by
    let q := fun x=>fringe σ (till x) d
    have hk : ∀ᶠ x : ℝ in atTop,q x ≤ (b x)⁻¹ := by
      filter_upwards [tail_delay G L (σ/d) (by positivity)] with x hx
      refine le_trans (le_of_eq ?_) hx; unfold q fringe; congr 1; ring
    have hh x : 0≤q x := fringe_nonneg ..
    have hQ : Tendsto q atTop (𝓝 0) := squeeze_zero' (Eventually.of_forall hh) hk (tendsto_inv_atTop_zero.comp he)
    have hv := ( (show Tendsto (fun x=>C* |t x|) atTop (𝓝 (C*|0|)) from hT.abs.const_mul _).add (hQ.const_mul C)).const_mul (2*C)
    simp only [abs_zero,mul_zero,add_zero] at hv
    apply squeeze_zero' ?_ ?_ hv
    · filter_upwards [he.eventually_ge_atTop 0] with x hx
      have hg := hh x; unfold q at hg
      have hi := h0 x; change 0 ≤ b x at hx; unfold wound; positivity
    filter_upwards [hk,he.eventually_gt_atTop 0] with x h hx
    have hp' := hh x; have hi := h0 x; change 0 < b x at hx
    have hf : 0≤2*C*(C*(t x)+C*q x) := by positivity
    change b x*(2*C*q x*(C*t x+C*q x)) ≤ _
    rw [abs_of_nonneg (h0 x)]
    have hZ : b x * q x ≤ 1 := by
      apply le_trans (mul_le_mul_of_nonneg_left h hx.le); exact (mul_inv_cancel₀ hx.ne').le
    linarith only [mul_le_mul_of_nonneg_left hZ hf]
  have hT : Tendsto temp atTop (𝓝 0) := by simpa only [pow_zero,one_mul] using radiusB_temp 0
  exact ⟨h _ (by decide) hC hσ (hT.comp he) (fun x=>Push.SectorMeasure.temp_nonneg (betaF G x L)),h _ L.property hC' hσ' hT Push.SectorMeasure.temp_nonneg⟩

variable {c f : Side} {S : StepData c f}
    {F : Tree.Forest S.ratio} {T : Tube G S} {x W : ℝ}

lemma site_compare (S : StepData c f) : sites c ≤ sites f := by
  have hl : (1:ℝ)≤S.patch.L.val := by exact_mod_cast S.patch.L.property
  rw [sites_ratio S]; exact le_mul_of_one_le_right (site_pos _).le (one_le_pow₀ hl)
lemma four_sites (S : StepData c f) : rich f+ (Fintype.card (Site c)-1) ≤ (4*Fintype.card (Site f)) := by
  have he : Fintype.card (Site c) ≤ Fintype.card (Site f) := by exact_mod_cast (show (Fintype.card (Site c):ℝ) ≤ (Fintype.card (Site f):ℝ) from site_compare S)
  unfold rich; omega
lemma seven_sites (S : StepData c f) : rich f+ Fintype.card (Bond c) ≤ (7*Fintype.card (Site f)) := by
  have he : Fintype.card (Site c) ≤ Fintype.card (Site f) := by exact_mod_cast (show (Fintype.card (Site c):ℝ) ≤ (Fintype.card (Site f):ℝ) from site_compare S)
  unfold rich Bond Edge Axis; rw [Fintype.card_prod,Fintype.card_fin]; omega

private lemma price_succession (ρ : Teller G) (L : Side) :
    let b := fun x=>betaF G x L
    ∀ᶠ x : ℝ in atTop, ∀ f : Side,∀ R : Rep G f,∀ Λ δ : ℝ,
      0 ≤ R.beta → R.beta ≤ 2*b x → R.p.threshold = fiery G x L → δ≤1 → Λ≤2*P (b x) →
        R.exCost ρ.top.paths Λ δ ≤ 4*ρ.top.paths+2 := by
  intro b; filter_upwards [(betaF_growth G L).eventually uniform_loop,(betaF_growth G L).eventually_gt_atTop 0] with x he hx
  intro f R Λ δ hy hB hv hδ hΛ
  let t := fiery G x L
  have ht : 0≤t := Push.SectorMeasure.temp_nonneg _
  rw [Rep.exCost, PathData.loopsPrice,hv]; rw [show 4*ρ.top.paths+2=1+(4*ρ.top.paths+1) by ring]
  refine add_le_add hδ (add_le_add ?_ ?_)
  · have hi := he.2.1
    have hp := he.2.2.1
    change b x * t^3 ≤ (1:ℝ) at hi
    change b x * t^4 ≤ (1:ℝ) at hp
    let q := ρ.top.paths
    have hh : 0≤q := ρ.top.paths_pos.le
    change _*(q*t^3+q*t^4) ≤ 4*q
    apply le_trans (mul_le_mul_of_nonneg_right hB (by positivity))
    linarith only [mul_le_mul_of_nonneg_left hi hh,mul_le_mul_of_nonneg_left hp hh]
  have hk := he.2.2.2 1 le_rfl; rw [Real.rpow_one] at hk
  exact (mul_le_mul_of_nonneg_right hΛ (by positivity)).trans hk

private lemma rental_sites {n v : Side} (S : StepData n v) (R : Rep G v)
    (ρ : Stage) (Z δ Λ x W : ℝ) (hC : R.exCost ρ.paths Λ δ ≤ Z)
    (ht : R.beta*wound ρ.width ρ.paths R.p.threshold (till x) 1 ≤ 1)
    (hm : 0≤W) (M : ℝ) (hM : 0≤M) :
    rental n R ρ 1 x W M Λ δ ≤ sites v*
      ((Z+(Fintype.card PlaqAxes:ℝ))+ (M+1) + Fintype.card PlaqAxes + 4*(2*W) +
        Real.log 2*(Fintype.card PlaqAxes+4+1)) := by
  have hf := site_compare S
  have he := (site_pos v).le
  let p := (Fintype.card PlaqAxes:ℝ)
  have hp : 0≤p := Nat.cast_nonneg _
  unfold rental rooms supplicant
  have hr : (Fintype.card (Cell v):ℝ)=sites v*p := by simp [sites,Cell,Face,Site,p]
  have hw : (Fintype.card (Bond n):ℝ)=sites n*4 := wires_sites _
  rw [hr,hw,mul_left_comm R.beta p]
  have ha := mul_le_mul_of_nonneg_left ht hp
  calc
    _ ≤ sites v*(Z+p*1)+(M+1)*sites v+sites v*p+sites v*4*(2*W)+Real.log 2*(sites v*p+sites v*4+sites v) := by
      refine add_le_add (add_le_add (add_le_add_left (add_le_add
        (mul_le_mul_of_nonneg_left (add_le_add hC ha) he) (mul_le_mul_of_nonneg_left hf (by positivity))) _)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hf (by norm_num : (0:ℝ)≤4)) (by positivity)))
        (mul_le_mul_of_nonneg_left (add_le_add (add_le_add_right (mul_le_mul_of_nonneg_right hf (by norm_num : (0:ℝ)≤4)) _) hf) (Real.log_nonneg (by norm_num)))
    _ = _ := by unfold p; ring

/-- Shaping the seal at fixed inputs (all Search currencies hired at the
same x gate, constant K etc. BEFORE x, not choosing anew from period-size
compact lemmas). `M` pays candidate probe cost per site (+ separate κ/4
allowable rate per share). -/
theorem surveyed (ρ : Teller G) (L : Side) (W κ M : ℝ) (hW : 0<W) (hκ : 0<κ) (hM : 0≤M) :
    ∃ A B p K : ℝ, 0≤A ∧ 0<B ∧ 0<p ∧ 1 ≤ K ∧ ∀ᶠ x : ℝ in atTop,
      let v := betaF G x L
      ∀ (c f : Side) (S : StepData c f), S.patch.L=L → 100*(1+radiusB x) ≤ c.val →
        ∀ (T : Tube G S), ρ.Funds S T →
        ∀ (F : Tree.Forest S.ratio) (R : Rep G f),∀ Λ δ y : ℝ,
          R.Lawful ρ.top.width ρ.top.paths Λ δ y → v/2 ≤ R.beta → R.beta ≤ 2*v →
          Presented.Fits T R x → y≤1 → δ≤1 → Λ ≤ 2*Vac.Numbers.P v →
            let t := fiery G x S.patch.L; let τ := Real.sqrt R.beta
            Survey ρ S T F R x W 1 Λ δ y K τ κ (κ/4) (κ/4) ∧ τ*t ≤ 2*Vac.Numbers.P v ∧
              rental c R ρ.top 1 x W M Λ δ ≤ sites f*A ∧ R.exCost ρ.top.paths Λ δ ≤ B ∧
              prefactor S G R.beta ≤ Real.exp (wires c*p)*(τ^Δ)^(Fintype.card (Bond c)) ∧
              R.beta*wound ρ.below.width ρ.below.paths (temp x) (till x) S.patch.L.val ≤ 1 := by
  let b := 4*ρ.top.paths+2
  let u := (Fintype.card PlaqAxes:ℝ)
  let C := ((b+u)+(M+1)+u+4*(2*W)+Real.log 2*(u+4+1))
  obtain ⟨p,hp,H⟩ := zed ρ
  obtain ⟨K,hK,Hk⟩ := sip G
  have h₁ := ρ.top.width_pos
  have h₂ := ρ.below.width_pos
  have hz := wounded_small (G:=G) L _ _ _ _ ρ.top.paths_pos h₁ ρ.below.paths_pos h₂
  have hC : 0≤C := by unfold C; have := ρ.top.paths_pos; have : 0 ≤ u := Nat.cast_nonneg _; have ht := Real.log_nonneg (show (1:ℝ)≤2 by norm_num); unfold b; positivity
  refine ⟨C,b,p,K,hC,by unfold b; have := ρ.top.paths_pos; positivity,hp,hK,?_⟩
  obtain ⟨Y,hY⟩ := eventually_atTop.mp H
  let v := fun x => betaF G x L
  filter_upwards [permit (G:=G) L (κ/2) (by positivity), hz.1.eventually (ge_mem_nhds (show (0:ℝ)<1/2 by norm_num)),
    hz.2.eventually (ge_mem_nhds (show (0:ℝ)<1/2 by norm_num)), settled_exterior ρ L W 1 hW zero_lt_one,
    (betaF_growth G L).eventually_ge_atTop 4,(betaF_growth G L).eventually_ge_atTop (2*Y^2),price_succession ρ L]
    with x hh ht he hf hv hy hr
  intro v' c f S hL hN T hT F R Λ δ y hR h h' hFits h0 hδ hΛ t τ
  obtain ⟨ht0,ht1,hτ,hSt,hcost,H⟩ := hh R.beta h h'
  have hτ0 : 0<τ := zero_lt_one.trans_le hτ
  have hβ : 0<R.beta := lt_of_lt_of_le (by change (0:ℝ) < betaF G x L / 2; linarith only [hv]) h
  have hτ2 : τ^2=R.beta := Real.sq_sqrt hβ.le
  have hτY : Y ≤ τ := by
    have hi : Y^2 ≤ R.beta := by linarith only [hy,h]
    nlinarith only [hi,hτ2,hτ0]
  have hq : R.p.threshold=fiery G x L := by rw [hFits.temp,hL]
  have hA : R.exCost ρ.top.paths Λ δ≤ b := hr _ R _ _ hβ.le h' hq hδ hΛ
  have hB : (0:ℝ)≤wound ρ.top.width ρ.top.paths R.p.threshold (till x) 1 := by unfold wound; have := fringe_nonneg ρ.top.width (till x) 1; have := R.p.threshold_pos; have := ρ.top.paths_pos; positivity
  have hd : (0:ℝ)≤wound ρ.below.width ρ.below.paths (temp x) (till x) L.val := by unfold wound; have := fringe_nonneg ρ.below.width (till x) L.val; have := Push.SectorMeasure.temp_nonneg x; have := ρ.below.paths_pos; positivity
  have hm := rental_sites S R ρ.top b δ Λ x W hA ?_ hW.le M hM
  rotate_left
  · apply le_trans (mul_le_mul_of_nonneg_right h' hB); rw [hq]; change betaF G x L * _ ≤ _ at ht; linarith only [ht]
  have hl : R.clip=ρ.top.clip := by rw [hFits.clip,hT.high]
  refine ⟨⟨hR,hT,hl,h0,?_,?_,hW.le,hτ,hτ2.symm,hq.symm ▸ hSt,?_,hK,?_,by positivity,?_⟩,?_,hm,hA,?_,?_⟩
  · rw [hL]; exact ht0
  · rw [hL]; exact ht1
  · intro A U k V hk ha hb; exact hf c f S hL hN T hT F A U k V hk ha hb R.beta hβ.le h'
  · rw [hL]; exact Hk (fiery G x L) ht0 ht1
  · rw [hL]; rw [show κ/4-κ+κ/4= -(κ/2) by ring]; exact H
  · unfold t; rw [hL]; exact hcost
  · simpa only [hτ2] using hY τ hτY c f S hT.knobs
  rw [hL]; change betaF G x L * _ ≤ _ at he
  apply le_trans (mul_le_mul_of_nonneg_right h' hd); linarith only [he]

end YM.Further.RootedInteractingRemainder
