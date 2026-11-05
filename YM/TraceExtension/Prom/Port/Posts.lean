import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Posts
/-!
  Variant of YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Posts for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure RG Next.SectorChange SectorNext.Vacuum Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Push.SectorMeasure
     YM.PhysicalNext.PhysicalGuard7f546 Curved MeasureTheory Bid Display Display.Docking Filter RG.Supply Next.Rank.Station Tree Thirst Display.Sew
open scoped Topology BigOperators Classical

-- m=M_L actual larger budget (even on shaded arcs), arithmetic pre-L. No
-- Theta recalibration being charged here. Budget e σ unmarked separately.
variable {G : Gauge} {j : ℕ}
variable (ξ : Purse) (s : Stage) (L : Side)

-- earlier show uses Posts.Cert
-- Not smuggling compatibility into Lease constructor. supplemental phase drift call

local notation "E" => load ξ.era
local notation "T0" => tinder ξ
private lemma plankedSky : ∀ᶠ t in atTop, ∀ x∈Set.Icc (t/2) t, ∀ y∈Set.Icc (t/2) t, wilt (walls x)*((Fintype.card (Site L):ℝ)*(salary (E+1)*gas ξ.era.coast y)) ≤ T0 t:= by
  let c:= (33:ℝ)^4*∑' i, welter i; let w:=(Fintype.card (Site L):ℝ)*salary (E+1)
  let d:=(-(2*ξ.goal:ℝ)-10)
  have h':0≤c:=mul_nonneg (by positivity) (tsum_nonneg fun _=>by unfold welter; positivity)
  have hW:0≤w:=mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hp': 0≤2-d:= by unfold d; linarith [Nat.cast_nonneg (α:=ℝ) ξ.goal]
  filter_upwards [Paint.q_power 4 1 zero_lt_one,Perch.half.eventually_ge_atTop 1,Perch.force ξ.era.coast.posA (2-d) 0 le_rfl hp',Paint.absorb (1+(d-2)) d (by linarith only) (c*w)] with t hx hv ht h x he y hY
  have ha:wilt (walls x) ≤ c*bill 1 t:= by
    rw [show wilt (walls x)=c*(walls x:ℝ)^4 by unfold wilt c; ring]; exact mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (wall_mono (hv.trans he.1) (hv.trans (he.1.trans he.2)) he.2)) _).trans hx) h'
  let g:=gas ξ.era.coast y
  have hf:g≤ bill (d-2) t:=Real.exp_le_exp.mpr (by linarith only [ht y hY])
  rw [←mul_assoc (Fintype.card (Site L):ℝ) (salary (E+1)) (gas ξ.era.coast y)]; change wilt _*(w*g)≤_; refine (mul_le_mul ha (mul_le_mul_of_nonneg_left hf hW) (mul_nonneg hW (gas_le ..).1.le) (h'.trans ?_)).trans ?_
  exact le_mul_of_one_le_right h' (Real.one_le_exp (by rw [mul_one]; exact boil_pos _)); rw [mul_mul_mul_comm,overlap];exact h
private lemma step_passSky (ξ : Purse) : ∀ᶠ t in atTop,
      Real.exp (2*tinder ξ t)-1 ≤ 1-Real.exp (-(16*tinder ξ t)) ∧ 16*tinder ξ t ≤ 1 ∧
       Line ξ.era ξ.goal 0 t * 2 * (16*tinder ξ t) ≤ kinetics t/4 ∧ Real.exp (2*tinder ξ t)-1+(kinetics t/4)≤ kinetics t ∧
       tinder ξ t ≤ kinetics t/16:=by
  let d:=(-(2*ξ.goal:ℝ)-10); let v:=tinder ξ; let m:ℝ:= (ξ.goal:ℝ)-3; let y:=fun t=> kinetics t
  have hs : 6 ≤ (ξ.goal:ℝ):= Nat.cast_le.mpr ξ.tolerance
  have hm : d<0:= by unfold d; linarith
  filter_upwards [(bill_hi hm).eventually (ge_mem_nhds (show (0:ℝ) < 1/16 by norm_num)), Paint.absorb d (-1/8) (by unfold d;linarith) 16,
    Paint.absorb (m+d) (-1/8) (by unfold m d; linarith only [hs]) 128] with t ht hh hE
  let C:= v t; let q:= 16*C; have hc : 0<C:=Real.exp_pos _; change C ≤ 1/16 at ht
  have hp :0 ≤ q:=mul_nonneg (by norm_num) hc.le
  have hv : q ≤ 1:=by unfold q; linarith only [ht]
  have hl:16*C≤ kinetics t:=hh
  have hk:Real.exp (2*C)-1≤4*C:= by have hh:= Real.abs_exp_sub_one_le (by rw [abs_of_nonneg]; all_goals linarith : |2*C|≤1); rw [abs_of_nonneg (by positivity : 0 ≤ 2*C)] at hh; linarith only [abs_le.mp hh]
  refine ⟨hk.trans ?_, hv,?_,?_,?_⟩
  · rw [Real.exp_neg]
    have hu:=Real.add_one_le_exp q
    have hz : 0<q+1:=by positivity
    have h:= inv_anti₀ hz hu
    have hq:(q+1)⁻¹ ≤ 1 - 4*C := by
      apply le_of_mul_le_mul_left _ hz; rw [mul_inv_cancel₀ hz.ne']
      unfold q at *; nlinarith only [mul_le_mul_of_nonneg_left ht hc.le,hc]
    change _≤1-(Real.exp q)⁻¹; linarith only [h,hq]
  · rw [show Line ξ.era ξ.goal 0 t=bill m t by
      unfold Line fareP firstN; rw [mul_zero,zero_add, Perch.bill,Perch.bill,← Real.exp_sub,max_eq_right]; exact congr_arg Real.exp (by unfold m;ring); apply Real.one_le_exp; linarith only [mul_le_mul_of_nonneg_left hs (boil_pos t),boil_pos t]]
    rw [← overlap] at hE; change _*(_*C)≤ kinetics t at hE; change _*2*(16*C)≤kinetics t/4; linarith only [hE]
  · change Real.exp (2*C) -1 + kinetics t/4≤ _; linarith only [hk,hl,hc]
  change C ≤ _; linarith only [hl]
lemma stipendFeastsSky (s0 : Steel ξ s L) (u : Stage) (hs : Steel ξ u L): ∀ᶠ t in atTop, ∀ (P Q : BudgetPoint),∀ x∈Set.Icc (t/2) t, ∀ y∈Set.Icc (t/2) t, P.B=walls y → Q.B=walls x→ P.B ≤ 2*Q.B → P.supportExponent=s.supportExponent → Q.supportExponent=u.supportExponent → Lease L P Q E (acres ξ x y) (Line ξ.era ξ.goal 0 t) (tinder ξ t) (kinetics t) (gas ξ.era.coast y):=by
  have hP : 0≤ E:= by unfold load; linarith only [ξ.spend]
  filter_upwards [plankedSky ξ L,step_passSky ξ, Flux.timing,Perch.half.eventually_ge_atTop 1] with t h hT hv hh P Q x hx y hy hp hQ he hW hS
  obtain ⟨h1,h2,h3,h4,h5⟩:=hT; let c:=tinder ξ t
  have ht:=hv Q (hQ.trans_le (wall_mono (hh.trans hx.1) (hh.trans (hx.1.trans hx.2)) hx.2)); have hJ := ht.day
  have hc : 0 ≤ c := (Real.exp_pos _).le
  have hL: 16*c≤ kinetics t:=by change c ≤ _ at h5; linarith only [h5]
  refine ⟨hP,acres_one .., le_max_left ..,⟨he,by linarith only [hP],hW.symm ▸ s0.rent⟩,hQ.symm ▸ h _ hx _ hy,⟨?_,?_⟩,h1,?_,h2,h3,h4,h5,?_,ht,hc,(gas_le ..).1.le⟩
  exact mul_nonneg (by norm_num) hc
  exact (mul_le_mul_of_nonneg_left (show 2*c ≤ kinetics t by linarith only [hc,hL]) (pow_nonneg (by positivity) 4)).trans hJ.grain
  rw [mul_comm]; exact (mul_le_mul_of_nonneg_left hL (show 0 ≤ ReLog.roof Q.B by unfold ReLog.roof; positivity)).trans hJ.grain
  exact (hS.trans_le hs.apt).trans (by linarith only)

variable {X : Sheet G} {R : Rolls X} {D : Protection R} {W : Delays D} (Z : Bar W)

end YM.PhysicalNext.InteractingRank
