import YM.TraceExtension.Prom.Order.Sofa
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Function Filter MeasureTheory Finset Lattice Wilson RG Precision Supply
open Pressure Push.SectorMeasure Next.Rank RankCovariance Thirst  Ac Baler Glyph Tapes Marker
open Display Display.Docking Display.Sew Value Flux SectorNext.Vacuum Station Perch Tapes.West Atlas
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{X:Sheet G}{D:Rolls X}{R:Protection D}{E:Delays R} {Z: Bar E}(W:Wait Z) {A:Levels G} (h:Paid W A)
-- warm cost µ + allowance at all stages. Delays payment at prior plateau.
def runTicket (Z : Bar E)(b:ℝ)(j:ℕ)(s:ℝ) : Prop:=
    let y:=Ship.preHat Z s; let L:= (D.L j).val; let n:=Real.log (L:ℝ); let p:= Ship.benchCost Z b (j-1) s
    -- floor gap in sqrt split etc. paid at both σ
    Real.exp 1 ≤ y ∧ (p:ℝ) * n ≤ s/2 ∧
      (p:ℝ)*n*G.slopeConstant ≤ y/4
lemma ascentSky (Z:Bar E)(b:ℝ)(j:ℕ)(h:G.Simple)(hv:0≤b):∀ᶠ s in atTop,runTicket Z b j s:=by
    let d:= Real.log ((D.L j).val:ℝ)
    have he := Gauge.slopeConstant_pos h; have ht := ((Ship.accommodate Z b (j-1) h hv).mul_const d).eventually (ge_mem_nhds (by rw[zero_mul];norm_num : 0*d < 1/4))
    have hh : Tendsto (Ship.preHat Z) atTop atTop :=Filter.tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop he)
    filter_upwards [hh.eventually_ge_atTop (Real.exp 1),ht,eventually_gt_atTop 0] with s hv hx hS
    refine ⟨hv,?_,?_⟩ <;> rw [div_mul_eq_mul_div,div_le_iff₀ hS] at hx
    · change _*d ≤ _; linarith only [hx,hS]
    unfold Ship.preHat; change _*d*_≤_; linarith only [mul_le_mul_of_nonneg_left hx he.le,Z.good]
section schedule
variable {i j k m:ℕ}
include h
lemma stepSky (hj:k ≤ j) (hi:m ≤ j) (hk:j ≤ i) :
    let L:= (D.L (A.clock.J i)).val
    A.S.scale j - A.S.scale m ≤ (↑(j-m):ℝ)*Real.log (L:ℝ):=by
    intro L
    clear hj
    induction j,hi using Nat.le_induction with
    | base=>rw [Nat.sub_self,Nat.cast_zero,zero_mul,sub_self]
    | succ j hj IH=>
       have he := IH (Nat.le_trans (Nat.le_succ _) hk)
       have hu : 0 < ((A.S.block j).val:ℝ):=Nat.cast_pos.mpr (A.S.block j).property
       have ht : ((A.S.block j).val:ℝ) ≤ L:= by
          rw [← A.fits.sameFactor,h.lengths]; exact Nat.cast_le.mpr (D.grow (A.fits.mono hk))
       rw [A.S.scale_succ,show j+1-m=j-m+1 by omega]; push_cast; linarith only [Real.log_le_log hu ht,he]
omit h in
lemma scaleSky {A:Levels G}: Monotone A.S.scale := monotone_nat_of_le_succ fun b=>by rw [A.S.scale_succ]; exact le_add_of_nonneg_right (Real.log_nonneg (by exact_mod_cast (A.S.block b).property))
lemma listSky (j): Ship.preHat Z (A.S.scale j)=Atlas.clim A j:= by unfold Ship.preHat clim Calendar.hatBeta; rw [h.bar]
variable {b u:ℝ}
private lemma slackSky (hk: A.clock.J k=m+1) (hj:m=A.clock.J i)(hn:i≤k) (ht: 0 ≤ b)(hw:j=stretch ((D.L m).val) b (clim A k)) (hCap: j ≤ k-i) (hu: u ≤ b) (hy:runTicket Z b (m+1) (A.S.scale k)) (hG:G.Simple):
   ShelterSky A k u:=by
   let L : ℝ:=(D.L m).val; let x:= clim A k
   have hp: 1 < L:= by unfold L; exact_mod_cast (le_trans (by norm_num:2≤3) (D.large m).size)
   have hr(j)(he:i≤j)(hℓ:j≤k): m ≤ A.clock.J j:= by rw[hj]; exact A.fits.mono he
   have hf(j)(he:i≤j)(hℓ:j<k): L ≤ ((A.S.block j).val:ℝ):= by rw[← A.fits.sameFactor,h.lengths]; exact Nat.cast_le.mpr (D.grow (hr (j+1) (he.trans (Nat.le_succ _)) hℓ))
   have ha l (he : i≤l) (n : ℕ) (hi:l≤n)(hz:n≤k) : L^(n-l) ≤ A.S.a l/A.S.a n:=by
      induction n,hi using Nat.le_induction with
      | base => rw [div_self (A.S.a_pos _).ne', Nat.sub_self,pow_zero]
      | succ n h' ih =>
        rw [show n+1-l=n-l+1 by omega, pow_succ, A.S.a_step, div_div_eq_mul_div]; rw [mul_comm (A.S.a l),mul_div_assoc,mul_comm (↑(A.S.block n).val:ℝ)]
        exact mul_le_mul (ih (by omega)) (hf _ (he.trans h') hz) (zero_le_one.trans hp.le) (div_nonneg (A.S.a_pos _).le (A.S.a_pos _).le)
   let a:= middleSky A u k; let w:=Station.widthSky A u k; let d:= bump L u x;let t := more L x; let hM := (bump_s _ _ hu _ hp x)
   have hJ : d+t ≤ j:= (Nat.add_le_add_right hM _).trans_eq hw.symm
   have hD : d+t ≤ k-i:= hJ.trans hCap
   have hS : mag A u k * A.clock.monitor k ^2 ≤ A.S.a (k-d)/A.S.a k:=by
      have hp' : mag A u k * A.clock.monitor k ^2 ≤ L^d:= (wanted hp (mul_pos (mag_pos ..) (pow_pos (Real.exp_pos _) _)) d).2 le_rfl
      have hv:= ha (k-d) (by omega) k (Nat.sub_le ..) le_rfl; rw [show k-(k-d)=d by omega] at hv; exact hp'.trans hv
   have h'a:k-d≤a:=gain_fee (Nat.sub_le ..) hS
   have hq:=beforeSky A u k; change a ≤ k at hq
   have hQ : (A.clock.coverSize k:ℝ)^10 ≤ A.S.a (a-t)/A.S.a a:= by
      have hap:0 < (A.clock.coverSize k:ℝ):=Nat.cast_pos.mpr (A.budget k).B_pos
      have hv: L^(a-(a-t))≤ _:= ha (a-t) (by omega) a (Nat.sub_le ..) hq
      rw [show a-(a-t)=t by omega] at hv; exact (le_trans ((wanted hp (pow_pos hap 10) t).2 le_rfl) hv)
   have hw': a-t ≤ w:= gain_fee (Nat.sub_le ..) hQ
   have hh:wheelSky A k=L:= by
        unfold wheelSky leastL; rw [h.lengths,hk,Nat.add_sub_cancel,min_eq_right]; exact D.grow (Nat.le_succ _)
   refine ⟨⟨gain_high (j:=k-d) (Nat.sub_le ..) hS,gain_high (j:=a-t) (Nat.sub_le ..) hQ,?_,fun j he hv=> ?_⟩,fun l hl hℓ=> ?_⟩
   · rw [hh]; unfold L; exact_mod_cast (show 2 ≤ (D.L m).val from le_trans (by norm_num) (D.large m).size)
   · rw [hk,Nat.add_sub_cancel]; change w ≤ j at he; exact hr _ (by omega) hv
   change w ≤ l at hl; let Z':=A.S.scale k; let c:= Real.log ((D.L (m+1)).val:ℝ)
   have hv: k-l ≤ j:=by omega
   have he':j=Ship.benchCost Z b m (A.S.scale k):=by rw [hw]; unfold Ship.benchCost;rw [listSky _ h]; rfl
   have ha' :0 ≤ c:=Real.log_nonneg (by exact_mod_cast (D.L (m+1)).property)
   have hz:= stepSky (k:=k) (i:=k) _ h (le_refl _) hℓ le_rfl; change _ ≤ _ * Real.log ((D.L _).val:ℝ) at hz; rw [hk] at hz
   have hf : G.slopeConstant*(A.S.scale k - A.S.scale l) ≤ clim A k/4:= by
      have he : (j:ℝ)*c*G.slopeConstant ≤ clim A k/4:= by
         rw [he', ← listSky _ h]; exact (show _ from hy.2.2)
      exact (by rw[mul_comm];exact (mul_le_mul_of_nonneg_right (hz.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hv) ha')) (Gauge.slopeConstant_pos hG).le).trans he)
   unfold clim Calendar.hatBeta at *
   constructor
   · linarith only [hf]
   exact add_le_add_right (mul_le_mul_of_nonneg_left (scaleSky hℓ) (Gauge.slopeConstant_pos hG).le) _
lemma atlasSky (hk: A.clock.J k=m+1) (hp:X.first ≤ m) (ht : ∀ s:ℝ,W.readyHere m ≤ s → runTicket Z b (m+1) s ∧ Ship.benchCost Z b m (3*s) ≤ W.window m s)
    (he:u ≤ b) (hb:0≤ b)(hg:G.Simple): W.readyHere m ≤ A.S.scale k ∧ ShelterSky A k u:=by
    obtain ⟨i,h1,h2,h3⟩:= h.run m hp
    let s:=A.S.scale i; let t:=A.S.scale k; let j:=i+W.window m s
    have h4:A.clock.J i=m:= h3 i (by omega) (by omega)
    have h5:A.clock.J j=m:=h3 j (by unfold j s;omega) (by exact le_rfl)
    have hj:j<k:= lt_of_not_ge fun H=>by have hv:=A.fits.mono H; rw [hk,h5] at hv; omega
    have hi:i ≤ k:=le_trans (Nat.le_add_right ..) hj.le
    have hv:s ≤ t:= scaleSky hi; have hz:=h1.trans (show s ≤ t from hv)
    have hq:= ht _ hz|>.1
    refine ⟨hz,slackSky W h hk h4.symm hi hb (Eq.refl _) ?_ he hq hg⟩
    let L:=D.L m; let c:= Real.log ((D.L (m+1)).val:ℝ);let M:=stretch (L.val:ℝ) b (clim A k); change M≤k-i
    have HH:0<c:= Real.log_pos (by exact_mod_cast (le_trans (by norm_num:2≤3) (D.large _).size))
    rcases le_or_gt t (3*s) with hl|hl
    · apply le_trans _ (b:=W.window m s) (by unfold j at hj;omega)
      obtain ⟨hx,hσ⟩:= ht _ h1; apply le_trans _ hσ
      have hu : clim A i ≤ clim A k:= by rw [← listSky _ h,← listSky _ h]; exact add_le_add_right (mul_le_mul_of_nonneg_left hv (Gauge.slopeConstant_pos hg).le) _
      have he:clim A k ≤ Ship.preHat Z (3*s):= by rw[← listSky _ h]; exact add_le_add_right (mul_le_mul_of_nonneg_left hl (Gauge.slopeConstant_pos hg).le) _
      exact rate_bump ((show Real.exp 1 ≤ clim A i by rw[← listSky _ h]; exact hx.1).trans hu) he (by exact_mod_cast (le_trans (by norm_num:2≤3) (D.large m).size) : 1 < ((D.L m).val:ℝ)) hb
    have hc : (M:ℝ)*c ≤ t/2:= by
       unfold M c; rw [← listSky _ h]; exact hq.2.1
    have hv := stepSky (k:=k) W h le_rfl hi (le_refl k); change _ ≤ _ * Real.log ((D.L _).val:ℝ) at hv;rw [hk] at hv
    have hp : 0 ≤ t:=by unfold t Schedule.scale; exact Real.log_nonneg (by unfold Schedule.a; rw [inv_inv]; exact_mod_cast (A.S.denominator k).property)
    apply (Nat.cast_le (α:=ℝ)).mp; apply le_of_mul_le_mul_right _ HH; change t-s≤ _*c at hv; linarith only [hc,hv,hp,hl]
end schedule
lemma lastsSky (Z:Bar E)(j:ℕ)(b:ℝ)(h:G.Simple)(hb:0≤b): Tendsto (fun s:ℝ=>(Ship.benchCost Z b j (3*s):ℝ)/s) atTop (𝓝 0) := by
    have ht: Tendsto (fun s:ℝ=>3*s) atTop atTop:=tendsto_id.const_mul_atTop (by norm_num)
    have he:= ((Ship.accommodate Z b j h hb).comp ht).const_mul 3; rw [mul_zero] at he
    refine he.congr (fun p=>?_)
    dsimp only [comp_apply];rw [div_eq_mul_inv,div_eq_mul_inv,mul_inv_rev];ring
end YM.PhysicalNext.InteractingRank.Soft
