import YM.FullVolume.Glide.Kiosk
/-! One-step norms & betas. On Common orbit, not required balanced. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lark.Glide
open Function Filter Set MeasureTheory Lattice RG Pressure RG.Shoot Wilson Precision RG.Supply Input Org
open Push Push.AbsoluteSums AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Song Geo
open ConnectedActivityE6
open Push.PriceCompiler Further.StrongStartup UniformSpace
open WilsonStartup Progress.DirectedRecipe Time UVNext.CouplingReset Roof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{c f:Side}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A} {p m N n:ℕ}
open Muse Pass FullVolume.Urns FullVolume.Shadow FullVolume.Amp
variable {t ξ w d q:ℝ} {L:Lyrics R t t}
    (Y:Plato L q w d ξ)(O:Ops L N p)
-- layout norm at all periods does not forget Reads; val if proof.
local notation "Ω"=> A.B.a.clock.hatBeta
local notation "B"=> A.B.a
local notation "K"=> A.B.kin
namespace Window
open Contest
variable (h:Stationary.Artes.Cadre A.post A.B.kin)(he: Next.Free.Amplify A.B.M)(hp:Jams.Wild R.shape A.delay)
variable {Y} {u v:ℕ→ℕ}{Q:∀ i,Ops L (u i) p}{Q':∀ i,Ops L (v i) p}{P:∀ i,Contest (u i) p L}{P':∀ i,Contest (v i) p L}{f f' g g':ℕ→ℝ}{X' Y':∀ i,cloud A.B.a i p}
variable (hU: Tendsto u atTop atTop)(hV:Tendsto v atTop atTop) (hP:Banked Y P Q f X' g)(hP':Banked Y P' Q' f' Y' g')
include h he hp hU hV hP hP'
lemma siege (m:ℕ): let y:= max (dist (f (m+1)) (f' (m+1))) (dist (X' (m+1)) (Y' (m+1))); dist (X' m) (Y' m) ≤ 8*glint*y ∧ ‖g m-g' m‖≤ 4*stow A.B.a w m*y:=by
    intro y
    choose K' hK hk using fun i=>guild Y (O:=Q i) (fun j _=> issued hV hP' j) (u i)
    have hw i: Glints atTop (fun _ : ℕ=> f' i) (fun n=>saga (P' n) i):=⟨f' i,tendsto_const_nhds, hP'.angles i⟩
    let T i:=dices Y (Q i) (P i)
    have hv i:Tendsto (fun n=> gifts (K' n) i) atTop (𝓝 (Y' i)):=by
        obtain ⟨x,hx,H⟩:=aglow Y h he hp hU hV hw hK (fun i=> cageM Y (Q' i) (P' i)) i; exact tendsto_nhds_unique H (hP'.fields i) ▸ hx
    have hz i:Tendsto (fun n=>price (K' n) i) atTop (𝓝 (g' i)):= by
        obtain ⟨x,hx,H⟩:= scored Y h he hp hU hV hw hK (fun i=> cageM Y (Q' i) (P' i)) i; exact tendsto_nhds_unique H (hP'.earns i) ▸ hx
    let i:=m+1; have hh : Tendsto (fun n=> max (dist (saga (P n) i) (f' i)) (dist (gifts (T n) i) (gifts (K' n) i))) atTop (𝓝 y):= ((hP.angles i).dist tendsto_const_nhds).max ((hP.fields i).dist (hv i))
    exact ⟨le_of_tendsto_of_tendsto ((hP.fields m).dist (hv m)) (hh.const_mul _) ((hU.eventually_gt_atTop m).mono fun n hn=> tickets Y (cageM Y (Q n) (P n)) (hK n) hn|>.1), le_of_tendsto_of_tendsto ((hP.earns m).sub (hz m)|>.norm) (hh.const_mul _) ((hU.eventually_gt_atTop m).mono fun n hn=> tickets Y (cageM Y (Q n) (P n)) (hK n) hn|>.2)⟩
omit he hp
set_option quotPrecheck false
local notation "Ω₀"=> fun n=>fromLambda (A.B.a.clock.hatBeta n) (f n)
local notation "Ω₁"=>fun n=> fromLambda (A.B.a.clock.hatBeta n) (f' n)
variable (hB:Glints atTop (fun i=> draws (P i) 0) (fun i=> draws (P' i) 0))
include hB
lemma arrest (i:ℕ): Ω₀ i- Ω₁ i= -∑ j∈Finset.range i,(g j-g' j):=by
    induction i with
    | zero=> obtain ⟨x,hx,H⟩:= hB; have hp: Ω₀ 0=Ω₁ 0 := (tendsto_nhds_unique (palm hU hP 0) hx).trans (tendsto_nhds_unique H (palm hV hP' 0)); rw [hp,sub_self]; simp
    | succ i ih => obtain ⟨s,hS⟩:= h.accounts i; rw [Finset.sum_range_succ]; linarith [trader hU hP hS,trader hV hP' hS] -- beta casts
-- uniform ran. no trunc and summation infinity. Drift limit pricing.
set_option quotPrecheck false
local notation "⊚" => fun i:ℕ=> max (dist (f i) (f' i)) (dist (X' i) (Y' i))
lemma ticketed (i:ℕ): (⊚ i) ≤ 1/4 := by
    refine max_le ?_ (by rw [dist_eq_norm]; exact (norm_sub_le ..).trans ((add_le_add (waveBound hP i) (waveBound hP' i)).trans (by norm_num)))
    have hb:=pressing Y (issued hU hP i) (issued hV hP' i)
    have hv:=arrest h hU hV hP hP' hB i; dsimp only at hv; rw [hv,norm_neg] at hb
    have hp: brace A.B.a i*dist (f i) (f' i) ≤glint* brace A.B.a i:= hb.trans ((norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun j=>stow _ w j) (fun j _=> by
       apply (norm_sub_le ..).trans; exact (add_le_add (pop hU hP j) (pop hV hP' j)).trans_eq (add_halves _))).trans (Y.largeG.radiusB i)))
    have hd:= braceP Y i; refine le_trans (le_of_mul_le_mul_left (hp.trans_eq (mul_comm ..)) hd) (by norm_num [glint])
include he hp
lemma accord (T:ℕ): f T=f' T∧ X' T=Y' T:=by
    let b:=sSup (range (⊚)); have hs: BddAbove (range (⊚)):=⟨_, forall_mem_range.mpr (ticketed h hU hV hP hP' hB)⟩
    have hx i:⊚ i≤ b:= le_csSup hs (Set.mem_range_self _)
    have hh i: 0≤⊚ i:= le_max_of_le_left dist_nonneg
    have hv:0≤b:= (hh 0).trans (hx 0)
    have hz i :=siege h he hp hU hV hP hP' i
    have hp : b≤ 8*glint*b:= csSup_le (Set.range_nonempty _) (forall_mem_range.mpr fun i=>by
        refine max_le ?_ ((hz i|>.1).trans (mul_le_mul_of_nonneg_left (hx (i+1)) (by norm_num [glint])))
        have hu:=pressing Y (issued hU hP i) (issued hV hP' i); have hr:= arrest h hU hV hP hP' hB i; dsimp only at hr; rw [hr,norm_neg] at hu
        apply le_of_mul_le_mul_left (hu.trans _) (braceP Y i)
        refine (norm_sum_le ..).trans ?_
        calc
         _ ≤ ∑ j∈ Finset.range i, (4*b)*stow A.B.a w j := Finset.sum_le_sum fun j _=> by
              have hh: 0 ≤ stow A.B.a w j:= by linarith [pop hU hP j,norm_nonneg (g j)]
              exact ((hz j|>.2).trans (mul_le_mul_of_nonneg_left (hx (j+1)) (mul_nonneg (by norm_num) hh))).trans_eq (by ring)
         _ ≤ (4*b)*(glint*brace A.B.a i):=by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (Y.largeG.radiusB i) (by positivity)
         _ ≤ _:= by rw [show (4*b)*(glint*brace A.B.a i)=brace A.B.a i*(4*glint*b) from (by ring)];  apply mul_le_mul_of_nonneg_left _ (braceP Y i).le; gcongr <;> norm_num [glint])
    norm_num [glint] at hp
    have hr:= hx T; have hL:= dist_nonneg (x:=f T) (y:=f' T); have h':0≤ dist (X' T) (Y' T):= dist_nonneg; exact ⟨dist_eq_zero.mp (le_antisymm ((le_max_left ..).trans (hr.trans (by linarith))) hL),dist_eq_zero.mp (le_antisymm ((le_max_right ..).trans (hr.trans (by linarith))) h')⟩
end Window
end YM.PhysicalNext.Repeat.Lark.Glide
