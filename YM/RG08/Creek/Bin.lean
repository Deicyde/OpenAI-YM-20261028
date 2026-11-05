import YM.RG08.Creek.Epoch
/-! # Exposure to all k-test inputs at capture

 Halo Ω_F worst pre registered B independent. General products arrive in those norm powers (not polynomial rates unless geometry pays). Remember here exp expenditure as a function of geometry variable. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Creek
open Function Finset Filter RG Lattice Laurent Quire Vale Bloch Next.Free Stationary Shade Wax Town Bands Plot Needle Tall Scores Push.AbsoluteSums Work.F08 Door Analysis
open Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset RG Bloch Conductor Staffer Reflect UVExt.Paths Summit Wings High Pill Taste Run PowerSeries Harvest
open scoped Topology ContDiff BigOperators Real Classical Matrix
variable {I:Type}[Fintype I][DecidableEq I]{V:Type}[NormedAddCommGroup V]{G:Gauge}{X:Chain}{m N k i j n E r D t:ℕ}{R C w v A B:ℝ}{a b:I→ℕ}{p:List I}{ν:G.ColorIndex}{D':ChartRatio G}
lemma stride_v (k:ℕ)(x:E4)(ψ:I→Profile D)(z:I→Cover)(h:z∈cope X k k ψ x R) (hv:0≤C)(he:∀ i j:I,i≠j→ Resolve (ψ i).val (ψ j).val C) (hR:1/2≤R)(hz: C*(1+8*R)*(1+(A+8)) < 1): rural X.S A k k z univ:= by
   intro p q H; have hh : p.val≠q.val:= fun h=>H (Subtype.ext h); have hP i:=blush_v.mp (Fintype.mem_piFinset.mp h i)
   have he:= outskirt (hP p.val) (hP q.val) (he _ _ hh) hv (spanP_pos ..|>.le); have hc:0 ≤ C*(1+8*R):=by
      have hr:0≤R:=by linarith
      positivity
   have hp: spanP X k k=1:= by unfold spanP; exact div_self (X.S.a_pos _).ne'
   simp only [hp,mul_one] at he
   simp only [Function.comp_apply,asc_t]; refine le_of_not_gt (fun h=> not_le_of_gt hz (he.trans ?_)); exact mul_le_mul_of_nonneg_left (add_le_add (le_refl _) h.le) hc
-- spatial active near. use supports anchored around relative $Φ$. Work arbitrary scale polynomial if halo fixed
lemma blush_ring (φ:Profile D)(x:Rest)(C:ℝ)(hp:0≤C)(hr:Spatial φ.val (spanP X k i*C)) : blush φ X k i (spanP X k i • x.val) R ⊆ Lattice.box (circleP (spanP X k i*C) R (spanP X k i)+4):= by
   intro z hz; have hv:= reached_finite φ X k i (spanP X k i • x.val) R; have hC:= arc_bound (X:=X) k i x
   let P:= arcT X k i (spanP X k i • x.val); have hs(n:Axis): (P n).natAbs≤4:= (single_le_sum (f:=fun i=> (P i).natAbs) (fun i _=>Nat.zero_le _) (mem_univ n)).trans hC
   have hx := extent_p (z:=z) hr (blush_v.mp hz) -- fix hr shadow
   apply box_test.mpr; constructor <;> (intro a; let q:=circleP (spanP X k i*C) R (spanP X k i); have hp: ((z-P) a).natAbs ≤ q:=hx a; rw [Pi.sub_apply] at hp; have hh:=hs a; unfold q at *; omega) -- change _
-- samples on small region T, cost same Width
variable {T:Finset I}{X': Type}
lemma pail_of {F:Places I→Rooted V X' r}(h:Owns v T F A)(hc:0≤v)(p:Places I)(a:T): Pail (p a) v (F p) A:=by -- binder
   obtain ⟨U,H,hx⟩:= h.2.2 a; have hP:=H (pin T p);
   let s:Fleet T:= pin T p; let r:=p a;
   have ht:=budget_single (hx (p a)) (⟨s,rfl⟩: Held a r); change Tribe _ s _ (U s) ≤ _ at ht
   rw [only_pin h.1 p]; exact Ink.raise hP ((le_mul_of_one_le_left (hP.nonneg) (Real.one_le_exp (mul_nonneg hc (show 0≤ (Mounts a s:ℝ) from Nat.cast_nonneg _)))).trans ht)
lemma roam_lit {x:Cover}{F: Rooted V X' r}(hx:Pail x w F B)(hw:0≤w)(hp:w≤1)(hk:size x≤k): Quire.Lit F w (Real.exp ((r*k:ℕ):ℝ)*B):= by
    refine budget_mono (budget_scale ((Real.exp_pos _).le) hx) (fun i=> mul_nonneg (Real.exp_pos _|>.le) (norm_nonneg _)) (fun i=>?_)
    unfold pale; rw [←mul_assoc, ← Real.exp_add]; refine mul_le_mul_of_nonneg_right (Real.exp_monotone ?_) (norm_nonneg _)
    have hv : girth i= stretch 0 i := by simp [girth,stretch]
    have he : girth i ≤ stretch x i + r*k:= by apply le_trans (hv.symm ▸ spans x 0 i) (Nat.add_le_add (le_refl _) (Nat.mul_le_mul_left _ (by simpa using hk)))
    nlinarith only [mul_le_mul_of_nonneg_left (show (girth i:ℝ)≤ (stretch x i:ℝ)+ (r*k:ℕ) by exact_mod_cast he) hw, mul_le_mul_of_nonneg_right hp (show 0≤ ((r*k:ℕ):ℝ) from Nat.cast_nonneg _)]
-- bound in native $C$ derivative on each test no restriction hull, at scaled exterior costs span. D fixed
lemma campus (φ:Exam D)(o:E4)(t:Cover)(h: Reads φ C)(he:1 ≤ spanP X k i)(hx:0≤C) : ‖sheet D R (exteriorP φ (spanP X k i) o t)‖ ≤ (spanP X k i)^D*C := by
    let v:=spanP X k i
    have hv:0<v:=spanP_pos ..
    refine (bound D R _ (mul_nonneg (pow_nonneg hv.le _) hx)).mpr ?_; rintro ⟨⟨j,hj⟩,b⟩ x
    change ‖iteratedFDeriv ℝ j (exteriorP φ v o t).val _ _‖ ≤ _; unfold exteriorP; rw [Pages.facades _ _ _ _ (by omega)]
    simp only [_root_.smul_apply,norm_smul,Real.norm_of_nonneg (pow_nonneg hv.le j)]
    refine mul_le_mul (pow_le_pow_right₀ he (by omega)) ((ContinuousMultilinearMap.le_opNorm _ (basis ∘ b)).trans ?_) (norm_nonneg _) (pow_nonneg hv.le _)
    have hh (i:Axis):‖basis i‖=1:=by simp
    simp only [Function.comp_apply, hh, prod_const_one, mul_one]; exact h j (by omega) _
lemma spoke_mass (T: Finset I)(C:I→ℝ)(b:I→ Sight D R)(hC:0≤C)(he:∀ i∈T,‖b i‖≤ C i): ‖Wax.sampleK T b‖ ≤ ∏ i∈ T,C i:= by
   have hx: 0≤ ∏ i∈T,C i:=prod_nonneg fun i _=>hC i
   refine ContinuousLinearMap.opNorm_le_bound _ hx fun v=> (v.le_opNorm (speak T b)).trans ?_; rw [mul_comm]; refine mul_le_mul_of_nonneg_right ((ContinuousMap.norm_le (speak T b).val hx).mpr ?_) (norm_nonneg _)
   intro x; change ‖profileP T b x‖≤_; change ‖∏ i:T, (b i.val).val (x i.val).1 (x i.val).2‖≤_; rw [norm_prod,← Finset.prod_coe_sort T]; exact prod_le_prod (fun _ _=> norm_nonneg _) (fun i _=> (norm_mark D R _ _ _).trans (he i i.property))
-- rooted low budgets. at fixed all coordinates all F within A_i. T nonempty essential on cost.
lemma gust_lit {F: Rooted ℝ X' r}{V': Rooted ℝ X' j}(h:Quire.Lit F w A)(hp:Quire.Lit V' w B)(hw:0≤w) : Quire.Lit (braidV F V') w (A*B):= by
   refine stitching (Ink.pour (p:=interU F V') aboardB ?_ (ling_one hw))
   refine budget_mono (budget_prod h hp) (fun i=>mul_nonneg (Real.exp_pos _|>.le) (norm_nonneg _)) fun i=>le_of_eq ?_
   unfold interU; simp only [Function.comp_apply,norm_mul, ling]; have he: girth (aboardB i)=girth i.1+girth i.2:= by unfold girth aboardB; rw [Fin.sum_univ_add]; simp only [Fin.append_left, Fin.append_right]
   rw [he,Nat.cast_add,mul_add,Real.exp_add]; ring
end YM.RG08.Creek
