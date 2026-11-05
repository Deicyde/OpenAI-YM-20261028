import YM.TraceExtension.Shunt.Jelly
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Shunt
open RG Wilson Lattice Source Labels Finset Push.Local Next.Foundations MergeProof Planned.GuardedAtom Guard Extra.Histories Filter Function Relay Det
open MeasureTheory
open Pressure Stationary AnalyticBridge VerifiedReset Perfect Turret Shepherd Filch Fen Kits Pills Loft Xo Zn Swift Wicket Weir Push.Uniform StressFlux
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{n:Side} {T:SectionData F}{H:Hol G}{R:Rep G n}{x v w p c k u a:ℝ}
lemma veil{X:Coefficient F n}{f:Film G n}(h:AtomD T H R X f v c k)(hp:c≤u)(hr:k ≤ w): AtomD T H R X f v u w:=
   ⟨h.shape,h.charge.imp (fun i h=>⟨h.1.trans hp,h.2⟩),h.pays.imp (fun i h'=>⟨MergeProof.stackFee h'.1 hr,h'.2⟩),h.birth⟩
lemma stares(x:ℝ):Weir.smoke x= Doors.stain x:=by unfold Doors.stain smoke Swift.fog Wave Zn.RLog; rw[one_mul]
lemma relief(j:ℕ): Tigh (Real.sqrt ∘ smoke) j:=by
    filter_upwards [Doors.stain_beats j,eventually_gt_atTop (0:ℝ)] with x hx hy; refine ⟨Real.sqrt_nonneg _,?_⟩; rw[Function.comp_apply,stares]; exact le_of_mul_le_mul_right (le_trans hx (le_of_eq (inv_mul_cancel₀ (show x^j ≠0 by positivity)).symm)) (pow_pos hy _)
abbrev grantS(x:ℝ):= thetaP x^2 * Wave ((1:ℝ)/6) x
lemma trend(S : Stage) {H:Hol G} (T:SectionData F)(c:ℝ)(hc:0 ≤ c) :∀ᶠ x:ℝ in atTop,∀ (n:Side)(Λ:ℝ)(R:Rep G n), Age S x Λ R→ Keeper R.p R.activities→ Readable H T R.p n c→ T.footprint (0:Site n) ⊆ tempQ x →∀ (X:Peat G n), ClimateJ R X x (trayF x) (wideM x)→∃ Z:Coefficient F n,AtomD T H R Z (filmR X) (Weir.smoke x) (grantS x) x ∧ Z.x=Push.Local.weighted H F 0 (tempQ x) R.p.threshold (filmR X):=by
   let D:= readPrice H F; have hD:0 ≤D:= zero_le_one.trans (readPrice_pos ..); let C:= atomPrice H F c; have hC:0 ≤ C:=zero_le_one.trans (atomPrice_ge_one _ _ hc); let A:= Real.exp (S.supportExponent*TileNo); have hA:0 ≤A:=(Real.exp_pos _).le
   let V(x:ℝ):= C*trayF x; let v(x:ℝ):=wideM x + V x; let Y(x):= (( (high x+1)+(high x+1)+1)^4:ℕ);
   let K(x:ℝ):=2*(Y x:ℝ)*A*v x; have hV:Lim (-1) V:=by
       refine ( (board hC).prod ((tall.pow 2).prod (ferry (waveM _)))).spot (by norm_num)
   have hz: Lim 0 v:= Lim.plus (ferry (waveM _)) (hV.spot (by norm_num)); have ht:Lim 0 (fun x=>(Y x:ℝ)):=by
       let h:=expansion.gather (mass zero_le_one); unfold Y; push_cast; exact ferry (( (h.gather h).gather (mass zero_le_one)).crop 4)
   have hK: Lim 0 K:=by refine (((((board zero_le_two).prod ht).prod (board hA)).prod hz)).spot (by norm_num)
   have hr:= ((Lim.prod hK (oil 4 (relief 4))) (-(2:ℝ)) (by norm_num));
   have hP:= ((((waveM (1/8:ℝ)).times (D+A*C) (by positivity)).gather ((mass zero_le_one).inc (b:=1/8) (by norm_num))) (1/6) (by norm_num));
   filter_upwards [hr,hP,( (board (Real.exp_pos ((S.supportExponent+2)*TileNo)|>.le)).prod hz) 1 (by norm_num), ((ht.prod (oil 2 (relief 2))).tiny (by norm_num)), eventually_gt_atTop (1:ℝ)] with x hx hh hT hY hp n Λ R H' St hv hZ X hX
   let Q:=tempQ x (n:=n); have hs : 0< thetaP x:= H'.thresh ▸ R.p.threshold_pos; have hy: 0 ≤ V x:=mul_nonneg hC (mul_nonneg (by positivity) (Zn.wake ..).le); have hw:0 < smoke x:=Real.exp_pos _; have hw' : smoke x ≤ Real.sqrt (smoke x):=by apply (Real.le_sqrt hw.le hw.le).2; rw[sq]; exact mul_le_of_le_one_left hw.le (by rw[stares]; exact Doors.stain_le x)
   have hmQ : (Q.card:ℝ) ≤ Y x:= Nat.cast_le.mpr (le_trans (Corona.halo_size ..) (by simp[Y])); let y:= towerH x
   have hV:∀ U,‖filmR X U‖ ≤ wideM x:= fun U=> (Complex.norm_real _).trans_le (hX.price _);
   obtain ⟨Z,hv,hg⟩:= voyage T H R St Q _ H'.good hw ((mul_le_mul hmQ hw' hw.le (Nat.cast_nonneg _)).trans hY) hv (Real_regular hX.puff.regular) (Real_salary hX.puff.regular hX.puff.fare) hZ hV
   have ht:R.p.mass Q 1 ≤ A:=by unfold BudgetPoint.mass A; rw[H'.depth,mul_one]; apply Real.exp_monotone; gcongr; exacts [S.price_pos.le,tote S x Λ R H'];
   have hr:0≤ wideM x:= (Zn.wake ..).le; have hq:R.p.mass Q (v x) ≤ A*v x:= mul_le_mul_of_nonneg_right ((mul_one _).symm.le.trans (show _ from ht)) (show 0 ≤v x from add_nonneg hr hy)
   refine ⟨Z,veil hv ?_ ?_,hg⟩
   · let q:= R.p.mass Q (V x); have he1:q ≤ A*V x:=mul_le_mul_of_nonneg_right ((mul_one _).symm.le.trans (show _ from ht)) hy
     have hu : 2*(Q.card:ℝ)*Real.sqrt (smoke x)*R.p.mass Q (v x) ≤ x^(-(2:ℝ)):=by
         apply le_trans _ hx.2; change _ ≤ 2*(Y x:ℝ)*A*v x*Real.sqrt (smoke x); apply le_trans (mul_le_mul_of_nonneg_left hq (by positivity : 0≤2*(Q.card:ℝ)*Real.sqrt (smoke x))); apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmQ zero_le_two) (by positivity)) (show 0 ≤ A*v x from mul_nonneg hA (add_nonneg hr hy))); exact le_of_eq (by ring)
     have hf:0<x:=by linarith only[hp];
     have hs: x^(-(2:ℝ))≤ (thetaP x)^2:=by
         have hh:x⁻¹ ≤ thetaP x^ (2:ℕ):=by
              unfold thetaP; rw[mul_pow,_root_.inv_pow,Real.sq_sqrt hf.le]; exact le_mul_of_one_le_right (inv_nonneg.mpr hf.le) (one_le_pow₀ (wok _ _ (by positivity)))
         exact (Real.rpow_le_rpow_of_exponent_le hp.le (by norm_num : (-(2:ℝ)) ≤ -1)).trans ((Real.rpow_neg_one x).le.trans hh)
     change D*trayF x+q+_≤grantS x; apply le_trans (add_le_add (add_le_add_right he1 _) (hu.trans hs)); exact le_trans (le_of_eq (b:=thetaP x^ (2:ℕ)*((D+A*C)*Wave (1/8) x+1)) (by unfold V trayF; ring)) (mul_le_mul_of_nonneg_left hh.2 (by positivity))
   change Real.exp _*(v x)≤x
   exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by rw[H'.depth];gcongr;exacts [add_nonneg S.price_pos.le zero_le_two,tote S x Λ R H'])) (show 0 ≤ v x from add_nonneg hr hy)).trans (hT.2.trans (Real.rpow_one _).le)
end YM.Trace.Shunt
