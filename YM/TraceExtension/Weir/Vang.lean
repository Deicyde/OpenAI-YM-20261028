import YM.TraceExtension.Weir.Cement
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Weir
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory Push.SectorMeasure
open PhysicalNext.JointLoad.Heir Next.Foundations Push.Local Swift WardBin WardBin.Lies WardBin.Wheels Next.Fluctuations Planned.AtomRegular.Foliage Next.SectorChange
open Wicket Outer.Nodes
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side}
private lemma inkcap(G:Gauge)(S:Stage)(C:ℝ)(hc:0 < C):∀ᶠ x:ℝ in atTop,∀ (n:Side)(R:Rep G n)(Λ:ℝ)(h:Age S x Λ R), Shepherd.tariff R (wingC R (C*peace x) S.width S.paths Λ) (2*hue x) ≤ 1:=by
   let H(x:ℝ):= 4*x; let W:=Shepherd.wide G S.supportExponent; let Q:=Geo.lowerSize S.clip S.paths; let c:= W*momentPrice 1 (S.width/4)*Q; let f(x):= H x*(2*kindle G*(C*peace x)*thetaP x)*c+2*(W*(H x*(thetaP x^3*S.paths+thetaP x^4*S.paths)+thetaP x^2*humble x)); let g(x):=Extra.Multi.siteFactor (radiusB x); let F(x):=Fintype.card Signed * g x*(VerifiedReset.factor*f x)+ 2*hue x*g x;
   have hW:0 ≤ W:=(Real.exp_pos _).le;have hQ:0 ≤ Q:=by unfold Q Geo.lowerSize; positivity [S.clip.quadratic_pos,S.paths_pos];
   have hs:= S.paths_pos; have hz:S.width>0:= S.width_pos;have he:0 ≤ c:=mul_nonneg (mul_nonneg hW (momentPrice_pos _ (by positivity)).le) hQ;
   let a:ℝ:= -(1/48:ℝ); have hH:Lim 1 H:=by simpa only[Real.rpow_one,zero_add] using! (board (by norm_num:(0:ℝ) ≤ 4)).prod (sands 1)
   have hh:Lim a f:=by
      refine Lim.plus (a:= -(1/48:ℝ)) ?_ ?_
      · apply (((hH.prod (((board (show 0≤ 2*kindle G by unfold kindle; positivity[G.colorScale_pos])).prod ((board hc.le).prod cool)).prod tall )).prod (board he))).spot (by norm_num)
      have h1:= ((hH).prod (((tall.pow 3).prod (board hs.le)).plus (((tall.pow 4).prod (board hs.le)).spot (by norm_num))))
      exact ((board zero_le_two).prod ((board hW).prod (h1.plus ((((tall.pow 2).prod (ferry h_mass))).spot (by norm_num))))).spot (by norm_num)
   have hg: ConstMass 0 g:=by unfold g Extra.Multi.siteFactor; exact (mass (Real.exp_pos _).le).cop ((((upperB.times 16 (by norm_num)).gather (mass (by norm_num))).times _ (by norm_num)).crop _)
   have hF:Lim a F:=by refine ((( ((board (Nat.cast_nonneg (Fintype.card Signed))).prod (ferry hg)).prod ((board VerifiedReset.factor_pos.le).prod hh))).spot (by unfold a; norm_num) |>.plus ?_); exact (((board (show (0:ℝ)≤2 from zero_le_two)).prod chime).prod (ferry hg)).spot (by unfold a; norm_num)
   filter_upwards [hF.tiny (by unfold a; norm_num),eventually_gt_atTop (1:ℝ)] with x hv hx n R v h; have hθ:0 < thetaP x:=h.thresh ▸ R.p.threshold_pos;have hψ:0 < peace x:=pet x hx.le S|>.2.1; have hφ:0 ≤ kindle G:=by unfold kindle; positivity[G.colorScale_pos];
   apply le_trans _ hv; unfold F f g Shepherd.tariff wingC bedste Shepherd.crown; rw[h.hM.1,h.thresh,h.hM.2.1,h.depth]; have hV:0≤ v:= Cost.nonneg h.good.paths.two; dsimp only [W,Q,c,H]; gcongr <;> first|exact h.beta|exact h.bnd|unfold Extra.Multi.siteFactor <;> positivity|positivity[VerifiedReset.factor_pos]
-- Volume-independent sup cap for window.S.M. `Leap`.
private lemma globe(G:Gauge)(k:ℕ): ∃ A C:ℝ,0 ≤ A∧0 ≤ C∧ ∀ (n:Side)(U:Config G n)(v:Gal G n)(F:ℝ) (e:Lines G n 1)(u:G.El), 0 ≤ F→ Climate v k F A→ |clamor (beaconR e) v (tuna e u) U| ≤ C*F:=by
    let L: (G.ColorIndex→ℝ)→L[ℝ] G.Color:= (WithLp.linearEquiv 2 ℝ _).symm.toContinuousLinearMap
    refine ⟨G.colorScale,‖L‖,G.colorScale_pos.le,norm_nonneg _,fun n U v F e u hB hp=>?_⟩
    let o:=beaconR e; have he(i: Lines G n 1) : |v U i| ≤ F:= (hp.laps ℝ (fun _=> U) 0 (fun j=> allows_const _ (SectorAffine.mat_paid (U j)|>.le)) i).value
    let W:= edgeColor (v U) o; let T (i:G.ColorIndex):=W i; have ht:‖T‖ ≤ F:= (pi_norm_le_iff_of_nonneg hB).mpr fun i=>he (o.1,Exterior.coord o.2,i)
    rw [clamor,zeal]; let X:=tuna e u; change |inner ℝ W X| ≤ _; exact (abs_real_inner_le_norm ..).trans (by rw[show ‖X‖=1 from litChrom ..,mul_one]; exact (L.le_opNorm T).trans (mul_le_mul_of_nonneg_left ht (norm_nonneg _)))
structure Garden (x:ℝ)(Λ:ℝ)(m:ℕ)(Z:ℝ)(S:Stage)(R:Rep G n)(Y:Gal G n) : Prop where
   credit : Shepherd.tariff R (wingC R (Z*peace x) S.width S.paths Λ) (2*hue x) ≤ 1
   season(i:Lip n G): i∈allotZ (Bay n x) m→ProofC R (beaconR i.1).1 (tailH R i.1 Y) (loomH i.1 (loc i.2*peace x)) (tempQ x) (Z*peace x)
   tax(i:Lip n G): i∈allotZ (Bay n x) m→∀ U v, ‖tailH R i.1 Y U v‖ ≤ x
   vessel (u:Config G n)(q:ℕ): |callX R (Shepherd.field R q) Y (peace x) m (Bay n x) u/peace x| ≤ x^ (2:ℕ)
lemma glory(G:Gauge) (S : Stage)(m d k:ℕ)(T: Collar G S.order) : ∃ Z C:ℝ,0 < Z∧0 ≤ C∧∀ᶠ x:ℝ in atTop,∀ (n:Side)(Λ:ℝ)(R:Rep G n)(Y:Gal G n), Age S x Λ R→Clouded Y (Bay n x) → Climate Y k (thinM x) C → Garden x Λ m Z S R Y:=by
    obtain ⟨A,C,hA,hC,H⟩:=globe G k
    obtain ⟨Z,hZ,he⟩:=cast_shape G S m d T
    let V(x:ℝ):= x*(Real.exp 2+1); let F(x:ℝ):= cardB G x*(wheat m*V x)*(peace x)⁻¹
    have hI: Lim (1:ℝ) id:=by simpa only [Real.rpow_one] using! sands 1
    have hV: Lim (1:ℝ) V:=by simpa only [add_zero] using! hI.prod (board (show 0≤Real.exp 2+1 by positivity))
    have hF:∀ᶠ x:ℝ in atTop,F x≤x^(2:ℕ):=by
        have hf: ConstMass 0 (cardB G):=by unfold cardB; push_cast; exact (((balloon.gather balloon).gather (mass zero_le_one)|>.crop 4).cop (mass (Nat.cast_nonneg _)))
        filter_upwards [(((ferry hf).prod ((board (show 0≤ wheat m from sum_nonneg fun i _=> abs_nonneg _)).prod hV)).prod fieryG) 2 (by norm_num)] with x hx; exact hx.2.trans (Real.rpow_two ..).le
    refine ⟨Z,A,hZ,hA,?_⟩; filter_upwards [he, (((board hC).prod (ferry (waveM (1/200)))) 1 (by norm_num)), inkcap G S Z hZ, hF,eventually_gt_atTop (1:ℝ)] with x h hx hp hv hB n Λ R Y ha hb hh
    let c:=tempQ (n:=n) x; let H':= dec_b n x; obtain ⟨ht,hl,hx',h₁,h₂,h₃,hM⟩:= h 1100 le_rfl (by unfold towerH; omega) Λ n R ha
    have hT(o:Site n) : inspected {o} ⊆ halo 9 {o}:= (Next.Rank.Thirst.inspect _).trans (sprout_mono _ (show 8≤(9:ℕ) by norm_num)); specialize hp n R Λ ha
    let P:=allotZ (G:=G) (Bay n x) m; have hs(i:Lip n G) (hi:i∈P): ProofC R (beaconR i.1).1 (tailH R i.1 Y) (loomH i.1 (loc i.2*peace x)) c (Z*peace x):=by
       obtain ⟨hZ,h⟩:=mem_product.mp hi; exact horn R i.1 _ Y _ hb _ ((hT _).trans (hM _ (mem_product.mp hZ|>.1))) ((dec_b ..).1.trans (dec_b ..|>.2)) hl (hx' _ h)
    have hY(i:Lines G n 1)(u v) : |windowH R i Y u v|≤ x:=by unfold windowH; split; exact (H n u Y _ i v (Zn.wake ..).le hh).trans (hx.2.trans (Real.rpow_one _).le); rw[abs_zero]; positivity
    refine ⟨hp,hs,fun i _ u v=> (Complex.norm_real _).trans_le (hY _ u v),fun U q=>?_⟩
    have h₁(i:Lip n G)(hi:i∈P):= lampG R i.1 _ _ _ hb _ _ (hs i hi) q ha.good ha.coverage ha.dialect ha.high hp (show _ from H'.2 (H'.1 (show (beaconR i.1).1∈ _ from mem_product.mp ((mem_product.mp hi).1)|>.1))) x (hY i.1) U
    let u:=peace x; have hu:0 < u:= (pet x hB.le S).2.1
    apply le_trans _ hv; unfold callX; rw [abs_div, abs_of_pos hu]; unfold F; rw [div_eq_mul_inv]; apply mul_le_mul_of_nonneg_right _ (inv_pos.mpr hu).le; rw[← Real.norm_eq_abs]; apply le_trans (norm_sum_le ..); refine le_trans (sum_le_sum (g:=fun i:Lip n G=> |wage m i.2| * V x) (fun i hi=> ?_)) ?_
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_left ((h₁ i hi).trans_eq (by unfold V; ring)) (norm_nonneg _)
    unfold allotZ; rw [sum_product]; dsimp only; simp_rw [← Finset.sum_mul]; rw [sum_const, nsmul_eq_mul,mul_assoc]; refine mul_le_mul_of_nonneg_right ?_ (show 0≤ wheat m*V x by unfold V; positivity [show 0 ≤ wheat m from sum_nonneg fun i _=>abs_nonneg _]); rw [card_product,card_univ]; apply Nat.cast_le.mpr; apply Nat.mul_le_mul_right; exact le_trans (Corona.halo_size ..) (by simp)
end YM.Trace.Weir
