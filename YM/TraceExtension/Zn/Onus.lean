import YM.TraceExtension.Zn.Wary
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Zn
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits Pills Loft Xo
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {F:ℝ→ℝ}{a b c:ℝ}{k:ℕ}{G:Gauge}{n:Side}
lemma pour(G:Gauge)(hG:G.Simple)(S:Stage)(A:ℝ)(k:ℕ)(hA:0 ≤ A): ∀ᶠ x:ℝ in atTop,∀ (n:Side)(R:Rep G n) (Z:Dart G n), Made S x R→Sight x R Z →
    ∀ᶠ L:Finset ℕ in atTop, Splendor (loopP R x L) (ExtS n x) k (wideM x) A ∧ Drift _ (loopP R x L) ∧ (∀ i, rill (loopP R x L) (YCore x Z i) = rill (piste R loopF (spikes R loopF L (rim x))) (YCore x Z i))∧
       (∀ i,rill (loopP R x L) (YCore x Z i)=rill (quietL R x L) (YCore x Z i)-rill (Zech R x L) (YCore x Z i)) ∧ (∀ i, HearthV (rill (loopP R x L) (YCore x Z i)) (ExtS n x) k (wideM x) A)∧
       (∀ i,HearthV (rill (Zech R x L) (YCore x Z i)) (ExtS n x) k (calorie x) A)∧∀ a:G.ColorIndex,20*(high x+rim x+10)< n.val→ Holt a (fun i=> rill (quietL R x L) (YCore x Z i)∘ input G n)=0:=by
    obtain ⟨D,T,u,hD,hT,H⟩:=Pills.sandy hG k A hA
    obtain ⟨E,p,hE,h⟩:=policy G k A hA
    let σ:=S.width; have hσ:0<σ:= S.width_pos
    let e(x:ℝ):=shock x+Real.exp (-(σ/4)*rim x)*(momentPrice 1 (σ/2)*humble x); let B(x:ℝ):= biete G (e x); let c(x:ℝ):= Pills.pier (puff x) (B x) T
    have he: Tigh e 98:=shockT.tight (show 99≤100 by omega)|>.join ((stern 100 (show 0<σ/4 by positivity)).fly (h_mass.times (momentPrice 1 (σ/2)) (momentPrice_pos _ (by positivity)).le))
    have hh:Tigh B 97:=by
       rw[show B=fun x=> biete G 1*(e x) from funext fun x=> by unfold B biete; ring]; exact he.fact _ (by unfold biete; positivity)
    have hc:Tigh c 95:=by
       let f:ℝ→ℝ:=fun x=> (((10:ℝ)+puff x+(10+puff x)+1) ^ (4:ℕ)); unfold c Pills.pier; push_cast; have hp:= (mass (show 0 ≤ (10:ℝ) by norm_num)).gather balloon; exact (hh.fly (mass hT)).fly (show ConstMass 0 f from (((hp.gather hp).gather (mass zero_le_one)).crop 4))
    let P(x:ℝ):= DockAmt G (radiusB x) D (puff x) u (humble x) σ; have hp: ConstMass (1/1000) P:= bills _ _ _ _ (by positivity) hσ h_mass
    let F(x:ℝ):=DockAmt G (radiusB x) E (puff x) p (humble x) σ; have hf: ConstMass (1/1000) F:= bills _ _ _ _ (by positivity) hσ h_mass
    have hn: Tigh (fun x=> hornS G x k (c x)) 94:=by
        have hm(x:ℝ):hornS G x k (c x)=hornS G x k 1*c x:=by unfold hornS; ring
        simp_rw [hm]; exact hc.mult (honest G k (mass (show 0≤ (1:ℝ) by norm_num)))
    filter_upwards [hc, hn.tight (show 30≤94 by omega), hp _ (by norm_num: (1/1000:ℝ)<1/50), (honest G k hp) _ (by norm_num:(1/2000:ℝ)+1/1000<1/50), hf _ (by norm_num: (1/1000:ℝ)<1/50), weather G A hA k (1/2000) (by norm_num), Work.E01.radiusB_tendsto.eventually_ge_atTop 2,rim_gt 10,eventually_gt_atTop (0:ℝ)] with x hc hh hp hk hV hx hB hR ht n R J hJ hv
    have h':= hJ.2.2; rw[←hJ.1] at h'; have hB:2≤ R.p.B:= hJ.2.1.symm ▸ hB
    filter_upwards [washR R σ S.paths (humble x) (shock x) (rim x) h' (by unfold shock; positivity)] with L hl
    let W:=loopP R x L; let V:= ExtS n x; let U:=ski R loopF L (rim x); let Vw:=YCore x J; have hZ: Turret.sprout (0:Site n) (salo R (puff x) (rim x)) = V:=by
        rw [adriftR R x S hJ]
    have H1(i):= hx n J R hv i; have hu(i): rill W (Vw i)= rill U (Vw i):= (husk R loopF (spikes R loopF L _) (H1 i|>.1) hB).symm
    have ha:Splendor W (Turret.sprout 0 (salo R (puff x) (rim x))) k (DockAmt G R.p.B E (puff x) p (humble x) σ) A:= h ℕ loopF n 0 R S.paths _ _ σ h' hG hB (offloop R h') L (puff x) (rim x)
    rw[hZ,hJ.2.1] at ha; obtain ⟨hq,hL,hf,hC⟩:=H n R L σ S.paths (humble x) h' hB Vw (fun _=> mew x) (rim x) (puff x) hR (fun i=> (H1 i).1) (fun i=> (H1 i).2.1) (B x) hl
    refine ⟨ha.up (fun _ h=>h) hV.2,hymn R loopF _ _,hu,fun i=> (hu i).trans (hq i),fun i=>?_,fun i=>?_,fun a h=>?_⟩
    · change HearthV (rill W (Vw i)) _ _ _ _; rw [hu]; have he: HearthV (rill U (Vw i)) _ k _ A:= hf i;
      rw[hZ,hJ.2.1] at he; exact mot k _ _ _ _ _ _ le_rfl he ((honour_l x k hp.1).trans hk.2)
    · have he:= hL i
      rw [show _=_ from hZ] at he; exact mot k _ _ _ _ _ _ le_rfl he ((honour_l x k hc.1).trans hh.2)
    refine hC _ ?_ ?_
    · intro v hv; rw[adriftR R x _ hJ] at hv; rw [separation_comm]; obtain ⟨k,hk,he⟩:=halo_spec.mp hv; rw[mem_singleton.mp hk] at he; omega
    rw[adriftR R x _ hJ]; omega
lemma creation(G:Gauge)(hG:G.Simple)(S:Stage)(A:ℝ)(k:ℕ)(ha:0≤ A): ∀ᶠ x:ℝ in atTop,∀ (n:Side)(R:Rep G n)(Q:Dart G n), Made S x R → Sight x R Q→ Craft S x R Q k A:=by
    filter_upwards [sense G A k ha,weather G A ha k (1/200) (by norm_num),powcap, cloche G A ha k,primeB G hG S A ha k,zprime G hG S A ha k, pour G hG S A k ha] with x hx hv hZ hp hT hC hk n R Q hu he
    obtain ⟨h,hQ,hP,hA⟩:= hx n Q R he; have ht(i):=(hv n Q R he i).1; obtain ⟨hh,hJ⟩:= hp n Q R he
    refine ⟨h,hQ,hP,fun i=> (hA i).top le_rfl hZ le_rfl,ht,fun i=> (hv n _ R he i).2.1,fun i=>?_,hh,?_, hk n R Q hu he,fun i X _ _ W y hf =>?_ ,hJ⟩
    · exact ⟨fun j hj hi=> ((hv n Q R he i).2.2.1.values j hj hi).trans hZ⟩
    · filter_upwards[hT n R Q hu he,hC n R Q hu he] with L hl hh; obtain ⟨h₁,h₂,h₃,h₄⟩:= hl; refine ⟨h₁,h₂,h₃,h₄,fun i=>?_⟩; rw [h₃ i]; exact hh i
    exact ((lushTide (ht i)) X W y hf).sub contDiffAt_const
where
  powcap:∀ᶠ x:ℝ in atTop,tightf x≤ calorie x:=by filter_upwards[eventually_gt_atTop (1:ℝ)] with x hx using inv_anti₀ (show 0<x^(30:ℕ) by positivity) (pow_le_pow_right₀ hx.le (by norm_num))
end YM.Trace.Zn
#print axioms YM.Trace.Zn.creation
