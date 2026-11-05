import YM.TraceExtension.Zn.Cask
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Zn
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits Pills Loft Xo
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {F:ℝ→ℝ}{a b c:ℝ}{k:ℕ}{G:Gauge}{n:Side}
lemma zprime(G:Gauge)(hG:G.Simple)(S:Stage)(A:ℝ)(ha:0 ≤ A)(k:ℕ) : ∀ᶠ x:ℝ in atTop,∀ (n:Side)(R:Rep G n) (Z:Dart G n), Made S x R→Sight x R Z →
    ∀ᶠ L:Finset GreenA in atTop, ∀ i, Allows 4 ((boom (Meld Z x) i 0-rill (piste R legF (spikes R legF L (rim x))) (YCore x Z i))∘input G n) 0 (calorie x):=by
    obtain ⟨K,P,hK,H⟩:= Fen.east G 4; let D:= S.width; let Y:=panne S
    have hY:0 ≤ Y:=by unfold Y panne Geo.lowerSize; positivity[S.clip.quadratic_pos,S.paths_pos]
    let U(x:ℝ):= bankCost (radiusB x)*K*(momentPrice P (D/2)*Y); let Z(x):=Real.exp (-(D/4)*rim x)*U x; let T (x):=bankCost (radiusB x)*K*shock x+Z x
    have hd:0 < D:= S.width_pos; have hu:ConstMass 0 U:= (bnk.cop (mass hK)).cop (mass (mul_nonneg (momentPrice_pos _ (by positivity)).le hY))
    have hz:Tigh Z 99:= (stern 100 (show 0<D/4 by positivity)).fly hu
    have ht:Tigh T 98:= (shockT.mult (bnk.cop (mass hK))).join hz
    let V(x):= vocation G (eastD x) (tightf x) (U x)+vocation G (eastD x) (Loft.trophy x+tightf x) (T x)
    have hV2:Tigh (fun x=> vocation G (eastD x) (Loft.trophy x+tightf x) (T x)) 94:=by
       have hp:=heat_two G 100 (by norm_num) T _ ht (cupM.gather (stays 70|>.smokes))
       convert! hp using 1; funext i; unfold vocation eastD; ring
    have hV:Tigh V 65:= (heat_two G 100 (by norm_num) tightf U (stays 70) hu).join (hV2.tight (show 66 ≤ 94 by omega))
    let a(x):=shock x*gable G (Perfect.east x/5) 4+tightf x*gable G (eastD x/5) 4+V x
    have hh:Tigh a 64:=by
       have hd: (fun x=>gable G (eastD x/5) 4)=(fun x=>gable G (Perfect.east x/(100*5)) 4):=by ext1 x; unfold eastD; rw [div_div]
       refine Tigh.join (Tigh.join ((shockT.tight (show 67≤100 by omega)).fly (gelling 5 (by norm_num) (G:=G) 4)) ((Tigh.tight (stays 70) (show 67≤70 by omega)).fly (a:=0) ?_)) hV
       rw[hd]; exact gelling _ (by norm_num) _
    filter_upwards [hu 1 zero_lt_one,ht, eastP,eventually_gt_atTop (0:ℝ),hh.tight (show 30≤64 by omega),weather G A ha k _ (by norm_num:0<(1/200:ℝ)),sense G A k ha,Work.E01.radiusB_tendsto.eventually_ge_atTop 2] with x hx hz hv hp' hh hg hs hb n R Q hm hQ
    have hb:2≤R.p.B:= hm.2.1.symm ▸ hb; let V' := YCore x Q; have hw:=hm.2.2; rw [← hm.1] at hw
    have he:= H n R D S.paths (humble x) hw hb; have hZ: bankCost R.p.B * K * (momentPrice P (D/2)* (Geo.lowerSize R.clip S.paths+(S.paths+S.paths))) = U x:=by rw[hm.1,hm.2.1]
    have hp:0 < shock x:=by unfold shock; positivity
    filter_upwards [he.2 (rim x) (shock x) hp] with L hl i
    have hu(e): Allows 4 (outD (Fen.Main R) e ∘ input G n) 0 (U x):= hZ ▸ he.1 e
    let H:= ski R legF L (rim x); have hm'(e): Allows 4 (outD (Main R-H) e ∘ input G n) 0 (T x):=by have hv:=hl e; rw[hZ,hm.2.1] at hv; exact hv
    obtain ⟨hg,_,h1,h2⟩:=hg n Q R hQ i
    let W:=V' i; have hw':W∈ rains G n:= hg.rises
    have he:=div_pos hv.1 (by norm_num:0<(100:ℝ)); have hM:0 ≤ tightf x:=by unfold tightf; positivity
    have hf:= duck R hw L (rim x) hG (o:=0) (hQ.1.sound.palm i 0) hw' h1 h2 he hM (sum_nonneg fun _ _=> abs_nonneg _) hx.1 hz.1 hu hm'
    have ht := shedU R i (rim x) 0 L hQ.1 (hs n Q R hQ|>.2.2.2 i) he hM hv.1 hp.le hw' hf
    exact ht.mono hh.2
end YM.Trace.Zn
