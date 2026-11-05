import YM.TraceExtension.Zn.Arc
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Zn
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits Pills Loft Xo
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {F:ℝ→ℝ}{a b c:ℝ}{k:ℕ}{G:Gauge}{n:Side}
lemma bills(X:ℝ→ℝ) (T q:ℝ)(u:ℕ)(ht:0≤ T)(hq:0<q)(hx:ConstMass a X):ConstMass a (fun x=> DockAmt G (radiusB x) T (puff x) u (X x) q):=by unfold DockAmt; push_cast; have ht':=(hx.times (momentPrice u (q/2)) (momentPrice_pos _ (by positivity)).le).times T ht; have h:=(((balloon.gather balloon).gather (mass zero_le_one)).crop 4).prod (bnk.prod ht'); simpa only [zero_add] using! h
abbrev panne(S:Stage):=Geo.lowerSize S.clip S.paths+(S.paths+S.paths)
def hornS(G:Gauge)(x:ℝ)(k:ℕ)(Y:ℝ):ℝ:=(( (high x+high x+1)^4:ℕ)*Fintype.card (Loc G 1):ℕ)*(2^k*mew x*Y)
lemma honour_l(x:ℝ)(k:ℕ){t:ℝ}(ht:0≤ t): blare G (ExtS n x) k (mew x) t ≤ hornS G x k t:=by
   apply mul_le_mul_of_nonneg_right ?_ (show 0 ≤ (2:ℝ)^k * mew x *t from by have hh:=wake (1/2000) x; unfold mew; positivity)
   exact Nat.cast_le.mpr (Nat.mul_le_mul_right _ ((Corona.halo_size ..).trans (by simp)))
lemma honest(G:Gauge)(k:ℕ)(h:ConstMass a F):ConstMass (1/2000+a) (fun x=>hornS G x k (F x)):=by
    unfold hornS; push_cast; refine ?_; have hx:= (((((expansion.gather expansion).gather (mass zero_le_one)).crop 4).cop (mass (show 0 ≤ (Fintype.card (Loc G 1):ℝ) by positivity))).prod (((waveM (1/2000)).times ((2:ℝ)^k) (by positivity)).prod h)); simpa only [zero_add] using! hx
set_option maxHeartbeats 640000 in
lemma primeB(G:Gauge)(hG:G.Simple)(S:Stage)(A:ℝ)(ha:0 ≤ A)(k:ℕ): ∀ᶠ x:ℝ in atTop,∀ (n:Side)(R:Rep G n) (Z:Dart G n), Made S x R→Sight x R Z →
    ∀ᶠ L:Finset GreenA in atTop, Splendor (mainP R x L) (ExtS n x) k (thinM x) A ∧ Drift _ (mainP R x L) ∧ (∀ i, rill (mainP R x L) (YCore x Z i) = rill (piste R legF (spikes R legF L (rim x))) (YCore x Z i)) ∧ (∀ i,HearthV (rill (mainP R x L) (YCore x Z i)) (ExtS n x) k (thinM x) A):=by
   obtain ⟨C,hC,H⟩:= phare G hG A ha k
   obtain ⟨W,P,hW,h⟩:= policy G (k+1) C hC
   obtain ⟨W',P',hW',h'⟩:= policy G k A ha
   let f(x):= DockAmt G (radiusB x) W (puff x) P (panne S) S.width
   let g(x):= DockAmt G (radiusB x) W' (puff x) P' (panne S) S.width
   have hp: 0≤ panne S:=by unfold panne Geo.lowerSize; positivity [S.clip.quadratic_pos, S.paths_pos]
   have hf:= bills (G:=G) (X:=fun _=>panne S) _ S.width P (by linarith only[hW]) S.width_pos (mass hp)
   have hg: ConstMass 0 g:= bills (X:=fun _=>panne S) W' _ P' (by linarith only[hW']) S.width_pos (mass hp)
   have hv:= honest G k (F:=f) hf
   filter_upwards [hg (1/200) (by norm_num), hf (1/200) (by norm_num), hv (1/200) (by norm_num),weather G A ha k (1/2000) (by norm_num), Work.E01.radiusB_tendsto.eventually_ge_atTop 2] with x hx hy hz ht hB n R Z hm hJ
   have ha := hm.2.2; rw [← hm.1] at ha; have hB: 2≤ R.p.B:= hm.2.1.symm ▸ hB
   have hS: SumBudget (Pointed R legF S.width) (panne S):=by unfold panne; rw [← hm.1]; exact off_budget R ha
   filter_upwards with L
   let F:= mainP R x L; have hT: ExtS n x=Turret.sprout (0:Site n) (salo R (puff x) (rim x)):=by rw [adriftR R x S hm]
   have hψ: Drift ℝ F:=hymn R legF (spikes R legF L _) _
   have hiK(K:ℝ)(E:ℕ)(p:ℕ)(D:ℝ)(he:Splendor F (Turret.sprout (0:Site n) (salo R (puff x) (rim x))) E (DockAmt G R.p.B K (puff x) p (panne S) S.width) D): Splendor F (ExtS n x) E (DockAmt G (radiusB x) K (puff x) p (panne S) S.width) D:= by rw[hT,← hm.2.1]; exact he
   have ht1(i):= ht n Z R hJ i
   have hu := hiK W (k+1) P C (h GreenA legF n 0 R S.paths _ (panne S) _ ha hG hB hS L (puff x) (rim x))
   have hL:= hiK W' k P' A (h' GreenA legF n 0 R S.paths _ (panne S) _ ha hG hB hS L (puff x) (rim x))
   refine ⟨hL.up (fun _ h=>h) hx.2,hψ,fun i=>(husk R legF _ (ht1 i|>.1) hB).symm,fun i=>?_⟩
   let B:= ExtS n x; have hC := (ht1 i|>.1).wider (show Bay n x⊆ B from sprout_mono _ (show puff x≤high x by unfold high; omega))
   exact mot k _ _ (blare G B k (mew x) (f x)) A A B le_rfl (H n _ F B (mew x) (f x) hψ (ht1 i|>.2.1) hC hu) ((honour_l _ _ hy.1).trans hz.2)
end YM.Trace.Zn
