import YM.AnalyticNext.QUARTIC_MATCH.Pre.Trial
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Moment



/-!
# Exact `crossings` on auxiliary periods: no Rack sufficiency hypothesis

ric from Echo. The uncut kernels in this very same M retain their
 generation. Extent Ladder must still pay Gap etc on other periods.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Pane
open Filter Function Set Lattice Wilson RG RG.Supply Input Precision Org
open Push.PriceCompiler Push.SectorMeasure Push.AbsoluteSums ConnectedActivityE6 AnalyticBridge.VerifiedReset
open UVNext UVNext.PricedKernels Bloch Echo Next.Free Craft Laurent Work.F08 AnalyticNext.QuarticMatch.Pre.Rows Exterior Next.Fluctuations
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {a : Levels G} {s : Horizon a} {K : MapPrices}
set_option maxHeartbeats 360000 in
lemma panes (h : s.Suffices K) {m N : ℕ} (hm : m<N) (c f : Side) (H : f.val=c.val*(a.S.block m).val) : let S := again a m c f H
    Towers.Diagonal S (s.H N (m+1)) (s.H N m) (s.towers N m) := by
  let i:= a.clock.J m; let j:= a.clock.J (m+1); let T:= s.towers N m; let A:= s.H N (m+1); let B:= s.H N m; let L:= a.S.block m; let P:= (a.clock.op m 0).patch
  have hs := h.costs N m hm; obtain ⟨hv,hS⟩:=hs.2.2.2 [] (Nat.zero_le _)
  have hi : Whole A.metric := ⟨K.α j,_,K.alpha_pos _,(h.rows N (m+1) hm).2.1⟩
  have hj : Whole B.metric := ⟨K.α i,_,K.alpha_pos _,(h.rows N m hm.le).2.1⟩
  have ht : Whole T.A0 := ⟨K.α j,_,K.alpha_pos _,hv⟩
  have hw : Whole T.T := ⟨K.α j,_,K.alpha_pos _,hS⟩
  let M : Cross L (TypeFace 1) (TypeFace 1) := transRows (word P); have hM:Whole M:=(word_pay P).flipped
  let Q i' := a.S.side m i'; let R i':= a.S.side (m+1) i'; have hV p : (R p).val=(Q p).val*L.val:= (a.S.oneStep m p).exact_size
  have ha p := h.crossings N m p hm
  have hx := schedule_sides a.S m
  have hh (c f : Side) (h : f.val=c.val*L.val) : listens M c f h=(mean (again a m c f h)).transpose := mean_eq (again a m c f h)
  have hy := heardAcross (L:=L) ht; have hQ := heardAcross (L:=L) hM; have hL:= heardAcross (L:=L) hw
  intro S
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · change Precision.K (A.metric.acts f)* listens T.A0 c f H= _; rw [← show listens _ c f _=_ from hh c f H]
    exact allAcross (L:=L) (hy.from (kSound (heard hi))) (hQ.then (kSound (heard hj))) Q R hV hx (fun p=> by rw [hh _ _ (hV p)]; exact (ha p).trial.primal) _ _ H
  · let r := a.clock.kernel.penalty
    let W:= (oneSound (TypeFace 1)).minus ((kSound (heard hj)).scales r⁻¹)
    have hp c f h: (net M T.A0).acts c=(listens M c f h).transpose*listens T.A0 c f h:= net_action (vertical L c f h) hM ht
    have he p : (net M T.A0).acts (Q p)=1-r⁻¹ • Precision.K (B.metric.acts (Q p)) := by rw [hp _ _ (hV p),hh,Matrix.transpose_transpose]; exact (ha p).trial.dual
    have hz := Echo.all (heard (hM.flipped.prod ht)) W Q hx he c
    change (net M T.A0).acts c=_ at hz; rw [hp _ _ H,hh,Matrix.transpose_transpose] at hz
    exact hz
  · apply Matrix.transpose_injective; simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [← show listens _ c f _=_ from hh c f H]
    apply allAcross (L:=L) (hL.from (dSound 1).transpose) (hQ.then (dSound 1).transpose) Q R hV hx _ _ _ H
    intro p; have ht := congr_arg Matrix.transpose (ha p).transport; simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at ht
    rw [hh]; exact ht
  have hA : Whole A.diagonal := ⟨K.α j,_,K.alpha_pos _,(h.rows N (m+1) hm).1⟩
  have hB : Whole B.diagonal := ⟨K.α i,_,K.alpha_pos _,(h.rows N m hm.le).1⟩
  exact allAcross (L:=L) ((hL.then (heard hB)).then (dSound 1)) (hy.from ((heard hA).multiply (dSound 1))) Q R hV hx (fun p=> (ha p).stays) c f H
end YM.PhysicalNext.Repeat.Pane
