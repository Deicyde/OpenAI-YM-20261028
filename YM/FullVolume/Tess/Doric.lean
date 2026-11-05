import YM.FullVolume.Tess.Bars
/- derivative recovery from uniform data alone. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Tess
open Filter Function Set Metric MeasureTheory Lattice RG Ray Asymptotics
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
open Extraction Extraction.Lease Difference Amp
variable {S:Schedule} {n N j m p:ℕ}{K:Set (Points n)}
local notation "A"=>S.a
local notation "T"=>MotionIndex n
structure Scroll {Y:Type}[MetricSpace Y] (S:Schedule) (K:Set (Points n))(g:ℕ→ Positions n→Y) (F:Points n→ Y): Prop where
    land : ContinuousOn F K
    wins : ∀ ε:ℝ,0<ε→∀ᶠ i in atTop, ∀ y:Positions n,tag (S.a i) y∈K → dist (g i y) (F (tag (S.a i) y))< ε
namespace Scroll
section
variable {Y : Type}[MetricSpace Y]{g:ℕ→Positions n→ Y} {G:Points n→Y} (h: Scroll S K g G)
variable {v:ℕ→ℕ}{x:ℕ→ Positions n} (hp:Tendsto v atTop atTop)
include h hp
lemma retreat {y:Points n}(hy:y∈K)(hx:∀ᶠ i:ℕ in atTop,tag (S.a (v i)) (x i)∈K)(he:Tendsto (fun i=> tag (S.a (v i)) (x i)) atTop (𝓝 y)):Tendsto (fun i=>g (v i) (x i)) atTop (𝓝 (G y)):=by
    let F i:=tag (A (v i)) (x i)
    have ht:Tendsto F atTop (𝓝[K] y):= tendsto_nhdsWithin_iff.mpr ⟨he,hx⟩; have hv: Tendsto (fun i=>G (F i)) atTop (𝓝 (G y)):= (h.land y hy).tendsto.comp ht
    apply hv.congr_dist
    apply Metric.tendsto_nhds.mpr; intro ε he; filter_upwards [hx,hp.eventually (h.wins ε he)] with i hi hv; rw [dist_zero_right,Real.norm_of_nonneg dist_nonneg,dist_comm]; exact hv _ hi
lemma inure {y:Points n}(hy:y∈interior K)(he:Tendsto (fun i=> tag (S.a (v i)) (x i)) atTop (𝓝 y)): Tendsto (fun i=>g (v i) (x i)) atTop (𝓝 (G y)):=h.retreat hp (interior_subset hy) (he.eventually (mem_interior_iff_mem_nhds.mp hy)) he
end
variable {g:ℕ→Positions n→ ℂ} {G:Points n→ℂ}{P:MotionIndex n→ℕ→Positions n→ℂ}{H:MotionIndex n→Points n→ℂ}
variable (h: Scroll S K g G)(hp:∀ j:MotionIndex n,Scroll S K (P j) (H j))
variable (hV: ∀ᶠ i in atTop, ∀ (x:Positions n)(j:MotionIndex n), tag (S.a i) x∈ K → tag (S.a i) (x+drive j) ∈ K → g i (x+drive j) - g i x= S.a i • P j i x)
include h hp hV
lemma vivify {x:Points n}(hx:x∈interior K): HasFDerivAt G (stretch (fun j=> H j x)) x:=by
    let V:= stretch (fun j=> H j x); let q:= Fintype.card (MotionIndex n)
    rw [hasFDerivAt_iff_isLittleO, isLittleO_iff]; intro ε he
    let c:= ε/(2*(q+1:ℕ)); have hc:0<c:= div_pos he (by positivity)
    have he :∀ᶠ y in 𝓝 x, y∈ interior K ∧ ∀ i:MotionIndex n, dist (H i y) (H i x) ≤ c:= (show ∀ᶠ y in 𝓝 x,y∈ interior K from isOpen_interior.mem_nhds hx).and (eventually_all.mpr fun i=> ((hp i).land x (interior_subset hx)|>.continuousAt (mem_interior_iff_mem_nhds.mp hx)).tendsto.eventually (closedBall_mem_nhds _ hc))
    obtain ⟨r,hr,hR⟩:= Metric.nhds_basis_closedBall.mem_iff.mp he
    filter_upwards [ball_mem_nhds x (show 0< r/4 from div_pos hr (by norm_num))] with y hy; rw [mem_ball] at hy
    let u i := address (S.a i) x; let w i:=address (S.a i) y; let X i:= tag (A i) (u i); let Y i:= tag (A i) (w i)
    have hX:Tendsto X atTop (𝓝 x):= Extraction.chosen x; have hY:Tendsto Y atTop (𝓝 y):= Extraction.chosen y
    have hv:y∈interior K:= hR (Metric.mem_closedBall.mpr (by linarith only [hy,hr]))|>.1
    have hY1:= h.inure (v:=id) (x:=w) tendsto_id hv hY
    have hX1:= h.inure (v:=id) (x:=u) tendsto_id hx hX
    have hJ:Tendsto (fun i=> ‖g i (w i)-g i (u i)-V (Y i-X i)‖) atTop (𝓝 ‖G y-G x -V (y-x)‖):= ((hY1.sub hX1).sub (V.continuous.continuousAt.tendsto.comp (hY.sub hX))).norm
    have hP:= (hY.dist hX).const_mul ε; rw [dist_eq_norm y x] at hP
    apply le_of_tendsto_of_tendsto hJ hP
    have ha:= eventually_all.mpr fun i:MotionIndex n=> (hp i).wins c hc
    have hr4: 0< r/4:= by positivity
    have hy': dist y x<r/2:=by linarith only [hy,hr]
    filter_upwards [hV,ha,hX.eventually (Metric.closedBall_mem_nhds x hr4),(hY.dist hX).eventually (ge_mem_nhds hy'), S.shrinks.eventually (ge_mem_nhds hr4)] with i hi ha hv hw hS
    let f(u0:Positions n):=g i u0 - V (tag (A i) u0)
    change ‖g i (w i)-g i (u i)- V (Y i-X i)‖ ≤ ε*dist (Y i) (X i)
    rw [map_sub,← sub_sub_sub_comm]; change ‖f (w i)-f (u i)‖≤ _; rw [← dist_eq_norm]
    refine (stroll (S.a_pos _) f (u i) (w i) (r/2) (2*c) (by positivity) hw (fun u₀ j hu=>?_)).trans (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
    · let s:= tag (A i) u₀; let z:=tag (A i) (u₀+drive j); have hh: dist z s=A i:=by simpa only [one_smul,Nat.cast_one,one_mul] using! paidDist u₀ (A i) (S.a_pos _) j 1
      have h' : dist s x≤ r/2 + r/4:= (dist_triangle _ (X i) x).trans (add_le_add hu (Metric.mem_closedBall.mp hv)); have hZ:z∈ K:=interior_subset (hR (Metric.mem_closedBall.mpr ((dist_triangle z s x).trans (le_trans (add_le_add (hh.trans_le hS) h') (by linarith)))) |>.1)
      have hs := hR (show s∈ Metric.closedBall x r from Metric.mem_closedBall.mpr (by linarith only [h',hr])); have he':s∈ K:=interior_subset hs.1
      have hq:=hi u₀ j he' hZ; have h : V (tag (A i) (u₀+drive j)) - V s= A i • H j x:=by rw [tagged,map_add,map_smul, add_sub_cancel_left, loyal]
      rw [dist_eq_norm]; unfold f; rw [sub_sub_sub_comm, hq,h,← smul_sub, norm_smul,Real.norm_of_nonneg (S.a_pos _|>.le), ← dist_eq_norm]
      apply mul_le_mul_of_nonneg_left _ (S.a_pos _|>.le); exact le_trans (dist_triangle _ (H j s) (H j x)) ((add_le_add (ha j u₀ he'|>.le) (hs.2 _)).trans_eq (by ring))
    let c' :ℝ:= q
    have hu : c*(2*(q+1:ℕ))=ε:= div_mul_cancel₀ ε (by positivity)
    push_cast at hu
    linarith only [hc,hu]
end Scroll
end YM.FullVolume.Tess
#print axioms YM.FullVolume.Tess.Scroll.vivify
