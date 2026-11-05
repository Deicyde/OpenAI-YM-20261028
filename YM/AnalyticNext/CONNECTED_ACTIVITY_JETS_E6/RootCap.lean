import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Shutter
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Trail

/-!
# Cap on real V source of the transported affine row

Strengthen H^{-1/2+o} to C(L)*t using a fresh weak comparison at a
pre-fixed radius for each test. No global V requirement. For cut tails
here pay one-by-one before compressing at D. Work for k even nonalive,
so b loaded on genuine branch. Later derivatives fixed U separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.SliceRows
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Work.E04
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {P : Teller G} {S : StepData c f} {T : Tube G S}

private def preCap (n : ℕ) := 16*(2*(n+1:ℕ)+1:ℝ)^5 * (Fintype.card PlaqAxes:ℝ)*2
private lemma gauge_at (V : Config G c) (o : Site c) {x : ℝ} (h : Room P S T x) (n : ℕ)
    (hv : n ≤ radiusB x) (ht : Clean V x o (n+1)) : ∃ z : Site c→G.El, ∀ b : Bond c, separation o b.1 ≤ n →
      G.chord (Lattice.gauge z V b) ≤ preCap n*Pressure.fiery G x S.patch.L := by
  obtain ⟨z,hz⟩ := Work.E08.axial_patch o V n (n+1) le_rfl (by have he := h.buys; omega) _ (SectorMeasure.temp_nonneg x)
    (fun i hi p => ht.toll (b:=(i,p)) hi)
  refine ⟨z,fun i hi => ?_⟩; unfold preCap; rw [mul_assoc _ 2 _]
  exact (hz i hi).trans (mul_le_mul_of_nonneg_left h.temperatures (by positivity))

private lemma faces_near (V : Config G c) (i : Cell f) {x : ℝ} (h : Room P S T x)
    (hp : Clean V x (S.ratio.parent i.1) 5) :
    G.chord (faceValue (replica S.ratio V) i) ≤ 4*(preCap 4*Pressure.fiery G x S.patch.L) := by
  let o := S.ratio.parent i.1
  have ht : 4 ≤ radiusB x := le_trans (by norm_num) h.sight.1
  obtain ⟨z,hz⟩ := gauge_at V _ h 4 ht hp
  let U := replica S.ratio (gauge z V)
  let v : Config G f := fun j => if distAt S j o ≤ 4 then U j else 1
  let t := preCap 4 * Pressure.fiery G x S.patch.L
  have he : 0≤t := by have := h.fiery; unfold t preCap; positivity
  have hs j : G.chord (v j) ≤ t := by
    unfold v; split
    next hg =>
      unfold U replica; split
      next _ => rwa [G.chord_one]
      exact hz _ hg
    next hg => rwa [G.chord_one]
  rw [show G.chord (faceValue (replica S.ratio V) i)=G.chord (faceValue U i) by
    unfold U; rw [← copied S.ratio S.patch.odd_side,face_gauge, G.chord_conj]]
  unfold faceValue
  rw [travel_near _ (parent_step S) U v _ _ 4 (by simp [square]) (fun j hj => Eq.symm (if_pos (c:=distAt S j o≤4) hj))]
  apply (travel_chord v _ _ _ hs).trans_eq
  norm_num [square,t]

private lemma X_local (V : Config G c) (p : Twin f) {x : ℝ} (h : Room P S T x)
    (hx : Clean V x (S.ratio.parent p.1.1) (radiusB x)) :
    ‖T.Xf (till x) (replica S.ratio V) p‖ ≤
      (4*preCap 4*(Real.sqrt P.top.clip.direct+P.top.paths))*Pressure.fiery G x S.patch.L := by
  obtain ⟨X,Y,H,-⟩ := h.accepted.feeds
  let R := till x
  let b := p.1
  let V' := replica S.ratio V; let t := Pressure.fiery G x S.patch.L
  let Z := 4*(preCap 4*t)
  have hC : 0 ≤ P.top.paths := P.top.paths_pos.le
  have hz := h.sight.1
  have he := h.fiery
  have hZ : 0 ≤ Z := by unfold Z t preCap; positivity
  have hp (i : Cell f) (hi : separation (S.ratio.parent b.1) (S.ratio.parent i.1)+5 ≤ radiusB x) :
      ‖G.curvature (faceValue V' i)‖ ≤ Z := (G.curvature_norm _).trans (faces_near V i h (hx.shrink hi))
  have hk : 0 ≤ Real.sqrt P.top.clip.direct := Real.sqrt_nonneg _
  have hg : (4*preCap 4*(Real.sqrt P.top.clip.direct+P.top.paths))*t=(Real.sqrt P.top.clip.direct+P.top.paths)*Z := by unfold Z; ring
  change ‖T.Xf R V' p‖ ≤ _*t; rw [hg]
  unfold Tube.Xf plotted; split
  next hw =>
    let W := shortenTerm T.up R 1 V' b
    have hh i : ‖W i‖ ≤ Z*rich T.up P.top.width b.2 i := by
      unfold W shortenTerm; let A := T.up.row b.2 i; split
      next hs =>
        rw [PathData.ellTerms,atSite_path,norm_smul, G.norm_adjoint]
        apply (mul_le_mul_of_nonneg_left (hp _ ?_) (norm_nonneg _)).trans
        · rw [mul_comm Z, Real.norm_eq_abs]; apply mul_le_mul_of_nonneg_right _ hZ; unfold rich
          exact le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg P.top.width_pos.le (Nat.cast_nonneg _)))
        have hh := Work.E04.slot_separation A.2 b.1 (n:=f)
        have he := Work.E04.parent_separation S.ratio b.1 (slotFace A.2 b.1).1
        apply le_trans (Nat.add_le_add_right he 5)
        change separation b.1 (slotFace A.2 b.1).1 ≤ A.2.length at hh
        change A.2.length*1 ≤ R at hs; unfold R till at *; omega
      next ht => rw [norm_zero]; exact mul_nonneg hZ ((H.rows b.2).1 i)
    have hP := budget_mono (budget_scale hZ (H.rows b.2)) (fun i => norm_nonneg (W i)) hh
    exact ((norm_tsum_le_tsum_norm hP.2.1).trans hP.2.2).trans ((mul_comm ..).le.trans
      (mul_le_mul_of_nonneg_right (by linarith) hZ))
  next hw =>
    unfold shoot; rw [norm_smul,h.accepted.high,Real.norm_eq_abs,abs_of_nonneg hk]
    apply mul_le_mul (le_add_of_nonneg_right hC) (hp p.1 (by unfold b; rw [separation_self]; omega))
      (norm_nonneg _) (add_nonneg hk hC)

lemma reference_v (g : Site c→G.El) (hp : P.Funds S T) (x : ℝ) (k : S.Choices) (p : Rod c f) (V : Config G c) :
    baseStroke T x k (gauge g V) p = G.adjoint (g (focus S p)) (baseStroke T x k V p) := by
  unfold baseStroke; rw [← copied S.ratio S.patch.odd_side,entry_turn hp]

lemma crowns (P : Teller G) (D : Patch) (hd : D.Branches P.bind G) (L : Side) : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ x in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=D → S.patch.L=L → Room P S T x →
    ∀ (V : Config G c) (k : S.Choices) (p : Rod c f), Clean V x (focus S p) (radiusB x) →
      ‖baseStroke T x k V p‖ ≤ C*Pressure.fiery G x S.patch.L := by
  obtain ⟨Y,r,hY,hr,H⟩ := extend_interior G
  obtain ⟨J,q,hJ,hq,h⟩ := z_chart_cost D P.bind G hd
  let u := predReach D
  let K := preCap u
  let A := Y*K
  let C₁ := (4*preCap 4*(Real.sqrt P.top.clip.direct+P.top.paths))
  have : 0 < Fintype.card PlaqAxes := by decide
  have hK : 0<K := by unfold K preCap; positivity
  have hA : 0<A := mul_pos hY hK
  have hc : 0<C₁ := by unfold C₁ preCap; have := P.top.paths_pos; positivity
  have hz := (Rate.flame (L:=L) (G:=G))
  refine ⟨C₁+2*J*A,by positivity,?_⟩
  filter_upwards [(hz.mul_left K).below (by norm_num) r hr,(hz.mul_left A).below (by norm_num) (min 1 q) (lt_min zero_lt_one hq)] with
    x hx hy c f S T hS hL hR V k p hp
  let t := Pressure.fiery G x S.patch.L
  have ht : 0<t := hR.fiery; have h' : Pressure.fiery G x L=t := by unfold t; rw [hL]
  rcases p with p|b
  · refine (X_local V p hR hp).trans ?_; apply mul_le_mul_of_nonneg_right _ ht.le
    exact le_add_of_nonneg_right (show 0≤ 2*J*A by positivity)
  rw [h'] at hx hy
  obtain ⟨hs,hq⟩ := le_min_iff.mp ((le_abs_self _).trans hy)
  have hd' : u+1 ≤ radiusB x := by have hh := hR.frame; unfold u; rw [← hS]; omega
  let o := b.1
  have hk : Clean V x o (u+1) := hp.shrink (by change separation b.1 b.1+_ ≤ _; rw [separation_self]; omega)
  obtain ⟨g,H'⟩ := gauge_at V o hR _ (by omega : u≤radiusB x) hk
  obtain ⟨B,hb,hV⟩ := H id o u (gauge g V) _ (show 0 ≤ K*t from (mul_pos hK ht).le) ((le_abs_self _).trans hx) H'
  let W := toLog (linearCopy S.ratio (collect G B))
  let w : PairLogs G f c := (W,B)
  have hw : ‖w‖ ≤ A*t := by
    have he : ‖W‖ ≤ ‖B‖ := by unfold W; rw [counted]; exact cp_cap S _
    exact (max_le he le_rfl).trans (hb.trans (by unfold A; rw [mul_assoc]))
  obtain ⟨hx,hh⟩ := h c f S hS hR.accepted.knobs k b w
  have hz : baseStroke T x k (gauge g V) (.inr b) = zTest S k b w := by
    change Z S _ _ b=_; unfold Z zTest
    have he : represent W=replica S.ratio (represent B) := by unfold W; rw [represent,collects]; exact exp_copy ..
    rw [prediction_near_eq (funds_branch hR.accepted) (replica S.ratio (gauge g V)) (represent W) k b ?_]
    unfold Pressure.Tube.Z; simp only [w]; rw [hV b (by unfold o; simp)]
    rw [he]; apply replica_near; rwa [hS]
  rw [← G.norm_adjoint (g (focus S (.inr b))),← reference_v g hR.accepted, hz]
  calc
    _ ≤ J*‖w‖^2 + J*‖w‖ := ((show ‖zTest S k b w‖≤‖zTest S k b w-zLin S W B b‖+‖zLin S W B b‖ from by
      simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub (zTest S k b w) _ 0).trans (add_le_add (hh (hw.trans hq)) hx))
    _ ≤ _ := by
      change _ ≤ _ * t
      have hp := norm_nonneg w; have hz := hw.trans hs
      nlinarith [mul_le_mul_of_nonneg_left hw hJ.le, mul_le_mul_of_nonneg_left (show ‖w‖^2 ≤ ‖w‖ by nlinarith) hJ.le]
end YM.ConnectedActivityE6.SliceRows
