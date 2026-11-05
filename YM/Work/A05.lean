import YM.Bid.Angular
import YM.Work.A05.Weak

/-!
Use finitely many tests of the free-slot maps at caps `d` and `d+1`.
Request sufficient room for the tests and the whole shells around them
from Track. Use each scaling system satisfying that request exactly as
it is, including its common stress meter, recovering *both* maps.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.A05
open Set Function Filter Table Climb Ward
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {L : Register G} {S : Table L}

namespace Observer

def cut (o : Observer S) : E4 → ℝ := Classical.choose (has_window o.x o.hx)
lemma cut_window (o : Observer S) : Table.Window o.x o.cut := Classical.choose_spec (has_window o.x o.hx)

structure Room (o : Observer S) (d N D : ℕ) (R : ℝ) : Prop where
  stress : 4 ≤ D
  caps : d+1 ≤ D
  rest : ∀ i, (o.q i).1 ≤ D
  total : o.n+2 ≤ N
  fits : o.x ∈ Scaling.window R _
  ringFits : ∀ y ∈ tsupport (fderiv ℝ o.cut), Points.cons y o.x ∈ Scaling.window R _

lemma enough (o : Observer S) (d : ℕ) :
    ∃ D N R, 1 ≤ R ∧ ∀ E ≥ D, ∀ n ≥ N, ∀ B ≥ R, Room o d n E B := by
  have hq : ∀ᶠ E : ℕ in atTop, ∀ i, (o.q i).1 ≤ E := eventually_all.mpr fun i => eventually_ge_atTop _
  obtain ⟨E,hE,ht,he⟩ := (hq.and ((eventually_ge_atTop (d+1)).and (eventually_ge_atTop 4))).exists
  have hc : ∀ᶠ R : ℝ in atTop, o.x ∈ Scaling.window R _ := by
    filter_upwards [compact_fits isCompact_singleton (Set.singleton_subset_iff.mpr o.hx)] with R hr
    exact hr (Set.mem_singleton o.x)
  obtain ⟨r,hr⟩ := eventually_atTop.1 (hc.and (shell_fits o.hx o.cut_window))
  refine ⟨E,o.n+2,max 1 r,le_max_left ..,fun u hu m hm v hv => ?_⟩
  obtain ⟨hh,hR⟩ := hr v ((le_max_right ..).trans hv)
  exact ⟨he.trans hu,ht.trans hu,fun i => (hE i).trans hu,hm,hh,hR⟩

lemma enough_all (s : Finset (Observer S)) (d : ℕ) :
    ∃ D N R, 1 ≤ R ∧ ∀ E ≥ D, ∀ n ≥ N, ∀ B ≥ R, ∀ o ∈ s, Room o d n E B := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0,0,1,le_rfl,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨e,n,r,h,hp⟩ := ih
    obtain ⟨f,m,u,h',hq⟩ := i.enough d
    refine ⟨max e f,max n m,max r u,le_max_of_le_left h,fun T hT N hN B hB j hj => ?_⟩
    obtain rfl|hj := Finset.mem_insert.1 hj
    · exact hq _ ((le_max_right ..).trans hT) _ ((le_max_right ..).trans hN) _ ((le_max_right ..).trans hB)
    exact hp _ ((le_max_left ..).trans hT) _ ((le_max_left ..).trans hN) _ ((le_max_left ..).trans hB) j hj

lemma gets_translation (o : Observer (Bel L)) (H : S.Smooth) (T : Lighthouse L) (H' : (Bel L).Smooth)
    {a : (Bel L).RealSpin} (hl : T.Goes L a) {J : S.Stress} {p : Climb.Parts S} {Y : Ward.SpinRows S}
    (hg : StressLaws S J p Y) (X : Scaling S) {d N D m : ℕ} {R : ℝ} (hr : Room o d N D R)
    (hw : X.jets N D m R) (hk : X.meter J T.J) (b : Axis) (v : (Bel L).Field d) :
    Tendsto (fun k => o.moving X (d+1) k (((X.r k / X.xi k) • X.aisle k d (leaves p d)) b v)) atTop
      (𝓝 (o.test (d+1) (leaves (T.κ • T.W.deriv) d b v))) := by
  have hd : d ≤ D := (Nat.le_succ d).trans hr.caps
  have he := reaches_grad X H H' hk o.x o.hx o.cut_window b hw hr.total hr.stress hr.ringFits o.q hr.rest d v hd
  have ht : shellGrad (Bel L) T.J o.cut b o.x o.q v = o.test (d+1) (leaves (T.κ • T.W.deriv) d b v) := by
    rw [hl.delta.translation o.hx _ o.cut_window]; unfold test; rw [frontRead_at]; rfl
  rw [ht] at he
  refine he.congr (fun k => ?_)
  have hc := window_stretch (X.positive k) o.cut_window
  rw [hg.translation (smul_conf (X.positive k) o.hx) _ hc]
  change _ = frontRead _ _ _ (X.U k (d+1) ((X.r k/X.xi k) • X.carry k (leaves p d b) v))
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) _ (X.carry k (leaves p d b) v),map_smul, map_smul,
    X.carries_f,frontRead_at]; rfl

lemma gets_rotation (o : Observer (Bel L)) (H : S.Smooth) (T : Lighthouse L) (H' : (Bel L).Smooth)
    {a : (Bel L).RealSpin} (hl : T.Goes L a) {J : S.Stress} {p : Climb.Parts S} {Y : Ward.SpinRows S}
    (hg : StressLaws S J p Y) (X : Scaling S) {d N D m : ℕ} {R : ℝ} (hr : Room o d N D R)
    (hw : X.jets N D m R) (hk : X.meter J T.J) (i : Spin.Ind) (v : (Bel L).Field d) :
    Tendsto (fun k => o.moving X d k (((X.xi k)⁻¹ • Spin.transport Y (X.U k d) i) v)) atTop
      (𝓝 (o.test d ((T.κ • Spin.leaf T.K.lie d i) v))) := by
  let g := Spin.K i
  have hd : d ≤ D := (Nat.le_succ d).trans hr.caps
  have he := reaches_spin X H H' hk o.x o.hx o.cut_window g hw hr.total hr.stress hr.ringFits o.q hr.rest d v hd
  have ht : shellSpin (Bel L) T.J o.cut g o.x o.q v = o.test d ((T.κ • Spin.leaf T.K.lie d i) v) := by
    rw [hl.delta.rotation o.hx _ o.cut_window]; unfold test; rw [frontRead_at]; rfl
  rw [ht] at he
  refine he.congr (fun k => ?_)
  have hc := window_stretch (X.positive k) o.cut_window
  rw [hg.rotation (smul_conf (X.positive k) o.hx) _ hc]
  let U := X.U k d
  change _ = frontRead _ _ _ (U ((X.xi k)⁻¹ • U.symm (Y d g (U v))))
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) _ (U.symm (Y d g (U v))),map_smul, map_smul,
    U.apply_symm_apply,frontRead_at]; rfl
end Observer

/-- Transport the flux pair on any Track with adequate finite requests. -/
theorem answer : YM.Bid.A05 := by
  intro G C S H V _ _ T J d p Y h
  classical
  obtain ⟨s,hs⟩ := Observer.exists_reads T.hT (d+1)
  obtain ⟨t,ht⟩ := Observer.exists_reads T.hT d
  obtain ⟨D,N,R,hR,hB⟩ := Observer.enough_all (s ∪ t) d
  refine ⟨D,N,0,R,hR,fun X E n m r hE hn _ hr hz => ?_⟩
  have ha (o) (ho : o ∈ s) := hB _ hE _ hn _ hr o (Finset.mem_union_left t ho)
  have hb (o) (ho : o ∈ t) := hB _ hE _ hn _ hr o (Finset.mem_union_right s ho)
  constructor
  · unfold Bid.ConLap
    refine tendsto_pi_nhds.mpr fun b => ?_
    apply clm_convergence; intro u
    refine recover_on s (fun o => o.test (d+1)) hs (fun o k => o.moving X (d+1) k) ?_ _ _ ?_
    · intro o ho v
      have hw := ha o ho
      exact o.reads_converge X hz.thick ((Nat.le_succ _).trans hw.total) hw.rest hw.fits (d+1) hw.caps v
    intro o ho
    exact o.gets_translation H.smooth T.T T.hT.smooth T.lit h.raw X (ha o ho) hz.thick hz.loc b u
  intro j; apply clm_convergence; intro u
  refine recover_on t (fun o => o.test d) ht (fun o k => o.moving X d k) ?_ _ _ ?_
  · intro o ho v
    have hw := hb o ho
    exact o.reads_converge X hz.thick ((Nat.le_succ _).trans hw.total) hw.rest hw.fits d
      ((Nat.le_succ d).trans hw.caps) v
  intro o ho
  exact o.gets_rotation H.smooth T.T T.hT.smooth T.lit h.raw X (hb o ho) hz.thick hz.loc j u
end YM.Work.A05
