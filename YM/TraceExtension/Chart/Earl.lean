import YM.TraceExtension.Chart.Auth
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Over
open Set Function Filter Analysis MeasureTheory Table Ward Climb Extraction Work Work.A05
open Next.UVStress Labels
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {C:Family G}{S:Table C.book}{n:ℕ}
-- scale witness varies.Real linear. This tends the shell precisely; not an integrated insertion identity.
lemma reaches_mutable (X : Scaling S) (H : S.Smooth) (H' : (Climb.Bel C.book).Smooth)
    {J : ℕ→ S.Stress} {T : (Climb.Bel C.book).Stress} (hc:Tendsto (fun i=>Year X i (J i)) atTop (𝓝 T))
    (x : Points (n+1)) (hx : x ∈ conf _) {χ W : E4 → ℝ} (hw : Window x χ) (a b : Axis) (hW : Continuous W)
    {N D m : ℕ} {R : ℝ} (hh : X.jets N D m R) (hn : n+2 ≤ N) (hd : 4 ≤ D)
    (ht : ∀ y ∈ tsupport (fderiv ℝ χ), Points.cons y x ∈ Scaling.window R _)
    (v : Fin (n+1) → (Climb.Bel C.book).Tag) (hv : ∀ i, (v i).1 ≤ D) :
    Tendsto (fun k => (↑(X.r k) : ℂ) * ∫ z, sheet 1 (stretch (X.r k) χ) a (stretch (X.r k) W) (X.r k • x)
        (Fin.cons ⟨4,J k a b⟩ (X.pins k ∘ v)) z) atTop
      (𝓝 (∫ y, sheet 1 χ a W x (Fin.cons ⟨4,T a b⟩ v) y)) := by
  let B (k:ℕ):=reader _ (X.positive k) x hx H hw a hW (X.pins k∘v)
  let A(k):=(B k).comp (X.U k 4).toLinearMap
  let F:=reader 1 one_pos x hx H' hw a hW v
  have he(u): Tendsto (fun k=> A k u) atTop (𝓝 (F u)):=by
     have hz:= tendsto_sheet X H H' x hx hw a hW hh hn ht (Fin.cons ⟨4,u⟩ v) (caps_cons_le u v hd hv)
     simp_rw [pins_cons] at hz; exact hz
  apply (Dash.arcing (Dash.fit_plane A F he) (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hc a) b)).congr
  intro k; let r:=X.r k; let W':=J k; change B k (X.U k 4 ((r^4:ℝ) • ((X.U k 4).symm (W' a b))))=_
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ), map_smul,map_smul,LinearEquiv.apply_symm_apply,integrate_sheet_scale (X.positive k) _ _ hw.1]; change (↑(r^4:ℝ):ℂ)* _=(↑r:ℂ)* ((r:ℂ)^3*_); push_cast; ring_nf; rfl
lemma drape(X : Scaling S) (H : S.Smooth) (H' : (Climb.Bel C.book).Smooth)
    {J : ℕ→ S.Stress} {T : (Climb.Bel C.book).Stress} (hc:Tendsto (fun i=>Year X i (J i)) atTop (𝓝 T))
    (x : Points (n+1)) (hx : x ∈ conf _) {χ : E4 → ℝ} (hw : Window x χ) (b : Axis)
    {N D m : ℕ} {R : ℝ} (hh : X.jets N D m R) (hn : n+2 ≤ N) (hd : 4 ≤ D)
    (ht : ∀ y ∈ tsupport (fderiv ℝ χ), Points.cons y x ∈ Scaling.window R _)
    (v : Fin n → (Climb.Bel C.book).Tag) (hv : ∀ i, (v i).1 ≤ D) (d:ℕ)(u: (Climb.Bel C.book).Field d)(hu:d≤ D):
    Tendsto (fun k=> (↑(X.r k):ℂ)* shellGrad S (J k) (stretch (X.r k) χ) b (X.r k • x) (X.pins k ∘ v) (X.U k d u)) atTop
        (𝓝 (shellGrad (Climb.Bel C.book) T χ b x v u)):=by
    unfold shellGrad; simp only [mul_neg,Finset.mul_sum]; apply Tendsto.neg; apply tendsto_finsetSum; intro a _
    have he:= reaches_mutable X H H' hc x hx hw a b (W:=fun _=>1) continuous_const hh hn hd ht (Fin.cons ⟨d,u⟩ v) (caps_cons_le u v hu hv)
    simpa only [pins_cons,sheet,weight,stretch,one_smul,mul_one,disc] using he
variable {f: Extraction.Order} {X:Scaling S} (HS:S.Hierarchy)(H:(Climb.Bel C.book).Hierarchy) (J:DiffPlan S) (U:DiffPlan (Climb.Bel C.book))(hX:Approaches (path X) (isoPanel X))(hJ:J.Derivatives S)(hU:U.Derivatives (Climb.Bel C.book))(ho:U.Orientation H.spin)
include HS H hU hJ hX
lemma pay_jet (d:ℕ)(a:Axis)(v: (Climb.Bel C.book).Field d)(o:Work.A05.Observer (Climb.Bel C.book)): Tendsto (fun i=> (X.r i:ℂ)* S.useAt S (X.r i • o.x) (Fin.cons (α:=fun _=>S.Tag) ⟨d+1,J.deriv d a (X.U i d v)⟩ (X.pins i ∘ o.q))) atTop (𝓝 (o.test (d+1) (U.deriv d a v))) :=by
    obtain ⟨D,N,R,hR,hr⟩:= o.enough d; have ht:=hr _ le_rfl _ le_rfl _ le_rfl; have hx:= comparison_jets HS hJ H hU X hX N D 0 R (zero_lt_one.trans_le hR)
    let L(i):= tiltScale X J i d a; let Tg(k):=o.moving X (d+1) k; let p:= o.test (d+1); have hv:Tendsto (fun i=>L i v) atTop (𝓝 (U.deriv d a v)):= Dash.arcing (bend_limit HS hJ H hU X d a hX) tendsto_const_nhds
    have hh(g):Tendsto (fun k=> Tg k g) atTop (𝓝 (p g)):= o.reads_converge _ hx ((Nat.le_succ _).trans ht.total) ht.rest ht.fits (d+1) ht.caps g
    apply (Dash.arcing (Dash.fit_plane Tg p hh) hv).congr; intro i; let r:= X.r i;let s:= J.deriv d a (X.U i d v); let f:=X.U i (d+1);let A:= Work.A05.frontRead (X.r i • o.x) (X.pins i ∘ o.q) (d+1); change A (f (r • (f.symm s)))= _
    rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul,map_smul,LinearEquiv.apply_symm_apply];exact congr_arg _ (frontRead_at ..)
end YM.Trace.Over
