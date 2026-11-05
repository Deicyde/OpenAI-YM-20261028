import YM.Next.UV_STRESS.Invert
import YM.Next.UV_STRESS.Local


/-!
# Comparison already in rescaled coordinates, any fixed compact on Conf
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {L : Register G} {T : Table L} {n : ℕ} {C : Family G} {S : Table C.book} {X : Scaling S}
variable {W : DiffPlan S} {V : DiffPlan (Bel C.book)}

section Rows

abbrev tiltScale (X : Scaling S) (W : DiffPlan S) (k d : ℕ) (a : Axis) :=
    X.r k • X.carry k (leaves W.deriv d a)

lemma scaled_identity (H : S.Hierarchy) (h : W.Derivatives S) (X : Scaling S) (k : ℕ) (p : Fin n)
    (v : Fin n → (Bel C.book).Tag) (a : Axis) {x : Points n} (hx : x∈conf n) :
    Points.gradient p a (tested (X.r k) (isoPanel X k) v) x =
      tested (X.r k) (isoPanel X k) (update v p ⟨(v p).1+1,tiltScale X W k (v p).1 a (v p).2⟩) x := by
  let V := panels (isoPanel X k)
  let y := X.r k • x
  let d := (v p).1
  have he : y∈conf n := (enlarged (X.positive k) x).1 hx
  have hv := cont_disc H (V ∘ v) he
  let f := X.carry k (leaves W.deriv d a) (v p).2
  let j : (Bel C.book).Tag := ⟨d+1,X.r k • f⟩
  change Points.gradient p a (fun x => disc (V ∘ v) (X.r k • x)) _ = disc (V ∘ update v p j) y
  rw [Work.A04.gradient_scaled _ _ _ (hv.differentiableAt (by simp))]; unfold Points.gradient
  rw [Ward.fromD W H h he, Ward.born W]
  have hz : V ∘ update v p j=update (V ∘ v) p (V j) := by
    ext1 i; by_cases h:i=p
    · subst i; simp
    simp [h]
  rw [hz]
  have hF : X.U k (d+1) (X.r k • f) = X.r k • (W.deriv d a (X.U k d (v p).2)) := by
    have ht := ((X.U k (d+1)).toLinearMap.restrictScalars ℝ).map_smul (X.r k) f
    change X.U k (d+1) (X.r k • f) = X.r k • X.U k (d+1) f at ht
    rw [ht]; congr 1; exact X.carries_f ..
  change X.r k • disc (update (V ∘ v) p ⟨d+1,W.deriv d a (X.U k d (v p).2)⟩) y =
    disc (update (V ∘ v) p ⟨d+1,X.U k (d+1) (X.r k • f)⟩) y
  rw [hF,← takes,← takes]; symm
  exact ((here (V ∘ v) y p (d+1)).restrictScalars ℝ).map_smul _ _

open MeterTest

lemma head_tilt (H : S.Hierarchy) (hs : W.Derivatives S) (X : Scaling S) (d k : ℕ)
    (a : Axis) (v : (Bel C.book).Field d) (y : MeterTest (Bel C.book)) :
    rescaled H.smooth (isoPanel X k) y (X.r k) (X.positive k) (d+1) (tiltScale X W k d a v) =
      - (Dash.down y.t 0 a).applyTo (tested (X.r k) (isoPanel X k) (y.headTest d v)) := by
  let q := y.headTest d v
  let f := tested (X.r k) (isoPanel X k) q
  rw [rescaled_eval, ← Dash.compactTest (K:=f) (smoothZoom H.smooth _ (X.positive k)) y.t 0 a]
  apply y.t.apply_eq
  intro x hx; change _ = Points.gradient 0 a f x
  rw [show Points.gradient 0 a f x = _ from scaled_identity H hs X k 0 q a hx]
  have hp (w : (Bel C.book).Field (d+1)) : y.headTest (d+1) w = update q 0 (⟨d+1,w⟩ : (Bel C.book).Tag) := by
    unfold headTest; simp [q,headTest]
  rw [hp]
  rfl

lemma bend_limit (H : S.Hierarchy) (h : W.Derivatives S) (L : (Bel C.book).Hierarchy) (hp : V.Derivatives (Bel C.book))
    (X : Scaling S) (d : ℕ) (a : Axis) (ht : Approaches (path X) (isoPanel X)) :
    Tendsto (fun k => tiltScale X W k d a) atTop (𝓝 (leaves V.deriv d a)) := by
  classical
  have he (y : MeterTest (Bel C.book)) (x : (Bel C.book).Field d) :
      Tendsto (fun k => rescaled H.smooth (isoPanel X k) y (X.r k) (X.positive k) (d+1) (tiltScale X W k d a x)) atTop
        (𝓝 (zeroScale y L.smooth _ (leaves V.deriv d a x))) := by
    let z := {y with t:=Dash.down y.t 0 a}
    simp_rw [head_tilt H h]
    have hv := Tendsto.neg (reads_limit H.smooth L.smooth ht z d x)
    simp_rw [rescaled_eval,zeroScale_eq] at hv
    have ho : y.zeroScale L.smooth (d+1) (leaves V.deriv d a x)= -(z.t.applyTo (disc (z.headTest d x))) := by
      rw [zeroScale_eq,show z.t=Dash.down y.t 0 a from rfl,← Dash.compactTest (smoothDisc L.smooth _) y.t 0 a]
      apply y.t.apply_eq
      intro i hi
      exact hp.kernels d a x hi y.q
    rw [ho]; exact hv
  obtain ⟨s,hv⟩ := detects (Bel C.book) L (d+1)
  suffices hz : Tendsto (fun k => LinearMap.toContinuousLinearMap (tiltScale X W k d a).toLinearMap) atTop
      (𝓝 (LinearMap.toContinuousLinearMap (V.deriv d a))) by exact hz
  apply Dash.fit_plane
  intro v
  refine Work.A04.tendsto_of_fitted (fun k => LinearMap.pi fun y : s => rescaled H.smooth (isoPanel X k) y.val
    (X.r k) (X.positive k) (d+1)) _ hv ?_ ?_
  · exact fun x => tendsto_pi_nhds.mpr fun y => reads_limit H.smooth L.smooth ht y.val (d+1) x
  exact tendsto_pi_nhds.mpr fun y => he y.val v
end Rows

section moving
variable {t : Caps n}
abbrev Ribbon (T : Table L) {n : ℕ} (t : Caps n) := (i : Fin n) → T.Field (t i)
def hang {T : Table L} (t : Caps n) (w : Ribbon T t) (i : Fin n) : T.Tag := ⟨t i,w i⟩

lemma flowing (H : S.Hierarchy) (L : (Bel C.book).Hierarchy) (X : Scaling S)
    (ht : Approaches (path X) (isoPanel X)) (v : ℕ → Ribbon (Bel C.book) t) (x : Ribbon (Bel C.book) t)
    (hz : ∀ i, Tendsto (fun k => v k i) atTop (𝓝 (x i))) :
    Fades (fun k => tested (X.r k) (isoPanel X k) (hang t (v k)) - disc (hang t x)) := by
  let A (i) := (Bel C.book).Field (t i)
  let R (b : Code A) (k : ℕ) := tested (X.r k) (isoPanel X k) (hang t (combination A b))
  let F (b : Code A) := disc (hang t (combination A b))
  let U (b : Code A) k := coords A b (v k) • (R b k - F b)
  let D (b : Code A) k := (coords A b (v k)-coords A b x) • F b
  refine ((Fades.sum U Finset.univ ?_).plus (Fades.sum D Finset.univ ?_)).congr ?_ (Eventually.of_forall (fun k y hy => ?_))
  · intro b _
    exact (ht.values n (hang t (combination A b))).times (tendsto_coords A b hz)
  · intro b _
    have he := (tendsto_coords A b hz).sub_const (coords A b x)
    rw [sub_self] at he
    exact Fades.small_scalar (smoothDisc L.smooth _) he
  · exact fun k => (smoothZoom H.smooth _ (X.positive k)).sub (smoothDisc L.smooth _)
  let M := (S.classMoment S t (X.r k • y)).compLinearMap fun i => (X.U k (t i)).toLinearMap
  let N := (Bel C.book).classMoment (Bel C.book) t y
  change ((∑ b : Code A, U b)+(∑ b, D b)) k y = M (v k)-N x
  have hu b : R b k y=M (combination A b) := rfl
  have hv b : F b y=N (combination A b) := rfl
  rw [basis_tuple A _ M,basis_tuple A _ N,← Finset.sum_sub_distrib]
  simp only [Pi.add_apply, Finset.sum_apply, U, D, Pi.smul_apply, Pi.sub_apply,hu,hv, smul_eq_mul]
  rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun b _ => by ring

-- Composing with position gradients stays in moving

def Travels (n : ℕ) (X : Scaling S) (K : ℕ→Points n→ℂ) : Prop :=
    ∃ (t : Caps n) (v : ℕ → Ribbon (Bel C.book) t) (x : Ribbon (Bel C.book) t),
      (∀ i, Tendsto (fun k => v k i) atTop (𝓝 (x i))) ∧
        K = fun k => tested (X.r k) (isoPanel X k) (hang t (v k)) - disc (hang t x)

/-- Update a tuple without switching the type of the companion positions. -/
def updated (i : Fin n) (e : ℕ) (v : Ribbon T t) (x : T.Field e) : Ribbon T (update t i e) := fun j =>
    if h : j=i then by rw [h,update_self]; exact x else by rw [update_of_ne h]; exact v j

lemma hangs (i : Fin n) (e : ℕ) (v : Ribbon T t) (x : T.Field e) : hang (update t i e) (updated i e v x) =
    update (hang t v) i ⟨e,x⟩ := by
  ext1 j; by_cases h : j=i
  · subst j; simp [hang,updated]
  simp [hang,updated,h]

lemma tendsto_updated (i : Fin n) (e : ℕ) {v : ℕ → Ribbon T t} {x : Ribbon T t}
    (ht : ∀ i, Tendsto (fun k => v k i) atTop (𝓝 (x i)))
    {w : ℕ → T.Field e} {y : T.Field e} (hw : Tendsto w atTop (𝓝 y)) :
    ∀ j, Tendsto (fun k => updated i e (v k) (w k) j) atTop (𝓝 (updated i e x y j)) := by
  have he (d l : ℕ) (h : d=l) (f : ℕ → T.Field d) (b : T.Field d) (hc : Tendsto f atTop (𝓝 b)) :
      Tendsto (fun k => _root_.cast (congr_arg (T.Field ·) h) (f k)) atTop
        (𝓝 (_root_.cast (congr_arg (T.Field ·) h) b)) := by
    subst l; exact hc
  intro j; by_cases h : j=i
  · subst j; dsimp [updated]; simp
    exact he e (update t i e i) (by simp) _ _ hw
  simp only [updated,dif_neg h]
  -- casts, proof irrelevance after simplification
  exact he (t j) (update t i e j) (update_of_ne h .. |>.symm) _ _ (ht j)

lemma closed_path (H : S.Hierarchy) (h : W.Derivatives S) (L : (Bel C.book).Hierarchy) (hp : V.Derivatives (Bel C.book))
    (X : Scaling S) (ht : Approaches (path X) (isoPanel X)) (n : ℕ) : GradientFamily (Travels n X) where
  entry K hk := by
    obtain ⟨t,v,x,hv,rfl⟩ := hk; exact flowing H L X ht _ _ hv
  step K hk p a := by
    obtain ⟨t,v,x,hv,rfl⟩ := hk
    let d := t p
    let T := update t p (d+1)
    let w (k : ℕ) := updated p (d+1) (v k) (tiltScale X W k d a (v k p))
    let y := updated p (d+1) x (V.deriv d a (x p))
    have hy : ∀ j, Tendsto (fun k => w k j) atTop (𝓝 (y j)) :=
      tendsto_updated p (d+1) hv (Dash.arcing (bend_limit H h L hp X d a ht) (hv p))
    refine ⟨_,⟨T,w,y,hy,rfl⟩,Eventually.of_forall (fun k z hz => ?_)⟩
    dsimp only [T,w,y]; simp only [hangs]
    -- kernel difference after updating p
    let Wf := tested (X.r k) (isoPanel X k) (hang t (v k))
    let Vf := disc (hang t x)
    have hh : DifferentiableAt ℝ Wf z :=
        (((smoothZoom H.smooth _ (X.positive k)) _ hz).contDiffAt ((conf_open _).mem_nhds hz)).differentiableAt (by simp)
    have hf := (cont_disc L (hang t x) hz).differentiableAt (by simp)
    change fderiv ℝ (Wf - Vf) z (Points.direction p a) = _
    rw [fderiv_sub hh hf, _root_.sub_apply]
    change Points.gradient p a _ _ - Analysis.D _ (disc _) _ = _
    rw [scaled_identity H h X k p (hang t (v k)) a hz, Ward.fromD V L hp hz p a]; rfl

lemma travels_jet (H : S.Hierarchy) (h : W.Derivatives S) (L : (Bel C.book).Hierarchy) (hp : V.Derivatives (Bel C.book))
    (X : Scaling S) (ht : Approaches (path X) (isoPanel X)) (v : ℕ → Ribbon (Bel C.book) t) (x : Ribbon (Bel C.book) t)
    (hv : ∀ i, Tendsto (fun k => v k i) atTop (𝓝 (x i)))
    (j : ℕ) (s : Set (Points n)) (hs : IsCompact s) (hu : s ⊆ conf n) (ε : ℝ) (he : 0<ε) :
    ∀ᶠ k in atTop, ∀ y∈s,
      ‖iteratedFDeriv ℝ j (tested (X.r k) (isoPanel X k) (hang t (v k))) y - iteratedFDeriv ℝ j (disc (hang t x)) y‖ ≤ ε := by
  filter_upwards [(closed_path H h L hp X ht n).jets (show Travels n X _ from ⟨t,v,x,hv,rfl⟩) s hs hu j he] with k hk y hy
  specialize hk y hy
  -- symmetry/derivative closure is inside conf
  have hh := ((smoothZoom H.smooth (panels (isoPanel X k) ∘ (hang t (v k))) (X.positive k)) _ (hu hy)).contDiffAt
    ((conf_open _).mem_nhds (hu hy))
  have hF := cont_disc L (hang t x) (hu hy)
  rw [← iteratedFDeriv_sub_apply (show ContDiffAt ℝ (j : WithTop ℕ∞) (tested (X.r k) (isoPanel X k) (hang t (v k))) y from
    hh.of_le (WithTop.coe_le_coe.mpr le_top)) (hF.of_le (WithTop.coe_le_coe.mpr le_top))]; exact hk

lemma window_closed (R : ℝ) (n : ℕ) : IsCompact (Scaling.window R n) := by
  have he : IsClosed {x : Points n | spaced R⁻¹ x} := by
    rw [show {x : Points n|spaced R⁻¹ x} = ⋂ i : Fin n, ⋂ j : Fin n, ⋂ _ : i≠j,
      {x : Points n | R⁻¹ ≤ cubedist (x i) (x j)} from by ext; simp [spaced]]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun h => isClosed_le continuous_const
      (continuous_cubedist.comp (show Continuous (fun x : Points n => (x i,x j)) by fun_prop))
  rw [Scaling.window,show {x : Points n|spaced R⁻¹ x ∧ ‖x‖ ≤ R} = Metric.closedBall 0 R ∩ {x | spaced R⁻¹ x} from
    Set.ext (fun x => by simp [and_comm])]
  exact (isCompact_closedBall (0 : Points n) R).inter_right he

lemma comparison_jets (H : S.Hierarchy) (h : W.Derivatives S) (L : (Bel C.book).Hierarchy) (hp : V.Derivatives (Bel C.book))
    (X : Scaling S) (ht : Approaches (path X) (isoPanel X)) (N d m : ℕ) (R : ℝ) (hr : 0<R) : X.jets N d m R := by
  intro n _ j _ v hv ε he
  exact travels_jet H h L hp X ht (t:=fun i => (v i).1) (fun _ i => (v i).2) (fun i => (v i).2)
    (fun _ => tendsto_const_nhds) j _ (window_closed ..) (fun _ h => spaced_conf (inv_pos.mpr hr) h.1) ε he
end moving
end YM.Next.UVStress
