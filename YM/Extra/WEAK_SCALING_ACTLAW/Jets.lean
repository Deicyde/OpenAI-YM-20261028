import YM.Extra.WEAK_SCALING_ACTLAW.Adjust
import YM.Next.BOUNDARY.Unit

/-!
# One adjusted comparison family through all finite point jets on a window

For the lift from sampled to actual continuous convergence through coordinate
projection ties, pay a *successor* weak estimate and r*deriv convergence
there. For j-th norm jets pay all required descendants through j+1 at the
same stations. No tie displacement lower bound assumed for Scaling.jets.
-/
set_option maxHeartbeats 500000
set_option autoImplicit false
noncomputable section
namespace YM.Extra.WeakScaling
open Function Filter Set Table Ward Climb Spec
open scoped Topology ContDiff
variable {G : Gauge} {C : Family G} {S : Table C.book} {D n : ℕ}

abbrev MatrixTest (C : Family G) (d : Caps n) := MultilinearMap ℂ (fun i => (Free C).Field (d i)) ℂ

def matrixRead (A : Maps S) (k : ℕ) (d : Caps n) (x : Points n) : MatrixTest C d :=
  (S.classMoment S d x).compLinearMap (fun i => A k (d i))

abbrev forgetting (X : ℕ → ∀ d, YM.Spin.change S d) : Maps S := fun k d => (X k d).toLinearMap

/-- Preserve value tests or bounds (multiply by an arbitrary fixed real
station-dependent factor) along moving points through the adjustment. -/
lemma revised (U : Maps S) {r : ℕ → ℝ} (X A : ℕ → ∀ d, YM.Spin.change S d)
    (he : ∀ᶠ k in atTop, ∀ d ≤ D, ∀ v, A k d v = U k d v)
    (hr : ∀ d ≤ D, ∀ v, Tendsto (fun k => (A k d).symm (X k d v)) atTop (𝓝 v))
    {s : ℕ → ℕ} (hs : Tendsto s atTop atTop) {x : ℕ → Points n} (d : Caps n) (hd : ∀ i, d i ≤ D)
    (t : ℕ → ℝ) (F : MatrixTest C d)
    (h : ∀ v, Tendsto (fun i => t i • matrixRead U (s i) d (r (s i) • x i) v) atTop (𝓝 (F v))) (v) :
    Tendsto (fun i => t i • matrixRead (forgetting X) (s i) d (r (s i) • x i) v) atTop (𝓝 (F v)) := by
  let a (i : ℕ) (j : Fin n) := (A (s i) (d j)).symm (X (s i) (d j) (v j))
  apply (multi_fitted (fun i => t i • matrixRead U (s i) d (r (s i) • x i)) F h (u:=a)
    (fun i => (hr _ (hd i) _).comp hs)).congr'
  filter_upwards [hs.eventually he] with i hi
  change t i • matrixRead _ _ _ _ _ = _
  apply congrArg (HSMul.hSMul (t i) : ℂ → ℂ)
  apply congrArg ((S.classMoment S d _) : _ → ℂ)
  funext j
  exact (hi _ (hd j) (a i j)).symm.trans (LinearEquiv.apply_symm_apply ..)

structure Curve (V : DiffPlan S) (W : DiffPlan (Free C)) (h : S.RealSpin) (H : (Free C).RealSpin)
    (M D : ℕ) (Q : ℝ) where
  r : ℕ → ℝ
  pos k : 0 < r k
  shrinks : Tendsto r atTop (𝓝 0)
  delta : ℕ → ℝ
  positive k : 0 < delta k
  fine : Tendsto delta atTop (𝓝 0)
  X : ℕ → ∀ d, YM.Spin.change S d
  graded : ∀ᶠ k in atTop, Graded V W h H (X k) D
  deriv d : d < D → ∀ a v, Tendsto (fun k => (X k (d+1)).symm (r k • V.deriv d a (X k d v))) atTop (𝓝 (W.deriv d a v))
  sampled n : n ≤ M → ∀ v : Fin n → (Free C).Tag, capped D v → Sampled (apart Q n) delta (readMap (forgetting X) r v) (disc v)
  growth n : n ≤ M → ∀ v : Fin n → (Free C).Tag, capped D v → Follows (apart Q n) (fun k x => delta k • readMap (forgetting X) r v k x) 0

lemma trace_curve {f : Extraction.Order} (s : Seed C f S) {H : (Free C).Hierarchy} {M N E : ℕ} {Q : ℝ}
    (b : Survey S s.kernel.spin H.spin M E Q)
    (hF : ∀ d, Nonempty (YM.Spin.change S d)) (hM : N ≤ M) (hD : D ≤ E) (hw : ∀ d ≤ D, Equipped H d M E Q)
    {V : DiffPlan S} {W : DiffPlan (Free C)}
    (hi : V.Inclusions S) (hi' : W.Inclusions (Free C)) (hp : V.Derivatives S) (hp' : W.Derivatives (Free C))
    (hv : V.Orientation s.kernel.spin) (hv' : W.Orientation H.spin) :
    Nonempty (Curve V W s.kernel.spin H.spin N D Q) := by
  obtain ⟨X,hX,hp,he,hr⟩ := repaired s (H:=H) b hF hD hw hi hi' hp hp' hv hv'
  refine ⟨b.r,b.pos,b.shrinks,b.delta,b.positive,b.fine,X,hX,hp,fun n hn v hv => ?_,fun n hn v hv => ?_⟩
  · intro σ hσ x hx u hu hU
    let d := fun i => (v i).1
    have h := revised b.U X _ he hr hσ (x:=fun i => Extraction.tag (b.delta (σ i)) (u i)) d hv
      (fun _ => 1) ((Free C).classMoment (Free C) d x) (r:=b.r)
    have hh (w : ∀ i, (Free C).Field (d i)) := b.sampled n (hn.trans hM) (fun i => ⟨d i,w i⟩) (fun i => (hv i).trans hD) σ hσ x hx u hu hU
    exact (h (fun w => by simpa only [one_smul] using! hh w) (fun i => (v i).2)).congr'
      (Eventually.of_forall fun _ => one_smul ℝ _)
  intro σ hσ x hx u hu
  let d := fun i => (v i).1
  exact revised b.U X _ he hr hσ d hv (b.delta ∘ σ) 0
    (fun w => b.growth n (hn.trans hM) (fun i => ⟨d i,w i⟩) (fun i => (hv i).trans hD) σ hσ x hx u hu) _

/-- In tests involving successive derivatives in possibly different slots,
keep caps fixed while the coefficients may vary in the weak basis. -/
def Slot {L : Register G} {T : Table L} (d : ℕ) (w : ℕ → T.Tag) (v : T.Tag) :=
    ∃ e ≤ d, ∃ (b : ℕ → T.Field e) (y : T.Field e), Tendsto b atTop (𝓝 y) ∧ v = ⟨e,y⟩ ∧ ∀ i, w i = ⟨e,b i⟩

lemma Slot.weaken {d e : ℕ} {L : Register G} {T : Table L} (h : d ≤ e) {w : ℕ → T.Tag} {v : T.Tag}
    (hw : Slot d w v) : Slot e w v := by
  obtain ⟨l,hl,hh⟩ := hw; exact ⟨l,hl.trans h,hh⟩
lemma Slot.const {d : ℕ} {L : Register G} {T : Table L} (v : T.Tag) (h : v.1 ≤ d) :
    Slot d (fun _ => v) v := ⟨v.1,h,_,_,tendsto_const_nhds,rfl,fun _ => rfl⟩

lemma varying (U : Maps S) {s : ℕ → ℕ} {x : ℕ → Points n} {r t : ℕ → ℝ} (f : ∀ d : Caps n, MatrixTest C d)
    (h : ∀ d : Caps n, (∀ i, d i ≤ D) → ∀ v, Tendsto (fun i => t i • matrixRead U (s i) d (r (s i) • x i) v) atTop (𝓝 (f d v)))
    {w : ℕ → Fin n → (Free C).Tag} {v : Fin n → (Free C).Tag} (hw : ∀ j, Slot D (fun i => w i j) (v j)) :
    Tendsto (fun i => t i • readMap U r (w i) (s i) (x i)) atTop (𝓝 (f (fun j => (v j).1) (fun j => (v j).2))) := by
  choose d hd b y hy hv hW using hw
  rw [funext hv,show w = fun i j => ⟨d j,b j i⟩ from funext fun i => funext fun j => hW j i]
  exact multi_fitted (fun i => t i • matrixRead U (s i) d (r (s i) • x i)) (f d) (h d hd) hy

variable {V : DiffPlan S} {W : DiffPlan (Free C)} {M d : ℕ} {h : S.RealSpin} {H : (Free C).RealSpin} {Q : ℝ}
namespace Curve
variable (b : Curve V W h H M D Q)

def shift (k : ℕ) (a : Axis) (v : (Free C).Tag) : (Free C).Tag :=
  ⟨v.1+1,(b.X k (v.1+1)).symm (b.r k • V.deriv v.1 a (b.X k v.1 v.2))⟩

def read (b : Curve V W h H M D Q) (w : Fin n → (Free C).Tag) := readMap (forgetting b.X) b.r w

lemma delay (hV : d < D) (a : Axis) {w : ℕ → (Free C).Tag} {v : (Free C).Tag} {σ : ℕ → ℕ} (hs : Tendsto σ atTop atTop)
    (hw : Slot d w v) : Slot (d+1) (fun i => b.shift (σ i) a (w i)) (Ward.rise W a v) := by
  obtain ⟨e,he,z,y,hz,rfl,hE⟩ := hw
  simp_rw [hE]
  let X (k) := (b.X k (e+1)).symm.toLinearMap.comp ((b.r k • (V.deriv e a)).comp (b.X k e).toLinearMap)
  have ht := Dash.fit_plane X (W.deriv e a) (b.deriv e (he.trans_lt hV) a)
  exact ⟨e+1,Nat.succ_le_succ he, _,_,Dash.arcing (ht.comp hs) hz,rfl,fun i => rfl⟩

lemma shuffle (hV : d < D) {w : ℕ → Fin n → (Free C).Tag} {v : Fin n → (Free C).Tag} {σ : ℕ → ℕ} (hs : Tendsto σ atTop atTop)
    (hw : ∀ j, Slot d (fun i => w i j) (v j)) (a : Axis) (i j : Fin n) :
    Slot (d+1) (fun k => update (w k) i (b.shift (σ k) a (w k i)) j) (update v i (Ward.rise W a (v i)) j) := by
  by_cases h : j=i
  · subst j; simpa only [update_self] using b.delay hV a hs (hw i)
  simpa only [Function.update_of_ne h] using (hw j).weaken d.le_succ

lemma gradient (hS : S.Hierarchy) (hV : V.Derivatives S) (w : Fin n → (Free C).Tag) (k : ℕ) (i : Fin n) (a : Axis)
    {x : Points n} (hx : x∈conf n) : Analysis.D (Points.direction i a) (b.read w k) x = b.read (update w i (b.shift k a (w i))) k x := by
  let F := routed (forgetting b.X) k
  let y := b.r k • x
  have he := Work.A04.scale_conf _ (b.pos k) hx
  change Points.gradient i a (fun y => disc (F ∘ w) (b.r k • y)) x = disc (F ∘ update w i (b.shift k a (w i))) y
  rw [Work.A04.gradient_scaled _ _ _ ((cont_disc hS _ he).differentiableAt (by simp))]
  change b.r k • Analysis.D _ (disc _) y = _
  rw [Ward.fromD _ hS hV he,Function.comp_update]
  let u := V.deriv _ a (b.X k _ (w i).2)
  have h₁ : F (b.shift k a (w i)) = ⟨(w i).1+1,b.r k • u⟩ := by
    simp [F,routed,shift,u]
  rw [h₁,← Ward.takes, ← Ward.takes]
  exact (((here (F ∘ w) y i ((w i).1+1)).restrictScalars ℝ).map_smul (b.r k) u).symm

lemma read_limit (hS : S.Hierarchy) (hV : V.Derivatives S) (hQ : 0 < Q) (hn : n ≤ M) (w : Fin n → (Free C).Tag)
    (hw : capped d w) (hd : d < D) : Follows (apart Q n) (b.read w) (disc w) := by
  apply interpolate (apart_open Q n) b.positive b.fine
    (fun k x hx => (readMap_smooth hS (b.pos k) (apart_conf hQ hx)).differentiableAt (by simp))
    (b.sampled n hn w (hw · |>.trans hd.le))
  intro ⟨j,a⟩ s hs x hx z hz
  have he := varying (forgetting b.X) (fun _ : Caps n => (0 : MatrixTest C _))
    (fun e (he : ∀ i, e i ≤ d+1) v => b.growth n hn (fun i => ⟨e i,v i⟩) (fun i => (he i).trans hd) s hs x hx z hz)
    (b.shuffle hd (v:=w) hs (fun i => Slot.const (w i) (hw i)) a j)
  apply he.congr'
  filter_upwards [hz.eventually ((apart_open Q n).mem_nhds hx)] with i hi
  change _ = _ • Analysis.D _ (b.read w _) _; rw [b.gradient hS hV w _ j a (apart_conf hQ hi)]; rfl

lemma mixture (hS : S.Hierarchy) (hV : V.Derivatives S) (hQ : 0 < Q) (hn : n ≤ M)
    {w : ℕ → Fin n → (Free C).Tag} {v : Fin n → (Free C).Tag} (hw : ∀ j, Slot d (fun i => w i j) (v j)) (hd : d < D)
    {s : ℕ → ℕ} (hs : Tendsto s atTop atTop) {x : Points n} (hx : x ∈ apart Q n) {z} (hz : Tendsto z atTop (𝓝 x)) :
    Tendsto (fun i => b.read (w i) (s i) (z i)) atTop (𝓝 (disc v x)) := by
  have he (e : Caps n) (he : ∀ i, e i ≤ d) (v : (i : Fin n) → (Free C).Field (e i)) :=
    b.read_limit hS hV hQ hn (fun i => ⟨e i,v i⟩) he hd s hs x hx z hz
  have ht := varying (forgetting b.X) (r:=b.r) (x:=z) (s:=s) (t:=fun _ => 1) (fun d => (Free C).classMoment (Free C) d x)
    (fun e he' v => by simpa only [one_smul] using! he e he' v) hw
  simpa only [one_smul] using! ht

lemma all_orders (hS : S.Hierarchy) (hV : V.Derivatives S) (hH : (Free C).Hierarchy) (hW : W.Derivatives (Free C)) (hQ : 0 < Q)
    (hn : n ≤ M) {w : ℕ → Fin n → (Free C).Tag} {v : Fin n → (Free C).Tag} (hw : ∀ j, Slot d (fun i => w i j) (v j))
    (m : ℕ) (hd : d + m < D) {s : ℕ → ℕ} (hs : Tendsto s atTop atTop) {x : Points n} (hx : x ∈ apart Q n)
    {z} (hz : Tendsto z atTop (𝓝 x)) :
    Tendsto (fun i => iteratedFDeriv ℝ m (b.read (w i) (s i)) (z i)) atTop (𝓝 (iteratedFDeriv ℝ m (disc v) x)) := by
  have hx' := apart_conf hQ hx
  induction m generalizing w v d with
  | zero =>
    apply norm_fit_jet; intro u
    simpa only [iteratedFDeriv_zero_apply] using! b.mixture hS hV hQ hn hw hd hs hx hz
  | succ m ih =>
    apply norm_fit_jet; intro u
    let dirs (p : Fin (m+1)) := Points.direction (u p).1 (u p).2
    let i := (u 0).1
    let a := (u 0).2
    let w' k := update (w k) i (b.shift (s k) a (w k i))
    let v' := update v i (Ward.rise W a (v i))
    have pivot (F G : Points n → ℂ) (y) (hc : ContDiffAt ℝ ∞ F y) (he : Analysis.D (Points.direction i a) F =ᶠ[𝓝 y] G) :
        iteratedFDeriv ℝ (m+1) F y dirs = iteratedFDeriv ℝ m G y (Fin.tail dirs) := by
      nth_rw 1 [← Fin.cons_self_tail dirs, Analysis.cons_inner (hc.of_le (WithTop.coe_le_coe.mpr le_top))]
      change iteratedFDeriv ℝ m (Analysis.D (Points.direction i a) F) y _ = _
      rw [(he.iteratedFDeriv ℝ m).eq_of_nhds]
    have nhds' (x : Points n) (hx : x ∈ conf n) : ∀ᶠ y in 𝓝 x, y∈conf n := (conf_open n).mem_nhds hx
    change Tendsto _ _ (𝓝 (iteratedFDeriv ℝ (m+1) (disc v) x dirs))
    rw [pivot (disc v) (disc v') x (cont_disc hH _ hx') ((nhds' _ hx').mono fun _ h => Ward.fromD W hH hW h ..)]
    have he := ih (w:=w') (v:=v') (b.shuffle (by omega : d < D) hs hw a i) (by omega)
    apply (((ContinuousMultilinearMap.apply ℝ _ ℂ (Fin.tail dirs)).continuous.tendsto _).comp he).congr'
    filter_upwards [hz.eventually ((conf_open _).mem_nhds hx')] with k hk
    exact (pivot _ (b.read (w' k) (s k)) _ (readMap_smooth hS (b.pos _) hk)
      ((nhds' _ hk).mono fun _ h => b.gradient hS hV (w k) (s k) i a h)).symm

lemma tested (hS : S.Hierarchy) (hV : V.Derivatives S) (hH : (Free C).Hierarchy) (hW : W.Derivatives (Free C))
    {R : ℝ} (hr : 1 ≤ R) (hQ : R < Q) (hn : n ≤ M) (v : Fin n → (Free C).Tag) (hv : capped d v) (m : ℕ) (hd : d + m < D)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ k in atTop, ∀ x ∈ Scaling.window R n,
      ‖iteratedFDeriv ℝ m (b.read v k) x - iteratedFDeriv ℝ m (disc v) x‖ ≤ ε := by
  have he : Follows (apart Q n) (fun k => iteratedFDeriv ℝ m (b.read v k)) (iteratedFDeriv ℝ m (disc v)) :=
    fun s hs x hx z hz => b.all_orders (s:=s) (x:=x) (z:=z) (w:=fun _ => v) (v:=v) hS hV hH hW (by linarith) hn (fun j => Slot.const _ (hv j)) m hd hs hx hz
  have hx := (window_inside hr hQ (n:=n)).trans (apart_conf (by linarith))
  exact he.onCompact (compact_window ..) (window_inside hr hQ) (fun x h =>
    ((cont_disc hH _ (hx h)).continuousAt_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)).continuousWithinAt) hε
end Curve
end YM.Extra.WeakScaling
