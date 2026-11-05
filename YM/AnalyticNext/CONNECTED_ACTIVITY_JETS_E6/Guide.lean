import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.DataKernel
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Rod

/-!
# Per-row price of V response on a clean patch

Keep the paths even at zero entries. For linear comparison, arbitrary
bounded *sup* log extension on a given orientation's patch of V. Local
V curvature need be healthy. Compare only near the selected gap/row;
no stationarity of whole Step (yet). Uniform post-L. At supplied
horizons and their `Bed` the linear N comparator is zero by Roll
including zero harmonic modes (not assuming scalar phase value).
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations Work.E03
open Bloch Laurent
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {L : Side} {c f n : Side} {S : StepData c f} {T : Tube G S}

lemma Rate.broadens {w : ℝ → ℝ} {e τ : ℝ} (h : Rate G L e w) (ht : 0<τ) (hf : ∀ᶠ x in atTop,0 ≤ w x) :
    Rate G L e (fun x => widen (till x) (w x) τ) := by
  refine (Rate.weaken (a:=0+e) ?_ (by simp))
  have he := ((Rate.const 1 |>.add (Rate.radius_price (G:=G) (L:=L))).mul h).add
    (Rate.cutoff ht)
  refine he.compare ?_
  filter_upwards [hf] with x hx
  have hw : 0 ≤ widen (till x) (w x) τ := widen_nonneg _ hx
  rw [abs_of_nonneg hw]; apply le_trans _ (le_abs_self _)
  unfold widen; gcongr; exact Nat.div_le_self _ _

namespace SliceRows
open DataKernel

def guide (T : Tube G S) (x : ℝ) (V : Config G c) : Rod c f → G.Color :=
  Sum.elim (T.Mv (till x) (Pressure.temp x) V) (T.Mw (till x) (Pressure.temp x) V)

def linearGuide (T : Tube G S) (b : LogField G c) : Rod c f → G.Color :=
  Sum.elim (zip (flatF T) (xLin T.low T.down b)) (zip (flatI T) (xLin T.low T.down b))

lemma guide_gauge (h : P.Funds S T) (x : ℝ) (V : Config G c) (z : Site c → G.El) (p : Rod c f) :
    guide T x (gauge z V) p=G.adjoint (z (focus S p)) (guide T x V p) := by
  rcases p with p|b
  · exact mvg h ..
  exact mwg h ..

lemma zip_zero_N (hP : P.Funds S T) (b : LogField G c) (i : Co c Gain) :
    zip (flatN T) (xLin T.low T.down b) i=0 := by
  obtain ⟨B,D,-,he,hR⟩ := hP.tilts
  obtain ⟨a,b',-,hp⟩ := hP.feeds
  rw [← hP.low] at hp
  let s := Work.E03.meshEquiv c
  let X := D.full T.low c*d 1 c
  ext j
  have he (i): (xLin T.low T.down b (s.symm i)) j= (X *ᵥ parts G 1 b j) i := by
    rw [xLin_component T.low T.down D hp he]
    change (_ *ᵥ _) (s (s.symm i))=_; rw [Equiv.apply_symm_apply]
  refine Eq.trans (scalar_zip (T.R.o.acts c) (Equiv.refl _) s (xLin T.low T.down b) i j) ?_
  simp_rw [he]; change (T.R.o.acts c*ᵥ(X*ᵥparts _ _ _ j)) i=0
  rw [Matrix.mulVec_mulVec,show T.R.o.acts c*X=0 from by rw [show X=D.full T.low c*d 1 c from rfl,← Matrix.mul_assoc,hR.oPart]]
  simp

section vector
variable {ι : Type*} [Fintype ι] (Q : Config G c → ι → Twin c → Pay G) (D : ι → Twin c → Pay G)
  (v : ι → Site c)

lemma complete_vision {x} (hr : Room P S T x) (V : Config G c) (o : Site c) (U : Config G c)
    (hv : AgreeNear id o (radiusB x/4) V U) (hV : Clean V x o (radiusB x/4))
    (i : Twin c) (hx : separation o i.1.1 ≤ till x) : T.vision (till x) (Pressure.temp x) V i =
      T.Xn (till x) U i := by
  have he := hr.sight.1
  have hh (i : Twin c) (hx : separation o i.1.1 ≤ till x) : T.Xn (till x) U i=T.Xn (till x) V i :=
    (plotted_near id (sep_step (c:=c)) V U T.low T.down (till x) S.patch.L.val i S.patch.L.property
      (hv.shrink (by change separation o i.1.1 + (till x+4) ≤ _; unfold till at *; omega))).symm
  rw [hh _ hx]
  unfold Tube.vision Tube.Xn thinned plotted; split
  next hm =>
    rw [if_pos (hV.kept hr _ (by unfold till at hx; omega))]
  next hn =>
    split
    next he => rw [one_smul]
    next hn =>
      rw [min_eq_left (by
        have hp : 0 < toll V i.1 := lt_of_le_of_ne (G.chord_nonneg _) (Ne.symm hn)
        rw [le_div_iff₀ hp,one_mul]
        exact hV.toll (b:=i.1) (by unfold till at hx; omega)), one_smul]

lemma zip_guide (i : ι) (s : ℝ) (V : Config G c) (b : LogField G c) {X Z U W : ℝ} (_hW : 0 ≤ W)
    (hV : Clean V s (v i) (radiusB s/4)) (h : AgreeNear id (v i) (radiusB s/4) V (represent b))
    (hR : Room P S T s) (hq : Rule (till s) Q v (fun i => i.1.1))
    (hd : NearFlat (Q (represent b)) D X W) (_hX : 0 ≤ X) (hZ : 0 ≤ Z) (hU : 0 ≤ U)
    (hp : ∀ i, ‖xLin T.low T.down b i‖ ≤ Z)
    (hu : ∀ i, ‖plotted T.down T.low (till s) S.patch.L.val (represent b) i-xLin T.low T.down b i‖ ≤ U) :
    ‖zip (Q V) (T.vision (till s) (Pressure.temp s) V) i-zip D (xLin T.low T.down b) i‖ ≤
      X*U+X*W*Z := by
  have he : zip (Q V) (T.vision (till s) (Pressure.temp s) V) i=zip (Q (represent b)) (T.Xn (till s) (represent b)) i := by
    unfold zip; apply sum_congr rfl; intro j _
    rw [hq.stencil i V (represent b) (h.shrink (by rw [separation_self,zero_add]; unfold till; omega)) j]
    by_cases hn : Q (represent b) i j=0
    · rw [hn, _root_.zero_apply, _root_.zero_apply]
    rw [complete_vision hR V _ _ h hV _ (hq.reach _ _ _ hn)]
  let f := T.Xn (till s) (represent b)
  let g := xLin T.low T.down b
  let B := Q (represent b)
  rw [he]; change ‖zip B f i-zip D g i‖ ≤ _
  have hz : zip B f i-zip D g i=zip B (f-g) i+zip (B-D) g i := by
    unfold zip; simp only [Pi.sub_apply,map_sub,_root_.sub_apply,sum_sub_distrib]; abel
  rw [hz]; exact (norm_add_le _ _).trans (add_le_add (Work.E07.zip_uniform B _ i (hd.cut.rows _) hU hu)
    (Work.E07.zip_uniform (B-D) g i (hd.close.rows _) hZ hp))
end vector

/-- Physical linear response of target V costs on any log comparison in a clean hull. -/
theorem read_guides (P : Teller G) (L : Side) {H : ℝ → ℝ} (h : Rate G L (-(1/2)) H) (hp : ∀ᶠ x in atTop,0 ≤ H x) :
    ∃ e : ℝ → ℝ, Rate G L (-1) e ∧ ∀ᶠ x in atTop, 0 ≤ e x ∧ ∀ (c f : Side) (S : StepData c f) (T : Tube G S),
      S.patch.L = L → Room P S T x → ∀ (V : Config G c) (b : LogField G c), ‖b‖ ≤ H x →
      let B := radiusB x; let R := till x; let y := Pressure.temp x
      (∀ p : Rod c f, Clean V x (focus S p) (B/4) → AgreeNear id (focus S p) (B/4) V (represent b) →
        ‖guide T x V p - linearGuide T b p‖ ≤ e x) ∧
        ∀ i : Co c Gain, Clean V x i.1 (B/4) → AgreeNear id i.1 (B/4) V (represent b) →
          ‖zip (T.N R V) (T.vision R y V) i‖ ≤ e x := by
  obtain ⟨X,s,r,hX,hs,hr,hg⟩ := kernel_chart_cost G L P.η P.C P.width
  obtain ⟨Z,r',hZ,hr',hz⟩ := x_chart_cost G P.below L.val L.property
  let t := P.below.width/L.val
  have ht : 0 < t := div_pos P.below.width_pos (side_pos L)
  let M x := Z*H x
  let U x := M x*widen (till x) (H x) t
  let e x := X*U x + X*widen (till x) (H x) s*M x
  have hm := h.mul_left Z
  have hd := h.broadens ht hp; have hi := h.broadens hs hp
  have he : Rate G L (-1) e := by
    have hf := ((hm.mul hd).mul_left X).add ((hi.mul_left X).mul hm)
    convert hf using 1; norm_num
  refine ⟨e,he,?_⟩
  filter_upwards [h.below (by norm_num) (min r r') (lt_min hr hr'),hp] with x hh hH
  let u := H x; let W := widen (till x) u s; let Z' := M x
  have hw := widen_nonneg (τ:=t) (till x) hH
  have hU : 0 ≤ U x := mul_nonneg (mul_nonneg hZ.le hH) hw
  have hw' : 0 ≤ W := widen_nonneg _ hH
  have he' : 0 ≤ e x := add_nonneg (mul_nonneg hX.le hU) (mul_nonneg (mul_nonneg hX.le hw')
    (mul_nonneg hZ.le hH))
  refine ⟨he',?_⟩
  intro c f S T hL hR V b hb B R y
  have hP := hR.accepted
  have hv : u ≤ min r r' := (le_abs_self _).trans hh
  obtain ⟨hF,hI,hN⟩ := hg S T hL ⟨_,hP.crosses⟩ R b u hb (hv.trans (min_le_left ..))
  obtain ⟨a₁,a₂,-,hi⟩ := hP.feeds
  have hy (i : Twin c) : ‖xLin T.low T.down b i‖ ≤ Z' ∧
      ‖plotted T.down T.low R S.patch.L.val (represent b) i - xLin T.low T.down b i‖ ≤ U x := by
    rw [hP.low,hL]; exact hz c T.down a₂ hi R b u hb (hv.trans (min_le_right ..)) i
  constructor
  · intro p hy' hb'; rcases p with p|b'
    · exact zip_guide (T.Φ R) (flatF T) (fun i => focus S (.inl i)) p x V b hw' hy' hb' hR (crosses R T P hP) hF hX.le (show 0 ≤ Z' from mul_nonneg hZ.le hH)
        hU (fun i => (hy i).1) (fun i => (hy i).2)
    exact zip_guide (T.Φ' R) (flatI T) (fun i => focus S (.inr i)) b' x V b hw' hy' hb' hR (sameLevel R S.patch.L.val S.patch.L.property T.R.mn
      (Row.rights _ _ hP.crosses.1 P.width.le) pole mesh) hI hX.le (show 0 ≤ Z' from mul_nonneg hZ.le hH)
      hU (fun i => (hy i).1) (fun i => (hy i).2)
  intro i h1 h2
  have he := zip_guide (T.N R) (flatN T) Prod.fst i x V b hw' h1 h2 hR
    (sameLevel R S.patch.L.val S.patch.L.property T.R.o (Row.rights _ _ hP.crosses.2.1 P.width.le) id mesh)
    hN hX.le (show 0 ≤ Z' by unfold Z' M; positivity) hU (fun i => (hy i).1) (fun i => (hy i).2)
  rw [zip_zero_N hP,sub_zero] at he; exact he
end SliceRows
end YM.ConnectedActivityE6
