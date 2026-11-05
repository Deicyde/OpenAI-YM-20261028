import YM.UVExtension.Reward.Tides
import YM.UVExtension.Free.Lease

/-! Consumer views for normalized data. The weighted statement uses the actual exponential
path width (no dimension-dependent loss). -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Reward
open Lattice RG Supply Stationary Projection Precision Bloch Laurent Exterior Wilson Tree Filter Function Finset MenuView
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {L : Rolls s} {Θ : Protection L} {a : Levels G} {P : MapPrices} {K V : Horizon a} {Z : ChartRatio G} {W : Delays Θ} {y : Bar W} {w : Wait y} {Q : PostCost L} {D : Knobs a} {ε : ℝ} {m N :ℕ}
lemma reportBuried {T : MapPrices}(h:Free.Report V T): Buried V:= by
  have he m := h.bed m
  constructor
  · intro i; obtain ⟨t,h⟩:= he i; exact ⟨_,h.roots.entries⟩
  intro i; obtain ⟨t,h⟩:= he i; exact ⟨_,h.metric.entries⟩
section limits

def Filled (K:ℕ→ PathData G)(R : PathData G) := ∀ᶠ n in atTop, (∀ i j, ((K n).row i j).2=(R.row i j).2) ∧ (∀ i, ((K n).loop i).leg=(R.loop i).leg) ∧ (∀ i, ((K n).cubic i).leg=(R.cubic i).leg) ∧ ∀ i,((K n).quartic i).leg=(R.quartic i).leg

def Levies {n : ℕ}(f g : ℕ→ Atom G n)(σ:ℝ)(ε:ℝ):Prop:=
  SumBudget (fun i=> ({f i with coeff:=(f i).coeff-(g i).coeff}).budget σ) ε

def Envelope (K:ℕ→ PathData G)(R : PathData G)(σ : ℝ):Prop:= Filled K R ∧ ∀ ε:ℝ,0<ε→∀ᶠ x in atTop,
    (∀ i : PlaqAxes, SumBudget (fun j=> |((K x).row i j).1-(R.row i j).1| * Real.exp (σ*(R.row i j).2.length)) ε) ∧ Levies (K x).loop R.loop σ ε∧ Levies (K x).cubic R.cubic σ ε∧Levies (K x).quartic R.quartic σ ε

lemma translate_data {U:ℕ→ PathData G}{U'} {T: PathData G}{σ}(h:Envelope U T σ)(hp:∀ᶠ i in atTop,U' i=U i):Envelope U' T σ:=
    ⟨(h.1.and hp).mono fun _ hh=> hh.2.symm ▸ hh.1,fun _ he=> ((h.2 _ he).and hp).mono fun _ hh=> hh.2.symm ▸ hh.1⟩

lemma root_stage {s B : ℝ} {f:ℕ→Bed}{R: Bed}(h:Tendsto (fun n=>(f n).roots) atTop (𝓝 R.roots))(_hs:0<s)(hv: ∀ᶠ n in atTop,(f n).roots.strip s B) {w:ℝ}(he:w<s){b:ℝ}(hx:0<b):∀ᶠ x in atTop, ∀ i : PlaqAxes,
     SumBudget (fun j=> |(rowPath (f x) i j).1-(rowPath R i j).1| * Real.exp (w*(rowPath R i j).2.length)) b:=by
  let d:= Fintype.card PlaqAxes*(Real.exp (w*4)); have hp:Fintype.card PlaqAxes≠0:=by decide
  have hd : 0<d:=by unfold d; positivity
  have hb: rowPrice w (b/d)=b:=by unfold rowPrice d; field_simp
  filter_upwards [(Free.reported h hv).interior w he (b/d) (div_pos hx hd)] with x ht i
  let U: Bed:= { R with roots:=(f x).roots-R.roots }
  rw [← hb]; exact price_paths (B:=U) ht i

lemma atom_stage {I:Type}{n:ℕ} [NeZero n](e:Chip G n → I) {f:ℕ→Projection.Ortho I}{z: Projection.Ortho I}{s c:ℝ}(h:HLimit f z){w:ℝ}(ht:w<s){r}(hp:0<r): ∀ᶠ i in atTop, Levies (issue (blend e s c (f i))) (issue (blend e s c z)) w r:=by
  let K i (x:ℕ):= issue (blend e s c (f i-z)) x
  have he i x : K i x= { (issue (blend e s c (f i)) x) with coeff:= (issue (blend e s c (f i)) x).coeff-(issue (blend e s c z) x).coeff }:=by
    unfold K issue artery; congr 1; funext j; unfold blend; simp only [lp.coeFn_sub,Pi.sub_apply,mul_sub]
  suffices H: ∀ᶠ i in atTop, SumBudget (fun x=> (K i x).budget w) r by
    refine H.mono fun i hi=> ?_; unfold Levies; simp_rw [← he]; exact hi
  have hz : HLimit (fun i=> f i-z) 0 := by
    have H:= h.add (HLimit.strong (tendsto_const_nhds (x:=-z))); simpa only [add_neg_cancel] using! H
  let P i x:= (K i x).budget w
  obtain ⟨b,hb⟩:= hz.bound
  have hv0 i : Summable (P i):= (budget_hyp _ _ _ _ ht).2.1
  have hv x : Tendsto (fun i=> P i x) atTop (𝓝 0):=by
    have hL i : P i x= (∑ j, |c*grain G n (-s) x*(f i-z) (e (x,j))|)*grain G n w x:=by
      unfold P K Atom.budget Atom.magnitude; simp_rw [longWay,blend_coeff]; rfl
    have hh j : Tendsto (fun i=> |c*grain G n (-s) x*(f i-z) (e (x,j))|) atTop (𝓝 0):=by
      have ht:Tendsto (fun i=>(f i-z) (e (x,j))) atTop (𝓝 0):= hz.hit _
      simpa only [mul_zero, abs_zero] using! (ht.const_mul _).abs
    simp_rw [hL]; simpa only [sum_const_zero,zero_mul] using! (tendsto_finsetSum _ (fun i _=> hh i)).mul_const (grain G n w x)
  have hm i x : 0 ≤ P i x:=by unfold P Atom.budget Atom.magnitude; positivity
  have hh': Tendsto (fun i=>∑' x,P i x) atTop (𝓝 0):=by
    simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence (((grainSum (G:=G) (n:=n) (sub_pos.mpr ht)).2.1).mul_left (|c| *b*Fintype.card (Ink G (n+1)))) hv (hb.mono fun i hi x=> by rw [Real.norm_of_nonneg (hm ..)]; exact strobe e s c (f i-z) b hi w x)
  exact (hh'.eventually_le_const hp).mono fun i hi=> ⟨hm i,hv0 _,hi⟩
lemma package {g:ℕ→Cube G}{x:Cube G}(h: Working D V P m) (hv:Buried V)(hz:HLimit g x): ∃ R w,(a.params m).width<w ∧ ∀ u<w, Envelope (fun i=> sat D V i m (g i)) R u:=by
  obtain ⟨r,hr⟩:= hv.root m
  let R:Bed:= { V.H m m with roots:=r }; let E:=label D m; let p:=a.clock.J m
  refine ⟨E.path R x,min (P.α p) (D.widths m),lt_min h.width1 (h.width2.trans (half_lt_self E.width_pos)),fun u hh=> ⟨?_,fun ε he=> ?_⟩⟩
  · exact Eventually.of_forall fun i=> ⟨fun _ _=> rfl,fun _=> rfl,fun _=> rfl,fun _=> rfl⟩
  have hx:= root_stage (R:=R) hr (P.alpha_pos _) ((eventually_ge_atTop m).mono fun i hi=> ((h.beside i hi).2.1)) (hh.trans_le (min_le_left ..)) he
  have hu':u<E.grainWidth:= hh.trans_le (min_le_right ..)
  have hT := atom_stage (n:=1) Sum.inl (c:=E.coil) hz hu' he; have h3:=atom_stage (n:=2) (Sum.inr∘ Sum.inl) (c:=E.mold) hz hu' he; have h4:=atom_stage (n:=3) (Sum.inr∘Sum.inr) (c:=E.mold) hz hu' he
  exact hx.and (hT.and (h3.and h4))
structure Ends (a:Levels G)(K : ℕ→ℕ→ PathData G)(A:ℕ→ℕ→ℝ) : Prop where
    prices m: Arrives fun n=> A n m
    fields m: ∃ R w,(a.params m).width<w ∧∀ u < w, Envelope (fun n=> K n m) R u

theorem ticket (h:Paid w a) (p:G.ColorIndex)(hz:LocalRatio Z)(hp:Ahead wavePulse ε)(hh:Mints D P V Q Z ε)(hr:Buried V):∃ T:Kin V Z, FullPaths T Q∧ Ends a T.path T.alpha:=by
  obtain ⟨T,hT,y,hY,hv,x,α,hx,hy⟩:= turning h p hz hp hh hr
  refine ⟨T,hT, ⟨fun i=> ⟨_,(hy _).2⟩,fun i=>?_⟩⟩
  obtain ⟨R,w,hw,hW⟩:=package (hh.work i) hr (hy i).1
  exact ⟨R,w,hw,fun t ht=> translate_data (hW _ ht) ((eventually_gt_atTop _).mono fun n hn=> (hv n i hn).symm)⟩
end limits
end YM.UVExtension.Reward
