import YM.TraceExtension.Wicket.Shade
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Wicket
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory Push.SectorMeasure
open PhysicalNext.JointLoad.Heir Next.Foundations Push.Local Swift
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side}{R:Rep G n}{B:BudgetPoint}{s A C:ℝ}{U:Config G n}{i:Edge (Site n)}
abbrev Tint(i:Edge (Site n))(v:G.Color)(s:ℝ): Config G n→ Config G n := fun U=> rung U i v s
lemma tint_c (i:Edge (Site n))(s:ℝ) : Continuous (Function.uncurry (fun v:G.Color=>Tint i v s)):=by
     unfold uncurry Tint; simp_rw [seatB]; change Continuous fun p:G.Color × Config G n=>StressFlux.modify _ _ _ _; refine continuous_pi (fun j=>?_); unfold StressFlux.modify; split_ifs <;> fun_prop
lemma Tint.arm {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X] {p:X} {f:X→ Config G n} {v:X→G.Color} (h:Army f p)(he:ContDiffAt ℝ ω v p) : Army (fun y=>Tint i (v y) s (f y)) p:= (Army.powL (x:=p) (ContDiffAt.const_smul (c:=s) ((phB i).contDiff.contDiffAt.comp _ he))).mul h
lemma Tint.turn(i:Edge (Site n))(s:ℝ)(V:Coats G n)(U:Config G n)(x:G.Color):Tint i (G.adjoint (V i.1) x) s (Lattice.gauge V U)=Lattice.gauge V (Tint i x s U):=by unfold Tint; rw [seatB,seatB,←map_smul,adjoint_exp,modify_g]
lemma Tint.holds(i:Edge (Site n))(s:ℝ)(P:Support n)(V U:Config G n)(x:G.Color)(h:Agrees P U V):Agrees P (Tint i x s U) (Tint i x s V):= by unfold Tint; rw [seatB,seatB]; exact modify_local _ _ _ _ h
lemma Tint.focus {i : Edge (Site n)}{B : BudgetPoint}{p:G.Color}{D:ℝ}(hp:G.chord (G.lieExp (s • p)) ≤ D)(hz:64*D ≤ B.threshold)(h:Healthy (B.threshold/8) {i.1} U): Healthy (B.threshold/4) {i.1} (Tint i p s U):=by
   refine disjoint_left.mpr fun j hj hV=> ?_; rw [mem_singleton.mp hj] at hV; obtain ⟨F,hF,hx⟩:= (flags_spec ..).mp hV; have ht:G.chord (faceValue U F) ≤ B.threshold/8:=le_of_not_gt fun he=> disjoint_left.mp h (mem_singleton_self _) ((flags_spec ..).mpr ⟨_,hF,he⟩)
   let V:= Tint i p s U; have he(j:Edge (Site n)):knot (U j) (V j) ≤ D:=by unfold V Tint; rw[seatB]; exact paint_local _ _ _ _ hp ..
   have hy:|G.chord (faceValue U F)-G.chord (faceValue V F)| ≤ 4*D:= (castC ..).trans (by simpa [faceValue,square] using hike U V he F.1 (square F.2.val.1 F.2.val.2))
   linarith only [hy,hz,ht,(show B.threshold/4<G.chord (faceValue V F) from hx),neg_le_abs (G.chord (faceValue U F)-G.chord (faceValue V F)),B.threshold_pos]
lemma Tint.gate {i:Edge (Site n)}{p:G.Color}{D:ℝ}(hp: G.chord (G.lieExp (s • p)) ≤ D) (hz:64*D ≤ R.p.threshold)(h: Healthy (R.p.threshold/8) {i.1} U): flags R.p.threshold U = flags R.p.threshold (Tint i p s U):=by
   have ht:= Tint.focus hp hz h; unfold Tint at *; rw[seatB] at ht ⊢; exact (smallC _ _ _ R D hp (by linarith only [R.p.threshold_pos,hz]) U ht).1
private def moon (V:Config G n)(x:Directions G n)(j:Edge (Site n)):= G.adjoint (V j) (x j)
lemma left_spin (V:Config G n)(x:Peat G n)(U:Config G n)(l : List (Directions G n)):leftDerivs (fun w=> x (V*w)) l U=leftDerivs x (l.map (moon V)) (V*U):=by
    induction l generalizing U with
    | nil=>rfl
    | cons a b h=> rw [List.map_cons]; unfold leftDerivs; simp_rw [h]; apply congr_arg (fun f:ℝ→ℝ=> deriv f 0); funext i; apply congr_arg (leftDerivs x _); funext j; simp only [increment,Pi.mul_apply,Pi.smul_apply,moon,← map_smul,adjoint_exp]; group
lemma Tint.troop {f:Peat G n}{V U:Config G n}{x:Site n} {k:ℕ}(h:Clear k (B.dirBound x) (V*U) f C): Clear k (B.dirBound x) U (fun w=>f (V*w)) C := by
    let F(y):=V*increment U y; have hf:F 0=V*U:=by simp [F]
    refine ⟨chart_comp (W:=F) (by rw [hf]; exact h.wake) ((Army.park V 0).mul (incrementA U 0)),fun l hl hh=>?_⟩
    rw [left_spin]; apply h.pay _ (by simpa using hl); simp only[List.forall_mem_map]; intro j hj i; unfold moon; rw[G.norm_adjoint]; exact hh _ hj _
section regular
variable {P P':Support n} {E:Peat G n} {x:Site n}
lemma orbit_shift (h:B.Regular P E)(hx:B.supBounds x P E A) : B.supBounds (0:Site n) P E (((1+(separation x 0:ℝ))^B.power)^B.order*A):=by
   let L:= Complex.ofRealCLM; let F:Config G n→ℂ:=L ∘ E; have hf(U)(hz:Healthy B.threshold P U):Chart B.order F U:= L.contDiff.contDiffAt.comp _ (h.smooth U hz)
   have ht:B.Regular P F:=⟨fun u v he=> congr_arg L (h.sites _ _ he),L.continuous.measurable.comp h.borel,fun v U=>congr_arg L (h.symmetry _ _),hf,fun u hv A _ hl=> left_has A hl (hf _ hv)⟩
   have he(U)(H:Healthy B.threshold P U)(l:List (Directions G n))(hl:l.length ≤ B.order): ‖leftDerivs F l U‖ = ‖leftDerivs E l U‖:=by unfold F; rw[left_linear L l (h.smooth _ H) hl]; exact Complex.norm_real _
   have hh:=bound_shift (f:=F) (B:=B) (a:=A) (o:=x) ⟨hx.1,fun U hV l hl hp=> (he U hV l hl).trans_le (hx.2 U hV l hl hp)⟩ ht (0:Site n); exact ⟨hh.1,fun U hV l hl hp=> (he U hV l hl).symm.trans_le (hh.2 U hV l hl hp)⟩
abbrev Mellow (G:Gauge)(n:Side):= Config G n→ G.Color→ℝ
def frog (i:Edge (Site n))(s:ℝ)(B:BudgetPoint)(E:Peat G n):Mellow G n:=fun U v=> dapple i.1 B U*(E U-E (Tint i v s U))
structure Cohort(B:BudgetPoint)(P:Support n)(o:Edge (Site n))(F:Mellow G n):Prop where
    sites(v): LocalOn P fun U=> F U v
    shift(U:Config G n) (v:G.Color)(g:Site n→G.El): F (Lattice.gauge g U) (G.adjoint (g o.1) v)=F U v
    meas : Measurable (uncurry F)
    earns {X:Type}[NormedAddCommGroup X] [NormedSpace ℝ X](V:X→ Config G n)(p:X)(t:X→ G.Color) : Army V p→ ContDiffAt ℝ ω t p→Healthy B.threshold P (V p)→ ‖t p‖ ≤ 1→ ContDiffAt ℝ B.order (fun x=> F (V x) (t x)) p
abbrev Career (B:BudgetPoint)(P:Support n)(F:Mellow G n)(A:ℝ):Prop :=∀ (U:Config G n),Healthy B.threshold P U→∀ v:G.Color,‖v‖≤1→Clear B.order (B.dirBound (0:Site n)) U (fun U=> F U v) A
lemma frogger (hE:R.p.Regular P E)(hQ:halo 9 {i.1} ⊆ P')(hp:P ⊆ P')(D:ℝ) (hD:∀ v:G.Color, ‖v‖≤1→G.chord (G.lieExp (s • v))≤D)(hz:64*D≤ R.p.threshold) : Cohort R.p P' i (frog i s R.p E):=by
   let f:= frog i s R.p E; let p:=R.p; let q:= dapple i.1 p (G:=G); have h:= uriP R.p P' i.1 hQ (G:=G)
   refine ⟨fun w U V hx=> ?_,fun U v j=>?_,?_,?_⟩
   ·
     have hw:= agrees_mono hx (coe_subset.mpr hp); unfold frog; dsimp only; rw[h.sites _ _ hx,hE.sites _ _ hw,hE.sites _ _ (Tint.holds i s P V U w hw)]
   · unfold frog; rw [h.symmetry,hE.symmetry,Tint.turn,hE.symmetry]
   · have hc : Continuous (fun p:Config G n × G.Color=> Tint i p.2 s p.1):= (tint_c i s (G:=G)).comp (f:=fun p:Config G n × G.Color=>(p.2,p.1)) (continuous_snd.prodMk continuous_fst)
     have hm: Measurable (fun p:Config G n × G.Color=> Tint i p.2 s p.1):=hc.measurable
     exact (Measurable.mul (h.borel.comp measurable_fst) ((hE.borel.comp measurable_fst).sub (hE.borel.comp hm)))
   intro X _ _ V x t hV hx hB hw; by_cases hg:Healthy (R.p.threshold/8) {i.1} (V x)
   · let W(y):=Tint i (t y) s (V y); have hy: Healthy p.threshold P (V x):= Disjoint.mono_left hp hB; have ht: Healthy p.threshold P (W x):=by unfold Healthy; rw[←Tint.gate (i:=i) (U:=V x) (R:=R) (hD _ hw) hz hg]; exact hy
     exact ContDiffAt.mul (chart_comp (k:=R.p.order) (W:=V) (f:=dapple i.1 R.p) (h.smooth _ hB) hV) (ContDiffAt.sub (chart_comp (k:=R.p.order) (f:=E) (W:=V) (hE.smooth _ hy) hV) (chart_comp (k:=R.p.order) (f:=E) (W:=W) (hE.smooth _ ht) (Tint.arm (i:=i) (s:=s) hV hx)))
   apply contDiffAt_const.congr_of_eventuallyEq (f:=fun _=>(0:ℝ)); filter_upwards [hV.cont.eventually ((healthy_closed ..).isOpen_compl.mem_nhds hg)] with y hy; unfold frog; rw [dapple_zero hy,zero_mul]
def hikeFee (B:BudgetPoint)(r:ℕ):ℝ:= ((1+(r:ℝ))^B.power)^B.order
lemma hikeFee_nonneg (B:BudgetPoint)(r:ℕ):0≤ hikeFee B r:=by unfold hikeFee; positivity
lemma hjibe (B:BudgetPoint){x y:ℕ}(h:x ≤y):hikeFee B x ≤ hikeFee B y:=by unfold hikeFee;gcongr
lemma canon {B:BudgetPoint} (h:B.Regular P E)(he:B.supBounds x P E A)(r:ℕ)(hh:separation x 0 ≤ r) (hp:Healthy B.threshold P U): Clear B.order (B.dirBound (0:Site n)) U E (hikeFee B r*A) := ⟨h.smooth _ hp,fun l hl hV=> ((orbit_shift h he).2 U hp l hl hV).trans (mul_le_mul_of_nonneg_right (hjibe B hh) he.1)⟩
def vat(B:BudgetPoint)(r:ℕ)(C:ℝ):= 2^B.order*(hikeFee B r*C)*(2*hikeFee B r)
lemma frog_price (hE:R.p.Regular P E)(he:R.p.supBounds x P E A)(hQ:halo 9 {i.1} ⊆ P')(hp:P ⊆ P')(r:ℕ)(hL:separation x 0 ≤ r)(hM:separation i.1 0 ≤ r)(hx:R.p.supBounds i.1 P' (dapple i.1 R.p (G:=G)) C)(D:ℝ)(hD:∀ v:G.Color, ‖v‖≤1→G.chord (G.lieExp (s • v))≤D)(hz:64*D≤ R.p.threshold) : Career R.p P' (frog i s R.p E) (vat R.p r C*A):=by
   let F:= dapple i.1 R.p (G:=G); intro U hU v hv; let hH:= (uriP R.p P' i.1 hQ (G:=G)); have ht':= canon hH hx _ hM hU; let B:=R.p
   by_cases hy:Healthy (B.threshold/8) {i.1} U
   · have hh : Healthy B.threshold P U:= Disjoint.mono_left hp hU; let V(y : Config G n):= Tint i v s y; have hw:Healthy B.threshold P (V U):=by unfold Healthy;rw[← Tint.gate (hD v hv) hz hy]; exact hh
     refine (ht'.mul ((canon hE he r hL hh).sub (Tint.troop (B:=R.p) (canon hE he r hL hw)))).weaken ?_
     exact le_of_eq (by unfold vat;ring)
   apply (clear_const (a:=0) (by unfold vat; rw[abs_zero]; positivity[hikeFee_nonneg R.p r,hx.1,he.1])).congr
   filter_upwards [((incrementA U 0).cont).eventually (show {u:Config G n| Healthy (B.threshold/8) {i.1} u}ᶜ∈𝓝 (increment U 0) from (by rw[Work.G07.at_zero_increment]; exact (healthy_closed ..).isOpen_compl.mem_nhds hy))] with y hy
   change frog _ _ _ _ _ _=0; unfold frog; rw [dapple_zero hy,zero_mul]
end regular
end YM.Trace.Wicket
