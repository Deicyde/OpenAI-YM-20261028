import YM.Bid.Grow

/-!
# C23: fixed-height integrations on the Chamber itself
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.C23
open Function Set Filter MeasureTheory Measure Spectral Mink Boundary Boundary.Small OS Complex
open scoped Topology NNReal BigOperators InnerProductSpace
variable {G : Gauge} {L : Register G} {S T : Table L} {C : Chamber T timeAxis}

/-- Along legs staying strictly inside, `F` is operator-norm continuous.
Use *strong* continuity instead on the transverse translations. -/
lemma rip_continuous {X : Type*} [TopologicalSpace X]
    (w : X → ℂ) (p : ℝ≥0) (x : X → Space3) (f : X → C.H)
    (hw : Continuous w) (hx : Continuous x) (hf : Continuous f) (h : ∀ q, (p:ℝ)<(w q).im) :
    Continuous fun q => rip (C:=C) (w q) p (x q) (f q) := by
  have hi : Continuous fun q => Small.interval (w q) p := by
    unfold Small.interval; fun_prop
  have he : Continuous fun q => C.flow.F (Small.interval (w q) p) :=
    C.flow.localHeat.continuousOn.comp_continuous hi (fun q => (Small.down ..).2 (h q))
  have hu : Continuous fun q => bufferF (x q) := Continuous.subtype_mk
    (f := fun q => position (x q) 0) (divide.symm.continuous.comp (hx.prodMk continuous_const)) _
  exact he.clm_apply (C.flow.cont_cross f _ hf hu)

/-- Strong continuity and a bound for trains with fixed insertions, varying
leg positions. Require the complex durations are in the interior. -/
lemma train_control {X : Type*} [TopologicalSpace X] (B : Small S C) (p : ℝ≥0) (n : ℕ)
    (z : X → Times n) (x : X → SpacePoints n) (v : Fin n → S.Union) (u : X → ℂ) (s : X → Space3)
    (hz : ∀ i, Continuous fun q => z q i) (hx : ∀ i, Continuous fun q => x q i)
    (hu : Continuous u) (hs : Continuous s)
    (hgap : ∀ q i j, i<j → (↑(p+p):ℝ) < ((z q j)-(z q i)).im)
    (hstart : ∀ q i, (↑(p+p):ℝ) < ((z q i)-u q).im) :
    (Continuous fun q => B.trainB p n (z q) (x q) v (u q) (s q)) ∧
    ∀ q, ‖B.trainB p n (z q) (x q) v (u q) (s q)‖ ≤ (∏ i, ‖B.bar p (v i)‖)*‖C.omega‖ := by
  induction n generalizing u s with
  | zero => exact ⟨continuous_const, fun _ => by simp [Small.trainB]⟩
  | succ n ih =>
    obtain ⟨ht,hb⟩ := ih (fun q => Fin.tail (z q)) (fun q => Fin.tail (x q)) (Fin.tail v)
      (fun q => z q 0) (fun q => x q 0) (fun i => hz i.succ) (fun i => hx i.succ) (hz 0) (hx 0)
      (fun q i j e => hgap q i.succ j.succ (by simpa using e)) (fun q i => hgap q 0 i.succ (Fin.succ_pos _))
    let f := fun q => B.trainB p n (Fin.tail (z q)) (Fin.tail (x q)) (Fin.tail v) (z q 0) (x q 0)
    refine ⟨?_,?_⟩
    · exact rip_continuous (fun q => z q 0-u q) (p+p) (fun q => x q 0-s q)
        (fun q => B.bar p (v 0) (f q)) ((hz 0).sub hu) ((hx 0).sub hs)
        ((B.bar p (v 0)).continuous.comp ht) (fun q => hstart q 0)
    intro q
    rw [Fin.prod_univ_succ, mul_assoc]
    exact (Small.flanks _ _ (x q 0-s q) (B.bar p (v 0) (f q)) (hstart q 0)).trans
      (((B.bar p (v 0)).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hb q) (norm_nonneg _)))

lemma shot_control (B : Small S C) (p : ℝ≥0) (n : ℕ) (v : Fin n → S.Union) (y : Heights n)
    (h : Small.ample p y) : Continuous (B.shot p n v y) ∧
    ∀ q, ‖B.shot p n v y q‖ ≤ (∏ i, ‖B.bar p (v i)‖)*‖C.omega‖ := by
  have hn : 0 ≤ (p:ℝ) := p.property
  have hk (q : Points n) (i j : Fin n) (e : i<j) : (↑(p+p):ℝ) < (shift q y j - shift q y i).im := by
    have hh := h.1.2.2 i j e
    simp [shift]
    linarith
  have hz (i : Fin n) : Continuous fun q : Points n => shift q y i := by
    unfold shift; fun_prop
  have hx (i : Fin n) : Continuous fun q : Points n => trace q i := by
    unfold trace; fun_prop
  have ho (q : Points n) (i : Fin n) : (p:ℝ) < (shift q y i).im := by
    have he := h.2 i
    simp [shift]; linarith
  cases n with
  | zero => exact ⟨continuous_const,fun _ => by simp [Small.shot]⟩
  | succ n =>
    obtain ⟨ht,hb⟩ := train_control B p n
      (fun q : Points (n+1) => Fin.tail (shift q y)) (fun q => Fin.tail (trace q)) (Fin.tail v)
      (fun q => shift q y 0) (fun q => trace q 0)
      (fun i => hz i.succ) (fun i => hx i.succ) (hz 0) (hx 0)
      (fun q i j e => hk q i.succ j.succ (by simpa using e)) (fun q i => hk q 0 i.succ (Fin.succ_pos _))
    let f := fun q => B.trainB p n (Fin.tail (shift q y)) (Fin.tail (trace q)) (Fin.tail v) (shift q y 0) (trace q 0)
    refine ⟨?_,?_⟩
    · exact rip_continuous (fun q => shift q y 0) p (fun q => trace q 0)
        (fun q => B.bar p (v 0) (f q)) (hz 0) (hx 0) ((B.bar p (v 0)).continuous.comp ht) (fun q => ho q 0)
    intro q
    rw [Fin.prod_univ_succ,mul_assoc]
    exact (Small.flanks _ _ (trace q 0) (B.bar p (v 0) (f q)) (ho q 0)).trans
      (((B.bar p (v 0)).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hb q) (norm_nonneg _)))

/-- In particular, tensor products of tests in the words can really be
integrated. Fixed strict profile; no uniform bound here as the height
vanishes. Thus no `rated` hypothesis needed at this step. -/
lemma shot_int (B : Small S C) (p : ℝ≥0) {n : ℕ} (v : Fin n → S.Union) (y : Heights n) (f : Joint n)
    (h : Small.ample p y) : Integrable (fun q => f q • B.shot p n v y q) := by
  obtain ⟨ht,hb⟩ := shot_control B p n v y h
  let N := (∏ i, ‖B.bar p (v i)‖)*‖C.omega‖
  have hn : 0 ≤ N := by unfold N; positivity
  apply (f.integrable.norm.mul_const N).mono (f.continuous.smul ht).aestronglyMeasurable
  refine ae_of_all _ fun i => ?_
  change ‖f i • B.shot p n v y i‖ ≤ ‖‖f i‖ * N‖
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) hn)]
  exact mul_le_mul_of_nonneg_left (hb i) (norm_nonneg _)

/-- For arity zero one still needs the edge translation law on the
vacuum; first continue `E_t Ω = Ω` inside the half-plane. -/
lemma vacuum_heat (C : Chamber T timeAxis) (t : ℝ≥0) : C.flow.E t C.omega=C.omega := by
  unfold Chamber.omega
  rw [← C.atBirth,OS.inAir]

lemma vacuum_F (C : Chamber T timeAxis) {z : ℂ} (hz : z∈OS.Semigroup.inside) : C.flow.F z C.omega=C.omega := by
  let f : ℂ → C.H := fun w => C.flow.F w C.omega
  have hf : AnalyticOnNhd ℂ f OS.Semigroup.inside := fun _ he =>
    (ContinuousLinearMap.apply ℂ C.H.space C.omega).analyticAt _ |>.comp (C.flow.localHeat _ he)
  have hg : OS.Semigroup.duration 1∈OS.Semigroup.inside := OS.Semigroup.dur.mpr (by norm_num)
  have hh : EqOn f (fun _ => C.omega) OS.Semigroup.inside := by
    apply hf.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const
      (convex_halfSpace_gt reCLM.toLinearMap.isLinear 0 |>.isPreconnected) hg
    intro hn
    have hy : Tendsto OS.Semigroup.duration (𝓝[>] (1:ℝ≥0)) (𝓝[≠] (OS.Semigroup.duration 1)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact (Complex.continuous_ofReal.comp continuous_subtype_val).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin] with i hi
      change OS.Semigroup.duration i ≠ OS.Semigroup.duration 1
      exact fun he => (mem_Ioi.mp hi).ne' (Subtype.ext (Complex.ofReal_injective he))
    obtain ⟨i,hi,hq⟩ := ((hy.eventually hn).and self_mem_nhdsWithin).exists
    apply hi
    have hp := lt_trans (by norm_num : (0:ℝ≥0)<1) (mem_Ioi.mp hq)
    unfold f; rw [C.flow.roots_heat hp,vacuum_heat]
  exact hh hz

lemma vacuum_translation (C : Chamber T timeAxis) (b : E4) : C.flow.unit.translation b C.omega=C.omega := by
  have hv (t : Cross timeAxis) : C.flow.U t C.omega=C.omega := by
    unfold Chamber.omega
    rw [← C.across,OS.overAir]
  change C.flow.edge _ (C.flow.U _ C.omega)=_
  rw [hv]
  have hn := (OS.Semigroup.length (q:=b timeAxis)).2 (by norm_num : (0:ℝ≥0)<1)
  calc
    _ = C.flow.edge (b timeAxis) (C.flow.E 1 C.omega) := by rw [vacuum_heat]
    _ = _ := (C.flow.high _ _).trans (vacuum_F C hn)

lemma rip_shift (w : ℂ) (p : ℝ≥0) (x : Space3) (b : E4) (v : C.H) (h : (p:ℝ)<w.im) :
    rip (C:=C) (w+(time b:ℂ)) p (x+spatial b) v = C.flow.unit.translation b (rip (C:=C) w p x v) := by
  have he := (Small.down ..).2 h
  have ht : Small.interval (w+(time b:ℂ)) p = Small.interval w p + OS.Semigroup.sideways (time b) := by
    unfold Small.interval OS.Semigroup.sideways; ring
  have hu : bufferF (x+spatial b) = OS.Semigroup.SEP timeAxis b + bufferF x := by
    apply Subtype.ext
    change position (x+_) 0 = (b-time b • basis _) + position x 0
    apply Mink.ext_by <;> simp [sub_eq_add_neg,add_comm]
  have hh q : C.flow.F (Small.interval w p) (C.flow.U (OS.Semigroup.SEP timeAxis b) q) =
      C.flow.U (OS.Semigroup.SEP timeAxis b) (C.flow.F (Small.interval w p) q) :=
    DFunLike.congr_fun (C.flow.stays he _) q
  change C.flow.F _ (C.flow.U _ v) = C.flow.edge (time b) (C.flow.U _ (C.flow.F _ (C.flow.U _ v)))
  rw [hu,C.flow.space,ht,← C.flow.along he]
  simp only [ContinuousLinearMap.comp_apply, hh]

lemma train_shift (B : Small S C) (p : ℝ≥0) (n : ℕ) (z : Times n) (x : SpacePoints n) (v : Fin n → S.Union)
    (u : ℂ) (s : Space3) (t : ℂ) (b : Space3) :
    B.trainB p n (fun i => z i+t) (fun i => x i+b) v (u+t) (s+b) = B.trainB p n z x v u s := by
  induction n generalizing u s with
  | zero => rfl
  | succ n ih =>
    rw [Small.trainB,Small.trainB]
    rw [add_sub_add_right_eq_sub, add_sub_add_right_eq_sub]
    change rip (C:=C) _ _ _ ((B.bar p (v 0))
      (B.trainB p n (fun i => Fin.tail z i+t) (fun i => Fin.tail x i+b) _ (z 0+t) (x 0+b))) = _
    rw [ih]

lemma shot_shift (B : Small S C) (p : ℝ≥0) (n : ℕ) (v : Fin n → S.Union) (y : Heights n) (q : Points n) (b : E4)
    (h : Small.ample p y) : B.shot p n v y (q+points (fun _ => b)) = C.flow.unit.translation b (B.shot p n v y q) := by
  cases n with
  | zero => exact (vacuum_translation C b).symm
  | succ n =>
    let d := points (n:=n+1) fun _ => b
    let z := shift q y
    let x := trace q
    have hz : shift (q+d) y = fun i => z i+(time b:ℂ) := by
      funext; simp [d,z,shift]; abel
    have hx : trace (q+d) = fun i => x i+spatial b := by
      funext; simp [d,x,trace]
    have hn : (p:ℝ)<(z 0).im := by
      have he := h.2 0
      simp [z,shift]; linarith [show (0:ℝ) ≤ p from p.property]
    rw [Small.shot,Small.shot]
    rw [hz,hx]
    dsimp only
    change rip (C:=C) _ _ _ (B.bar p (v 0)
      (B.trainB p n (fun i => Fin.tail z i+(time b:ℂ)) (fun i => Fin.tail x i+spatial b) _ _ _)) = _
    rw [train_shift B p n (Fin.tail z) (Fin.tail x) (Fin.tail v) (z 0) (x 0)]
    exact rip_shift (z 0) p (x 0) b _ hn

lemma integral_shift (B : Small S C) (p : ℝ≥0) {n : ℕ} (v : Fin n → S.Union) (y : Heights n) (f : Fin n → Test4)
    (h : Small.ample p y) (b : E4) :
    (∫ q, (Joint.materialize n (fun i => Joint.push (Poincare.translation b) (f i)) q) • B.shot p n v y q) =
    C.flow.unit.translation b (∫ q, Joint.materialize n f q • B.shot p n v y q) := by
  let d := points (n:=n) fun _ => b
  let g := Joint.materialize n fun i => Joint.push (Poincare.translation b) (f i)
  have he (q : Points n) : g (q+d) = Joint.materialize n f q := by
    simp [d,g,Poincare.backwards,Poincare.translation]
  rw [← ContinuousLinearMap.integral_comp_comm (C.flow.unit.translation b) (shot_int B p v y (Joint.materialize n f) h)]
  rw [← integral_add_right_eq_self (fun q => g q • B.shot p n v y q) d]
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  dsimp only
  rw [he,shot_shift B p n v y q b h,map_smul]

lemma heatCup_n (B : Small S C) (v : Sentence S) (k : ℝ) (n : ℕ) (h : v.length=n) :
    B.heatCup v k = ∫ q : Points n, (Joint.materialize n (fun i => (v.get (Fin.cast h.symm i)).2) q) •
      B.shot (Small.logD k) n (fun i => (v.get (Fin.cast h.symm i)).1) (Small.profile k n) q := by
  subst n; rfl

lemma heatCup_shift (B : Small S C) (K : Spins S) {R l} (ht : K.Descends R l) (v : Sentence S) (b : E4) (k : ℝ) (h : 0<k) :
    B.heatCup (K.po (Poincare.translation b) v) k = C.flow.unit.translation b (B.heatCup v k) := by
  let w := K.po (Poincare.translation b) v
  have he : w.length=v.length := by simp [w,Spins.po]
  have hx : (fun i => (w.get (Fin.cast he.symm i)).1) = fun i => (v.get i).1 := by
    funext i; simp [w,Spins.po,Letter.read,Poincare.translation,ht.identity]
  have hy : (fun i => (w.get (Fin.cast he.symm i)).2) = fun i => Joint.push (Poincare.translation b) (v.get i).2 := by
    funext i; simp [w,Spins.po,Letter.read]
  rw [heatCup_n B w k v.length he, hx,hy]
  exact integral_shift B _ _ _ _ (Small.suitable h) b

theorem answer : YM.Bid.C23 := by
  intro G L S T V P A B K R H _ ht
  exact ⟨fun v t h => shot_int B _ _ _ _ (Small.suitable h),heatCup_shift B K ht⟩
end YM.Work.C23
