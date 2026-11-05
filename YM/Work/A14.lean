import YM.Bid.Angular

/-!
A14, continuation from `Port`. The configuration-space Ward identity is assumed
at all separated points (not just on a line); the angular maps in that identity
are exactly those differentiating the given `act`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.A14
open Set Function Filter Table Ward
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {L : Register G} {S : Table L} {n : ℕ}

/-! Elementary geometry / differentiation along one-parameter actions. -/

private lemma decomposePoints (x : Points n) :
    ∑ i : Fin n, ∑ a : Axis, x i a • Points.direction i a = x := by
  apply PiLp.ext
  intro j
  have he : ∑ a : Axis, x j a • basis a = x j := by
    apply PiLp.ext
    intro b
    simp
  simpa [Points.direction, Pi.single_apply, smul_ite] using he

private lemma mul_move (s r : Ortho) (x : Points n) :
    Points.move (s*r) x = Points.move s (Points.move r x) :=
  PiLp.ext fun i => Ortho.move_mul s r (x i)

private lemma one_move (x : Points n) : Points.move 1 x = x :=
  PiLp.ext fun i => Ortho.move_one (x i)

private lemma unmove (s : Ortho) (x : Points n) :
    Points.move s (Points.move s⁻¹ x) = x :=
  PiLp.ext fun i => Ortho.move_inv s (x i)

/-- Positions have velocity Kx (evaluated at the moving point). -/
private theorem velocity (K : Ortho.Skew) (x : Points n) (t : ℝ) :
    HasDerivAt (fun s => Points.move (Ortho.oneParameter K s) x)
      (points fun i => M4.move K.val ((Points.move (Ortho.oneParameter K t) x) i)) t := by
  let A : M4 →L[ℝ] Points n := LinearMap.toContinuousLinearMap {
    toFun m := points fun i => M4.move m (x i)
    map_add' m l := by
      ext1 i
      change (Matrix.toEuclideanLin (m+l)) (x i) =
        (Matrix.toEuclideanLin m) (x i) + (Matrix.toEuclideanLin l) (x i)
      rw [map_add, LinearMap.add_apply]
    map_smul' a m := by
      ext1 i
      change (Matrix.toEuclideanLin (a • m)) (x i) = a • (Matrix.toEuclideanLin m) (x i)
      rw [map_smul, LinearMap.smul_apply] }
  have he : HasDerivAt (fun s => Points.move (Ortho.oneParameter K s) x)
      (A (K.val * NormedSpace.exp (t • K.val))) t :=
    A.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const' K.val t)
  have hm : A (K.val * NormedSpace.exp (t • K.val)) =
      points fun i => M4.move K.val ((Points.move (Ortho.oneParameter K t) x) i) :=
    PiLp.ext fun i => M4.move_mul K.val (NormedSpace.exp (t • K.val)) (x i)
  rw [hm] at he
  exact he

private lemma parameter_zero (K : Ortho.Skew) : Ortho.oneParameter K 0 = 1 := by
  apply Subtype.ext
  change NormedSpace.exp ((0:ℝ) • K.val) = 1
  simp

private lemma parameter_add (K : Ortho.Skew) (s t : ℝ) :
    Ortho.oneParameter K (s+t) = Ortho.oneParameter K s * Ortho.oneParameter K t := by
  apply Subtype.ext
  haveI : NormedAlgebra ℚ M4 := .restrictScalars ℚ ℝ _
  change NormedSpace.exp ((s+t) • K.val) =
    NormedSpace.exp (s • K.val) * NormedSpace.exp (t • K.val)
  rw [add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl K.val).smul_left s).smul_right t)

/-- `Port` gives the derivative at zero. Use it at the already-moved label. -/
private theorem labelVelocity {H : S.RealSpin} {U : Rotation S} (hU : Spin.Port U H)
    (d : ℕ) (v : S.Field d) (K : Ortho.Skew) (t : ℝ) :
    HasDerivAt (fun s => U.act d (Ortho.oneParameter K s) v)
      (U.lie d K (U.act d (Ortho.oneParameter K t) v)) t := by
  let w := U.act d (Ortho.oneParameter K t) v
  let F := fun r => U.act d (Ortho.oneParameter K r) w
  have hd : HasDerivAt F (U.lie d K w) 0 := hU.spinAt d K w
  have hi : HasDerivAt (fun s : ℝ => s-t) 1 t := (hasDerivAt_id t).sub_const t
  have he := hd.scomp_of_eq t hi (by simp)
  rw [one_smul] at he
  have hf : F ∘ (fun s : ℝ => s-t) = fun s : ℝ => U.act d (Ortho.oneParameter K s) v := by
    funext s
    dsimp only [F, Function.comp_apply, w]
    rw [← hU.sends, ← parameter_add, sub_add_cancel]
  rw [hf] at he
  exact he

/-! Fixed-cap tuples of labels, for joint differentiation. In particular we
need joint (position AND label) differentiation along the orbit, not just separate
fixed-label estimates without justification of the product rule. -/

private abbrev Tuple (S : Table L) (d : Caps n) := (i : Fin n) → S.Field (d i)

private def moment (S : Table L) (d : Caps n) (p : Points n × Tuple S d) :=
  S.classMoment S d p.1 p.2

private theorem joint (H : S.Hierarchy) (d : Caps n) (x : Points n) (v : Tuple S d)
    (hx : x ∈ conf n) : ContDiffAt ℝ ∞ (moment S d) (x, v) := by
  classical
  let I (i : Fin n) := Fin (Module.finrank ℂ (S.Field (d i)))
  let B (i : Fin n) : Module.Basis (I i) ℂ (S.Field (d i)) := Module.finBasis ℂ _
  let b (r : ∀ i, I i) (i : Fin n) := B i (r i)
  let a (r : ∀ i, I i) (i : Fin n) (p : Points n × Tuple S d) := (B i).repr (p.2 i) (r i)
  letI (i : Fin n) : Fintype (I i) := inferInstanceAs (Fintype (Fin _))
  -- full fixed index sets (including possible empty cases), not supports depending on p
  have he : moment S d = fun p => ∑ r : ∀ i, I i,
      (∏ i, a r i p) * S.classMoment S d p.1 (b r) := by
    funext p
    dsimp only [moment]
    let f (i) (j : I i) := (B i).repr (p.2 i) j • B i j
    calc
      _ = S.classMoment S d p.1 (fun i => ∑ j, f i j) := by
        congr 1
        funext i
        exact ((B i).sum_repr _).symm
      _ = ∑ r : ∀ i, I i, S.classMoment S d p.1 (fun i => f i (r i)) :=
        (S.classMoment S d p.1).map_sum f
      _ = _ := Finset.sum_congr rfl (fun r _ => (S.classMoment S d p.1).map_smul_univ
        (fun i => a r i p) (b r))
  rw [he]
  refine ContDiffAt.sum fun r _ => ?_
  have ha (i) : ContDiffAt ℝ ∞ (a r i) (x,v) := by
    let P : Tuple S d →L[ℝ] S.Field (d i) := ContinuousLinearMap.proj i
    let R := LinearMap.toContinuousLinearMap (((B i).coord (r i)).restrictScalars ℝ)
    change ContDiffAt ℝ ∞ (fun p : Points n × Tuple S d => R (P p.2)) (x,v)
    exact ((R.comp P).contDiff.contDiffAt.comp (x,v) contDiffAt_snd)
  exact (contDiffAt_prod (fun i _ => ha i)).mul
    ((Ward.cont_disc H (fun i => ⟨d i,b r i⟩) hx).comp (x,v) contDiffAt_fst)

private theorem movingLabels (H : S.Hierarchy) (d : Caps n) (x : Points n) (hx : x ∈ conf n)
    (w : ℝ → Tuple S d) (t : ℝ) (dw : Tuple S d) (hw : HasDerivAt w dw t) :
    HasDerivAt (fun u => moment S d (x, w u))
      (∑ i : Fin n, disc (update (fun j => (⟨d j,w t j⟩ : S.Tag)) i ⟨d i,dw i⟩) x) t := by
  let Q : ContinuousMultilinearMap ℝ (fun i => S.Field (d i)) ℂ := {
    toMultilinearMap := (S.classMoment S d x).restrictScalars ℝ
    cont := by
      refine continuous_iff_continuousAt.mpr (fun v : Tuple S d => ?_)
      exact ((joint H d x v hx).comp v (contDiffAt_const.prodMk contDiffAt_id)).continuousAt }
  have he : HasDerivAt (fun u => moment S d (x, w u)) (Q.linearDeriv (w t) dw) t :=
    (Q.hasFDerivAt _).comp_hasDerivAt t hw
  rw [ContinuousMultilinearMap.linearDeriv_apply] at he
  convert he using 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have ht : update (fun j => (⟨d j,w t j⟩ : S.Tag)) i ⟨d i,dw i⟩ =
      fun j => (⟨d j, update (w t) i (dw i) j⟩ : S.Tag) := by
    funext j
    by_cases h : j=i
    · subst j; simp
    simp only [update_of_ne h]
  rw [ht]
  rfl

private theorem movingPoints (H : S.Hierarchy) (V : DiffPlan S) (hd : V.Derivatives S)
    (v : Fin n → S.Tag) (y : ℝ → Points n) (t : ℝ) (hx : y t ∈ conf n) (dy : Points n)
    (hy : HasDerivAt y dy t) : HasDerivAt (fun u => disc v (y u))
      (∑ i : Fin n, ∑ a : Axis, dy i a • disc (update v i (Ward.rise V a (v i))) (y t)) t := by
  let D := fderiv ℝ (disc v) (y t)
  have he : HasDerivAt (fun u => disc v (y u)) (D dy) t :=
    ((Ward.cont_disc H v hx).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hy
  have hv : D dy = ∑ i : Fin n, ∑ a : Axis, dy i a • disc (update v i (Ward.rise V a (v i))) (y t) := by
    conv_lhs => rw [← decomposePoints dy]
    simp only [map_sum, map_smul]
    simp_rw [← Ward.fromD V H hd hx]
    rfl
  rwa [hv] at he

/-! Full covariance: one-parameter orbits, Signed, then algebraic closure. -/

private theorem parameterDeriv (H : S.Hierarchy) (V : DiffPlan S) (hd : V.Derivatives S)
    (U : Rotation S) (hU : Spin.Port U H.spin) (K : Ortho.Skew) (x : Points n)
    (hx : x ∈ conf n) (v : Fin n → S.Tag) (t : ℝ) :
    let y := fun s => Points.move (Ortho.oneParameter K s) x
    let q := fun s => U.label (Ortho.oneParameter K s) ∘ v
    HasDerivAt (fun s => S.useAt S (y s) (q s)) (angular V U.lie (q t) K (y t)) t := by
  intro y q
  let d (i : Fin n) := (v i).1
  let w : ℝ → Tuple S d := fun s i => U.act (d i) (Ortho.oneParameter K s) (v i).2
  let dy := points fun i => M4.move K.val (y t i)
  let dw : Tuple S d := fun i => U.lie (d i) K (w t i)
  have hp : y t ∈ conf n := Points.move_in _ hx
  have hy : HasDerivAt y dy t := velocity K x t
  have hw : HasDerivAt w dw t := hasDerivAt_pi.mpr (fun i => labelVelocity hU (d i) (v i).2 K t)
  -- Identify the two components of the joint derivative by freezing
  -- (respectively) the label tuple and the position tuple.
  let D := fderiv ℝ (moment S d) (y t,w t)
  have hD : HasFDerivAt (moment S d) D (y t,w t) :=
    ((joint H d _ _ hp).differentiableAt (by simp)).hasFDerivAt
  have h₁ : HasDerivAt (fun s => disc (q t) (y s)) (D (dy,0)) t :=
    HasFDerivAt.comp_hasDerivAt (l := moment S d) t hD (hy.prodMk (hasDerivAt_const t (w t)))
  have h₂ : HasDerivAt (fun s => moment S d (y t,w s)) (D (0,dw)) t :=
    HasFDerivAt.comp_hasDerivAt (l := moment S d) t hD ((hasDerivAt_const t (y t)).prodMk hw)
  have hA : D (dy,dw) = angular V U.lie (q t) K (y t) := calc
    _ = D (dy,0) + D (0,dw) := by rw [← map_add]; simp
    _ = angular V U.lie (q t) K (y t) := by
      rw [h₁.unique (movingPoints H V hd (q t) y t hp dy hy),
        h₂.unique (movingLabels H d (y t) hp w t dw hw)]
      rw [angular, Finset.sum_add_distrib, add_comm]
      rfl
  have hh : HasDerivAt (fun s => S.useAt S (y s) (q s)) (D (dy,dw)) t :=
    HasFDerivAt.comp_hasDerivAt (l := moment S d) t hD (hy.prodMk hw)
  rwa [hA] at hh

private def Cov (U : Rotation S) (s : Ortho) :=
  ∀ (n : ℕ) (v : Fin n → S.Tag), ∀ x ∈ conf n,
    S.useAt S (Points.move s x) (U.label s ∘ v) = S.useAt S x v

private lemma label_one {U : Rotation S} {H : S.RealSpin} (hU : Spin.Port U H) (p : S.Tag) :
    U.label 1 p = p := by
  simp only [Rotation.label, hU.fixes]

private lemma label_mul {U : Rotation S} {H : S.RealSpin} (hU : Spin.Port U H) (s r : Ortho)
    (p : S.Tag) : U.label (s*r) p = U.label s (U.label r p) := by
  simp only [Rotation.label,hU.sends]
  rfl

private lemma unlabeled {U : Rotation S} {H : S.RealSpin} (hU : Spin.Port U H) (s : Ortho)
    (v : Fin n → S.Tag) : U.label s ∘ (U.label s⁻¹ ∘ v) = v := by
  funext i; rw [Function.comp_apply, Function.comp_apply, ← label_mul hU, mul_inv_cancel, label_one hU]

private lemma cov_one {U : Rotation S} {H : S.RealSpin} (hU : Spin.Port U H) : Cov U 1 := by
  intro n v x _
  rw [one_move, show U.label 1 ∘ v = v from funext fun i => label_one hU (v i)]

private lemma cov_mul {U : Rotation S} {H : S.RealSpin} (hU : Spin.Port U H)
    {s r : Ortho} (hs : Cov U s) (hr : Cov U r) : Cov U (s*r) := by
  intro n v x hx
  rw [mul_move, show U.label (s*r) ∘ v = U.label s ∘ (U.label r ∘ v) from
    funext fun i => label_mul hU s r (v i)]
  exact (hs n _ _ (Points.move_in r hx)).trans (hr _ v x hx)

private lemma cov_inv {U : Rotation S} {H : S.RealSpin} (hU : Spin.Port U H)
    {s : Ortho} (hs : Cov U s) : Cov U s⁻¹ := by
  intro n v x hx
  have he := hs n (U.label s⁻¹ ∘ v) _ (Points.move_in s⁻¹ hx)
  rw [unmove, unlabeled hU] at he
  exact he.symm

private theorem cov_parameter (H : S.Hierarchy) (V : DiffPlan S) (hd : V.Derivatives S)
    (U : Rotation S) (hU : Spin.Port U H.spin)
    (hs : ∀ (n : ℕ) (x : Points n), x ∈ conf n → Still V U.lie x)
    (K : Ortho.Skew) (t : ℝ) : Cov U (Ortho.oneParameter K t) := by
  intro n v x hx
  let f := fun s => S.useAt S (Points.move (Ortho.oneParameter K s) x) (U.label (Ortho.oneParameter K s) ∘ v)
  have he (s : ℝ) : HasDerivAt f 0 s := by
    have hh : HasDerivAt f (angular V U.lie (U.label (Ortho.oneParameter K s) ∘ v) K
        (Points.move (Ortho.oneParameter K s) x)) s := parameterDeriv H V hd U hU K x hx v s
    rwa [hs n _ (Points.move_in _ hx) _ K] at hh
  have hc : f t = f 0 := is_const_of_deriv_eq_zero
    (fun s => (he s).differentiableAt) (fun s => (he s).deriv) t 0
  change f t = _
  rw [hc]
  unfold f
  rw [parameter_zero]
  exact cov_one hU n v x hx

private theorem cov_signed (H : S.Hierarchy) (U : Rotation S) (hU : Spin.Port U H.spin)
    (s : Signed) : Cov U s.ortho := by
  intro n v x hx
  have hu (p : L.Token) : U.label s.ortho (S.classTokens p) = S.classTokens (L.move s p) := by
    simp only [Rotation.label, Table.classTokens, hU.signed, S.mirror_project]
    rfl
  let w : Fin n → L.Token := fun i => Ward.expose (v i)
  have he : U.label s.ortho ∘ v = S.classTokens ∘ (L.move s ∘ w) := by
    funext i
    exact (congr_arg (U.label s.ortho) (Ward.sends_back (v i)).symm).trans (hu (w i))
  rw [he, Table.at_project S S H.laws.toSymmetric (fun _ => le_rfl) (Points.move_in _ hx),
    H.spin.mirror s hx]
  exact Ward.raw v x

private theorem oriented (hg : YM.Bid.A13) (H : S.Hierarchy) (V : DiffPlan S) (hd : V.Derivatives S)
    (U : Rotation S) (hU : Spin.Port U H.spin) (hs : ∀ n (x : Points n), x ∈ conf n → Still V U.lie x) :
    U.Oriented S := by
  let A : Subgroup Ortho := {
    carrier := {s | Cov U s}
    one_mem' := cov_one hU
    mul_mem' := cov_mul hU
    inv_mem' := cov_inv hU }
  have hi : YM.Bid.AxisGens ≤ A := by
    apply (Subgroup.closure_le A).mpr
    rintro x (⟨s,rfl⟩ | ⟨K,t,rfl⟩)
    · exact cov_signed H U hU s
    exact cov_parameter H V hd U hU hs K t
  rw [show YM.Bid.AxisGens = ⊤ from hg] at hi
  intro n v x hx K
  exact (show Cov U K from hi (Subgroup.mem_top K)) n v x hx

/-! Laws extracted by testing at the moved positions against arbitrary exterior
words. `Spin.team` already does this for filtration, we also need preservation
of the unit and transformation of gradients. -/

private lemma pullHead {U : Rotation S} (ho : U.Oriented S) (s : Ortho)
    (x : Points (n+1)) (hx : x ∈ conf (n+1)) (q : Fin n → S.Tag) (d : ℕ) (v : S.Field d) :
    S.useAt S (Points.move s x) (Fin.cons ⟨d,U.act d s v⟩ (U.label s ∘ q)) =
      S.useAt S x (Fin.cons ⟨d,v⟩ q) := by
  have he : Fin.cons (α := fun _ => S.Tag) ⟨d,U.act d s v⟩ (U.label s ∘ q) =
      U.label s ∘ (Fin.cons (α := fun _ => S.Tag) ⟨d,v⟩ q) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp only [Function.comp_apply, Fin.cons_zero, Fin.cons_succ]
    rfl
  rw [he]
  exact ho _ _ _ hx s

private theorem unit_fixed (H : S.Hierarchy) (U : Rotation S) (hU : Spin.Port U H.spin)
    (ho : U.Oriented S) (d : ℕ) (s : Ortho) : U.act d s (S.unit d) = S.unit d := by
  apply S.field_ext H.laws.toSymmetric
  intro n q x hx
  let y := Points.move s⁻¹ x
  have hy : y ∈ conf _ := Points.move_in _ hx
  let r := U.label s⁻¹ ∘ q
  have hi := pullHead ho s y hy r d (S.unit d)
  have he : U.label s ∘ r = q := unlabeled hU s q
  rw [show Points.move s y=x from unmove s x, he] at hi
  rw [hi, S.at_unit H.laws hx, S.at_unit H.laws hy]
  have hm : Points.move s (Points.tail y) = Points.tail x := by
    apply PiLp.ext; intro i; exact Ortho.move_inv s (x i.succ)
  have hh := ho n r (Points.tail y) (Points.tail_in hy) s
  rw [hm, he] at hh
  exact hh.symm

private def moveCLM (s : Ortho) : Points n →L[ℝ] Points n := LinearMap.toContinuousLinearMap {
  toFun := Points.move s
  map_add' p r := PiLp.ext fun i => (Ortho.motion s).map_add (p i) (r i)
  map_smul' a p := PiLp.ext fun i => (Ortho.motion s).map_smul a (p i) }

private lemma transport_direction (s : Ortho) (i : Fin n) (a : Axis) :
    moveCLM s (Points.direction i a) = ∑ b : Axis, s.val b a • Points.direction i b := by
  let p := Points.direction i a
  have he : ∀ j : Fin n, ∑ b : Axis, moveCLM s p j b • Points.direction j b =
      if j = i then ∑ b : Axis, s.val b a • Points.direction i b else 0 := by
    intro j
    by_cases h : j=i
    · subst j
      apply Eq.trans _ (if_pos rfl).symm
      apply Finset.sum_congr rfl
      intro b _
      change M4.move _ (Points.direction i a i) b • _ = _
      simp [Points.direction]
    rw [if_neg h]
    apply Finset.sum_eq_zero
    intro b _
    change (Ortho.motion s) (Points.direction i a j) b • _ = _
    rw [Points.direction, PiLp.single_eq_of_ne _ h, map_zero]
    simp
  rw [← decomposePoints (moveCLM s p)]
  simp_rw [he]; simp

/-- Chain rule under simultaneous motion. Column `a`, not row `a`. -/
private theorem pullGrad (s : Ortho) (y : Points n) (f : Points n → ℂ)
    (hf : DifferentiableAt ℝ f (Points.move s y)) (a : Axis) (i : Fin n) :
    Points.gradient i a (fun x => f (Points.move s x)) y =
      ∑ b : Axis, s.val b a • Points.gradient i b f (Points.move s y) := by
  change fderiv ℝ (f ∘ moveCLM s) y (Points.direction i a) = _
  rw [fderiv_comp y (show DifferentiableAt ℝ f (moveCLM s y) from hf) (moveCLM s).differentiableAt,
    (moveCLM s).fderiv, ContinuousLinearMap.comp_apply, transport_direction]
  simp only [map_sum, map_smul]; rfl

private theorem vectorLaw (H : S.Hierarchy) (V : DiffPlan S) (hd : V.Derivatives S)
    (U : Rotation S) (hU : Spin.Port U H.spin) (ho : U.Oriented S) (d : ℕ) (s : Ortho)
    (a : Axis) (v : S.Field d) : U.act (d+1) s (V.deriv d a v) =
      ∑ i : Axis, ((s.val i a : ℝ) : ℂ) • V.deriv d i (U.act d s v) := by
  apply S.field_ext H.laws.toSymmetric
  intro n q x hx
  let y := Points.move s⁻¹ x
  let r := U.label s⁻¹ ∘ q
  have hi : U.label s ∘ r = q := unlabeled hU s q
  have hy : y ∈ conf _ := Points.move_in _ hx
  have hxy : Points.move s y = x := unmove s x
  have he := pullHead ho s y hy r (d+1) (V.deriv d a v)
  rw [hxy, hi] at he
  rw [he, hd.kernels d a v hy]
  let f : Points (n+1) → ℂ := fun z => S.useAt S z (Fin.cons ⟨d,U.act d s v⟩ q)
  have hp : Points.gradient 0 a (fun z => S.useAt S z (Fin.cons ⟨d,v⟩ r)) y =
      Points.gradient 0 a (fun z => f (Points.move s z)) y := by
    apply Analysis.GermD
    filter_upwards [(conf_open _).mem_nhds hy] with z hz
    have Hf := pullHead ho s z hz r d v
    rw [hi] at Hf
    exact Hf.symm
  have hf : DifferentiableAt ℝ f (Points.move s y) := by
    rw [hxy]
    exact (Ward.cont_disc H (Fin.cons ⟨d,U.act d s v⟩ q) hx).differentiableAt (by simp)
  rw [hp, pullGrad s y f hf, hxy]
  unfold f
  simp_rw [← hd.kernels _ _ _ hx]
  let A := Fin.cons (α := fun _ : Fin (n+1) => S.Tag) ⟨d+1,(0 : S.Field (d+1))⟩ q
  have Hx (p : S.Field (d+1)) : S.useAt S x (Fin.cons ⟨d+1,p⟩ q) = Ward.here A x 0 (d+1) p := by
    rw [Ward.takes]; unfold disc; congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [A]
  simp_rw [Hx, map_sum, map_smul]
  exact Finset.sum_congr rfl (fun i _ => RCLike.real_smul_eq_coe_smul (K := ℂ) _ _)

/-- Reusable last step (also for the same-table case where covariance is obtained
by other means). Translational/differential orientation data are not being used
as hypotheses beyond `Hierarchy`, `Inclusions`, `Derivatives`. -/
theorem laws_of_oriented (H : S.Hierarchy) (V : DiffPlan S) (hi : V.Inclusions S)
    (hd : V.Derivatives S) (U : Rotation S) (hU : Spin.Port U H.spin)
    (ho : U.Oriented S) : U.Laws V H.spin := by
  exact {
    spin := hU.spin
    fixes := hU.fixes
    group := hU.sends
    signed := hU.signed
    real := hU.real
    identity := unit_fixed H U hU ho
    filtered := fun _ _ w s v => Spin.team U H hU ho V hi w s v
    vector := vectorLaw H V hd U hU ho
    infinitesimal := hU.spinAt }

theorem answer : YM.Bid.A14 := by
  intro hg G L S H V hi hd U hU hs
  have ho := oriented hg H V hd U hU hs
  exact ⟨laws_of_oriented H V hi hd U hU ho, ho⟩

end YM.Work.A14
