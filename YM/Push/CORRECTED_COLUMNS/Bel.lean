import YM.Push.CORRECTED_COLUMNS.Sampling
import YM.Work.A01.Support
import YM.Work.E06

/-!
# To PairSep from a Maxwell RP input

Don't assume positivity of the determinant or absence of further Wick
null directly to construct Columns. Analytically continue the first
slot with all other points fixed avoiding collision. Any x annihilated
by pairs then vanishes on *all* probes. Here only invoke ordinary RP at
one axis (not open in complex contour) and `RealSpin` on this same table.
These are still **inputs** of a free-data computation; no construction
of MaxwellData in this module.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.Bel
open Filter Function Set Maxwell Maxwell.Wick Maxwell.WaveOn Tensor OS Cells Table Word Analysis
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexOrder
variable {G : Gauge}

private lemma analyticCurl (x : E4) (h : x ≠ 0) (a b c d : Axis) : ContDiffAt ℝ ω (bareCurl a b c d) x := by
  have hn := norm_pos_iff.mpr h
  have hf : ContDiffAt ℝ ω Green x := by
    unfold Green; exact contDiffAt_const.mul ((contDiff_norm_sq ℝ).contDiffAt.inv (ne_of_gt (sq_pos_of_pos hn)))
  have hv (a b c : Axis) : ContDiffAt ℝ ω (if b=a then grad c Green else 0) x := by
    split_ifs
    · exact dSmooth hf (basis c) le_top
    exact contDiffAt_const
  have hx (a b c : Axis) : ContDiffAt ℝ ω (curlOpp a b c) x := (hv _ _ _).sub (hv _ _ _)
  unfold bareCurl; exact (dSmooth (hx b c d) (basis a) le_top).sub (dSmooth (hx a c d) (basis b) le_top)

private lemma allLeg {j l : ℕ} (p : Maxwell.Probe G j) (q : Maxwell.Probe G l) (x : E4) (hx : x ≠ 0) :
    ContDiffAt ℝ ω (legKernel p q) x := by
  have hf (F : Maxwell.Field G.Color) (hv : ∀ i j, ContDiffAt ℝ ω (F i j) x) k : ContDiffAt ℝ ω (nth F k) x := by
    refine contDiffAt_pi.mpr (fun a => contDiffAt_pi.mpr (fun b => ?_))
    exact (contDiffAt_const (c:=(k.factorial:ℝ)⁻¹)).smul ((hv a b).iteratedFDeriv_right (i:=k) le_top)
  have hg (c i l) : ContDiffAt ℝ ω (scalarTest (G:=G) (extension p) c i l) x := by
    exact (extension p).toContinuousLinearMap.contDiff.contDiffAt.comp _
      (hf _ (fun a b => (tint _).contDiff.contDiffAt.comp _ (analyticCurl x hx a b i l)) _)
  have ht i l : ContDiffAt ℝ ω (responded G (extension p) i l) x :=
    ContDiffAt.sum (fun i' _ => (hg i' i l).smul contDiffAt_const)
  exact (contDiffAt_const (c:=((-1:ℝ)^l))).mul ((extension q).toContinuousLinearMap.contDiff.contDiffAt.comp x (hf _ ht l))

lemma analyticFree (A : Labels.Frames G) {n} (q : Fin n → (Maxwell.standard A).Token) {x : Points n} (h : x∈conf n) :
    ContDiffAt ℝ ω (fun y => (freeTable A).read y q) x := by
  classical
  simp_rw [decodes,Wick.sumFormula]; refine ContDiffAt.sum (fun i _ => contDiffAt_const.mul (ContDiffAt.sum (fun j _ => ?_)))
  unfold Occ.graph
  apply contDiffAt_prod; intro p _
  have hh : Function.Injective x.ofLp := h
  let P (a : Fin n) := PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin n => E4) a
  let j' := Occ.partner j p
  let f := P p.label - P j'.label
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp x
    ((allLeg _ _ (f x) (sub_ne_zero.mpr (hh.ne (Occ.different j p).symm))).comp x f.contDiff.contDiffAt)

lemma homogeneous (A : Labels.Frames G) : (freeTable A).Homogeneous := by
  intro n x hx y v
  simp_rw [decodes,Wick.sumFormula]
  apply Finset.sum_congr rfl; intro i _
  apply congr_arg _; apply Finset.sum_congr rfl; intro j _
  unfold Occ.graph; apply Finset.prod_congr rfl; intro p _
  simp only [Occ.edge,entry,Points.across_coord,add_sub_add_right_eq_sub]

-- RP alone at one coordinate. Nonnegative kernel proof uses RealSpin too.
def oneRP {G : Gauge} {L : Register G} (T : Table L) (a : Axis) : Prop := ∀ n : ℕ, ∀ w : Fin n → Future L a,
    ∀ c : Fin n → ℂ, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, star (c i)*c j*T.gram a (w i).val (w j).val
lemma viaAll {G : Gauge} {L : Register G} {T : Table L} (p : T.RP) (a : Axis) : oneRP T a := fun m w v =>
    p a m (fun i => (w i).val) (fun i => (w i).property) v

private lemma situated {G : Gauge} {L : Register G} {T : Table L} {a : Axis} (h : T.Basic) (p : T.RealSpin)
    (he : oneRP T a) : Nonempty (Schwinger T a) := by
  apply Kernel.host
  apply NNKernel.criterion
  · intro x y
    have he : Word.distinct (Word.reflect y.val a ++ x.val) := twoSides y.property x.property
    have hv (w v : L.Word) : Word.reflect (w++v) a = Word.reflect v a ++ Word.reflect w a := by simp [reflectedPoint]
    change star (T.expect _) = T.expect _
    rw [← twice_expect h p a _ he, hv, OS.reflect_twice]
  intro m x c
  refine le_trans (he m x c) (le_of_eq ?_)
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

variable {G : Gauge} (L : Labels.Frames G) {a : Axis}
private lemma position {n : ℕ} (x : Points n) (v : Fin n → (Maxwell.standard L).Token)
    (p : (Maxwell.standard L).Token) (y : E4) :
    Word.realize (Fin.cons p v) (Points.cons y x)=(y,p)::Word.realize v x := by simp [Word.realize,Points.cons,List.ofFn_succ]

-- `RP` to Prop world. If positive spin supplied. All positions free.
theorem columnsOf (C : Family G) (S : Table C.book) (d : ℕ) (hv : (Cells.standard C).RealSpin) (h : oneRP (Cells.standard C) a) :
    ∃ X : Columns C S d, ∀ x : (Cells.standard C).Field d, x ≠ 0 → ∃ i, (X.row i).tests (Cells.standard C) X.basis x ≠ 0 := by
  apply Sampling.columns C d S hv
  let F := C.labels
  let A := freeTable F
  let B := Maxwell.standard F
  intro x H; obtain ⟨v,rfl⟩ := A.onto d x
  change A.project d v=0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply (A.criterion ..).2; intro n z p hp
  let w := Fin.cons (α:=fun _=> B.Token) ⟨d,v⟩ z
  obtain ⟨P⟩ := situated (Maxwell.table_regular F) hv h
  -- zero if spectators positive, first negative at axis
  have heal (y : Points n) (hy : y∈conf _) (hh : ∀ i, 0 < y i a) (t : E4) (ht : t a < 0) : A.read (Points.cons t y) w=0 := by
    let q : B.Word := [(t,⟨d,v⟩)]
    let f := Word.reflect q a; have hm := OS.reflect_twice a q
    let u := Ortho.move (Signed.reflect a) t
    let g := B.adj d a v
    have hf : f=[(u,⟨d,g⟩)] := by unfold f; rw [Word.reflectedPoint]; rfl
    have hu : 0<u a := by simp [u,show t a < 0 from ht]
    let Y : Future B a := ⟨f, by rw [hf]; simp [Word.Positive,locations,hu]⟩
    let W : Future B a := ⟨Word.realize z y,Word.realized z y|>.mpr hy,fun p hp => ?_⟩
    · have Hx : A.gram a Y.val Y.val=0 := by
        change A.expect (Word.reflect f a++f)=0
        rw [hm,hf]; let s : Fin 2→ B.Token := ![⟨d,v⟩,⟨d,g⟩]; let X := points ![t,u]
        have hg : X∈conf _ := (realized s X).mp (show Word.distinct _ from ?_)
        rw [show q++_ = Word.realize s X from by simp [q,s,X,List.ofFn_succ,realize]]
        rw [A.readAt,← A.at_project A (Maxwell.table_sym _) (fun _ => le_rfl) hg]
        have hT : A.classTokens ∘ s= ![⟨d,A.project d v⟩,⟨d,A.project d g⟩] := by funext i; fin_cases i <;> rfl
        rw [hT]; exact H (A.project d g) X hg
        rw [locations]; have hp : t≠u := by intro h; rw [h] at ht; linarith
        simp [realize,List.ofFn_succ,X,hp]
      have he := P.measure Y W
      have hr : P.plant Y=0 := (inner_self_eq_zero).1 (by rw [P.measure,Hx])
      rw [hr,inner_zero_left] at he
      change 0=A.expect (Word.reflect f a++Word.realize z y) at he; rw [hm] at he
      rw [← A.readAt,position F]; exact he.symm
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hp; subst p; exact hh i
  -- translate spectators, also maybe move first negative (for a neighborhood, keeping the shift fixed). then extend ANALYTIC (Maxwell rational) through all configurations of the first point
  let X := Points.tail p
  let f (x : E4) := A.read (Points.cons x X) w
  let R := (Set.range X.ofLp)ᶜ
  have hx (x) (hh : x∈R) : Points.cons x X ∈ conf _ := Work.A01.conf_cons (Points.tail_in hp) (fun i he => hh ⟨i,he.symm⟩)
  have ht : AnalyticOnNhd ℝ f R := by
    intro x hh
    let g (y : E4) := Points.cons y X
    have hv : ContDiffAt ℝ ω g x := by
      let Y := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n+1) => E4)
      have hx : ContDiffAt ℝ ω (fun z => (g z).ofLp) x := contDiffAt_pi.mpr (fun i => ?_)
      · exact Y.symm.contDiff.contDiffAt.comp x hx
      refine Fin.cases ?_ (fun i => ?_) i <;> simp only [g,Points.cons, points_apply, Fin.cons_zero,Fin.cons_succ]
      · exact contDiffAt_id
      exact contDiffAt_const
    exact ((analyticFree F w (hx x hh)).comp x hv).analyticAt
  have h' : ∃ u : ℝ, ∀ i, -(X i a)<u := (eventually_all.2 (fun i : Fin n => eventually_gt_atTop (-(X i a)))).exists
  obtain ⟨u,h'⟩ := h'
  let o := u • basis a
  let Y := Points.across o X
  have hY : ∀ i, 0 < Y i a := by
    intro i; have hv := h' i; simp only [Y,o,Points.across_coord,WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply]; simpa using (by linarith : 0<X i a+u)
  let t₀ := (-1-u) • basis a
  have ht₀ : t₀ a < -u := by simp [t₀]; linarith
  have ha x (h : x a < -u) : x∈R := by
    rintro ⟨j,hj⟩; subst x; linarith [h' j]
  have hy : f =ᶠ[𝓝 t₀] 0 := by
    have hv : ∀ᶠ x : E4 in 𝓝 t₀, x a < -u := ((PiLp.proj (𝕜:=ℝ) 2 (fun _ : Axis => ℝ) a).continuous.continuousAt.tendsto).eventually (gt_mem_nhds ht₀)
    filter_upwards [hv] with i hi
    unfold f
    rw [← homogeneous F (n+1) _ (hx i (ha i hi)) o w]
    have he : Points.across o (Points.cons i X)=Points.cons (i+o) Y := by
      ext1 j; refine Fin.cases ?_ (fun j=> ?_) j <;> simp [Points.cons,Y]
    rw [he]; apply heal _ (Points.across_in _ (Points.tail_in hp)) hY
    change i a+o a<0; unfold o; simpa using (by linarith : i a+u<0)
  have hm : 1 < Module.rank ℝ E4 := by rw [← Module.finrank_eq_rank, show Module.finrank ℝ E4=4 from finrank_euclideanSpace_fin]; norm_num
  have hh : IsPreconnected R := ((finite_range X.ofLp).countable.isPathConnected_compl_of_one_lt_rank hm).isConnected.isPreconnected
  have hp₀ : p 0 ∈ R := by
    rintro ⟨k,hk⟩; exact Fin.succ_ne_zero k ((show Function.Injective p.ofLp from hp) hk)
  have hv := ht.eqOn_zero_of_preconnected_of_eventuallyEq_zero hh (ha _ ht₀) hy hp₀
  unfold f at hv
  rw [show Points.cons (p 0) X=p from by ext1 i; refine Fin.cases ?_ (fun i => ?_) i <;> simp [X,Points.cons,Points.tail]] at hv
  exact hv
end YM.Push.Corrected.Bel
