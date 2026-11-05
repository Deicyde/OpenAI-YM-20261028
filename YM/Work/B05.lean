import Mathlib.LinearAlgebra.Multilinear.Pi
import YM.Bid.Phase

set_option autoImplicit false
noncomputable section
namespace YM.Work.B05
open Set Filter Function MeasureTheory OS OS.Ground Org Org.Phase Spec Table Word Analysis Extraction Bid
open scoped Topology NNReal InnerProductSpace BigOperators ContDiff ENNReal

variable {G : Gauge} {C : Family G} {S : Table C.book} {V : Chamber S timeAxis}
    {A : Spread V} {F : Order} {n : ℕ}

private lemma ordinary (v : Fin n → C.book.Token) (hv : Grid.plain (C := C) v) (x : Points n) :
    List.Perm (reflect (realize v x) timeAxis) (Grid.anti (C:=C) (realize v x)) := by
  have he : conjugate (realize v x) = realize v x := by
    unfold conjugate realize
    rw [List.map_ofFn]; congr 1; ext1 i
    exact Prod.ext rfl (show C.book.conjugate (v i)=v i from by simp [Register.conjugate,hv i])
  unfold reflect
  rw [show conjugate (realize v x).reverse = (conjugate (realize v x)).reverse from List.map_reverse,he]
  exact (List.reverse_perm _).map _

private lemma at_tag (t : Theme V A) (b : B04) (s : Seed C F S) (X : Spec.Algebra S)
    (hc : Locals X s.kernel.spin) (hs : Steady V)
    (v : Fin n → C.book.Token) (k : ℕ) (x : Fin n → Lattice.Cover) (hp : Grid.plain (C := C) v)
    (hg : Order.grid C k x ∈ generic n) (p : Grid.Covering (C := C) k v x)
    (he : p.Works k v x F) (hd : distinct (Grid.Tag k v x)) :
    M A (Grid.Tag k v x) hd = M A (Grid.anti _) (Grid.apart hd) := by
  let w := Grid.Tag (C:=C) k v x
  let D := Grid.θ A w hd
  have h := t.opposite w hd (Word.reflects _ hd) |>.trans
    (t.changes (ordinary v hp (Order.grid C k x)) (Word.reflects _ hd) (Grid.apart hd))
  have ht : star D = -D := by
    change star (M A w hd - _) = -(M A w hd - _)
    rw [← h]; simp [star_sub]
  have hd' : ContinuousLinearMap.adjoint D.val = - D.val := congr_arg Subtype.val ht
  have hz := p.square A k v x hd he hs s.kernel (b v x k s.cutoff s.kernel s.generic hp hg)
  have hy : 0 ≤ (inner ℂ V.omega0 (D.val (D.val V.omega0))).re := by
    simp only [Grid.answer,pow_two] at hz; exact hz
  have hx : (inner ℂ (D.val V.omega0) (D.val V.omega0)).re=‖D.val V.omega0‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [← ContinuousLinearMap.adjoint_inner_right, hd',neg_apply,inner_neg_right, Complex.neg_re] at hx
  have h0 : ‖D.val V.omega0‖=0 := by nlinarith
  exact sub_eq_zero.mp (show D=0 from attains A (adjunction A hs s.kernel X.turns hc.motion) hs D (norm_eq_zero.mp h0))

private abbrev mir := Signed.mirror timeAxis
private abbrev reflectX {n} := Points.move (n:=n) mir.ortho

private lemma real_depot (t : Theme V A) (b : B04) (s : Seed C F S) (X : Spec.Algebra S)
    (hc : Locals X s.kernel.spin) (hs : Steady V) (hY : Grill C F)
    (p : Caps n) (v : C.book.Vector p) (hp : ∀ i, star (v i)=v i) :
    EqOn (fun y => depot V A y p v)
      (fun y => depot V A (reflectX y) p (fun i => C.book.mirrorGroup (p i) mir (v i))) (conf n) := by
  classical
  let u : Fin n → C.book.Token := fun i => ⟨p i,v i⟩
  let P (x : Points n) := (depot V A x p v).val
  let Q (x : Points n) := (depot V A x p (fun i => C.book.mirrorGroup _ mir (v i))).val
  have hP : ContinuousOn P (conf n) := (t.steep n u).continuousOn
  have hQ : ContinuousOn (Q ∘ reflectX) (conf n) := by
    apply (t.steep n (C.book.move mir ∘ u)).continuousOn.comp _ (fun _ h => Points.move_in _ h)
    let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => E4)
    exact (L.symm.continuous.comp (show Continuous (fun y : Points n => fun i => mir.ortho.motion (y i)) from
      continuous_pi fun i => (mir.ortho.motion.continuous.comp (show Continuous (fun y : Points n => y i) from by fun_prop)))).continuousOn
  let d := Finset.univ.sup p
  choose k hk hG using hY d
  have ht : Tendsto k atTop atTop := tendsto_atTop_mono hk tendsto_id
  have h : EqOn P (Q ∘ reflectX) (generic n) := by
    intro x hx
    let c (i) := address (C.S.a (k i)) x
    let a (i) := Order.grid C (k i) (c i)
    have hA : Tendsto a atTop (𝓝 x) := (chosen (S:=C.S) x).comp ht
    have he : ∀ᶠ i in atTop, a i ∈ generic n := hA.eventually ((genericOpen _).mem_nhds hx)
    have hf := tendsto_nhdsWithin_iff.mpr ⟨hA,he.mono fun _ h => generic_conf _ h⟩
    have hu := (hP x (generic_conf _ hx)).tendsto.comp hf
    apply tendsto_nhds_unique (hu.congr' _) ((hQ x (generic_conf _ hx)).tendsto.comp hf)
    filter_upwards [he] with i hi
    obtain ⟨Y,hY'⟩ := hG i n u (fun j => Finset.le_sup (s:=Finset.univ) (f:=p) (Finset.mem_univ j)) hp (c i) hi
    have h1 := generic_conf _ hi
    have h2 := Points.move_in mir.ortho h1
    have hg := at_tag t b s X hc hs u (k i) (c i) hp hi Y hY' ((realized ..).mpr h1)
    have ha : Grid.anti (Grid.Tag (C:=C) (k i) u (c i)) = realize (C.book.move mir ∘ u) (reflectX (a i)) := by
      unfold Grid.anti act realize
      exact List.map_ofFn
    simp only [comp_apply,P,Q,depot,dif_pos h1,dif_pos h2]
    have hh : ∀ (w : C.book.Word) (z : distinct w), Grid.anti (Grid.Tag (C:=C) (k i) u (c i)) = w →
        M A (realize u (a i)) ((realized ..).2 h1) = M A w z := fun _ _ h => by subst_vars; exact hg
    exact congr_arg Subtype.val (hh _ ((realized ..).mpr h2) ha)
  have hm : P =ᵐ[volume.restrict (conf n)] Q ∘ reflectX := ae_restrict_of_ae ((almostGeneric n).mono fun x hx => h hx)
  exact fun y hy => Subtype.ext (Measure.eqOn_of_ae_eq hm hP hQ (by rw [(conf_open n).interior_eq]; exact subset_closure) hy)

theorem answer : Bid.B05 := by
  intro b G C S F s hY X hc V A hs t w hw
  let u := Word.tokens w
  let p := fun i => (u i).1
  let v : C.book.Vector p := fun i => (u i).2
  let x := Word.positions w
  obtain ⟨P,hP⟩ := t.array _ p x
  obtain ⟨Q,hQ⟩ := t.array _ p (reflectX x)
  have he : P = Q.compLinearMap (fun i => C.book.mirrorGroup (p i) mir) := by
    apply MultilinearMap.pi_ext
    intro j
    apply MultilinearMap.ext_ring
    simp only [MultilinearMap.compLinearMap_apply, hP, hQ]
    refine real_depot t b s X hc hs hY p _ (fun i => ?_) hw
    change star (Pi.single (j i) 1 : _ → ℂ) = Pi.single (j i) 1
    ext m
    by_cases hm : m=j i <;> simp [hm]
  have h1 : realize (fun i => ⟨p i,v i⟩) x = w := Word.rebuilt w
  have h2 : realize (L:=C.book) (fun i => ⟨p i,C.book.mirrorGroup (p i) mir (v i)⟩) (reflectX x)=Grid.anti (C:=C) w := by
    refine Eq.trans ?_ (congr_arg (Grid.anti (C:=C)) h1)
    unfold Grid.anti act realize; rw [List.map_ofFn]; rfl
  have hg := DFunLike.congr_fun he v
  simp only [hP,MultilinearMap.compLinearMap_apply,hQ,depot,dif_pos (show x ∈ conf _ from hw),dif_pos (show reflectX x ∈ conf _ from Points.move_in _ hw)] at hg
  exact (show ∀ y z : C.book.Word, ∀ (hy : distinct y) (hz : distinct z), realize (L:=C.book) (fun i => ⟨p i,v i⟩) x=y →
    realize (L:=C.book) (fun i => ⟨p i,C.book.mirrorGroup (p i) mir (v i)⟩) (reflectX x)=z → M A y hy=M A z hz from
    fun _ _ _ _ h h' => by subst_vars; exact hg) _ _ _ _ h1 h2
end YM.Work.B05
