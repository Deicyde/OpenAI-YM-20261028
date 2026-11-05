import YM.Fields.Stems

/-!
# Action constructor from W motion, on starter of fixed Soil
-/
set_option autoImplicit false
noncomputable section
namespace YM.Boundary
open Function Set Filter Complex Analysis Kernel Mink MeasureTheory Distribution Probe
open scoped Topology BigOperators InnerProductSpace ComplexOrder ComplexConjugate
variable {G : Gauge} {L : Register G} {S : Table L}

namespace Spins
variable (X : Spins S)
def po (p : Poincare) (x : Sentence S) := x.map (Letter.read X p)
lemma post {R h} (hx : X.Descends R h) (p q x) : X.po (p*q) x=X.po p (X.po q x) := by
  unfold po; rw [List.map_map]; exact congr_arg (fun g => x.map g) (funext fun j => Letter.travels X hx ..)
lemma initial {R h} (hx : X.Descends R h) (x) : X.po 1 x=x := by
  simp only [po,show Letter.read X 1=id from funext fun i => Letter.stays_read X i hx] -- fix
  simp
end Spins
namespace Surface
def Transforms (W : Surface S) (J : StarOp S) (X : Spins S) :=
    ∀ i j p, W.kernel J (X.po p i) (X.po p j) = W.kernel J i j

def Strong (W : Surface S) (J : StarOp S) (X : Spins S) := ∀ i j,
    Continuous fun p => W.kernel J i (X.po p j)
end Surface
namespace Soil
variable {W : Surface S} {J : StarOp S} (Z : Soil W J)
lemma universal_embed {M : Hilbert} (q : Sentence S → M) (h : ∀ x y, inner ℂ (q x) (q y)=W.kernel J x y) :
    ∃ U : Z.H→L[ℂ] M, ‖U‖≤1 ∧ (∀ i,U (Z.plant i)=q i) ∧ ∀ v : Z.H,
    ‖U v‖=‖v‖ := by
  let F := Finsupp.linearCombination ℂ q
  have he (x y : Scroll S) : inner ℂ (F x) (F y)=inner ℂ (Z.stems x) (Z.stems y) := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add p v hP hQ => simp only [map_add,inner_add_left,hP,hQ]
    | single i a =>
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add p v hP hQ => simp only [map_add,inner_add_right,hP,hQ]
      | single j b => simp only [F,Gram.stems,Finsupp.linearCombination_single, inner_smul_left,inner_smul_right,Z.measure,h]
  have hp x : ‖F x‖=‖Z.stems x‖ := by
    nth_rw 1 [@norm_eq_sqrt_re_inner ℂ]; rw [he, ← @norm_eq_sqrt_re_inner ℂ]
  obtain ⟨U,hU,H⟩ := Z.by_bound q 1 zero_le_one (fun u => by rw [one_mul]; exact (hp u).le)
  have ht u : U (Z.stems u)=F u := by
    induction u using Finsupp.induction_linear with
    | zero => simp
    | add i j hi hj => simp only [map_add,hi,hj]
    | single i a => simp [F,Gram.stems,H]
  exact ⟨U,hU,H,fun i => congr_fun
    (Z.whole.equalizer U.continuous.norm continuous_norm (funext fun j => (congr_arg _ <| ht j).trans (hp j))) i⟩

lemma strong_life (Y : Poincare → Z.H.Op) (h : ∀ p,∀ v : Z.H, ‖Y p v‖=‖v‖) (hp : ∀ i,Continuous fun p => Y p (Z.plant i)) :
    ∀ v : Z.H,Continuous fun p => Y p v := by
  have he (i : Scroll S) : Continuous fun p => Y p (Z.stems i) := by
    induction i using Finsupp.induction_linear with
    | zero => simp; exact continuous_const
    | add i j hi hj => simp_rw [map_add]; exact hi.add hj
    | single i b => simp_rw [Kernel.Gram.stems,Finsupp.linearCombination_single,map_smul]; exact continuous_const.smul (hp i)
  intro v; apply continuous_iff_continuousAt.mpr; intro p
  apply Metric.tendsto_nhds.mpr; intro ε hε
  obtain ⟨_,⟨i,rfl⟩,hi⟩ := Metric.mem_closure_iff.mp (Z.whole v) (ε/3) (by positivity)
  filter_upwards [Metric.tendsto_nhds.mp (he i|>.tendsto p) (ε/3) (by positivity)] with u hu
  have hU k : dist (Y k v) (Y k (Z.stems i))=dist v (Z.stems i) := by rw [dist_eq_norm,dist_eq_norm, ← map_sub,h]
  apply lt_of_le_of_lt (dist_triangle _ (Y u (Z.stems i)) _)
  have ht := dist_triangle (Y u (Z.stems i)) (Y p (Z.stems i)) (Y p v)
  rw [dist_comm (Y p (Z.stems i)) (Y p v),hU] at ht
  rw [hU]; linarith

lemma mobilize (X : Spins S) {R h} (hr : X.Descends R h) (hp : W.Transforms J X) (hh : W.Strong J X) :
    ∃ Y : Action Z.H,∀ i p,Y.V p (Z.plant i)=Z.plant (X.po p i) := by
  choose U hU HT HS using fun p => Z.universal_embed (M:=Z.H) (Z.plant ∘ X.po p)
    (fun i j => (Z.measure (X.po p i) (X.po p j)).trans (hp i j p))
  have he p i : U p (Z.plant i)=Z.plant (X.po p i) := HT p i
  let B : Action Z.H :=
    { V := U
      one := Z.by_bud fun i => by rw [he,X.initial hr]; rfl
      mult := fun p q => Z.by_bud fun i => by rw [ContinuousLinearMap.comp_apply,he,he,he,X.post hr]
      usual := HS
      strong := strong_life Z U HS fun i => by
        simp_rw [he]
        apply continuous_iff_continuousAt.mpr; intro p; apply OS.ketC
        · simp_rw [Z.measure]; unfold Surface.Transforms at hp; simp_rw [hp]; exact continuousAt_const
        simp_rw [Z.measure]; exact (hh _ i).continuousAt }
  exact ⟨B,fun i p => HT p i⟩

lemma cultivates (X : Spins S) (U : Action Z.H) (h : ∀ i p,U.V p (Z.plant i)=Z.plant (X.po p i)) (he : W.Symbol) :
    Symmetries (F:=Z.starter he) X U := by
  have hc (p : Poincare) (i f) (hf : Z.stems i=f) : U.V p f∈Z.land := by
    subst f
    induction i using Finsupp.induction_linear with
    | zero => rw [map_zero,map_zero]; exact Z.land.zero_mem
    | add i j hi hj => rw [map_add,map_add]; exact Z.land.add_mem hi hj
    | single i z => simp_rw [Gram.stems,Finsupp.linearCombination_single,map_smul,h]; exact Z.land.smul_mem _ (Z.seed _).property
  let hV (p : Poincare) : MapsTo (U.V p) (Z.land : Set Z.H) Z.land := fun v ⟨i,hi⟩ => hc p i v hi
  refine ⟨hV,fun p => h [] p,?_⟩
  intro p x f a
  let g : Z.land→ₗ[ℂ] Z.land := (U.V p).toLinearMap.restrict (p:=Z.land) (q:=Z.land) (hV p)
  have ht i : g (Z.seed i)=Z.seed (X.po p i) := Subtype.ext (h i p)
  have hp : g.comp (Z.beginsOp (x,f))=(Z.beginsOp (X.rail p.Λ x,Joint.push p f)).comp g := by
    apply Z.buds; intro i
    rw [LinearMap.comp_apply,LinearMap.comp_apply,Z.actual, ht,ht, Z.actual]; rfl
  exact congr_arg Subtype.val (LinearMap.congr_fun hp a)
end Soil
end YM.Boundary
