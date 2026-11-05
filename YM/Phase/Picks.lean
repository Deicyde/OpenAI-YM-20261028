import YM.Phase.Detect


/-!
# Finite rescaling ranks in phase. Interface TEST on SAME project. No uniformity at
arity assumed. Detect hypotheses are full reflected expectations, not densities alone.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extraction.Retain
open Function Set Filter MeasureTheory Measure
open Table Cells CellHyp OS Ground Wilson Word
open scoped Topology NNReal ENNReal InnerProductSpace BigOperators ContDiff
variable {G : Gauge} {C : Family G} {S D : Table C.book} {V : Chamber S timeAxis} {d : ℕ} {X : Columns C S d}
variable {f : Order} (Y : X.Trials) (Q : Y.Valid f) (P : Spread V) (a : P.Resolution) (H : Funds Y Q P)

/-- Row tests on TARGET; compare any phase's actual lifts via scalar values. -/
def probe' (k : ℕ) (i : Fin X.amount) : D.Field d →ₗ[ℂ] ℂ :=
    Ward.here (x := Y.realPlace k i) (q := Fin.cons ⟨d,(0:D.Field d)⟩
      (fun s => ⟨d,D.project _ (Y.later k ((X.row i).uses s))⟩)) 0 d

lemma at_row (k : ℕ) (i) (x) : probe' (D := D) Y k i x = D.useAt D (Y.realPlace k i)
    (Fin.cons ⟨d,x⟩ fun s => ⟨d,D.project _ (Y.later k ((X.row i).uses s))⟩) := by
  unfold probe'
  rw [Ward.takes]; unfold Ward.disc; congr 1
  funext j; refine Fin.cases ?_ (fun s => ?_) j <;> simp

private def plot (i : Fin X.amount) : (standard C).Field d→ₗ[ℂ] ℂ :=
   Ward.here (q := Fin.cons ⟨d,(0:(standard C).Field d)⟩ (fun s => ⟨d,X.basis ((X.row i).uses s)⟩)) (X.row i).expected 0 _
private lemma plott (i : Fin X.amount) (v) : plot i v=(X.row i).tests _ X.basis v := by
  unfold plot; rw [Ward.takes]; unfold SampleRow.tests Ward.disc; congr 1
  ext1 s; refine Fin.cases ?_ (fun j => ?_) s <;> simp

lemma ready (k i c) (hD : D.Symmetric) (hh : Y.realPlace k i ∈ conf _) :
    probe' Y k i (D.project d (Y.later k c))= D.read (Y.realPlace k i) (fun s => token Y k i c s) := by
  rw [at_row,← D.at_project D hD (fun _ => le_rfl) hh]; congr 1
  funext s; refine Fin.cases ?_ (fun u => ?_) s <;> simp [token, Columns.Trials.names, Table.classTokens]



def testFns (i : Fin X.amount) (c : Fin (X.dim+1)) : Fin ((X.row i).extra+1) → (standard C).Tag := fun s =>
    ⟨d,X.basis (Columns.Trials.names (X := X) i c s)⟩

include Q in
lemma limits (i c) : Tendsto (fun k => (standard C).useAt (standard C) (Y.tested k i) (testFns (X := X) i c)) atTop
    (𝓝 ((X.row i).tests (standard C) X.basis (X.basis c))) := by
  let B := (standard C)
  have hx : (X.row i).expected ∈ conf _ := generic_conf _ (X.row i).probes
  have hp := ((B.class_smooth B (Maxwell.table_smooth C.labels) (testFns (X := X) i c)).continuousOn.continuousAt
    ((conf_open _).mem_nhds hx)).tendsto.comp (Q.tuned i)
  unfold SampleRow.tests
  rw [show Fin.cons (α := fun _ => B.Tag) ⟨d,X.basis c⟩ (fun j => ⟨d,X.basis ((X.row i).uses j)⟩)=testFns (X := X) i c by
    ext1 j; refine Fin.cases ?_ (fun l => ?_) j <;> simp [testFns, Columns.Trials.names]]
  exact hp

private lemma fOne {L : Register G} {S : Table L} (x : E4) (p : S.Tag) : S.expect [(x,Ward.expose p)] =
    S.useAt S (points (fun _ : Fin 1 => x)) (fun _ => p) := by
  exact S.readAt (fun _ : Fin 1 => Ward.expose p) (points (fun _ => x)) -- defeq list?
private lemma fTwo {L : Register G} {S : Table L} (x y : E4) (a b : S.Tag) : S.expect [(x,Ward.expose a),(y,Ward.expose b)] =
    S.useAt S (points ![x,y]) ![a,b] := S.readAt (fun j => Ward.expose (![a,b] j)) (points ![x,y])
include H
lemma result (hq : a.Out) {v} (h : a.receives D v) (hD : D.Symmetric) (i c) : Tendsto
    (fun k => probe' Y k i (D.project d (Y.later k c))) atTop (𝓝 ((X.row i).tests (standard C) X.basis (X.basis c))) := by
  have hc k : Y.realPlace k i∈ conf _ := generic_conf _ (Q.generic k i)
  let F k := D.read (Y.realPlace k i) (fun s => token Y k i c s)
  let U k := (standard C).useAt (standard C) (Y.tested k i) (testFns (X := X) i c)
  have hp (k : ℕ) : F k= D.expect (List.ofFn fun s => plant Y k i c s) := (D.readAt _ _).symm
  suffices he : Tendsto (fun k => F k-U k) atTop (𝓝 0) by
    simp_rw [ready Y _ i c hD (hc _)] -- Q binder?
    convert (he.add (limits Y Q i c)) using 1
    · funext k; exact (sub_add_cancel (F k) (U k)).symm
    simp
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  -- at arity 1 can still use counts. padded extra slot.
  have hu : ∀ k, U k=(standard C).expect (List.ofFn fun j => (Y.tested k i j, Ward.expose (testFns (X := X) i c j))) :=
    fun k => ((standard C).readAt (fun j => Ward.expose (testFns (X := X) i c j)) (Y.tested k i)).symm
  rcases eq_or_ne (X.row i).extra 0 with he|he
  · apply squeeze_zero (fun _ => norm_nonneg _) _ Y.small
    intro k
    have v0 {R : Type} (f : Fin ((X.row i).extra+1) → R) : List.ofFn f=[f 0] := by
      rw [List.ofFn_succ]; congr; simp [he]
    have hh : U k=Y.singleton k i c 0 := by
      rw [hu,v0]; exact fOne (S := standard C) (Y.tested k i 0) (testFns (X := X) i c 0)
    change ‖F k-U k‖ ≤ _
    rw [hp,v0,hh]; exact one_near Y Q P a H hq h _ _ _ _
  have he : (X.row i).extra=1 := by have := (X.row i).cap; omega
  let b : Fin ((X.row i).extra) := ⟨0,by omega⟩
  let s := b.succ
  let j (p : Fin ((X.row i).extra+1)) (k : ℕ) := Y.singleton k i c p
  let g (k) := Y.gap k+(‖j 0 k‖+‖j s k‖)*Y.gap k
  have ht (p) : ∃ C : ℂ,Tendsto (j p) atTop (𝓝 C) := by
    let T (x : Points ((X.row i).extra+1)) := points fun _ : Fin 1 => x p
    have hv : Continuous T := by unfold T points; fun_prop
    let E := T (X.row i).expected
    have hm : E ∈ conf _ := fun _ _ _ => @Subsingleton.elim (Fin 1) _ _ _
    refine ⟨_,(((standard C).class_smooth (standard C) (Maxwell.table_smooth _) (fun _ : Fin 1 => testFns (X := X) i c p)).continuousOn.continuousAt
      ((conf_open _).mem_nhds hm)).tendsto.comp (hv.continuousAt.tendsto.comp (Q.tuned i))⟩
  have hg : Tendsto g atTop (𝓝 0) := by
    obtain ⟨B,hb⟩ := ht 0; obtain ⟨G,hG⟩ := ht s
    simpa only [mul_zero,add_zero] using Y.small.add (((hb.norm).add hG.norm).mul Y.small)
  refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hg
  have hv2 {R : Type} (f : Fin ((X.row i).extra+1) → R) : List.ofFn f=[f 0,f s] := by
    rw [List.ofFn_succ]; congr
    apply nice _ b he
  have hb : U k=free2 Y k i c 0 s := by
    unfold free2 Columns.Trials.cumulant; rw [sub_add_cancel, hu,hv2]; exact fTwo (S := standard C) (Y.tested k i 0) (Y.tested k i s) _ _
  change ‖F k-U k‖ ≤ _; rw [hp,hv2,hb]; exact pair_near Y Q P a H hq h _ _ _ 0 s (by exact Fin.succ_pos b)
where nice {R : Type} {n : ℕ} (f : Fin (n+1) → R) (b : Fin n) (h : n=1) : List.ofFn (fun i => f i.succ)=[f b.succ] := by subst n; fin_cases b; rfl

omit H in
private theorem converge {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {i : Type*} [Fintype i]
    (H : Module.Basis i ℂ V) (f : ℕ → V →L[ℂ] E) (F : V →L[ℂ] E) (h : ∀ i,Tendsto (fun k => f k (H i)) atTop (𝓝 (F (H i)))) :
    Tendsto f atTop (𝓝 F) := by
  let L : (i→E) →ₗ[ℂ] V →L[ℂ] E := {
    toFun p := LinearMap.toContinuousLinearMap (H.constr ℂ p)
    map_add' p q := by change LinearMap.toContinuousLinearMap (H.constr ℂ (p+q))=_; rw [map_add (H.constr ..), map_add]
    map_smul' c p := by change LinearMap.toContinuousLinearMap (H.constr ℂ (c • p))=_; rw [map_smul (H.constr ..), map_smul];rfl }
  have he (g : V →L[ℂ] E) : L (fun i => g (H i))=g := by
    apply ContinuousLinearMap.coe_injective
    exact H.ext (fun i => H.constr_basis ..)
  have hL := L.continuous_of_finiteDimensional.continuousAt.tendsto.comp
    (tendsto_pi_nhds.mpr (show ∀ b, Tendsto ((fun x : i→E => x b) ∘ fun k i => f k (H i)) atTop (𝓝 (F (H b))) from h)) -- likely notation
  convert hL using 1
  · funext v; exact (he _).symm
  · rw [he]

theorem lift_detect (hi : a.Out) {v} (h : a.receives D v) (hD : D.Symmetric) (hp : D.respects S) : D.null d=S.null d := by
  let U k := X.basis.constr ℂ fun i => Y.later k i
  have he k : S.project d ∘ₗ U k= X.basis.constr ℂ fun i => S.project _ (Y.later k i) := X.basis.ext fun i => by simp [U]
  let f (k : ℕ) : (standard C).Field d→L[ℂ] (Fin X.amount → ℂ) := LinearMap.toContinuousLinearMap
    ((LinearMap.pi (probe' (D := D) Y k)).comp ((D.project d).comp (U k)))
  let F : (standard C).Field d →L[ℂ] (Fin X.amount→ℂ) := LinearMap.toContinuousLinearMap (LinearMap.pi (plot (X := X)))
  have hg k i j : f k (X.basis i) j=probe' Y k j (D.project d (Y.later k i)) := by simp [f,U]
  have hh i : Tendsto (fun n => f n (X.basis i)) atTop (𝓝 (F (X.basis i))) := by
    refine tendsto_pi_nhds.mpr fun j => ?_
    simp_rw [hg, show F (X.basis i) j=_ from plott j (X.basis i)]
    exact result Y Q P a H hi h hD j i
  have hx : Injective F := fun q p h => X.full (show _ from by
    change (fun i => (X.row i).tests _ _ q)=fun i => (X.row i).tests _ _ p; simp_rw [← plott]; exact h)
  obtain ⟨k,hk,Hk⟩ := (((converge X.basis _ _ hh).eventually (ContinuousLinearMap.isOpen_injective
      |>.mem_nhds hx)).and Q.span).exists
  change Injective (f k) at hk
  suffices hv : Surjective (S.project d ∘ₗ U k) by
    refine le_antisymm (fun i H' => ?_) (hp d)
    obtain ⟨w,hw⟩ := hv (S.project _ i)
    have ht : U k w - i ∈ D.null d := hp _ ((Submodule.Quotient.mk_eq_zero _).1 (show S.project d _=0 from
      by rw [map_sub]; exact sub_eq_zero.mpr hw))
    have he := (D.null d).add_mem ht H'
    rw [sub_add_cancel] at he
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change S.project d _=_
    rw [← hw]; suffices w=0 by rw [this,map_zero]
    apply hk; rw [map_zero]
    change (LinearMap.pi (probe' Y k)) (D.project d (U k w))=0
    rw [show D.project d (U k w)=0 from (Submodule.Quotient.mk_eq_zero _).mpr he,map_zero]
  apply LinearMap.range_eq_top.mp; rw [eq_top_iff,← Hk,Submodule.span_le]; rintro _ ⟨i,rfl⟩
  exact ⟨X.basis i,by simp [U]⟩
end YM.Extraction.Retain
