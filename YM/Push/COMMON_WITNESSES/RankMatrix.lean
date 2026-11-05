import YM.Next.EXTRACTION.Coordinates
import YM.Next.FOUNDATIONS.SU2
import YM.Push.COMMON_WITNESSES.RowEstimates

/-!
# Rank consequence on the *same* assembly, through RCorrected

One cannot ask for a span before processing the rank hypothesis and inner
then outer extraction. Here is a passage from the actual finite rank bills.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Common
open Function Filter Set Extraction Cells Table Next.Extract
open scoped Topology BigOperators ContDiff

variable {G : Gauge} {C : Family G} {d : ℕ} {T : Table C.book}
variable {X : Columns C T d} (Y : X.Trials)

/-- Row entries. Uses the exact bin's Fields whenever testing the
unselected table. For the phase table, `Materializes` (later) supplies the
iso; D.Entry here even works with native representatives of D. -/
def entry (D : Table C.book) (k : ℕ) (i : Fin X.amount) (c : Fin (X.dim+1)) : ℂ :=
   Retain.probe' Y k i (D.project d (Y.later k c))

def sumCoord (D : Table C.book) (k : ℕ) : (standard C).Field d →ₗ[ℂ] D.Field d :=
    X.basis.constr ℂ fun i => D.project d (Y.later k i)

lemma sc_basis (D : Table C.book) (k i) : sumCoord Y D k (X.basis i) = D.project d (Y.later k i) :=
    X.basis.constr_basis ..

def loomMap (D : Table C.book) (k : ℕ) : (standard C).Field d →L[ℂ] (Fin X.amount → ℂ) :=
    LinearMap.toContinuousLinearMap ((LinearMap.pi (Retain.probe' (D:=D) Y k)).comp (sumCoord Y D k))

def idealMap (X : Columns C T d) : (standard C).Field d →L[ℂ] (Fin X.amount → ℂ) :=
    LinearMap.toContinuousLinearMap (LinearMap.pi fun i : Fin X.amount =>
      Ward.here (q := Fin.cons ⟨d,(0:(standard C).Field d)⟩ (fun s => ⟨d,X.basis ((X.row i).uses s)⟩)) (X.row i).expected 0 _)

lemma idealRow (A : (standard C).Field d) (i : Fin X.amount) : idealMap X A i=(X.row i).tests (standard C) X.basis A := by
  change Ward.here _ (X.row i).expected 0 d A = _
  rw [Ward.takes]; unfold SampleRow.tests Ward.disc; congr 1
  funext j; refine Fin.cases ?_ (fun t => ?_) j <;> simp

lemma loomRow (D : Table C.book) (k i c) : loomMap Y D k (X.basis c) i = entry Y D k i c := by
  change Retain.probe' (D:=D) Y k i (sumCoord Y D k (X.basis c)) = _
  simp only [sc_basis, entry]

private lemma freeOne (x : E4) (p : (standard C).Tag) : (standard C).expect [(x,Ward.expose p)] =
    (standard C).useAt (standard C) (points (fun _ : Fin 1 => x)) (fun _ => p) :=
  (standard C).readAt (fun _ : Fin 1 => Ward.expose p) (points (fun _ => x))

private lemma freeTwo (x y : E4) (p q : (standard C).Tag) : (standard C).expect [(x,Ward.expose p),(y,Ward.expose q)] =
    (standard C).useAt (standard C) (points ![x,y]) ![p,q] :=
  (standard C).readAt (fun j => Ward.expose (![p,q] j)) (points ![x,y])

/-- Continuum entry errors uniform for all tables receiving the Prices (in
particular the same proof works simultaneously in arbitrary phase characters
later, no phasewise extraction). -/
lemma entry_bounds (H : Setup Y) (i c) : ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ (∀ k, 0 ≤ e k) ∧
    ∀ (D : Table C.book), D.Symmetric → Prices Y D → ∀ k,
      ‖loomMap Y D k (X.basis c) i - idealMap X (X.basis c) i‖ ≤ e k := by
  let B := standard C
  let U (k : ℕ) := B.useAt B (Y.tested k i) (Retain.testFns (X:=X) i c)
  have hu (k) : U k=B.expect (List.ofFn fun j => (Y.tested k i j, Ward.expose (Retain.testFns (X:=X) i c j))) :=
    ((standard C).readAt (fun j => Ward.expose (Retain.testFns (X := X) i c j)) (Y.tested k i)).symm
  let w := idealMap X (X.basis c) i
  have hv : Tendsto U atTop (𝓝 w) := by
    have hx : (X.row i).expected ∈ conf _ := generic_conf _ (X.row i).probes
    have hp := ((B.class_smooth B (Maxwell.table_smooth C.labels) (Retain.testFns (X := X) i c)).continuousOn.continuousAt
      ((conf_open _).mem_nhds hx)).tendsto.comp (H.tuned i)
    unfold w; rw [idealRow]
    unfold SampleRow.tests
    rw [show Fin.cons (α := fun _ => B.Tag) ⟨d,X.basis c⟩ (fun j => ⟨d,X.basis ((X.row i).uses j)⟩)=Retain.testFns (X := X) i c by
      ext1 j; refine Fin.cases ?_ (fun l => ?_) j <;> simp [Retain.testFns, Columns.Trials.names]]
    exact hp
  let b0 (k : ℕ) := ‖U k-w‖
  suffices he : ∃ g : ℕ → ℝ, Tendsto g atTop (𝓝 0) ∧ (∀ k, 0 ≤ g k) ∧
      ∀ D : Table C.book, Prices Y D → ∀ k : ℕ,
        ‖D.expect (List.ofFn fun s => Retain.plant Y k i c s)-U k‖ ≤ g k by
    obtain ⟨g,hg,hp,hq⟩ := he
    have hz : Tendsto b0 atTop (𝓝 0) := by simpa only [sub_self,norm_zero] using (hv.sub_const w).norm
    refine ⟨fun i => g i+b0 i,by simpa only [add_zero] using hg.add hz,fun i => add_nonneg (hp i) (norm_nonneg _),
      fun D hD h k => ?_⟩
    have he : loomMap Y D k (X.basis c) i = D.expect (List.ofFn fun s => Retain.plant Y k i c s) := by
      rw [loomRow,entry,Retain.ready Y k i c hD (generic_conf _ (H.generic k i))]; exact (D.readAt _ _).symm
    change ‖loomMap Y D k _ i-w‖ ≤ _
    rw [he]
    exact (norm_sub_le_norm_sub_add_norm_sub _ (U k) _).trans (add_le_add_left (hq D h k) _)
  rcases eq_or_ne (X.row i).extra 0 with hf|hf
  · refine ⟨Y.gap,Y.small,Y.allowed,fun D h k => ?_⟩
    have v0 {R : Type} (f : Fin ((X.row i).extra+1) → R) : List.ofFn f=[f 0] := by
      rw [List.ofFn_succ]; congr; simp [hf]
    have hc : U k = Y.singleton k i c 0 := by
      rw [hu,v0]; exact freeOne _ (Retain.testFns (X := X) i c 0)
    rw [v0,hc]; apply h.one
  have hf : (X.row i).extra=1 := by have := (X.row i).cap; omega
  let b : Fin ((X.row i).extra) := ⟨0,by omega⟩
  let s := b.succ
  let j (p : Fin ((X.row i).extra+1)) (k : ℕ) := Y.singleton k i c p
  let g (k) := Y.gap k+(‖j 0 k‖+‖j s k‖)*Y.gap k
  have ht (p) : ∃ C : ℂ,Tendsto (j p) atTop (𝓝 C) := by
    let L (x : Points ((X.row i).extra+1)) := points fun _ : Fin 1 => x p
    have hw : Continuous L := by unfold L points; fun_prop
    let E := L (X.row i).expected
    have hm : E ∈ conf _ := fun _ _ _ => @Subsingleton.elim (Fin 1) _ _ _
    refine ⟨_,(((standard C).class_smooth (standard C) (Maxwell.table_smooth _) (fun _ : Fin 1 => Retain.testFns (X := X) i c p)).continuousOn.continuousAt
      ((conf_open _).mem_nhds hm)).tendsto.comp (hw.continuousAt.tendsto.comp (H.tuned i))⟩
  have hg : Tendsto g atTop (𝓝 0) := by
    obtain ⟨B,hb⟩ := ht 0; obtain ⟨G,hG⟩ := ht s
    simpa only [mul_zero,add_zero] using Y.small.add (((hb.norm).add hG.norm).mul Y.small)
  refine ⟨g,hg,fun i => add_nonneg (Y.allowed i) (mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (Y.allowed i)),?_⟩
  intro D h k
  have hv2 {R : Type} (f : Fin ((X.row i).extra+1) → R) : List.ofFn f=[f 0,f s] := by
    rw [List.ofFn_succ]; congr
    apply onlyRow _ b hf
  have hb : U k=Retain.free2 Y k i c 0 s := by
    unfold Retain.free2 Columns.Trials.cumulant; rw [sub_add_cancel, hu,hv2]; exact freeTwo _ _ (Retain.testFns (X := X) i c 0) (Retain.testFns (X := X) i c s)
  rw [hv2,hb]; exact h.pair _ _ _ _ _ (Fin.succ_pos b)
where onlyRow {R : Type} {n : ℕ} (f : Fin (n+1) → R) (b : Fin n) (h : n=1) : List.ofFn (fun i => f i.succ)=[f b.succ] := by subst n; fin_cases b; rfl

/-- Pointwise in vectors of a given finite basis suffices, no uniformity
in the query for the hypothesis. Works for scheduled indices as well. -/
lemma matrix_convergence {α E B i : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup B] [NormedSpace ℂ B] [FiniteDimensional ℂ B] [Fintype i] (b : Module.Basis i ℂ E)
    (F : E →L[ℂ] B) (A : α → E →L[ℂ] B) (l : Filter α) (H : ∀ i,Tendsto (fun k => A k (b i)) l (𝓝 (F (b i)))) :
    Tendsto A l (𝓝 F) := by
  let M : (i→B) →ₗ[ℂ] E →L[ℂ] B := {
    toFun p := LinearMap.toContinuousLinearMap (b.constr ℂ p)
    map_add' p q := by change LinearMap.toContinuousLinearMap (b.constr ℂ (p+q))=_; rw [map_add (b.constr ..), map_add]
    map_smul' c p := by change LinearMap.toContinuousLinearMap (b.constr ℂ (c • p))=_; rw [map_smul (b.constr ..), map_smul];rfl }
  have he (g : E →L[ℂ] B) : M (fun i => g (b i))=g := ContinuousLinearMap.coe_injective (b.ext (fun _ => b.constr_basis ..))
  have hL := M.continuous_of_finiteDimensional.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr H)
  convert hL using 1
  · funext v; exact (he _).symm
  · rw [he]

lemma assembled_limit (H : Setup Y) {α : Type*} {l : Filter α} (k : α → ℕ) (h : Tendsto k l atTop)
    (D : α → Table C.book) (hp : ∀ i, (D i).Symmetric) (he : ∀ i, Prices Y (D i)) :
    Tendsto (fun i => loomMap Y (D i) (k i)) l (𝓝 (idealMap X)) := by
  apply matrix_convergence X.basis
  intro c
  refine tendsto_pi_nhds.mpr fun i => ?_
  obtain ⟨e,hg,_,hw⟩ := entry_bounds Y H i c
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(hg.comp h).eventually (gt_mem_nhds hε)] with j hj
  rw [dist_eq_norm]; exact lt_of_le_of_lt (hw _ (hp j) (he j) _) hj

lemma ideal_inj (X : Columns C T d) : Injective (idealMap X) := by
  intro p q hp
  apply X.full; funext i; dsimp only; rw [← idealRow,← idealRow,hp]

lemma directions (H : Setup Y) (D : Table C.book) (hD : D.Symmetric) (hp : Prices Y D) :
    ∀ᶠ k in atTop, Injective (sumCoord Y D k) := by
  have he := (assembled_limit Y H _ (tendsto_id (x:=atTop)) _ (fun _ => hD) fun _ => hp).eventually
    (ContinuousLinearMap.isOpen_injective.mem_nhds (ideal_inj X))
  filter_upwards [he] with k hk
  have hx : Injective (loomMap Y D k) := hk
  exact fun a b hab => hx (congr_arg (LinearMap.pi (Retain.probe' (D:=D) Y k)) hab)

/-- Rank from the common B presentation, **not** inferred from an
independently assembled table. Both directions for the SizeBill to check
compatibility of a producer port. -/
lemma size_pay {b : Presentation C} {S : Table C.book} {f : Order} {R : Dash.Bin S} {z} (h : Projected b f R z)
    {M V} (H : Base C f S M R T V) (X : Columns C T d) : SizeBill b f X ↔ Module.finrank ℂ (T.Field d) ≤ X.dim+1 := by
  let p := fun u : CoordMap C d => Module.finrank ℂ (LinearMap.range u.toLinearMap)
  have hc := Submodule.finrank_quotient_add_finrank (T.null d)
  change Module.finrank ℂ (T.Field d) + _ = _ at hc
  have hx : Module.finrank ℂ (T.Field d) = p (R d).trueP := by
    have hw := H.null d
    have he : Module.finrank ℂ (T.null d) = Module.finrank ℂ (LinearMap.ker (R d).trueP.toLinearMap) := by rw [hw]
    rw [he] at hc; exact Nat.add_right_cancel (hc.trans (LinearMap.finrank_range_add_finrank_ker (R d).trueP.toLinearMap).symm)
  have he : ∀ᶠ u : ℕ × ℕ in f.fuse, p (b.step d u) = p (R d).trueP := by
    have hyp (x y : CoordMap C d) (h : Module.finrank ℂ (LinearMap.ker x.toLinearMap) = Module.finrank ℂ (LinearMap.ker y.toLinearMap)) :
      p x = p y := by
      dsimp [p]; have hx := LinearMap.finrank_range_add_finrank_ker x.toLinearMap
      have hy := LinearMap.finrank_range_add_finrank_ker y.toLinearMap; omega
    obtain ⟨hb,hc⟩ := h.ranks d
    rw [f.fused]; unfold Order.late
    filter_upwards [hc] with i hi
    filter_upwards [hb (f.per i)] with l hl
    exact hyp _ _ (hl.trans hi)
  have hw : SizeBill b f X ↔ ∀ᶠ u : ℕ × ℕ in f.fuse, p (b.step d u) ≤ X.dim+1 := (Order.fused f (fun u => p (b.step d u) ≤ X.dim+1)).symm
  rw [hw,hx]
  constructor
  · intro h; obtain ⟨u,hu,hv⟩ := (he.and h).exists; rwa [hu] at hv
  intro ht; exact he.mono fun i hi => hi ▸ ht

/-- Span without an additional limit premise. The rank payment for d and the
finite root estimates suffice, after BOTH-stage extraction of comparison
coordinates. -/
theorem spans (hY : Setup Y) (H : T.Symmetric) (hp : Prices Y T) (h : Module.finrank ℂ (T.Field d) ≤ X.dim+1) :
    Module.finrank ℂ (T.Field d) = X.dim+1 ∧ ∀ᶠ k in atTop,
        Submodule.span ℂ (Set.range fun i => T.project d (Y.later k i)) = ⊤ := by
  have hi := directions Y hY T H hp
  have hn : Module.finrank ℂ ((standard C).Field d) = X.dim+1 := by
    rw [Module.finrank_eq_card_basis X.basis,Fintype.card_fin]
  have ht : Module.finrank ℂ (T.Field d) = X.dim+1 := by
    obtain ⟨k,hk⟩ := hi.exists
    have hh := LinearMap.finrank_le_finrank_of_injective hk; omega
  refine ⟨ht,?_⟩
  filter_upwards [hi] with k hk
  have he : Surjective (sumCoord Y T k) := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hn.trans ht.symm)).1 hk
  have hv := LinearMap.range_eq_top.mpr he
  rw [LinearMap.range_eq_map,← X.basis.span_eq, Submodule.map_span, ← Set.range_comp] at hv
  rw [show sumCoord Y T k ∘ X.basis = fun i => T.project d (Y.later k i) from funext (sc_basis Y T k)] at hv
  exact hv
end YM.Push.Common
