import YM.Bid.Grow

/-!
# Word insertion into joint tempered distributions
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.C29
open Function Boundary
open scoped BigOperators

variable {G : Gauge} {L : Register G} {S : Table L} {n : ℕ}

private lemma eval_update [DecidableEq (Fin n)] (v : Fin n → Test4) (i : Fin n)
    (f : Test4) (p : Points n) :
    (fun j => update v i f j (p j)) = update (fun j => v j (p j)) i (f (p i)) := by
  funext j
  by_cases h : j = i <;> simp [h]

/-- The product test as an algebraic multilinear map into **joint** tests. -/
def materialLinear (n : ℕ) : MultilinearMap ℂ (fun _ : Fin n => Test4) (Joint n) where
  toFun := Joint.materialize n
  map_update_add' v i f g := by
    ext1 p
    simp only [Joint.material_at, add_apply, eval_update v]
    exact (MultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).map_update_add (fun j => v j (p j)) i _ _
  map_update_smul' v i c f := by
    ext1 p
    simp only [Joint.material_at, smul_apply, eval_update v]
    exact (MultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).map_update_smul (fun j => v j (p j)) i _ _

variable (W : Surface S)

lemma expectCast (v : Fin n → Letter S) {b : Sentence S} (h : n = b.length)
    (e : ∀ i, b.get (Fin.cast h i) = v i) :
    W.expect b = W.W n (Prod.fst ∘ v) (Joint.materialize n (Prod.snd ∘ v)) := by
  subst n
  have : b.get = v := funext e
  simp only [Surface.expect, this, Function.comp_def]

lemma expectOfFn (v : Fin n → Letter S) :
    W.expect (List.ofFn v) = W.W n (Prod.fst ∘ v) (Joint.materialize n (Prod.snd ∘ v)) :=
  expectCast W v (by simp) (by simp)

/-- At one slot of a fixed-arity word insert both a label and a test. -/
lemma mixedSlot (v : Fin n → Letter S) (i : Fin n) :
    ∃ U : S.Union →ₗ[ℂ] Test4 →ₗ[ℂ] ℂ, ∀ x f,
      W.expect (List.ofFn (update v i (x,f))) = U x f := by
  let A := (W.W n).toLinearMap (Prod.fst ∘ v) i
  let B := (materialLinear n).toLinearMap (Prod.snd ∘ v) i
  let U : S.Union →ₗ[ℂ] Test4 →ₗ[ℂ] ℂ :=
    { toFun := fun x => (A x).toLinearMap.comp B
      map_add' := by intro x y; ext f; exact DFunLike.congr_fun (A.map_add x y) _
      map_smul' := by intro c x; ext f; exact DFunLike.congr_fun (A.map_smul c x) _ }
  refine ⟨U,fun x f => ?_⟩
  rw [expectOfFn, Function.comp_update, Function.comp_update]; rfl

private lemma insertSlot {m n : ℕ} {α : Type*} (v : Fin m → α) (w : Fin n → α) (x y : α) :
    update (Fin.append v (Fin.cons x w)) (Fin.natAdd m 0) y = Fin.append v (Fin.cons y w) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · have h : Fin.castAdd (n+1) i ≠ Fin.natAdd m 0 := by
      apply Fin.ne_of_lt
      exact (show i.val < m + 0 by simp)
    simp [h]
  induction j using Fin.cases with
  | zero => simp
  | succ j => simp [Fin.natAdd_inj]

lemma symbol : W.Symbol := by
  intro a b
  obtain ⟨U,hU⟩ := mixedSlot W (Fin.append a.get (Fin.cons (0,0) b.get)) (Fin.natAdd a.length 0)
  exact ⟨U,fun x f => by simpa only [insertSlot, List.ofFn_fin_append, List.ofFn_cons, List.ofFn_get] using hU x f⟩

/-- Continuous smearings slot by slot, with all label components constant. -/
lemma continuousExpect {T : Type*} [TopologicalSpace T] (v : T → Fin n → Letter S)
    (x : Fin n → S.Union) (he : ∀ p i, (v p i).1 = x i) (hc : ∀ i, Continuous fun p => (v p i).2) :
    Continuous (fun p => W.expect (List.ofFn (v p))) := by
  have h := (W.W n x).continuous.comp ((Joint.jointCont n).comp (continuous_pi hc))
  refine h.congr fun p => ?_
  rw [expectOfFn, show Prod.fst ∘ v p = x from funext (he p)]
  rfl

lemma cam (J : StarOp S) : W.Cam J := by
  intro a b x y
  let r := Sentence.rev J a
  let v (p : Test4 × Test4) : Fin (r.length + ((b.length+1)+1)) → Letter S :=
    Fin.append r.get (Fin.cons (J x, Probe.bar p.1) (Fin.cons (y,p.2) b.get))
  have he (p : Test4 × Test4) : W.kernel J ((x,p.1)::a) ((y,p.2)::b) = W.expect (List.ofFn (v p)) := by
    simp only [v, List.ofFn_fin_append, List.ofFn_cons, List.ofFn_get]
    simp [Surface.kernel, Sentence.rev, r, Letter.op]
  simp_rw [he]
  apply continuousExpect W v (Prod.fst ∘ v (0,0))
  · intro p i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp [v]
    induction j using Fin.cases with
    | zero => simp [v]
    | succ j => induction j using Fin.cases <;> simp [v]
  intro i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simpa [v] using (continuous_const (X := Test4 × Test4) (y := (r.get i).2))
  induction j using Fin.cases with
  | zero => simpa [v, Function.comp_def] using (Probe.bar (V := E4)).continuous.comp (continuous_fst (Y := Test4))
  | succ j =>
    induction j using Fin.cases with
    | zero => simpa [v] using (continuous_snd (X := Test4) (Y := Test4))
    | succ i => simpa [v] using (continuous_const (X := Test4 × Test4) (y := (b.get i).2))

theorem answer : YM.Bid.C29 := fun _ W J => ⟨symbol W, cam W J⟩

end YM.Work.C29
