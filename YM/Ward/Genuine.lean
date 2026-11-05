import YM.Ward.Sum

/-!
# Singleton-singleton row. `arc` coordinate sign d(t,j)=Ω x.
Pair responder and analytic positive radial kernel.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Ward
open Function Set Filter Complex Analysis Table OS Word
open scoped Topology NNReal ENNReal InnerProductSpace BigOperators ContDiff
variable {G : Gauge} {L : Register G} {S : Table L} {a b : Axis}

/-- point order important: upper FIRST, second origin -/
def pair (A B : S.Tag) (x : E4) : ℂ := disc ![A,B] (points ![x,0])
def toPair (x y : L.Plant) := [x,y]

lemma scan (H : S.Hierarchy) (u v : L.Plant) (ho : u.1 ≠ v.1) : S.expect (toPair u v) = pair
    (S.classTokens u.2) (S.classTokens v.2) (u.1-v.1) := by
  rw [← invariance H.translations (show distinct (toPair u v) from locations.mpr (by simp [toPair,ho])) (-v.1)]
  change S.expect [(u.1+-v.1,u.2),(v.1+-v.1,v.2)]=_
  rw [add_neg_cancel,← sub_eq_add_neg,exact_table (show distinct _ from locations.mpr (by simp [ho,sub_eq_zero])) H]
  unfold pair disc; congr 1
  · apply PiLp.ext; intro i; fin_cases i <;> rfl
  funext i; fin_cases i <;> rfl

lemma mirror_ne (v w : E4) (a : Axis) (hv : 0<v a) (hw : 0<w a) : w≠Ortho.move (Signed.reflect a) v := by
  intro he; have hh := congr_arg (fun x : E4 => x a) he
  simp [Signed.mirrored] at hh; linarith

def refl (B : S.Tag) (a : Axis) : S.Tag := S.classTokens (L.reflectedToken a (expose B))

lemma swing (V : Chamber S a) (h : S.Hierarchy) (B A : S.Tag) (v w : E4) (hv : 0<v a) (hw : 0<w a) :
    inner ℂ (spot V B v) (spot V A w) = pair A (refl B a) (w-Ortho.move (Signed.reflect a) v) := by
  rw [warm V B hv,warm V A hw,V.GNS.measure]
  unfold Table.gram; rw [reflectedPoint]
  change S.expect [(Ortho.move (Signed.reflect a) v,L.reflectedToken a _),(w,expose A)]=_
  have he := mirror_ne v w a hv hw
  have hh : distinct (L := L) [(w,expose A),(Ortho.move (Signed.reflect a) v,L.reflectedToken a (expose B))] := locations.mpr (by simp [he])
  rw [Table.order S h.laws.toSymmetric hh (List.Perm.swap ..)]
  change S.expect (toPair _ _) = _
  rw [scan h _ _ he]
  simp [refl]

lemma reflect_twice (hp : S.Hierarchy) (p : S.Tag) (a : Axis) : refl (refl p a) a=p := by
  -- adjoint involution before rotation, coherence
  have he (p : S.Tag) : refl p a = ⟨p.1, S.adj hp.spin p.1 a p.2⟩ := by
    unfold refl Register.reflectedToken classTokens expose; congr 1
    simp only
    -- rw rep
    rw [← S.adj_project, S.rep]
  rw [he,he]; simp only; rw [S.reflect_twice]

theorem radial (V : Chamber S a) (hp : S.Hierarchy) (A B : S.Tag) (t : ℝ) (ht : 0<t) :
    AnalyticAt ℝ (fun i => pair A B (i • basis a)) t := by
  let k := t/2
  have hk : 0<k := by unfold k; positivity
  let v := k • basis a
  let w := -(k • basis a)
  have hv : 0<v a := by simp [v,hk]
  have hu (p) (h : k<p) : 0 < inc a w p a := by simp [inc,w]; linarith
  have he := advancing V A w t (hu t (by unfold k; linarith))
  let L := innerSL ℂ (spot V (refl B a) v)
  apply (((L.restrictScalars ℝ).analyticAt _).comp he).congr
  filter_upwards [lt_mem_nhds (show k<t by unfold k; linarith)] with i hi
  change inner ℂ _ (spot V A (inc a w i))= _
  rw [swing V hp _ _ _ _ hv (hu i hi), reflect_twice hp]
  congr 1; ext p; simp [inc,v,w,Signed.mirrored]; split_ifs <;> simp

/-- The single-single pair linked on physical ``t`` (normal) and offset in b.
Instance to get norm estimates with pure rates. -/
theorem fires (V : Chamber S a) (h : S.Hierarchy) (W : DiffPlan S) (P : W.Derivatives S) (A : S.Tag)
    (x : E4) (hx : 0<x a) (j : b≠a) (F : ℝ → ℂ) (hF : AnalyticAt ℝ F 0)
    (HF : ∀ n : ℕ, iteratedDeriv n (fun s : ℝ => pair A (refl A a) ((2 * x a) • basis a+s • basis b)) 0=iteratedDeriv n F 0) (t : ℝ) :
    AnalyticAt ℝ (fun s => spot V A (inc b x s)) t := by
  apply Analysis.blossoms _ (blooms V W h P A j hx) _ F hF _ HF
  intro p q
  dsimp only
  rw [swing V h _ _ _ _ (step hx _ j) (step hx _ j)]
  congr 1
  apply PiLp.ext; intro i; simp [inc, Signed.mirrored]; split_ifs <;> simp_all ; ring
end YM.Ward
