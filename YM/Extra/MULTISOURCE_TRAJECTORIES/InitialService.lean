import YM.Extra.MULTISOURCE_TRAJECTORIES.BirthBounds
import YM.Extra.MULTISOURCE_TRAJECTORIES.Service
import YM.Next.FOUNDATIONS.Primary
/-!
# Cutoff/full-alphabet expenses before the step

Only actual singleton exponent inputs at the cutoff. Their bad-field
complements also enter the *complete* joint dictionary alongside actual Ks,
and the absolute estimate below pays all overlaps. Exponents on the old gas
must have been bought already. Compare .
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories
open RG Wilson Lattice Source Overlay Marker Mix Function Filter MeasureTheory Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge} {C : Family G} {V : Type} [Fintype V] [DecidableEq V] (R : Census V)
    {N p : ℕ}

namespace Probes
variable (Q : Probes C V N p) (W : Windows (C.side N p))

def born (i : V) : Hot R × W.Piece := (⟨R.fire i,by simp [Census.fire]⟩,⟨∅,by simp⟩)
omit [Fintype V] in
lemma born_injective : Injective (born R W) := fun _ _ h => (R.fire_inj ..).mp (congrArg (Subtype.val ∘ Prod.fst) h)

lemma top_H (i : V) : (Q.layers R W).H (born R W i) = Q.fraction i := by
  funext U; rw [masked_top]; simp [born]
lemma top_silent {a : Hot R × W.Piece} (ha : a ∉ Set.range (born R W)) : (Q.layers R W).H a = 0 := by
  funext U; rw [masked_top]; split
  next he =>
    exact sum_eq_zero fun i _ => if_neg (fun h => ha ⟨i, Prod.ext (Subtype.ext h.symm) (Subtype.ext he.symm)⟩)
  rfl

private lemma region_birth (i : V) : (Q.layers R W).region (born R W i) = Q.footprint i := Q.region_empty W i _ rfl rfl


def primaryPrice (F D : V → ℝ) (K : ℕ → ℝ) (hD : ∀ i,0≤D i)
    (hg : ∀ i,grain (C.path.rep N p N).p (Q.footprint i) (Q.fraction i) (Q.place i) (D i))
    (hr : ∀ i U, ‖Q.fraction i U‖ ≤ F i) (hK : ∀ i U, ‖(C.path.rep N p N).activities.K i U‖ ≤ K i) :
    (Q.layers R W).Prices where
  K := K
  boundK := hK
  jet := extend (born R W) D 0
  attach := extend (born R W) F 0
  nonnegative i := by
    by_cases hi : i∈Set.range (born R W)
    · obtain ⟨i,rfl⟩ := hi; rw [(born_injective R W).extend_apply]; exact hD i
    rw [extend_apply' _ _ _ hi]; rfl
  available i x h := by
    by_cases hi : i∈Set.range (born R W)
    · obtain ⟨i,rfl⟩ := hi; obtain rfl := mem_singleton.mp h
      rw [region_birth,top_H, (born_injective R W).extend_apply]
      change grain _ _ _ (Q.positions N _) _; rw [positions,ancestor_top,id_eq]; exact hg _
    rw [Q.top_silent R W hi, extend_apply' _ _ i hi]; exact grain_big (by
      refine ⟨le_rfl (a:=(0:ℝ)), fun U _ k _ _ => ?_⟩
      rw [show (0 : Config G (C.side N p) → ℂ) = (fun _ => 0) from rfl,Work.G07.left_const]; simp) (by simp)
  residue i U := by
    unfold Layers.residual
    by_cases hi : i∈Set.range (born R W)
    · obtain ⟨i,rfl⟩ := hi; rw [top_H, (born_injective R W).extend_apply]
      split
      · rw [norm_zero]; exact (norm_nonneg _).trans (hr _ U)
      exact hr i U
    rw [Q.top_silent R W hi,extend_apply' _ _ i hi]; simp

private lemma sum_budget {α β} {f : α ⊕ β → ℝ} {u v : ℝ} (h : SumBudget (f ∘ Sum.inl) u)
    (h' : SumBudget (f ∘ Sum.inr) v) : SumBudget f (u+v) := by
  have he := h.2.1.hasSum.sum h'.2.1.hasSum
  exact ⟨fun i => Sum.rec (h.1) (h'.1) i, he.summable, he.tsum_eq.trans_le (add_le_add h.2.2 h'.2.2)⟩

lemma primary_expenses (F D : V → ℝ) (K : ℕ → ℝ) (hD : ∀ i,0≤D i)
    (hg : ∀ i,grain (C.path.rep N p N).p (Q.footprint i) (Q.fraction i) (Q.place i) (D i))
    (hr : ∀ i U, ‖Q.fraction i U‖ ≤ F i) (hK : ∀ i U, ‖(C.path.rep N p N).activities.K i U‖ ≤ K i)
    {w γ : ℝ} (hw : 0<w) (hγ : 0 ≤ γ) (he : Real.exp (γ+γ)-1 ≤ 1) (hB : ((C.path.rep N p N).p.B+(C.path.rep N p N).p.B+1:ℕ)^4*((γ+γ):ℝ) ≤ 1)
    (hc : ∀ i,w*loaf (C.path.rep N p N).p (Q.footprint i) 0 (D i) ≤ 1)
    (hh : Ac.Hit (fun i => ((C.path.rep N p N).activities.forced i).support) (C.path.rep N p N).p.B K ((C.path.rep N p N).p.supportExponent+1) γ)
    (hs : Ac.Hit Q.footprint (C.path.rep N p N).p.B (fun i => w * F i) ((C.path.rep N p N).p.supportExponent+1) γ) :
    (Q.layers R W).Expenses w := by
  let q := Q.primaryPrice R W F D K hD hg hr hK
  let X := Q.layers R W
  have ha (b : Bool) : Layers.Sale q w 0 b := by
    refine ⟨le_rfl,hw,fun i => ?_,γ+γ,add_nonneg hγ hγ,he,hB,?_⟩
    · let price (j : Hot R × W.Piece) := Poly.toll (fun _ => w) (X.tag j)*loaf (C.path.rep N p N).p (X.region j) 0 (q.jet j)
      let f := fun j => if ranked (X.tag j)=b ∧ i∈(X.tag j).val then price j else 0
      refine ⟨fun j => ?_,Summable.of_finite,show ∑' j,f j ≤ 1 from ?_⟩
      · dsimp only; split
        · exact mul_nonneg (Poly.worth (fun _ => hw) _).le (mul_nonneg (Real.exp_pos _).le (q.nonnegative _))
        rfl
      rw [tsum_fintype,sum_eq_single (born R W i)]
      · unfold f; split; swap; exact zero_le_one
        exact le_trans (le_of_eq (by
          unfold price q; simp only [primaryPrice,(born_injective R W).extend_apply]
          rw [show X.tag (born R W i)=R.fire i from rfl,Poly.solo_toll,Q.region_birth ..])) (hc i)
      · intro j _ hj; unfold f; split; swap; rfl
        next hi =>
          by_cases h : j∈Set.range (born R W)
          · obtain ⟨j,rfl⟩ := h
            exact (hj (congrArg (born R W) (mem_singleton.mp hi.2).symm)).elim
          simp only [price,q,primaryPrice, extend_apply' _ _ j h,Pi.zero_apply,loaf,mul_zero]
      simp
    intro x; simp only [add_zero]
    refine sum_budget (hh x) (budget_image (born_injective R W) injective_id (fun i => ?_) (fun i hi => ?_) (hs x) ?_)
    · dsimp only [comp_apply]; split
      · exact mul_nonneg (Layers.rent_nn q _ (fun _ => hw) b _ ) (Real.exp_pos _).le
      rfl
    · dsimp only [comp_apply]; split
      · dsimp only [Layers.rental,q,Sum.elim_inr,primaryPrice]; rw [extend_apply' _ _ i hi]; simp
      rfl
    · intro j; dsimp only [id_eq,comp_apply,Layers.area,Layers.rental,Sum.elim_inr]
      simp only [Q.region_birth R W j,show (Q.layers R W).tag (born R W j)=R.fire j from rfl]
      simp [ranked,Census.fire,q,primaryPrice,(born_injective R W).extend_apply,Poly.toll]
  exact ⟨by simp [layers,Insertions.fragments],q, ha false,w,0,by simp,ha true⟩
end Probes
end YM.Extra.Trajectories
