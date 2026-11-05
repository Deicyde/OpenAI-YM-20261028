import YM.Axis.Word
import YM.Ground.Compress

/-!
# Multi-cluster train limits

Expose S.expect cutoffs via extraction & point transports. Merge permutation
conclusions can use this once Rot. Preserve tags. True independence even varying transverse.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OS.Ground
open Function Set Filter Word
open scoped Topology BigOperators InnerProductSpace NNReal ContDiff
variable {G : Gauge} {L : Register G} {S : Table L} {V : Chamber S timeAxis} (P : Spread V)

abbrev flight (f g : ℕ → E4) := Tendsto (fun i => (g i-f i) timeAxis) atTop atTop
abbrev Car (L : Register G) := Row.Core L × (ℕ → E4)

def line (q : List (Car L)) := q.Pairwise (fun p s => flight p.2 s.2)

def all (q : List (Car L)) (n : ℕ) : L.Word := (q.map fun i => carry i.1.val (i.2 n)).flatten
abbrev starU (q : List (Row.Core L)) : P.algebra := (q.map fun i => M P i.val i.property).prod

def door (u : L.Word) : Future L timeAxis := open scoped Classical in if h : Positive u timeAxis then ⟨u,h⟩ else air _
lemma receives (H : Steady V) (v : ℕ → V.H) (x : V.H) (h : Tendsto v atTop (𝓝 x)) (u : ℕ → ℝ≥0) (hu : Tendsto u atTop atTop)
    (s : ℕ → Cross timeAxis) : Tendsto (fun i => V.flow.U (s i) (V.flow.E (u i) (v i))) atTop (𝓝 (V.flow.orth x)) := by
  apply Metric.tendsto_nhds.mpr; intro ε he
  have hh := (V.flow.emerges x).comp hu
  filter_upwards [Metric.tendsto_nhds.mp h (ε/2) (by positivity),Metric.tendsto_nhds.mp hh (ε/2) (by positivity)] with i hi hp
  apply lt_of_le_of_lt (dist_triangle _ (V.flow.U (s i) (V.flow.E (u i) x)) _)
  have hx : V.flow.U (s i) (V.flow.orth x)=V.flow.orth x := H (V.D.orthogonalProjectionOnto x) _
  suffices he : dist (V.flow.E (u i) (v i)) (V.flow.E (u i) x) ≤ dist (v i) x by
    simp_rw [dist_eq_norm] at *
    conv => enter [1,2]; rw [← hx]
    rw [← map_sub,V.flow.unitary,← map_sub (V.flow.U (s i)),V.flow.unitary]
    simp only [Function.comp_apply] at hp;linarith
  rw [dist_eq_norm, ← map_sub (V.flow.E _),dist_eq_norm]
  exact ((V.flow.E (u i)).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (V.flow.shrinks _))

lemma future_train (H : Steady V) (q : List (Car L)) (w : Car L) (hw : Positive w.1.val timeAxis)
    (hp : ∀ i∈q, Positive i.1.val timeAxis) (h : line (w::q)) :
    let f i := carry (all (w :: q) i) (-w.2 i)
    (∀ᶠ i in atTop, Positive (f i) timeAxis) ∧
    Tendsto (fun i => V.GNS.plant (door (f i))) atTop
      (𝓝 (X P (⟨w.1.val,hw⟩ : Future L timeAxis) ((starU P (q.map Prod.fst)).val V.omega0))) := by
  induction q generalizing w with
  | nil =>
    simp only [all,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,
      paths,add_neg_cancel,rest, starU,List.prod_nil]
    refine ⟨Eventually.of_forall fun _ => hw,?_⟩
    simp only [door,hw, ↓reduceDIte];
    change Tendsto _ _ (𝓝 (X P _ V.omega0)); rw [coming]; exact tendsto_const_nhds
  | cons v q ih =>
    have hv := hp v (List.mem_cons_self)
    let W : Future L timeAxis := ⟨_,hw⟩
    let Q := fun i => all (v::q) i
    let g i := carry (Q i) (-v.2 i)
    obtain ⟨hu,hI⟩ := ih v hv (fun i hi => hp i (List.mem_cons_of_mem _ hi)) h.of_cons
    obtain ⟨d,hd⟩ := future_reach W
    intro f
    let Y i := v.2 i-w.2 i
    let p i := Y i timeAxis
    let D i := (p i - d).toNNReal
    let b i := Semigroup.SEP timeAxis (Y i)
    let L := (starU P (q.map Prod.fst)).val V.omega0
    let l := X P (⟨_,hv⟩ : Future _ _) L
    have ht : Tendsto p atTop atTop := (List.pairwise_cons.mp h).1 _ (List.mem_cons_self)
    have hE i (he : (d:ℝ) ≤ p i) (hg : Positive (g i) timeAxis) : f i=(entering hd (over (travel (door (g i)) (D i)) (b i))).val := by
      rw [show door (g i)=⟨_,hg⟩ from dif_pos hg]
      change carry (carry w.1.val (w.2 i) ++ Q i) _ = w.1.val ++ _
      rw [distribute,paths, add_neg_cancel, rest]; unfold over travel raised
      dsimp only [g]; rw [paths,paths,paths]; congr 2
      dsimp only [D]; rw [Real.coe_toNNReal _ (sub_nonneg.mpr he),sub_smul]
      change _ = -v.2 i + ((p i • basis timeAxis-_) + ((v.2 i-w.2 i-p i • basis timeAxis)+_))
      abel
    have hs := receives H _ l hI D (Real.tendsto_toNNReal_atTop.comp (show Tendsto _ _ _ from
      tendsto_atTop_add_const_right atTop _ ht)) b -- sub rewrite
    have hQ : (starU P ((v::q).map Prod.fst)).val V.omega0=V.D.orthogonalProjectionOnto l := by
      simp only [starU,List.map_cons,List.prod_cons]; change (M P v.1.val hv.1).val L=_
      rw [squeezed (v := ⟨_,hv⟩)]; exacts [rfl,H]
    have hx : ∀ᶠ i in atTop, f i=(entering hd (over (travel (door (g i)) (D i)) (b i))).val := (hu.and
      (ht.eventually (eventually_ge_atTop _))).mono fun i hh => hE _ hh.2 hh.1
    refine ⟨hx.mono (fun i hi => hi ▸ (entering hd _).property),?_⟩
    rw [hQ,standing P W hd]
    change Tendsto _ _ (𝓝 (P.place d _ (V.flow.orth l)))
    apply (((P.place d _).continuous.tendsto _).comp hs).congr'
    filter_upwards [hx] with i hi
    rw [hi]
    change P.place d _ (V.flow.U _ (V.flow.E _ (V.GNS.plant (door (g i)))))=_
    rw [← V.atBirth,← V.across, P.reads hd]
    congr 1
    exact (show door _=_ from by unfold door; rw [dif_pos (entering hd _).property]).symm

private lemma inside (H : Steady V) (Y : S.Hierarchy) (q : List (Car L)) (h : ∀ i∈q, Positive i.1.val timeAxis) (hp : line q) :
    (∀ᶠ i in atTop, distinct (all q i)) ∧
    Tendsto (fun i => S.expect (all q i)) atTop (𝓝 (inner ℂ V.omega0 ((starU P (q.map Prod.fst)).val V.omega0))) := by
  cases q with
  | nil =>
    refine ⟨Eventually.of_forall fun _ => (air timeAxis (L := L)).property.1,?_⟩
    have he : ‖V.omega0‖=1 := nil_norm V.GNS Y.laws
    simp only [List.map_nil, starU,List.prod_nil]
    change Tendsto (fun _ : ℕ => S.expect []) atTop (𝓝 (inner ℂ V.omega0 V.omega0))
    rw [show S.expect []=1 from Y.laws.trivial _ _,inner_self_eq_norm_sq_to_K,he]; simp
  | cons w q =>
    have hu := h w List.mem_cons_self
    obtain ⟨hq,hv⟩ := future_train P H q w hu (fun i hi => h i (List.mem_cons_of_mem _ hi)) hp
    refine ⟨hq.mono (fun i hi => by
      have hx := Word.still hi.1 (w.2 i); simpa using hx),?_⟩
    rw [show ((starU P ((w::q).map Prod.fst)).val V.omega0) = V.D.orthogonalProjectionOnto
      (X P (⟨_,hu⟩:Future _ _) ((starU P (q.map Prod.fst)).val V.omega0)) from by
      simp only [starU,List.map_cons,List.prod_cons]; rw [show _ * _=_ from rfl] -- silly
      exact congr_arg (fun f : V.VacuumOp => f _) (squeezed P H (⟨_,hu⟩:Future _ _)),
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
    refine (tendsto_const_nhds (x := V.omega0.val) |>.inner (𝕜 := ℂ) hv).congr' (hq.mono ?_)
    intro i hi
    change inner ℂ (V.GNS.plant (air timeAxis)) (V.GNS.plant _) = _
    rw [door,dif_pos hi,V.GNS.measure]
    exact invariance Y.translations (by have hx := Word.still hi.1 (w.2 i); simpa using hx) _

private def fix (p : Car L) : Car L :=
    let h := Spread.Resolution.place_exists p.1.property
    (⟨carry p.1.val h.choose, h.choose_spec.choose_spec.2.1.1⟩, fun i => p.2 i-h.choose)
private lemma fixes (p : Car L) : Positive (fix p).1.val timeAxis := (Spread.Resolution.place_exists p.1.property).choose_spec.choose_spec.2.1
private lemma fixes_M (H : Steady V) (p : Car L) : M P (fix p).1.val (fix p).1.property=M P p.1.val p.1.property :=
    spots P H (Spread.Resolution.place_exists p.1.property).choose_spec.choose_spec -- by choice
private lemma fixes_y (q : List (Car L)) (i : ℕ) : all (q.map fix) i=all q i := by
  induction q with
  | nil => rfl
  | cons p q ih =>
    have ht : carry (fix p).1.val ((fix p).2 i)=carry p.1.val (p.2 i) := by simp [fix]
    exact congr_arg₂ (· ++ ·) ht ih
private lemma fixes_star (H : Steady V) (q : List (Car L)) : starU P ((q.map fix).map Prod.fst)=starU P (q.map Prod.fst) := by
  induction q with
  | nil => rfl
  | cons p q hp => exact congr_arg₂ (· * ·) (fixes_M P H p) hp

lemma arcs (H : Steady V) (Y : S.Hierarchy) (q : List (Car L)) (h : line q) :
    (∀ᶠ i in atTop, distinct (all q i)) ∧
    Tendsto (fun i => S.expect (all q i)) atTop (𝓝 (inner ℂ V.omega0 ((starU P (q.map Prod.fst)).val V.omega0))) := by
  have hp : line (q.map fix) := List.pairwise_map.mpr (h.imp (by
    intro p s h
    let a := (Spread.Resolution.place_exists p.1.property).choose
    let b := (Spread.Resolution.place_exists s.1.property).choose
    apply Tendsto.congr (fun i => ?_) (tendsto_atTop_add_const_right _ (a timeAxis - b timeAxis) h)
    simp [fix, a,b]; ring))
  have ht := inside P H Y (q.map fix) (by rintro i hi; obtain ⟨p,-,rfl⟩ := List.mem_map.mp hi; exact fixes p) hp
  rwa [show all (q.map fix) = all q from funext fun i => fixes_y q i,fixes_star P H] at ht
end YM.OS.Ground
