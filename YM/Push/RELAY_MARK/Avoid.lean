import YM.Push.RELAY_MARK.Micro
import YM.Shift.Breath

/-!
# Path/panel avoidance and div-free microscopic equations

an option avoiding the Haar divergence
counterterm when choosing the *section* at RAuthors, not changing it at
running cutoffs. Charge enough independent plaquettes **away** from
the varied link (paths may pass through its source!), and choose
transport paths around it; the multiplier of the actual gradient can
then be made independent of that positive-link variable altogether.
Use distinct cover positions and prove the actual large-side avoidance
for every wrapped assignment before even talking about a measure. We will
still have to show these probes have enough rank under jet normalization.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function Set Filter MeasureTheory Wilson Lattice RG Source InnerProductSpace
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {n : Side}

section Paths

def edges (x : Cover) : Walk → Finset (Edge Cover)
  | [] => ∅
  | d::l => insert (d.used x) (edges (x+d.vec) l)

lemma edges_join (x : Cover) (w s : Walk) : edges x (w++s)=edges x w ∪ edges (stop x w) s := by
  induction w generalizing x <;> simp_all [edges,stop]

def avoids (x : Cover) (l : Walk) (b : Edge Cover) := b∉edges x l

lemma circumvent (b : Edge Cover) (x y : Cover) : ∃ p : Walk, stop x p=y ∧ avoids x p b := by
  have he (x : Cover) (d : Step) : ∃ p : Walk, stop x p=x+d.vec ∧ avoids x p b := by
    by_cases h : b=d.used x
    · rw [h]; obtain ⟨i,t|t⟩ := d
      · obtain ⟨a,ha⟩ := exists_ne i
        refine ⟨[posDir a,posDir i,negDir a], by simp only [stop, Step.vec_pos,Step.vec_neg]; change _ = _+step i; abel, ?_⟩
        have hx : (step a : Cover)≠0 := by intro h; have := congr_fun h a; simp at this
        simp [avoids, edges, posDir, negDir, Step.used, Step.vec, Ne.symm ha,hx]
      obtain ⟨a,ha⟩ := exists_ne i
      refine ⟨[posDir a,negDir i,negDir a],by simp only [stop,Step.vec_pos,Step.vec_neg]; change _ = _ + -(step i); abel,?_⟩
      have hx : (step a : Cover)≠0 := by intro h; have := congr_fun h a; simp at this
      simp [avoids, edges, posDir, negDir, Step.used,Step.vec, Ne.symm ha,hx]
    exact ⟨[d],rfl,by simp [avoids,edges,h]⟩
  have hl (p : Walk) (x : Cover) : ∃ s : Walk, stop x s=stop x p ∧ avoids x s b := by
    induction p generalizing x with
    | nil => exact ⟨[],rfl,by simp [avoids,edges]⟩
    | cons d p ih =>
      obtain ⟨s,hs,hS⟩ := he x d
      obtain ⟨l,hy,hL⟩ := ih (x+d.vec)
      exact ⟨s++l,by rw [stop_append,hs,hy,stop],by unfold avoids; rw [edges_join,Finset.mem_union,hs]; exact not_or.mpr ⟨hS,hL⟩⟩
  simpa only [route_end] using hl (route x y 1) x

def safe (b : Edge Cover) (s : Slot) := avoids 0 s.walk b ∧ avoids s.offset (square s.plaq.val.1 s.plaq.val.2) b

lemma safe_slot (b : Edge Cover) (x : Cover) (p : PlaqAxes) (h : avoids x (square p.val.1 p.val.2) b) :
    ∃ s : Slot, safe b s ∧ s.offset=x ∧ s.plaq=p := by
  obtain ⟨w,hw,hW⟩ := circumvent b 0 x
  exact ⟨⟨w,p⟩,⟨hW, by simp only [Slot.offset,hw]; exact h⟩,hw,rfl⟩

lemma finite_exception (b : Edge Cover) (p : PlaqAxes) : Set.Finite {x : Cover | ¬ avoids x (square p.val.1 p.val.2) b} := by
  let i := p.val.1; let j := p.val.2
  refine (Finset.finite_toSet ({b.1,b.1-step i,b.1-step j} : Finset Cover)).subset (fun x hx => ?_)
  simp only [mem_setOf_eq, avoids, square, edges,Finset.mem_insert, Finset.notMem_empty,
    not_not, or_false] at hx
  simp only [Finset.mem_coe, Finset.mem_singleton,Finset.mem_insert]
  have he : x+(step i)+(step j)-step i = x+step j := by abel
  have ht : x+(step i)+(step j) + (-step i) - step j=x := by abel
  rcases hx with hx|hx|hx|hx
  · exact Or.inl ((congr_arg Prod.fst hx).symm)
  · right; left; exact eq_sub_of_add_eq ((congr_arg Prod.fst hx).symm)
  · right; right; apply eq_sub_of_add_eq
    rw [← he]; exact (congr_arg Prod.fst hx).symm
  left; rw [← ht]; exact (congr_arg Prod.fst hx).symm

lemma travel_edges {x : Cover} {F : Walk} (U V : CoverConfig G)
    (h : ∀ i∈edges x F, U i = V i) : travel U x F = travel V x F := by
  induction F generalizing x with
  | nil => simp only [travel]
  | cons d w ih =>
    have hh (i) (hi : i ∈ edges (x + d.vec) w) := h i (Finset.mem_insert_of_mem hi)
    have ht : d.read U x = d.read V x := by simp only [Step.read, h _ (Finset.mem_insert_self ..)]
    simp only [travel, ht, ih hh]
end Paths

section Wrap

def placeEdge (o : Site n) (b : Edge Cover) : Edge (Site n) := (wrap n b.1+o,b.2)

lemma place_size (x : Cover) : ∃ (r M : ℕ), ∀ n : Side, M ≤ n.val → lift (wrap n x)=x ∧ pdist (wrap n x)≤r := by
  let r := Finset.univ.sup fun i : Axis => (x i).natAbs
  refine ⟨r,2*r+1,fun n hn => ?_⟩
  have he : lift (wrap n x)=x := lift_eq_iff.mpr ⟨rfl,fun i => by
    have ht : (x i).natAbs ≤ r := Finset.le_sup (f:=fun i => (x i).natAbs) (Finset.mem_univ i)
    omega⟩
  exact ⟨he, by rw [pdist,he]⟩

lemma eventually_apart (b e : Edge Cover) (h : b≠e) :
    ∃ M : ℕ, ∀ n : Side, M ≤ n.val → ∀ o : Site n, placeEdge o b ≠ placeEdge o e := by
  obtain ⟨r,M,he⟩ := place_size b.1
  obtain ⟨s,N,ht⟩ := place_size e.1
  refine ⟨max M N,fun n hn o h' => h (Prod.ext ?_ (show (placeEdge o b).2=(placeEdge o e).2 from congr_arg Prod.snd h'))⟩
  have hx : wrap n b.1=wrap n e.1 := add_right_cancel (b:=o) (congr_arg Prod.fst h')
  rw [← (he n ((le_max_left ..).trans hn)).1, hx]; exact (ht n ((le_max_right ..).trans hn)).1

def independent {X : Type*} (b : Edge Cover) (f : CoverConfig G → X) :=
    ∃ M : ℕ, ∀ n : Side, M ≤ n.val → ∀ o : Site n, ∀ (P : Config G n) A t, f (expandAt o (turnLink (placeEdge o b) A t P)) = f (expandAt o P)

lemma traveled (b : Edge Cover) (x : Cover) (p : Walk) (h : avoids x p b) :
    independent b (fun V : CoverConfig G => travel V x p) := by
  choose M hM using fun i : edges x p => eventually_apart i.val b (by intro he; exact h (he ▸ i.property))
  refine ⟨Finset.univ.sup M,fun n hn o V A t => travel_edges _ _ (fun i hi => ?_)⟩
  exact turn_away V A t (hM ⟨i,hi⟩ n ((Finset.le_sup (f:=M) (Finset.mem_univ ⟨i,hi⟩)).trans hn) o)

namespace independent
variable {b : Edge Cover} {X Y Z : Type*}

lemma const (y : X) : independent b (fun _ : CoverConfig G => y) := ⟨0,fun _ _ _ _ _ _ => rfl⟩
lemma map {f : CoverConfig G → X} (h : independent b f) (g : X → Y) : independent b (g ∘ f) := by
  obtain ⟨M,h⟩ := h; exact ⟨M,fun n hn o V A t => congr_arg g (h n hn o V A t)⟩
lemma join {f : CoverConfig G → X} {g : CoverConfig G → Y} (h : independent b f) (he : independent b g)
    (P : X → Y → Z) : independent b (fun V => P (f V) (g V)) := by
  obtain ⟨M,h⟩ := h; obtain ⟨N,he⟩ := he
  exact ⟨max M N,fun n hn o V A t => congr_arg₂ P (h n ((le_max_left ..).trans hn) o V A t)
    (he n ((le_max_right ..).trans hn) o V A t)⟩
end independent

lemma safe_read (b : Edge Cover) (s : Slot) (h : safe b s) : independent b (s.eval (G:=G)) := by
  apply independent.join (traveled b 0 s.walk h.1) (traveled _ _ _ h.2) (fun z a => G.adjoint z (G.curvature a))

lemma stem_place (U : Config G n) (o : Site n) (x : Cover) (j : Axis) (p : PlaqAxes) :
    stem (expandAt o U) x j p = stem U (wrap n x+o) j p := by
  simp only [stem,faceValue,travel_at]
  simp only [expandAt, map_sub, wrap_step]
  rw [sub_add_eq_add_sub]

lemma field_place (U : Config G n) (o : Site n) (b : Edge Cover) :
    field (expandAt o U) b=field U (placeEdge o b) := by
  simp [field,flux,stem_place,placeEdge]
end Wrap

section Micro

/- Haar multiplier at root after parallel transport of gradient. -/
def force (P : CoverConfig G) (w : Walk) (b : Edge Cover) :=
    G.adjoint (travel P 0 w) (field P b)

lemma continuous_force (w : Walk) (b : Edge Cover) : Continuous (fun U : CoverConfig G => force U w b) := by
  have he := (continuous_ad G).comp ((continuous_travel w (0:Cover) (G:=G)).prodMk (continuous_field G b))
  exact he

lemma twist_inner (g : G.El) (X Y : G.Color) : inner ℝ X (G.adjoint g Y) = inner ℝ (G.adjoint g⁻¹ X) Y := by
  let L : G.Color →ₗᵢ[ℝ] G.Color := { G.adjoint g with norm_map' := G.norm_adjoint g }
  have he := L.inner_map_map (G.adjoint g⁻¹ X) Y
  change inner ℝ (G.adjoint g _) (G.adjoint g _) = _ at he
  simpa only [← G.adjoint_mul,mul_inv_cancel,G.adjoint_one] using he

lemma cont_envelope {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {f : X → ℂ} (h : Continuous f) : Envelope f :=
  ⟨h.measurable,h.bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)⟩

lemma envelope_mul {X : Type*} [MeasurableSpace X] (f g : X → ℂ) (hf : Envelope f) (hg : Envelope g) : Envelope (fun x=> f x*g x) := by
  obtain ⟨c,hc⟩ := hf.cost; obtain ⟨d,hd⟩ := hg.cost
  exact ⟨hf.meas.mul hg.meas,c*d,fun V => by rw [norm_mul]; exact mul_le_mul (hc _) (hd _) (norm_nonneg _) ((norm_nonneg _).trans (hc V))⟩

lemma micro_force (X : G.Color) (f : Pre G) (w : Walk) (b : Edge Cover)
    (hw : avoids 0 w b) (hf : Continuous f) (he : independent b f) :
    Micro (fun P => (inner ℝ X (force P w b) : ℂ) * f P) := by
  let g (P : CoverConfig G) := travel P 0 w
  let V (P : CoverConfig G) := G.adjoint (g P)⁻¹ X
  let Z := fun P : CoverConfig G => (inner ℝ X (force P w b) : ℂ) * f P
  have ht : Continuous V := by
    have h := (continuous_ad G).comp (((continuous_travel w (0:Cover) (G:=G)).inv).prodMk (continuous_const (y:=X)))
    exact h
  have hl : Continuous Z := (Complex.continuous_ofReal.comp (continuous_const (y:=X)|>.inner (continuous_force w b))).mul hf
  obtain ⟨m,he⟩ := he
  obtain ⟨r,k,hk⟩ := place_size b.1
  let L := max 2 (max m k)
  obtain ⟨l,hv⟩ := (traveled (G:=G) b 0 w hw).map (fun t : G.El => G.adjoint t⁻¹ X)
  refine ⟨hl,r,max l L,fun n hn o β hb S hs hS => ?_⟩
  have hL : 2 ≤ n.val ∧ m ≤ n.val ∧ k ≤ n.val := max_le_iff.mp ((le_max_right ..).trans hn) |>.imp_right max_le_iff.mp
  let Gf : Config G n → G.Color := V ∘ expandAt o
  let F : Config G n → ℂ := f ∘ expandAt o
  have Hf : Continuous F := onStencil o hf
  have hv (P : Config G n) (A : G.Color) (t : ℝ) : Gf (turnLink (placeEdge o b) A t P) = Gf P := hv n ((le_max_left ..).trans hn) ..
  have hz (P : Config G n) (A : G.Color) (t : ℝ) : S (turnLink (placeEdge o b) A t P) = S P := by
    apply hs; intro i hi _; apply turn_away P A t
    intro h; subst i
    have hl : r < separation (wrap n b.1 + o) o := hi
    simp only [separation, add_sub_cancel_right] at hl
    exact not_lt_of_ge (hk n hL.2.2).2 hl
  let E := EuclideanSpace.basisFun G.ColorIndex ℝ
  let a (i : G.ColorIndex) (P : Config G n) := ((Gf P i : ℝ) : ℂ) * F P
  let c (i : G.ColorIndex) (P : Config G n) := a i P * S P
  let d (i : G.ColorIndex) (P : Config G n) := (inner ℝ (E i) (field P (placeEdge o b)) : ℂ) * c i P
  have hc (i : G.ColorIndex) : Envelope (c i) := envelope_mul _ _ (cont_envelope
    ((Complex.continuous_ofReal.comp ((PiLp.continuous_apply _ _ i).comp (onStencil o ht))).mul Hf)) hS
  have H (P : Config G n) : Z (expandAt o P)*S P = ∑ i, d i P := by
    unfold Z force; rw [twist_inner,field_place]
    let Y := field P (placeEdge o b)
    change ((inner ℝ (Gf P) Y : ℂ) * F P) * S P = _
    have hh : inner ℝ (Gf P) Y = ∑ i, Gf P i * inner ℝ (E i) Y := by
      have hu : ∑ i, Gf P i • E i = Gf P := E.sum_repr _
      nth_rw 1 [← hu]; simp [sum_inner, real_inner_smul_left]
    rw [hh,Complex.ofReal_sum,Finset.sum_mul,Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; unfold d c a Y; ring
  have hI (i : G.ColorIndex) : Integrable (d i) (law G n β) := times_integrable (Complex.continuous_ofReal.comp
    (continuous_const (y:=E i)|>.inner (continuous_field G _))) (hc i)
  change (∫ U, Z (expandAt o U)*S U ∂law G n β) = _
  simp_rw [H]; rw [integral_finsetSum _ fun i _ => hI i]
  refine Finset.sum_eq_zero fun i _ => equation_silent _ _ β hL.1 hb (hc i) ?_
  intro U t
  unfold c a; rw [hz,hv,show F (turnLink (placeEdge o b) (E i) t U) = F U from he n hL.2.1 ..]
end Micro
end YM.Push.Mark
