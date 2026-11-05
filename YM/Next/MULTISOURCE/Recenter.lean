import YM.Marker.Console
import YM.Next.MULTISOURCE.Bulk
import YM.Work.H03


/-!
# Support, regular and forced tests under hierarchy-anchored translations
-/
set_option autoImplicit false
noncomputable section

namespace YM.Multi.AxisShift
open RG Lattice Wilson Function Finset MeasureTheory Pack
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

variable {G : Gauge} {n : Side} (o : Site n)

def roots (X : Support n) := X.image (fun x => x+o)
@[simp] lemma add_mem (X : Support n) (x : Site n) : x+o ∈ roots o X ↔ x∈X := by
  simp [roots]

lemma behind (X : Support n) : roots (-o) (roots o X) = X := by
  unfold roots; rw [Finset.image_image]; simp

lemma roots_mono (X Y : Support n) (h : X ⊆ Y) : roots o X ⊆ roots o Y := image_subset_image h
@[simp] lemma roots_card (X : Support n) : (roots o X).card = X.card := card_image_of_injective X (add_left_injective o)

lemma flagging (t : ℝ) (U : Config G n) : roots o (flags t (translate o U))=flags t U := by
  simpa only [pull_one,show affine 1 o=fun x => x+o from funext fun x => by simp [affine],roots] using Work.H03.flags_send 1 o t U

lemma intersection (X : Support n) (t : ℝ) (U : Config G n) :
    roots o (X ∩ flags t (translate o U))=roots o X ∩ flags t U := by
  conv_rhs => rw [← flagging o t U]
  exact image_inter X _ (add_left_injective o)

lemma occupied (X I : Support n) (t : ℝ) (U : Config G n) :
    X ∩ flags t (translate o U)=I ↔ roots o X ∩ flags t U=roots o I := by
  rw [← intersection]; exact (image_injective (add_left_injective o)).eq_iff.symm

lemma health (X : Support n) (t : ℝ) (U : Config G n) :
    Healthy t X (translate o U) ↔ Healthy t (roots o X) U := by
  unfold Healthy; rw [Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_iff_inter_eq_empty]
  have he := occupied o X ∅ t U; simpa only [roots,image_empty] using he

lemma masks (X : Support n) (t : ℝ) (f : Config G n → ℂ) :
    masked t X f ∘ translate o=masked t (roots o X) (f ∘ translate o) := by
  funext x
  change masked _ _ _ _=_
  by_cases e : Healthy t X (translate o x)
  · rw [masked_eq _ _ _ _ e, masked_eq _ _ _ _ ((health ..).1 e)]; rfl
  rw [masked_ne _ _ _ _ e,masked_ne _ _ _ _ (mt (health ..).2 e)]

lemma agreeable (X : Support n) (U V : Config G n) (h : Agrees (roots o X) U V) :
    Agrees X (translate o U) (translate o V) := by
  intro e hi hj
  apply h (e.1+o,e.2) ((add_mem o X e.1).mpr hi)
  change e.1+o+step e.2∈ roots o X
  rw [add_right_comm]; exact (add_mem o X _).mpr hj

private lemma halos (Y : Support n) (b : ℕ) : halo b (roots o Y)=roots o (halo b Y) := by
  ext i
  obtain ⟨i,rfl⟩ := (Equiv.addRight o).surjective i
  change i+o∈ _ ↔ i+o∈_
  rw [add_mem,halo_spec,halo_spec]
  constructor
  · rintro ⟨j,hj,H⟩; obtain ⟨x,hx,rfl⟩ := mem_image.mp hj
    exact ⟨x,hx,by simpa using H⟩
  rintro ⟨j,hj,H⟩; exact ⟨j+o,(add_mem o Y j).mpr hj,by simpa using H⟩

private lemma shape (X D : Support n) (b : ℕ) (hh : covers b X D) : covers b (roots o X) (roots o D) := by
  unfold covers; rw [halos]
  refine ⟨roots_mono o _ _ hh.1,fun i hi j hj => ?_⟩
  obtain ⟨i,hp,rfl⟩ := mem_image.mp hi
  obtain ⟨j,hq,rfl⟩ := mem_image.mp hj
  exact Relation.ReflTransGen.lift (fun x : Site n => x+o) (fun a c h =>
    ⟨(add_mem ..).mpr h.1,(add_mem ..).mpr h.2.1, by simpa using h.2.2⟩) i j (hh.2 i hp j hq)

@[simp] lemma priced (X : Support n) (b : ℕ) : coverNumber b (roots o X)=coverNumber b X := by
  have h (o : Site n) (X : Support n) : coverNumber b (roots o X) ≤ coverNumber b X := by
    obtain ⟨D,h,he⟩ := coverNumber_realized b X
    rw [← he, ← roots_card o D]; exact Corona.list_cost b (shape o X D b h)
  exact le_antisymm (h _ _) (by simpa only [behind] using h (-o) (roots o X))

lemma visible : Continuous (translate o (K:=G.El)) := by unfold translate; fun_prop

lemma respects (f : Config G n → ℂ) (hf : GaugeInvariant f) : GaugeInvariant (f ∘ translate o) := by
  intro t U
  simp only [comp_apply]
  rw [show translate o (gauge t U)=gauge (fun x => t (x+o)) (translate o U) from ?_]; exact hf _ _
  funext e; simp only [Lattice.gauge, translate]; rw [add_right_comm _ (Lattice.step _)]

def evolve : Directions G n →L[ℝ] Directions G n where
  toFun l := fun i => l (i.1+o,i.2)
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  cont := continuous_pi fun _ => continuous_apply _

lemma stepped (f : Config G n → ℂ) (k) (U : Config G n) :
    leftDerivs (f ∘ translate o) k U = leftDerivs f (k.map (evolve o)) (translate o U) := by
  induction k generalizing U with
  | nil => rfl
  | cons i k ih => simp only [List.map_cons,leftDerivs,ih]; rfl

lemma legal {F : Config G n → ℂ} {P : BudgetPoint} {X : Support n} (h : P.Regular X F) :
    P.Regular (roots o X) (F ∘ translate o) := by
  refine ⟨fun i V H => h.sites _ _ (agreeable o X i V H), h.borel.comp (visible o).measurable,
    respects _ _ h.symmetry,fun U he => ?_,fun U he A l hl => ?_⟩
  · have hh := h.smooth _ ((health ..).2 he)
    apply hh.comp_of_eq _ (g:=(fun v : Directions G n => F (increment (translate o U) v)))
      (f:=evolve o) (ContinuousLinearMap.contDiff ..).contDiffAt (Set.mapsTo_univ _ _) (map_zero _)
  simp_rw [stepped]; exact h.hasDerivs _ ((health ..).2 he) _ _ (by simpa using hl)

lemma lift_bill {F : Config G n → ℂ} {P : BudgetPoint} {X : Support n} {x : Site n} {r : ℝ} (h : P.supBounds x X F r) :
    P.supBounds (x+o) (roots o X) (F ∘ translate o) r := by
  refine ⟨h.1,fun U he l hl hh => ?_⟩
  rw [stepped]; apply h.2 _ ((health ..).2 he) _ (by simpa using hl)
  intro i hi; obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hi
  intro j
  simpa only [evolve,ContinuousLinearMap.coe_mk', LinearMap.coe_mk,AddHom.coe_mk,
    separation_translate] using hh a ha (j.1+o,j.2)

lemma recenters {F : Config G n → ℂ} {P : BudgetPoint} {X : Support n} {p r : ℝ} (h : Banked P r X F p) :
    Banked P r (roots o X) (F ∘ translate o) p := by
  obtain ⟨T,A,f,hf,hk,H⟩ := h
  refine ⟨fun i => roots o (T i),fun i => A i ∘ translate o,f,fun i => ?_,?_,fun U => ?_⟩
  · refine ⟨roots_mono _ _ _ (hf i).1,legal o (hf i).2.1,(hf i).2.2.1,?_⟩
    intro j hj; obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hj
    exact lift_bill o ((hf i).2.2.2 _ hx)
  · simp only [burn,priced]; exact hk
  rw [Function.comp_apply,H]
  exact tsum_congr fun i => congr_fun (masks ..) U
end YM.Multi.AxisShift
