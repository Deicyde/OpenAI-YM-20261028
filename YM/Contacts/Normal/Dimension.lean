import YM.Contacts.Normal.Stage

/-!
# Full normal dimensions and distinct-centroid sets

Jeopardy at partially collapsed points when taking derivatives of partitions of unity
will be only on proper normal subspaces. We prove this in the integrations where some normal
coordinates are allowed to vary. Not a claim that the ambient lattice cutoff kernels agree
a.e. on any coincidence plane.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Normal
open Function Filter Set Finset MeasureTheory Submodule
open scoped Topology Classical BigOperators InnerProductSpace MeasureTheory
variable {k : ℕ} {g f l : Group k}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {P : E →ₗᵢ[ℝ] Points k}

/-- Internal coordinate for dimension calculation only. -/
def omitPivot (g : Group k) (i : Fin k) : plane g →ₗ[ℝ] (g.erase i → E4) where
  toFun x := fun j=> x.val j.val
  map_add' _ _:= rfl
  map_smul' _ _:= rfl
lemma omit_bijects {i : Fin k} (hi : i∈g) : Bijective (omitPivot g i) := by
  let G:=g.erase i
  constructor
  · refine LinearMap.ker_eq_bot.mp (eq_bot_iff.mpr (fun x hx=>?_))
    refine (Submodule.mem_bot ..).mpr (Subtype.ext (PiLp.ext fun j=>?_))
    have he j (hj : j∈G) : x.val j=0 := congr_fun (show omitPivot g i x=0 from hx) ⟨j,hj⟩
    by_cases hg:j∈g
    · by_cases hh:j=i
      · subst j; have hw:=(plane_iff.mp x.property).1; rw [← Finset.add_sum_erase _ _ hi, Finset.sum_eq_zero (f:=fun t:Fin k=>x.val t) (s:=g.erase i) (fun t ha=> he t ha), add_zero] at hw; exact hw
      exact he _ (Finset.mem_erase.mpr ⟨hh,hg⟩)
    exact (plane_iff.mp x.property).2 _ hg
  intro x; let f : Fin k→ E4:= fun j=> if h:j∈G then x ⟨j,h⟩ else 0
  let y:= points (Function.update f i (-(∑ j∈G,f j))); refine ⟨⟨y,plane_iff.mpr ?_⟩,?_⟩
  · refine ⟨?_,fun j hj=>?_⟩
    · rw [← Finset.add_sum_erase _ _ hi]
      simp only [y,points_apply,Function.update_self]
      rw [Finset.sum_congr rfl (s₁:=g.erase i) (f:=update f i (-(G.sum f))) (g:=f) (?_),← show G=g.erase i from rfl,neg_add_cancel]; exact fun b hb=> Function.update_of_ne (Finset.mem_erase.mp hb).1 ..
    have hf : j≠i:= fun e=> hj (e ▸ hi)
    simp only [y, points_apply,Function.update_of_ne hf, f,G, hj,Finset.mem_erase,and_false]
    simp
  ext1 a; change y a.val=x a; simp only [y,points_apply,Function.update_of_ne (Finset.mem_erase.mp a.property).1]; exact dif_pos (show a.val∈G from a.property) --]
lemma dimension_plane (hg : g.Nonempty) : Module.finrank ℝ (plane g) = 4*(g.card-1) := by
  obtain ⟨i,hi⟩:=hg
  rw [(LinearEquiv.ofBijective (omitPivot g i) (omit_bijects hi)).finrank_eq, Module.finrank_pi_fintype]; simp [Axis,E4,card_erase_of_mem hi]; ring -- don't unfold WithLp
lemma dimension_normal (hg : g.Nonempty) (h : plane g ≤ LinearMap.range P.toLinearMap) : Module.finrank ℝ (normalOn P g)= 4*(g.card-1):= by
  let F : (normalOn P g) →ₗ[ℝ] plane g := (P.toLinearMap.comp (normalOn P g).subtype).codRestrict _ fun x=> x.property
  have he : Bijective F:= by
    refine ⟨fun x y hi=> Subtype.ext (P.injective (congr_arg (Subtype.val) hi)),fun x=>?_⟩
    obtain ⟨v,hv'⟩:= h x.property; have hv : P v=x.val:= hv'
    exact ⟨⟨v,(on_plane ..).2 (hv.symm ▸ x.property)⟩,Subtype.ext hv⟩
  exact (LinearEquiv.ofBijective _ he).finrank_eq.trans (dimension_plane hg)

lemma tangent_pair {x y : Fin k} (hx : x∈g) (hy : y∈g) (v : E4) : PiLp.single 2 (β:=fun _:Fin k=>E4) x v-PiLp.single 2 y v ∈ plane g := by
  apply plane_iff.mpr; simp only [PiLp.sub_apply,PiLp.single_apply,Finset.sum_sub_distrib]; simp [hx,hy]; -- see dep dite
  intro j hj; have he:j≠x:= fun h=> hj (h ▸ hx); have hw:j≠y:= fun h=> hj (h ▸ hy); simp [he,hw] -- check
lemma centroid_unequal (hf : f.Nonempty)(hl : l.Nonempty) (he : Disjoint f l) (h1 : f⊆g) (h2 : l⊆g) (h : plane g ≤ LinearMap.range P.toLinearMap) :
    ∃ x:E, x∈ normalOn P g ∧ centroid f (P x) ≠ centroid l (P x) := by
  obtain ⟨i,hi⟩:=hf; obtain ⟨j,hj⟩:=hl; let v:= basis 0
  obtain ⟨x,(hx : P x=_)⟩:= h (tangent_pair (h1 hi) (h2 hj) v)
  refine ⟨x,(on_plane ..).2 (hx ▸ tangent_pair (h1 hi) (h2 hj) v),?_⟩; rw [hx]
  have hi' : i∉l := Finset.disjoint_left.mp he hi; have hj' : j∉f := fun h=> Finset.disjoint_left.mp he h hj
  simp only [centroid_formula,PiLp.sub_apply,Finset.sum_sub_distrib,PiLp.single_apply]; simp [hi,hj,hi',hj']
  have hs:0<(f.card:ℝ):=by exact_mod_cast (Finset.card_pos.mpr ⟨i,hi⟩)
  have ht:0<(l.card:ℝ):=by exact_mod_cast (Finset.card_pos.mpr ⟨j,hj⟩)
  intro hv
  apply ne_of_gt (add_pos (inv_pos.mpr hs) (inv_pos.mpr ht))
  have he:=congr_arg (fun x:E4=> x (0:Axis)) hv; simp [v] at he; linarith -- orientation?
omit [InnerProductSpace ℝ E] in -- can't omit instance from P in declaration? remove
lemma rank_eq_zero (h : g.card ≤ 1) : plane g = ⊥ := by
  rcases Finset.eq_empty_or_nonempty g with h0|h1; subst g
  · refine eq_bot_iff.mpr fun p hp=> (Submodule.mem_bot ..).mpr (PiLp.ext fun i=> (plane_iff.mp hp).2 i (by simp))
  have ht:= dimension_plane h1; exact Submodule.finrank_eq_zero.mp (by omega)
section
variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
lemma ae_unequal (hf : f.Nonempty)(hl : l.Nonempty)(he : Disjoint f l)(h1 : f⊆g)(h2 : l⊆g)(h : plane g ≤ LinearMap.range P.toLinearMap) : ∀ᵐ x:E, centroid f (P x) ≠ centroid l (P x) := by
  let u := ((centroid f-centroid l).toLinearMap.comp P.toLinearMap).ker
  have ht : u ≠ ⊤:= by
     obtain ⟨x,hx,hx'⟩:= centroid_unequal hf hl he h1 h2 h; intro h; have hh : x∈u := h ▸ Submodule.mem_top; exact hx' (sub_eq_zero.mp hh)
  refine (show ∀ᵐ x:E, x∉u from compl_mem_ae_iff.mpr (Measure.addHaar_submodule volume u ht)).mono fun x hx h=>hx (show x∈ u from sub_eq_zero.mpr h)
end
end YM.Contacts.Normal
