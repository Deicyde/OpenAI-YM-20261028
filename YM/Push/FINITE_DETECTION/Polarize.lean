import YM.Push.FINITE_DETECTION.Variables

/-!
# Endpoint Wick rule after independent linear substitutions at the occurrences

Work with Wick's actual definition permitting arbitrary order-1 variables at each
leg (linear combinations mixing orders). No Gaussian-measure assumption. Matchings
include even the one empty graph. Bilinear complex convention throughout.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.FiniteDetection.Free
open Function Set Filter Maxwell Wick Wick.Occ Equiv
open scoped Topology BigOperators ContDiff
variable {n : ℕ} {G : Gauge} {W : Powers G n}

def stationed (W : Powers G n) (i : Fin n) : Finset (Occ W) := Finset.univ.filter fun o => o.label = i

private def stamp {V : Powers G n} (x : Occ V) := (x.label,x.probe)
private def stampEquiv {V : Powers G n} (i : Fin n × Slot G) : Fin (V i.1 i.2) ≃ {a : Occ V // stamp a = i} where
  toFun u := ⟨atSlot i.1 i.2 u u.isLt,rfl⟩
  invFun u := ⟨u.val.index, by
    conv_rhs => rw [← u.property]
    exact u.val.legit⟩
  left_inv _ := rfl
  right_inv p := Subtype.ext <| Occ.ext (congr_arg Prod.fst p.property).symm (congr_arg Prod.snd p.property).symm rfl

lemma reshuffle (g : Occ W → Slot G) :
    let V (i : Fin n) := ∑ a ∈ stationed W i, Finsupp.single (g a) 1
    ∃ e : Occ W ≃ Occ V, (∀ p, (e p).label = p.label) ∧ (∀ p, (e p).probe = g p) := by
  classical
  intro V
  let f (x : Occ W) := (x.label,g x)
  have he (i) : Fintype.card {a // f a = i} = V i.1 i.2 := by
    simp only [V, Finsupp.finsetSum_apply, Finsupp.single_apply,Fintype.card_subtype, Finset.sum_boole]
    congr 1
    ext x; simp [stationed,Prod.ext_iff,f]
  let e (i) := ((Fintype.equivFin _).trans (finCongr (he i))).trans (stampEquiv i (V := V))
  exact ⟨Equiv.ofFiberEquiv e,fun p => congr_arg (fun x : Fin n × Slot G => x.1) (Equiv.ofFiberEquiv_map e p), fun p => congr_arg (fun x : Fin n × Slot G => x.2) (Equiv.ofFiberEquiv_map e p)⟩

lemma raw_formula (g : Occ W → Slot G) (x : Points n) :
    moment G x (fun i => ∏ a ∈ stationed W i, MvPolynomial.X (g a)) =
      ∑ P : Matching W, ∏ a ∈ corners P, Wick.entry (g a) (g (partner P a)) (x a.label) (x (partner P a).label) := by
  classical
  let V (i : Fin n) := ∑ a ∈ stationed W i, Finsupp.single (g a) 1
  have he i : monBasis G (V i) = ∏ a ∈ stationed W i, MvPolynomial.X (g a) := by
    change MvPolynomial.monomial (V i) 1 = _
    unfold V; rw [MvPolynomial.monomial_sum_one]; rfl
  obtain ⟨e,h,hg⟩ := reshuffle g
  obtain ⟨L,hL⟩ := induced (W := W) (Y := V) id injective_id (e := e) h
  simp_rw [← he, moment_basis,monomial]
  symm
  refine Fintype.sum_equiv L _ _ fun P => ?_
  have hh a := show partner (L P) (e a) = _ from (hL P a).symm
  have hv a : e a ∈ corners (L P) ↔ a ∈ corners P := by simp [corners,hh,h]
  refine Finset.prod_bij (fun a _ => e a) (fun a ha => (hv a).mpr ha) (fun _ _ _ _ h => e.injective h)
    (fun a ha => ⟨e.symm a,(hv _).mp (by simpa using ha),e.apply_symm_apply a⟩) (fun a _ => ?_)
  simp only [edge,hh,h,hg]

lemma stationed_update [DecidableEq (Occ W)] (u : Occ W → Vars G) (v : Occ W) (x : Vars G) :
    (fun i => ∏ a ∈ stationed W i, ordinary G (update u v x a)) =
      update (fun i => ∏ a ∈ stationed W i, ordinary G (u a)) v.label
        (ordinary G x * ∏ a ∈ (stationed W v.label).erase v, ordinary G (u a)) := by
  funext i
  by_cases hi : i=v.label
  · subst i
    rw [update_self, ← Finset.mul_prod_erase _ _ (show v ∈ stationed W v.label by simp [stationed]), update_self]
    congr 1; exact Finset.prod_congr rfl fun a ha => by rw [update_of_ne (Finset.ne_of_mem_erase ha)]
  rw [update_of_ne hi]; exact Finset.prod_congr rfl fun a ha => by
    rw [update_of_ne (fun hav => hi (Finset.mem_filter.mp (hav ▸ ha) |>.2.symm))]

def polarized (x : Points n) (W : Powers G n) : MultilinearMap ℂ (fun _ : Occ W => Vars G) ℂ where
  toFun u := moment G x fun i => ∏ a ∈ stationed W i, ordinary G (u a)
  map_update_add' u i a b := by
    rw [stationed_update u i,stationed_update u i a,stationed_update u i b,map_add,add_mul,MultilinearMap.map_update_add]
  map_update_smul' u i c b := by rw [stationed_update u i,stationed_update u i b,map_smul,smul_mul_assoc,MultilinearMap.map_update_smul]

def edged (P : Matching W) (B : Occ W → Occ W → Vars G →ₗ[ℂ] Vars G →ₗ[ℂ] ℂ) (u : Occ W → Vars G) :=
  ∏ v ∈ corners P, B v (partner P v) (u v) (u (partner P v))

lemma edged_linear [DecidableEq (Occ W)] (P : Matching W) (B : Occ W → Occ W → Vars G →ₗ[ℂ] Vars G →ₗ[ℂ] ℂ)
    (u : Occ W → Vars G) (v : Occ W) : ∃ f : Vars G →ₗ[ℂ] ℂ, ∀ x : Vars G, edged P B (update u v x) = f x := by
  let s := partner P
  let a := toCorner P v
  have hw := different P a
  have hv := inside P v
  let z := ∏ i ∈ (corners P).erase a, B i (s i) (u i) (u (s i))
  have he (x : Vars G) : edged P B (update u v x) = z * B a (s a) ((update u v x) a) ((update u v x) (s a)) := by
    unfold edged
    rw [← Finset.prod_erase_mul _ _ hv]
    congr 1; refine Finset.prod_congr rfl fun i hi => ?_
    have hl : toCorner P i ≠ toCorner P v := by rw [fixed P (Finset.mem_of_mem_erase hi)]; exact Finset.ne_of_mem_erase hi
    rw [update_of_ne (fun h => hl (congr_arg _ h)), update_of_ne (fun h => hl ((canonical P i).symm.trans (congr_arg _ h)))]
  by_cases ha : a = v
  · refine ⟨z • (B a (s a)).flip (u (s a)), fun x => ?_⟩
    have hm : s a ≠ v := fun h => hw (congr_arg _ (h.trans ha.symm))
    rw [he,update_of_ne hm,ha,update_self]; rfl
  have H : s a = v := turn P v ▸ congr_arg s (show a = s v by revert ha; unfold a toCorner; split <;> simp [s])
  exact ⟨z • B a (s a) (u a), fun x => by rw [he,update_of_ne ha, H,update_self]; rfl⟩

def edgedMap (P : Matching W) (B : Occ W → Occ W → Vars G →ₗ[ℂ] Vars G →ₗ[ℂ] ℂ) : MultilinearMap ℂ (fun _ : Occ W => Vars G) ℂ where
  toFun u := edged P B u
  map_update_add' u i a b := by obtain ⟨L,h⟩ := edged_linear P B u i; simp_rw [h,map_add]
  map_update_smul' u i c a := by obtain ⟨L,h⟩ := edged_linear P B u i; simp_rw [h,L.map_smul]

/-- Wick moment evaluation on variables (arbitrary complex linear combinations
across colors and orders) with the prescribed pattern of slots. -/
theorem linear_substitution (u : Occ W → Vars G) (x : Points n) :
    moment G x (fun i => ∏ a ∈ stationed W i, ordinary G (u a)) = ∑ P : Matching W, ∏ a ∈ corners P,
      tensorMatrix (fun i j => Wick.entry i j (x a.label) (x (partner P a).label)) (u a) (u (partner P a)) := by
  let B (a b : Occ W) := tensorMatrix (fun i j : Slot G => Wick.entry i j (x a.label) (x b.label))
  have he : polarized x W = ∑ P : Matching W, edgedMap P B := by
    apply Module.Basis.ext_multilinear (fun _ => Finsupp.basisSingleOne)
    intro g
    rw [sum_apply]
    change moment G x (fun i => ∏ a ∈ stationed W i, ordinary G (e (g a))) = ∑ P : Matching W, edged P B _
    simp only [edged,B,show ⇑(Finsupp.basisSingleOne : Module.Basis (Slot G) ℂ (Vars G)) = e from rfl,tensorMatrix_e,ordinary_e]
    exact raw_formula g x
  exact (MultilinearMap.congr_fun he u).trans (sum_apply ..)

open Classical in
lemma stationed_powers (W : Powers G n) (i) : (∏ a ∈ stationed W i, MvPolynomial.X (Occ.probe a)) = monBasis G (W i) := by
  change _ = MvPolynomial.monomial (W i) 1
  have he : W i = ∑ a ∈ stationed W i, Finsupp.single a.probe 1 := by
    ext j
    rw [Finsupp.finsetSum_apply]
    have h := Fintype.card_congr (stampEquiv (V := W) (i,j))
    simpa [Finsupp.single_apply, Fintype.card_subtype,stamp,Prod.ext_iff,stationed,Finset.filter_filter] using h
  rw [he,MvPolynomial.monomial_sum_one]; rfl
end YM.Push.FiniteDetection.Free
