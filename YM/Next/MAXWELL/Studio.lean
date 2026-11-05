import YM.Euclid.Pairing
import YM.Next.MAXWELL.Covariance
import YM.Next.MAXWELL.Gram


/-!
# Combine the two positive-half Wick words

Raw reflection formula. Arity and polynomial degrees unrestricted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis Table.Pairing Wick Factorization Fock
open scoped ContDiff Topology BigOperators ComplexOrder
variable {G : Gauge} {m n : ℕ}

def cabinet (a : Axis) (x : Points n) (y : Points m) (p : Fin n → WickPol G) (q : Fin m → WickPol G) :=
  moment G (closedUp a x y) (Fin.append (mirrorBar (Signed.reflect a) ∘ p) q)

private lemma split_ne (a : Fin n) (b : Fin m) : Fin.castAdd m a ≠ Fin.natAdd n b := by
  intro h
  have he := Fin.ext_iff.mp h; simp only [Fin.val_castAdd,Fin.val_natAdd] at he; omega

private theorem first [DecidableEq (Fin n)] (p : Fin n → WickPol G) (q : Fin m → WickPol G) (A : WickPol G) (i) (a : Axis) :
    let R := mirrorBar (G := G) (Signed.reflect a)
    Fin.append (R ∘ update p i A) q = update (Fin.append (R ∘ p) q) (Fin.castAdd m i) (R A) := by
  intro R
  ext1 j; refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · by_cases h : i=j <;> simp_all [Function.update,Ne.symm]
  rw [update_of_ne]
  · simp
  exact Ne.symm (split_ne _ _)

private theorem rear [DecidableEq (Fin m)] (p : Fin n → WickPol G) (q : Fin m → WickPol G) (A : WickPol G) (i) :
    Fin.append p (update q i A) = update (Fin.append p q) (Fin.natAdd n i) A := by
  ext1 j; refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [update_of_ne (split_ne _ _)]; simp
  by_cases h : i=j <;> simp_all [Function.update,Ne.symm]

def towerR (a : Axis) (x : Points n) (y : Points m) (p : Fin n → WickPol G) :
    MultilinearMap ℂ (fun _ : Fin m => WickPol G) ℂ where
  toFun q := cabinet a x y p q
  map_update_add' f k u v := by
    unfold cabinet
    simp_rw [rear,MultilinearMap.map_update_add]
  map_update_smul' f k c q := by
    unfold cabinet
    simp_rw [rear,MultilinearMap.map_update_smul]

def towerL (a : Axis) (x : Points n) (y : Points m) (q : Fin m → WickPol G) :
    MultilinearMap ℂ (fun _ : Fin n => WickPol G) ℂ where
  toFun p := star (cabinet a x y p q)
  map_update_add' f k u v := by
    unfold cabinet
    simp_rw [first f q (u+v) k a,first f q u k a, first f q v k a,map_add,
      MultilinearMap.map_update_add,star_add]
  map_update_smul' f k c p := by
    unfold cabinet
    simp_rw [first f q (c • p) k a,first f q p k a,map_smulₛₗ,MultilinearMap.map_update_smul]; simp


lemma cabinetL (a : Axis) (x : Points n) (y : Points m) (p : Fin n → WickPol G) (q : Fin m → WickPol G) :
    towerL a x y q p=star (cabinet a x y p q) := rfl

lemma mirror_bag {ι : Type*} (A : Ortho) (u : List ι) (T : ι → Factor G) (r : ι → Fin n) :
    mirrorBar A ∘ bag r T u = bag r (orientFactor A ∘ T) u := by
  ext1 i
  change reflectPol A (realForm _) = _; rw [real_bag,orient_bag]

/-- bag-packing commutes with embedding of tables. -/
lemma bag_app {ι κ : Type*} (u : List ι) (v : List κ) (s : ι → Fin n) (t : κ → Fin m)
    (P : ι → Factor G) (Q : κ → Factor G) :
    Fin.append (bag s P u) (bag t Q v) =
      bag (Sum.elim (Fin.castAdd m ∘ s) (Fin.natAdd n ∘ t)) (Sum.elim P Q)
        (u.map Sum.inl ++ v.map Sum.inr) := by
  ext1 i; refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    simp [bag, List.map_map,Function.comp_def, split_ne,
      Ne.symm (split_ne _ _)]

theorem cabinet_bag {ι κ : Type*} (u : List ι) (v : List κ) (s : ι → Fin n) (t : κ → Fin m)
    (P : ι → Factor G) (Q : κ → Factor G) {x : Points n} {y : Points m}
    (a : Axis) (h : closedUp a x y ∈ conf _) :
    cabinet a x y (bag s P u) (bag t Q v) =
      pairCost linkEntry (u.map (fun i => bottomEntry a (x (s i),P i)) ++ v.map (fun j => (y (t j),Q j))) := by
  rw [cabinet,mirror_bag,bag_app,bag_rec _ _ _ h, List.map_append]
  simp only [List.map_map, Function.comp_def, Sum.elim_inl,Sum.elim_inr,leave,enter]; rfl

section Expand

def gallery {k : ℕ} (p : Fin k → WickPol G) :=
    Fintype.piFinset fun i => ((monBasis G).repr (p i)).support

def arch {k : ℕ} (p : Fin k → WickPol G) (u : Powers G k) := ∏ i : Fin k, (monBasis G).repr (p i) (u i)

theorem cabinet_charges (p : Fin n → WickPol G) (q : Fin m → WickPol G) (a : Axis) (x : Points n) (y : Points m) :
    cabinet a x y p q = ∑ u ∈ gallery p, ∑ v ∈ gallery q, star (arch p u) * arch q v *
      cabinet a x y (fun i => monBasis G (u i)) (fun j => monBasis G (v j)) := by
  have he (p) : cabinet a x y p q = ∑ v ∈ gallery q, arch q v *
      cabinet a x y p (fun j => monBasis G (v j)) := Multilabel.expansion _ (towerR a x y p) q
  have ht := Multilabel.expansion (fun _ => monBasis G) (towerL a x y q) p
  rw [← star_star (cabinet a x y p q),← cabinetL, ht,star_sum];
  apply Finset.sum_congr rfl; intro u _
  rw [cabinetL, smul_eq_mul,star_mul,star_star,he (fun i => monBasis G (u i)),Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by unfold arch; ring
end Expand

/- finite-alphabet positive form for any list of bags (points on one
side past the plane). This even computes aux states for each element.
All basis lift occurrences are genuine upper probes. -/
theorem chambers {ι : Type*} [Fintype ι] (a : Axis) {n : ι → ℕ} (x : (i : ι) → Points (n i))
    (H : ∀ i, Table.Pairing.single (x i) a) (L : (i : ι) → List (Fin (n i) × Factor G)) (c : ι → ℂ) :
    0 ≤ ∑ i, ∑ j, star (c i) * c j * cabinet a (x i) (x j)
      (bag Prod.fst Prod.snd (L i)) (bag Prod.fst Prod.snd (L j)) := by
  classical
  let E (i : ι) := (L i).map (fun p => ((x i p.1, p.2) : Limb G))
  let F := Finset.univ.biUnion fun i => (E i).toFinset
  have he i : ∀ p ∈ E i,p ∈ F := fun p hp => Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,List.mem_toFinset.mpr hp⟩
  let q := fun p : F => (p.val : Limb G)
  let R (i : ι) := (E i).pmap (fun p h => (⟨p,h⟩ : ↥F)) (he i)
  have hs (i) : (R i).map q=E i := by unfold R q; rw [List.map_pmap]; simp
  have hA (i : F) : 0 < (q i).1 a := by
    obtain ⟨i,hi⟩ := i; obtain ⟨j,-,hv⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨s,ha,hk⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    subst i; exact (H j).2 s.1
  obtain ⟨B,hB⟩ := columns a q hA
  let Z := fun i => packet (fun i j : F => linkEntry (q i) (q j))
    (fun (i j : F) => ((B j i:ℝ):ℂ)) (R i)
  have hw i j : cabinet a (x i) (x j) (bag Prod.fst Prod.snd (L i)) (bag Prod.fst Prod.snd (L j)) = form (Z i) (Z j) := by
    rw [cabinet_bag _ _ _ _ _ _ a (Table.Pairing.spans (H i) (H j))]
    have ht : (List.map (fun (p : Fin (n i) × Factor G) => bottomEntry a (x i p.1,p.2)) (L i))=
        (R i).map (bottomEntry a ∘ q) := by rw [← List.map_map, hs]; simp [E,List.map_map,Function.comp_def]
    rw [ht]; rw [show (List.map _ (L j)) = (R j).map q from (hs j).symm]
    exact halves (bottomEntry a ∘ q) q _ _ _ (fun i j => link_ray a _ _) (fun i j => rfl)
      (fun i j => entry_match _ _ _ hB i j hA) _ _
  have hp := form_nonneg (∑ i, c i • Z i)
  simp_rw [form_gather,form_sum,form_rescale,form_scale, ← mul_assoc, ← hw] at hp
  exact hp

/-- Arbitrary polynomial norm. -/
theorem cabinets_positive {ι : Type*} [Fintype ι] (a : Axis) {n : ι → ℕ} (x : (i : ι) → Points (n i))
    (H : ∀ i, Table.Pairing.single (x i) a) (v : (i : ι) → Fin (n i) → WickPol G) (c : ι → ℂ) :
    0 ≤ ∑ i, ∑ j, star (c i) * c j * cabinet a (x i) (x j) (v i) (v j) := by
  classical
  choose L hL using fun i (p : ↥(gallery (v i))) => power_bag p.val
  have hp := chambers a (ι := Sigma fun i => ↥(gallery (v i))) (fun i => x i.1) (fun i => H i.1)
    (fun i => L i.1 i.2) (fun i => c i.1*arch (v i.1) i.2.val)
  simp_rw [hL] at hp
  refine le_of_le_of_eq hp ?_
  rw [Fintype.sum_sigma]; simp_rw [cabinet_charges (v _) (v _) a,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  simp_rw [Fintype.sum_sigma]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
  -- convert the two subtype sums
  rw [← Finset.sum_attach (gallery (v i))];
  apply Finset.sum_congr (show _ = _ from rfl); intro k _
  rw [← Finset.sum_attach (gallery (v j))]
  apply Finset.sum_congr (show _ = _ from rfl); intro r _
  simp only [star_mul]; ring
end YM.Maxwell.Free
