import YM.Euclid.Words
import YM.Next.MAXWELL.House
import YM.Next.MAXWELL.Pulls



/-! # Equivariance on Wick moments, actual arities -/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Function Set Filter Tensor Analysis Wick
open scoped Topology ContDiff BigOperators

variable {G : Gauge} {j n m : ℕ}

/-- List version of the polynomial basis expansion. -/
lemma mon_list {σ : Type*} (w : σ →₀ ℕ) : ∃ L : List σ,
    (MvPolynomial.basisMonomials σ ℂ) w = (L.map (MvPolynomial.X (R:=ℂ))).prod ∧
    (∀ i ∈ L, i ∈ w.support) ∧ L.length = w.sum (fun _ k => k) := by
  classical
  let L := w.toMultiset.toList
  have he : (L : Multiset σ) = w.toMultiset := Multiset.coe_toList _
  refine ⟨L, ?_, ?_, ?_⟩
  · rw [MvPolynomial.coe_basisMonomials]
    suffices h : ∀ p : List σ, MvPolynomial.monomial (Multiset.toFinsupp (p : Multiset σ)) (1:ℂ) =
        (p.map MvPolynomial.X).prod from by simpa [he] using h L
    intro p
    induction p with
    | nil => simp
    | cons a p ih =>
      rw [List.map_cons,List.prod_cons,← ih,MvPolynomial.X,MvPolynomial.monomial_mul]
      simp
      change Multiset.toFinsupp ({a} + (p : Multiset σ)) = _; rw [map_add]; simp
  · intro i hi
    simp [L] at hi; exact Finsupp.mem_support_iff.mpr hi
  exact (show _ from (congr_arg Multiset.card he).trans (Finsupp.card_toMultiset _))

lemma power_bag (p : Powers G n) : ∃ v : List (Fin n × Factor G), bag Prod.fst Prod.snd v = fun i => monBasis G (p i) := by
  classical
  choose L he _ _ using fun i => mon_list (p i)
  let t (i : Fin n) := (L i).map fun s => (i,coordF s)
  have ht (i j) : bag Prod.fst Prod.snd (t i) j = if j=i then monBasis G (p i) else 1 := by
    unfold t; by_cases h : j=i
    · subst j; simpa [bag,letter_coord,List.map_map, Function.comp_def, monBasis] using (he i).symm
    simp [bag,List.map_map, Function.comp_def,h]
  have h (s : Finset (Fin n)) : ∃ v : List (Fin n × Factor G), ∀ j, bag Prod.fst Prod.snd v j=
      if j∈s then monBasis G (p j) else 1 := by
    induction s using Finset.induction_on with
    | empty => exact ⟨[],fun j => by simp [bag]⟩
    | @insert i s hi ih =>
      obtain ⟨v,h⟩ := ih
      refine ⟨t i++v,fun j => ?_⟩
      by_cases H : j=i <;> simp_all [bag_merge]
  obtain ⟨v,hv⟩ := h Finset.univ
  exact ⟨v,funext fun i => by simpa using hv i⟩

def reflectPol (s : Ortho) : WickPol G →ₐ[ℂ] WickPol G :=
  MvPolynomial.aeval fun p : Slot G => symbol p.1 (probeTurn s (coordinateLeg p))

lemma reflects_eval (s : Ortho) (A : TaylorTower G) (p : WickPol G) :
    probe A (reflectPol s p)=probe (fun i => solutionTurn s⁻¹ (A i)) p := by
  suffices h : (probe A).comp (reflectPol s) = probe (fun i => solutionTurn s⁻¹ (A i)) from
    DFunLike.congr_fun h p
  ext i
  rw [AlgHom.comp_apply,reflectPol,MvPolynomial.aeval_X,symbol_test]
  rw [probe,MvPolynomial.aeval_X]; rfl

theorem pol_one (p : WickPol G) : reflectPol 1 p=p := equalPol _ _ (by
  intro A; rw [reflects_eval,inv_one]; simp only [solution_id])

theorem pol_mul (s t : Ortho) (p : WickPol G) : reflectPol (s*t) p=reflectPol s (reflectPol t p) := equalPol _ _ (by
  intro A; simp_rw [reflects_eval,mul_inv_rev,solution_rep])

lemma pulls_label (p : Labels.Label G j) (s : Ortho) :
    observable G j (Labels.tensor s p) = reflectPol s (observable G j p) := by
  apply equalPol
  intro A; rw [reflects_eval]
  change probe _ (reduceEq (Labels.rotated _ _)) = probe _ (reduceEq _)
  rw [jet_value,jet_value,Labels.rotated,Labels.eval_changed]
  apply congr_arg (fun X => Labels.read X p.val)
  funext i; exact gauge_orient s⁻¹ _

lemma reflect_symbol (s : Ortho) (p : Probe G j) : reflectPol s (symbol j p) = symbol j (probeTurn s p) :=
  equalPol _ _ (by intro A; rw [reflects_eval,symbol_test, symbol_test]; rfl)

def realForm : WickPol G →+* WickPol G := MvPolynomial.map (starRingEnd ℂ)

lemma real_eval (p : WickPol G) (A : TaylorTower G) : probe A (realForm p) = star (probe A p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [probe,realForm]
  | add p q hp hq => simp only [map_add,hp,hq,star_add]
  | mul_X p i hp => rw [map_mul,map_mul,map_mul,hp]; simp [probe,realForm]

lemma real_eats (p : Labels.Label G j) :
    observable G j (Labels.realBar p) = realForm (observable G j p) := by
  apply equalPol
  intro A; rw [real_eval]
  change probe _ (reduceEq (Labels.conjPol _)) = star (probe _ (reduceEq _))
  rw [jet_value,jet_value,Labels.conj_value]; rfl

lemma real_symbol (p : Probe G j) : realForm (symbol j p)=symbol j p :=
  equalPol _ _ (by intro A; rw [real_eval,symbol_test]; simp)

def mirrorBar (s : Ortho) : WickPol G →ₛₗ[starRingEnd ℂ] WickPol G where
  toFun p := reflectPol s (realForm p)
  map_add' _ _ := by simp
  map_smul' z p := by
    simp_rw [realForm, ← MvPolynomial.C_mul',map_mul]
    simp

def orientFactor (s : Ortho) (p : Factor G) : Factor G := ⟨p.1,probeTurn s p.2⟩

lemma orient_letter (s : Ortho) (p : Factor G) : reflectPol s (letter p) = letter (orientFactor s p) := reflect_symbol _ _

lemma orient_bag (s : Ortho) {ι α : Type*} [DecidableEq α] (q : ι → α) (L : ι → Factor G) (p : List ι) (i : α) :
    reflectPol s (bag q L p i) = bag q (orientFactor s ∘ L) p i := by
  induction p with
  | nil => exact map_one _
  | cons a p ih => rw [bag_cons,map_mul,ih,bag_cons]; split_ifs <;> simp [orient_letter]

lemma real_bag {ι α : Type*} [DecidableEq α] (q : ι → α) (L : ι → Factor G) (p : List ι) (i : α) :
    realForm (bag q L p i) = bag q L p i := by
  induction p with
  | nil => exact map_one _
  | cons a p ih => rw [bag_cons,map_mul,ih]; split_ifs
                   · rw [letter,real_symbol]
                   simp

lemma moment_rotation (x : Points n) (H : x ∈ conf n) (v : Fin n → WickPol G) (s : Ortho) :
    moment G (Points.move s x) (fun i => reflectPol s (v i)) = moment G x v := by
  classical
  let L := (moment G (Points.move s x)).compLinearMap (fun _ => (reflectPol s).toLinearMap)
  change L v = _
  suffices he : L = moment G x from DFunLike.congr_fun he v
  apply Module.Basis.ext_multilinear (fun _ => monBasis G)
  intro V
  obtain ⟨u, hu⟩ := power_bag V
  rw [← hu]
  change moment G (Points.move s x) (fun i => reflectPol s (bag Prod.fst Prod.snd u i)) = _
  simp_rw [orient_bag]
  rw [show (fun i => bag Prod.fst (orientFactor s ∘ Prod.snd) u i) = _ from rfl,
    bag_rec Prod.fst _ u (Points.move_in s H),bag_rec Prod.fst _ u H,pair_transfer,pair_transfer]
  congr 1; funext a b
  by_cases hv : x a.1=x b.1
  · simp only [Points.move_coord,hv,link_zero]
  simp only [Points.move_coord, Function.comp_apply,link_eq _ _ _ _ hv,
    link_eq _ _ _ _ ((Ortho.move_injective s).ne hv),orientFactor,K_orientation _ _ _ hv]

lemma moment_real (x : Points n) (_H : x ∈ conf n) (v : Fin n → WickPol G) :
    moment G x (fun i => realForm (v i)) = star (moment G x v) := by
  let L : MultilinearMap ℂ (fun _ : Fin n => WickPol G) ℂ :=
    { toFun q := star (moment G x (mirrorBar 1 ∘ q))
      map_update_add' w i a b := by
        have hm A : mirrorBar 1 ∘ update w i A = update (mirrorBar 1 ∘ w) i (mirrorBar 1 A) := by
          funext j; by_cases H : j=i <;> simp_all
        simp_rw [hm,map_add,MultilinearMap.map_update_add,star_add]
      map_update_smul' w i z a := by
        have hm A : mirrorBar 1 ∘ update w i A = update (mirrorBar 1 ∘ w) i (mirrorBar 1 A) := by
          funext j; by_cases H : j=i <;> simp_all
        simp_rw [hm,map_smulₛₗ, MultilinearMap.map_update_smul]; simp }
  have he : L = moment G x := by
    classical
    apply Module.Basis.ext_multilinear (fun _ => monBasis G)
    intro V
    obtain ⟨u,hu⟩ := power_bag V
    rw [← hu]; change star (moment G x (mirrorBar 1 ∘ _)) = _
    rw [show mirrorBar 1 ∘ bag Prod.fst Prod.snd u = bag Prod.fst Prod.snd u from
      funext fun i => (pol_one _).trans (real_bag ..), hu, moment_basis]
    unfold monomial Occ.graph Occ.edge entry
    simp
  apply star_injective; rw [star_star]
  have h : L v = moment G x v := he ▸ rfl
  change star (moment G x (mirrorBar 1 ∘ v))= _ at h
  rw [show mirrorBar 1 ∘ v = fun i => realForm (v i) from funext fun i => pol_one _] at h
  exact h

lemma moment_across (x : Points n) (p : Fin n → WickPol G) (t : E4) : moment G (Points.across t x) p = moment G x p := by
  classical
  rw [sumFormula,sumFormula]; apply Finset.sum_congr rfl; intro i _; congr 1
  unfold monomial Occ.graph Occ.edge entry; simp

end YM.Maxwell.Free
