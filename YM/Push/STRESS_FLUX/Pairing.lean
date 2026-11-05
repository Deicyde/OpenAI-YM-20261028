import YM.Bid.Craft
import YM.Push.STRESS_FLUX.Polynomial
import YM.Shift.Breath

/-! Some concrete two-point free detector calculations needed for normalizing the stress.
No positivity or detection assumption about the freeTable. The calculation is on its actual
moments, with no within-site contractions, even when symbols repeat.
-/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux
open Function Set Filter Gauge Maxwell Wick
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace

variable {G : Gauge}
namespace Double
open Occ
private abbrev Two := Fin 2
private def power (p q : Slot G) := Finsupp.single p (1:ℕ) + Finsupp.single q 1
private lemma mon_power (p q : Slot G) : monBasis G (power p q) = MvPolynomial.X p * MvPolynomial.X q := by
  simp [power, monBasis, MvPolynomial.X, MvPolynomial.monomial_mul]

lemma one_monomial (x : Points 1) (p q : Slot G) : moment G x (fun _ => MvPolynomial.X p * MvPolynomial.X q) = 0 := by
  let A : Powers G 1 := fun _ => power p q
  have hp (i) : 0 < A i p := by simp [A, power]
  haveI : IsEmpty (Matching A) := ⟨fun Q => Q.property.2 (atSlot 0 p 0 (hp 0)) (Subsingleton.elim ..)⟩
  rw [← mon_power, moment_basis (fun _ => power p q)]
  change ∑ v : Matching A, graph x v = 0
  exact Fintype.sum_empty _

private def powers (A : Two → Two → Slot G) : Powers G 2 := fun i => power (A i 0) (A i 1)
variable (A : Two → Two → Slot G)
private def first (i : Two) : Occ (powers A) := atSlot i (A i 0) 0 (by simp [powers,power])
private def second (i : Two) : Occ (powers A) := atSlot i (A i 1) (if A i 0=A i 1 then 1 else 0) (by split_ifs <;> simp_all [powers,power])
private def seek (v : Two × Two) : Occ (powers A) := ![first A v.1, second A v.1] v.2
@[simp] private theorem seek_label (i j) : (seek A (i,j)).label=i := by fin_cases j <;> rfl
@[simp] private theorem seek_probe (i j) : (seek A (i,j)).probe=A i j := by fin_cases j <;> rfl

private def spot : Two × Two ≃ Occ (powers A) := Equiv.ofBijective (seek A) <| by
  constructor
  · rintro ⟨i,j⟩ ⟨k,l⟩ h
    have hr := congr_arg Occ.label h; simp only [seek_label] at hr; subst k; congr 1
    have he : seek A (i,0) ≠ seek A (i,1) := fun e => by
      have hh := congr_arg Occ.probe e; simp only [seek_probe] at hh
      have hi := congr_arg Occ.index e
      change 0 = (if A i 0=A i 1 then 1 else 0) at hi; simp [hh] at hi
    fin_cases j <;> fin_cases l <;> first | rfl | exact (he h).elim | exact (he h.symm).elim
  intro v
  have hi := v.legit
  simp only [powers,power,Finsupp.add_apply,Finsupp.single_apply] at hi
  split_ifs at hi with h₁ h₂ h₂
  · rcases show v.index=0 ∨ v.index=1 by omega with hv|hv
    · exact ⟨(v.label,0), Occ.ext rfl h₁ hv.symm⟩
    refine ⟨(v.label,1), Occ.ext rfl h₂ ?_⟩
    change (if A _ 0 = A _ 1 then 1 else 0)=v.index
    rw [hv,if_pos (h₁.trans h₂.symm)]
  · exact ⟨(v.label,0), Occ.ext rfl h₁ (show 0 = v.index by omega)⟩
  · refine ⟨(v.label,1), Occ.ext rfl h₂ ?_⟩
    change (if A _ 0 = A _ 1 then 1 else 0)=v.index
    rw [if_neg (by rwa [h₂])]; omega
  omega

@[simp] private lemma spot_label (i j) : (spot A (i,j)).label=i := seek_label ..
@[simp] private lemma spot_probe (i j) : (spot A (i,j)).probe=A i j := seek_probe ..

/-- Match across the two positions by a permutation of copies. -/
private def maps (s : Equiv.Perm Two) : Equiv.Perm (Two × Two) := Involutive.toPerm
    (fun v => if v.1=0 then (1,s v.2) else (0,s.symm v.2)) (by rintro ⟨i,j⟩; fin_cases i <;> simp)
private def joined (s : Equiv.Perm Two) : Matching (powers A) := ⟨(spot A).permCongr (maps s), by
  have he : maps s * maps s = 1 := by ext ⟨i,j⟩ <;> fin_cases i <;> simp [Equiv.Perm.mul_apply, maps]
  constructor
  · ext1 v; obtain ⟨z,rfl⟩ := (spot A).surjective v
    simpa [Equiv.Perm.mul_apply] using DFunLike.congr_fun he z
  intro v; obtain ⟨⟨i,j⟩,rfl⟩ := (spot A).surjective v
  fin_cases i <;> simp [maps] ⟩

private lemma joined_first (s : Equiv.Perm Two) (j) : (joined A s).val (spot A (0,j)) = spot A (1,s j) := by simp [joined,maps]

private lemma matching_ext {P Q : Matching (powers A)} (h : ∀ i, partner P (spot A (0,i)) = partner Q (spot A (0,i))) : P=Q := by
  apply Subtype.ext; apply Equiv.ext; intro v
  have he {v} (hz : v.label=0) : partner P v = partner Q v := by
    obtain ⟨⟨i,j⟩,rfl⟩ := (spot A).surjective v
    simp only [spot_label] at hz; subst i; apply h
  rcases eq_or_ne v.label 0 with ht|ht; exact he ht
  have hi : (partner P v).label=0 := by have := different P v; omega
  apply (partner Q).injective (a₁:=partner P v) (a₂:=partner Q v)
  rw [← he hi, turn,turn]

private def bij : Equiv.Perm Two ≃ Matching (powers A) := Equiv.ofBijective (joined A) <| by
  constructor
  · intro s t h
    ext1 i
    have he : (spot A (1,s i)) = spot A (1,t i) := by rw [← joined_first, ← joined_first,h]
    exact congr_arg Prod.snd ((spot A).injective he)
  intro P
  have he (i : Two) : ∃ j : Two, partner P (spot A (0,i)) = spot A (1,j) := by
    obtain ⟨⟨a,j⟩,h⟩ := (spot A).surjective (partner P (spot A (0,i)))
    have hi := different P (spot A (0,i)); rw [← h,spot_label,spot_label] at hi
    have ha := Fin.eq_one_of_ne_zero a hi
    subst a; exact ⟨j,h.symm⟩
  choose p hp using he
  have hi : Injective p := fun i j h => by
    exact congr_arg Prod.snd ((spot A).injective ((partner P).injective (a₁:=spot A (0,i)) (a₂:=spot A (0,j)) (by rw [hp, hp, h])))
  let s := Equiv.ofBijective p ⟨hi,Finite.injective_iff_surjective.mp hi⟩
  refine ⟨s, matching_ext A (fun i => (joined_first A s i).trans (hp i).symm)⟩

lemma two_monomial (x : Points 2) : moment G x (fun i => MvPolynomial.X (A i 0) * MvPolynomial.X (A i 1)) =
    ∑ s : Equiv.Perm Two, ∏ k : Two, entry (A 0 k) (A 1 (s k)) (x 0) (x 1) := by
  simp_rw [← mon_power]; change moment G x (fun i => monBasis G (powers A i)) = _; rw [moment_basis (W:=powers A)]; unfold monomial
  rw [← Equiv.sum_comp (bij A)]; symm; refine Finset.sum_congr rfl fun s _ => ?_
  let P := joined A s
  change _ = ∏ p ∈ corners P, edge x p (partner P p)
  refine Finset.prod_bij (fun k _ => spot A (0,k)) (fun k _ => ?_) (fun i _ j _ he => congr_arg Prod.snd ((spot A).injective he)) ?_ (fun i _ => ?_)
  · simp [corners,P,partner,joined_first]
  · intro p hp; obtain ⟨⟨i,j⟩,rfl⟩ := (spot A).surjective p
    simp only [corners,Finset.mem_filter,Finset.mem_univ,true_and,spot_label] at hp
    have hi : i=0 := by
      by_contra! h; rw [Fin.eq_one_of_ne_zero i h] at hp
      have ht (i : Fin 2) : ¬ 1 < i := by decide +revert
      exact ht _ hp
    subst i; exact ⟨j, Finset.mem_univ _,rfl⟩
  simp [edge,P,partner,joined_first]

lemma concrete_monomial (x : Points 2) (p q r s : Slot G) : moment G x ![MvPolynomial.X p * MvPolynomial.X q, MvPolynomial.X r * MvPolynomial.X s] =
    entry p r (x 0) (x 1) * entry q s (x 0) (x 1) + entry p s (x 0) (x 1) * entry q r (x 0) (x 1) := by
  classical
  have he := two_monomial ![![p,q],![r,s]] x
  have hp : (Finset.univ : Finset (Equiv.Perm Two)) = {1, Equiv.swap 0 1} := by
    ext1 i; suffices i=1 ∨ i=Equiv.swap 0 1 by simpa
    have ht := i.injective.ne (show 0 ≠ (1:Two) by decide)
    by_cases hq : i 0=0
    · left; rw [hq] at ht; exact Equiv.ext (Fin.forall_fin_two.mpr ⟨hq, Fin.eq_one_of_ne_zero _ ht.symm⟩)
    right; rw [Fin.eq_one_of_ne_zero _ hq] at ht
    have hv (i : Fin 2) : 1 ≠ i → i=0 := by decide +revert
    exact Equiv.ext (Fin.forall_fin_two.mpr (by simp [Fin.eq_one_of_ne_zero _ hq, hv _ ht]))
  simp only [hp, Finset.sum_insert (show 1∉({Equiv.swap (0:Two) 1} : Finset (Equiv.Perm Two)) by decide),Finset.sum_singleton] at he
  simp only [show (fun i : Fin 2 => MvPolynomial.X (![![p,q],![r,s]] i 0) * MvPolynomial.X (![![p,q],![r,s]] i 1)) =
      (![MvPolynomial.X p * MvPolynomial.X q, MvPolynomial.X r * MvPolynomial.X s] : _ → WickPol G) from funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩),
    Fin.prod_univ_two,Equiv.swap_apply_left,Equiv.swap_apply_right,Equiv.Perm.one_apply] at he
  exact he
end Double

def onePoint (x : Points 1) : WickPol G →ₗ[ℂ] ℂ := (moment G x).toLinearMap (fun _ => 0) 0
lemma onePoint_at (x : Points 1) (p : WickPol G) : onePoint x p = moment G x (fun _ => p) := by
  unfold onePoint; rw [MultilinearMap.toLinearMap_apply]; congr! 1; funext i; fin_cases i; simp

def head (x : Points 2) (q : WickPol G) : WickPol G →ₗ[ℂ] ℂ := (moment G x).toLinearMap ![0,q] 0
def tail (x : Points 2) (p : WickPol G) : WickPol G →ₗ[ℂ] ℂ := (moment G x).toLinearMap ![p,0] 1
lemma head_at (x : Points 2) (p q : WickPol G) : head x q p = moment G x ![p,q] := by unfold head; rw [MultilinearMap.toLinearMap_apply]; congr! 1; funext i; fin_cases i <;> simp
lemma tail_at (x : Points 2) (p q : WickPol G) : tail x p q = moment G x ![p,q] := by unfold tail; rw [MultilinearMap.toLinearMap_apply]; congr! 1; funext i; fin_cases i <;> simp

private abbrev Leg (G : Gauge) := Maxwell.Probe G 0
def product (G : Gauge) : Leg G →ₗ[ℝ] Leg G →ₗ[ℝ] WickPol G :=
  let F : Leg G →ₗ[ℝ] WickPol G := {
    toFun := symbol 0
    map_add' p q := equalPol _ _ (by intro y; simp [symbol_test])
    map_smul' r p := equalPol _ _ (by
      intro y; rw [show ∀ u : WickPol G, Maxwell.probe y ((RingHom.id ℝ) r • u) = r • Maxwell.probe y u from
        fun u => ((Maxwell.probe y).toLinearMap.restrictScalars ℝ).map_smul r u]
      simp [symbol_test,Complex.real_smul]) }
  (LinearMap.mul ℝ _).compl₁₂ F F

lemma product_eq (p q : Leg G) : product G p q = symbol 0 p * symbol 0 q := rfl

private abbrev idx (G : Gauge) := Fin (legDim G 0)
private def coordLeg (G : Gauge) (i : idx G) := coordinateLeg (G:=G) ⟨0,i⟩
private lemma onCoords {V : Type*} [AddCommGroup V] [Module ℝ V] (A B : Leg G →ₗ[ℝ] Leg G →ₗ[ℝ] V)
    (h : ∀ i j : idx G, A (coordLeg G i) (coordLeg G j) = B (coordLeg G i) (coordLeg G j)) : A=B := by
  let b := (frame G 0).dualBasis
  have he (i) : coordLeg G i = b i := LinearMap.ext (fun s => (Module.Basis.dualBasis_apply (frame G 0) i s).symm)
  refine b.ext fun i => b.ext fun j => ?_
  rw [← he, ← he, h]

private lemma product_basis (i j : idx G) : product G (coordLeg G i) (coordLeg G j) =
    MvPolynomial.X ⟨0,i⟩ * MvPolynomial.X ⟨0,j⟩ := by rw [product_eq]; exact congr_arg₂ (·*·) (symbol_coordinate (G:=G) ⟨0,i⟩) (symbol_coordinate (G:=G) ⟨0,j⟩)

def pairingC {x : E4} (hx : x ≠ 0) : Leg G →ₗ[ℝ] Leg G →ₗ[ℝ] ℂ :=
  (pairing hx).compr₂ Complex.ofRealCLM.toLinearMap
private lemma pairingC_entry {x : Points 2} (hx : x 0 ≠ x 1) (i j : idx G) :
    pairingC (sub_ne_zero.mpr hx) (coordLeg G i) (coordLeg G j) = entry ⟨0,i⟩ ⟨0,j⟩ (x 0) (x 1) := rfl

theorem onePoint_prod (p q : Leg G) (x : Points 1) : onePoint x (product G p q) = 0 := by
  let L := (product G).compr₂ ((onePoint x).restrictScalars ℝ)
  have he : L=0 := onCoords _ _ (fun i j => show onePoint x (product G _ _) = 0 by
    rw [product_basis, onePoint_at]; exact Double.one_monomial x _ _)
  exact congr_arg (fun L : Leg G →ₗ[ℝ] Leg G →ₗ[ℝ] ℂ => L p q) he

private def bilinearSquare {V : Type*} [AddCommGroup V] [Module ℝ V] (r s : V →ₗ[ℝ] ℂ) : V →ₗ[ℝ] V →ₗ[ℝ] ℂ :=
    (LinearMap.mul ℝ ℂ).compl₁₂ r s + (LinearMap.mul ℝ ℂ).compl₁₂ s r

lemma twoPoint_prod (p q r s : Leg G) (x : Points 2) (hx : x 0 ≠ x 1) :
    let K := pairingC (G:=G) (sub_ne_zero.mpr hx)
    head x (product G r s) (product G p q) = K p r * K q s + K p s * K q r := by
  intro K
  have he (r s p q : idx G) : head x (product G (coordLeg G r) (coordLeg G s)) (product G (coordLeg G p) (coordLeg G q)) =
      bilinearSquare (K.flip (coordLeg G r)) (K.flip (coordLeg G s)) (coordLeg G p) (coordLeg G q) := by
    rw [product_basis,product_basis,head_at,Double.concrete_monomial]; simp only [← pairingC_entry hx]; rfl
  have hp (i j : idx G) : tail x (product G p q) (product G (coordLeg G i) (coordLeg G j)) =
      bilinearSquare (K p) (K q) (coordLeg G i) (coordLeg G j) := by
    have h := onCoords ((product G).compr₂ ((head x (product G (coordLeg G i) (coordLeg G j))).restrictScalars ℝ)) _ (he i j)
    rw [tail_at, ← head_at]; exact congr_arg (fun L : Leg G →ₗ[ℝ] Leg G →ₗ[ℝ] ℂ => L p q) h |>.trans (by dsimp [bilinearSquare]; ring)
  rw [head_at, ← tail_at]
  have h := congr_arg (fun L : Leg G →ₗ[ℝ] Leg G →ₗ[ℝ] ℂ => L r s)
    (onCoords ((product G).compr₂ ((tail x (product G p q)).restrictScalars ℝ)) _ hp)
  exact h.trans (by dsimp [bilinearSquare]; ring)

/-- Test by literal color-summed curvature products. -/
def fieldLeg (G : Gauge) (c : G.ColorIndex) (i j : Axis) : Leg G := constrain (Maxwell.fromF G (fun _ => 0) c i j)
lemma reduce_pair (a b i j : Axis) : reduceEq (pair G a b i j).val = ∑ c, product G (fieldLeg G c a b) (fieldLeg G c i j) := by
  apply Maxwell.equalPol
  intro X
  rw [Maxwell.jet_value, pair_value]
  simp_rw [map_sum,product_eq,map_mul,Maxwell.symbol_test]
  simp_rw [show ∀ a b, curl0 (G:=G) a b (Maxwell.gaugeJet (X 0)) = Tensor.diagonal ((X 0).val a b) 0 from
    fun a b => congr_arg (fun Q : Maxwell.TwoJet G.Color 0 => Tensor.diagonal (Q a b) 0) (Maxwell.match_leg (X 0)),
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct, Complex.ofReal_sum,Complex.ofReal_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm ..

lemma propagator {z : E4} (hz : z ≠ 0) (c d : G.ColorIndex) (a b i j : Axis) :
    pairingC hz (fieldLeg G c a b) (fieldLeg G d i j) = if c=d then (bareCurl a b i j z : ℂ) else 0 := by
  unfold fieldLeg
  change (↑(pairing hz _ _) : ℂ) = _
  rw [raw_mixed (j:=0) (l:=0) _ _ _ _ _ _ _ _ hz]; split_ifs <;> simp [Tensor.coeff]

def chains (z : E4) (a b c d i j k l : Axis) := bareCurl a b i j z * bareCurl c d k l z + bareCurl a b k l z * bareCurl c d i j z
lemma vacuum_pair (a b c d : Axis) (x : Points 1) : onePoint x (reduceEq (pair G a b c d).val) = 0 := by rw [reduce_pair]; simp [onePoint_prod]
lemma chains_read (G : Gauge) {x : Points 2} (hx : x 0 ≠ x 1) (a b c d i j k l : Axis) :
    head x (reduceEq (pair G i j k l).val) (reduceEq (pair G a b c d).val) = G.lieDim * (chains (x 0-x 1) a b c d i j k l : ℂ) := by
  rw [reduce_pair,reduce_pair,map_sum]; simp_rw [head_at,← tail_at,map_sum,tail_at,← head_at,twoPoint_prod _ _ _ _ x hx]
  simp only [propagator]; simp +contextual [chains, ColorIndex, Finset.sum_add_distrib]; ring
end YM.StressFlux
