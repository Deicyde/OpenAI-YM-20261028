import YM.Maxwell.Wick

/-! Explicit two-leg cross pairings for the *actual* Wick moment. In particular
handles all multiplicities when slots coincide. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Maxwell Wick Wick.Occ Function Set
variable {G : Gauge}

-- Use a literal two by two grid to model occurrences, whether probes repeat or not.
private abbrev T2 := Fin 2
private abbrev Deck (G : Gauge) := T2 → T2 → Slot G
private abbrev Grid2 := T2 × T2

private def power (A : Deck G) : Powers G 2 := fun i =>
  Finsupp.single (A i 0) 1 + Finsupp.single (A i 1) 1

private lemma two_cases (i : T2) : i=0 ∨ i=1 := by fin_cases i <;> decide

private def into (A : Deck G) (u : Grid2) : Occ (power A) := by
  classical
  exact if u.2=0 then atSlot u.1 (A u.1 0) 0 (by simp [power]) else
    atSlot u.1 (A u.1 1) (if A u.1 0 = A u.1 1 then 1 else 0) (by
      simp only [power, Finsupp.add_apply, Finsupp.single_eq_same]; split_ifs with h
      · simp [h]
      exact Nat.zero_lt_succ _)

@[simp] private lemma site_into (A : Deck G) (u : Grid2) : (into A u).label = u.1 := by
  unfold into; split <;> rfl
@[simp] private lemma probe_into (A : Deck G) (u : Grid2) : (into A u).probe = A u.1 u.2 := by
  obtain ⟨i,j⟩ := u; rcases two_cases j with rfl|rfl <;> simp [into]

private lemma occurrence_iso (A : Deck G) : Bijective (into A) := by
  classical
  constructor
  · rintro ⟨i,j⟩ ⟨b,d⟩ h
    have h1 := congr_arg (fun p : Occ (power A) => p.label) h
    have h2 := congr_arg (fun p : Occ (power A) => p.probe) h
    simp only [site_into,probe_into] at h1 h2
    change i=b at h1; subst b
    have h3 := congr_arg (fun p : Occ (power A) => p.index) h
    change A i j = A i d at h2
    rcases two_cases j with rfl|rfl <;> rcases two_cases d with rfl|rfl
    all_goals first | rfl | simp [into,h2] at h3
  · intro p
    let i := p.label
    have hp := p.legit
    change p.index < (power A i) p.probe at hp
    simp only [power,Finsupp.add_apply,Finsupp.single_apply] at hp
    by_cases hr : A i 0 = A i 1
    · rw [← hr] at hp
      by_cases he : A i 0 = p.probe
      · rw [if_pos he] at hp
        have he' := hr ▸ he
        rcases (show p.index = 0 ∨ p.index=1 by omega) with hd|hd
        · exact ⟨(i,0),Occ.ext (site_into ..) (by rw [probe_into]; exact he) (by simp [into, hd])⟩
        exact ⟨(i,1),Occ.ext (site_into ..) (by rw [probe_into]; exact he') (by simp [into,hr,hd])⟩
      rw [if_neg he] at hp; omega
    by_cases he : A i 0 = p.probe
    · rw [if_pos he,if_neg (show A i 1 ≠ p.probe by rw [← he]; exact Ne.symm hr)] at hp
      exact ⟨(i,0),Occ.ext (site_into ..) (by rw [probe_into]; exact he) (by simp [into]; omega)⟩
    by_cases he' : A i 1 = p.probe
    · rw [if_pos he', if_neg he] at hp
      exact ⟨(i,1),Occ.ext (site_into ..) (by rw [probe_into]; exact he') (by simp [into,hr]; omega)⟩
    rw [if_neg he',if_neg he] at hp; omega

-- index the pairings by the two possible matchings from site 0 to 1
section Matching
variable {W : Powers G 2} (e : Grid2 ≃ Occ W) (he : ∀ u : Grid2, (e u).label=u.1)

private def cross2 (s : Equiv.Perm T2) (u : Grid2) : Grid2 :=
    if u.1=0 then (1,s u.2) else (0,s.symm u.2)
@[simp] private lemma cross_left (s : Equiv.Perm T2) (i : T2) : cross2 s (0,i) = (1,s i) := rfl
@[simp] private lemma cross_right (s : Equiv.Perm T2) (i : T2) : cross2 s (1,i) = (0,s.symm i) := rfl
@[simp] private lemma cross_swap (s : Equiv.Perm T2) (u : Grid2) : cross2 s (cross2 s u)=u := by
  obtain ⟨i,j⟩ := u; rcases two_cases i with rfl|rfl <;> simp

private def matchingAt (s : Equiv.Perm T2) : Matching W :=
  ⟨{ toFun p := e (cross2 s (e.symm p))
     invFun p := e (cross2 s (e.symm p))
     left_inv p := by simp
     right_inv p := by simp },by
    constructor
    · ext1 p; change e (cross2 s (e.symm (e (cross2 s (e.symm p))))) = p; simp
    intro p
    obtain ⟨⟨i,j⟩,rfl⟩ := e.surjective p
    change (e (cross2 s (e.symm _))).label ≠ _
    rcases two_cases i with rfl|rfl <;> simp [he]⟩

@[simp] private lemma matching_at (s : Equiv.Perm T2) (u : Grid2) :
    partner (matchingAt e he s) (e u) = e (cross2 s u) := by
  change e (cross2 s (e.symm _)) = _; simp

private lemma give_map : Bijective (matchingAt e he) := by
  classical
  constructor
  · intro s t h
    ext1 i
    have hh := congr_arg (fun v : Matching W => e.symm (partner v (e (0,i)))) h
    simpa using congr_arg Prod.snd hh
  · intro p
    let L (u : Grid2) := e.symm (partner p (e u))
    have hx u : (L u).1 ≠ u.1 := by
      simpa [L, ← he] using different p (e u)
    have hl (u) : L (L u)=u := by simp [L]
    let f (i : T2) := (L (0,i)).2
    let g (i : T2) := (L (1,i)).2
    have hf (i) : L (0,i)=(1,f i) := Prod.ext (by
      have hp := hx (0,i); rcases two_cases (L (0,i)).1 with h|h
      · exact (hp h).elim
      exact h) rfl
    have hg (i) : L (1,i)=(0,g i) := Prod.ext (by
      have hp := hx (1,i); rcases two_cases (L (1,i)).1 with h|h
      · exact h
      exact (hp h).elim) rfl
    have hq i : g (f i)=i := by
      have h := hl (0,i); rw [hf,hg] at h; exact congr_arg Prod.snd h
    have hr i : f (g i)=i := by
      have h := hl (1,i); rw [hg,hf] at h; exact congr_arg Prod.snd h
    let s : Equiv.Perm T2 := ⟨f,g,hq,hr⟩
    refine ⟨s, Subtype.ext ?_⟩
    ext1 v
    obtain ⟨⟨i,j⟩,rfl⟩ := e.surjective v
    change partner (matchingAt e he s) _ = partner p _
    rw [matching_at]; apply e.symm.injective
    change e.symm _=L (i,j); rw [e.symm_apply_apply]
    rcases two_cases i with rfl|rfl
    exacts [(hf j).symm,(hg j).symm]

include he in
private lemma corner_product (x : Points 2) (s : Equiv.Perm T2) :
    ∏ i : T2, edge x (e (0,i)) (e (1,s i)) = graph x (matchingAt e he s) := by
  apply Finset.prod_bij (fun i _ => e (0,i))
  · intro i _; simp [corners, matching_at, he]
  · intro a _ b _ h; exact congr_arg Prod.snd (e.injective h)
  · rintro v hv
    obtain ⟨⟨i,j⟩,rfl⟩ := e.surjective v
    rcases two_cases i with rfl|rfl
    · exact ⟨j,Finset.mem_univ _,rfl⟩
    exfalso; simp [corners,matching_at,he] at hv
  intro a _; simp
end Matching

private lemma perm_sum {Y : Type*} [AddCommMonoid Y] (f : Equiv.Perm T2 → Y) :
    ∑ s, f s = f (Equiv.refl _) + f (Equiv.swap 0 1) := by
  classical
  let L (i : T2) : Equiv.Perm T2 := if i=0 then Equiv.refl _ else Equiv.swap 0 1
  have ht (p q : Equiv.Perm T2) (h : p 0=q 0) : p=q := by
    ext1 i; rcases two_cases i with rfl|rfl
    · exact h
    have hp := p.injective.ne (show (1:T2)≠0 by decide)
    have hq := q.injective.ne (show (1:T2)≠0 by decide)
    rw [h] at hp
    rcases two_cases (p 1) with h|h <;> rcases two_cases (q 1) with w|w <;>
      rcases two_cases (q 0) with z|z <;> simp_all
  have he (i : T2) : L i 0=i := by rcases two_cases i with rfl|rfl <;> simp [L]
  let e : T2 ≃ Equiv.Perm T2 := ⟨L,fun s => s 0,he,fun s => ht _ _ (he _)⟩
  rw [← Equiv.sum_comp e, Fin.sum_univ_two]
  simp [e,L]

private lemma powder (x : Points 2) (A : Deck G) :
    Wick.monomial x (power A) =
      entry (A 0 0) (A 1 0) (x 0) (x 1) * entry (A 0 1) (A 1 1) (x 0) (x 1) +
      entry (A 0 0) (A 1 1) (x 0) (x 1) * entry (A 0 1) (A 1 0) (x 0) (x 1) := by
  let e := Equiv.ofBijective (into A) (occurrence_iso A)
  have he u : (e u).label=u.1 := site_into ..
  have hq u : (e u).probe=A u.1 u.2 := probe_into ..
  rw [Wick.monomial, ← Equiv.sum_comp (Equiv.ofBijective _ (give_map e he))]
  change (∑ s : Equiv.Perm T2, graph x (matchingAt e he s)) = _
  simp_rw [← corner_product e he, Fin.prod_univ_two, edge, he,hq]
  rw [perm_sum]; simp

private lemma moment_grid (x : Points 2) (A : Deck G) :
    moment G x (fun i => MvPolynomial.X (A i 0) * MvPolynomial.X (A i 1)) =
      entry (A 0 0) (A 1 0) (x 0) (x 1) * entry (A 0 1) (A 1 1) (x 0) (x 1) +
      entry (A 0 0) (A 1 1) (x 0) (x 1) * entry (A 0 1) (A 1 0) (x 0) (x 1) := by
  rw [show (fun i => MvPolynomial.X (A i 0) * MvPolynomial.X (R:=ℂ) (A i 1)) = fun i =>
      monBasis G (power A i) by funext i; simp [MvPolynomial.X,MvPolynomial.monomial_mul, monBasis,power], moment_basis]
  exact powder ..


/-- first letter at 0, second at 1. -/
def readings {α : Type*} (p q : α) : Fin 2 → α := Fin.cons (α:=fun _ : Fin 2 => α) p (fun _ => q)
@[simp] theorem read_zero {α : Type*} (p q : α) : readings p q 0=p := rfl
@[simp] theorem read_one {α : Type*} (p q : α) : readings p q 1=q := by
  change readings p q (0:Fin 1).succ = q; simp [readings]

/-- complex bilinear pair polynomial evaluation with pinned positions. -/
def wickTwo (G : Gauge) (x : Points 2) : WickPol G →ₗ[ℂ] WickPol G →ₗ[ℂ] ℂ where
  toFun p :=
    { toFun q := moment G x (readings p q)
      map_add' q r := by
        let f := (moment G x).toLinearMap (readings p 0) 1
        have he q : f q = moment G x (readings p q) := by
          change moment G x (update _ _ _) = _
          congr 1; funext i; rcases two_cases i with rfl|rfl <;> simp
        rw [← he, ← he, ← he]; exact map_add f ..
      map_smul' a q := by
        let f := (moment G x).toLinearMap (readings p 0) 1
        have he q : f q = moment G x (readings p q) := by
          change moment G x (update _ _ _) = _
          congr 1; funext i; rcases two_cases i with rfl|rfl <;> simp
        rw [← he, ← he]; exact map_smul f .. }
  map_add' p q := by
    apply LinearMap.ext; intro r
    change (moment G x).curryLeft (p+q) (fun _ => r) = _
    rw [map_add]; rfl
  map_smul' a p := by
    apply LinearMap.ext; intro r
    change (moment G x).curryLeft (a • p) (fun _ => r) = _
    rw [map_smul]; rfl

open MvPolynomial in
private lemma letters (x : Points 2) (i j a b : Slot G) :
    wickTwo G x (X i * X j) (X a * X b) = entry i a (x 0) (x 1) * entry j b (x 0) (x 1) +
      entry i b (x 0) (x 1) * entry j a (x 0) (x 1) := by
  let A : Deck G := readings (readings i j) (readings a b)
  have he := moment_grid x A
  simp only [A, read_zero, read_one] at he
  convert he using 1
  change moment G x (readings (X i * X j) (X a * X b)) = _
  congr 1; funext s; rcases two_cases s with rfl|rfl <;> simp

variable {j l : ℕ}

private theorem withProbe (f : Probe G j → Prop)
    (k : ∀ i : Fin (legDim G j), f (coordinateLeg ⟨j,i⟩))
    (hz : f 0) (ha : ∀ p q, f p → f q → f (p+q)) (hs : ∀ c : ℝ, ∀ p, f p → f (c • p)) : ∀ p, f p := by
  let V : Submodule ℝ (Probe G j) := { carrier := {u | f u}, zero_mem' := hz, add_mem' := ha _ _, smul_mem' := fun t => hs t _ }
  intro p; change p ∈ V
  have he : p = ∑ i : Fin (legDim G j), p (frame G j i) • coordinateLeg ⟨j,i⟩ := by
    apply (frame G j).ext
    intro i
    simp only [coordinateLeg]
    classical simp
  rw [he]
  exact Submodule.sum_mem V fun i _ => V.smul_mem _ (k i)

private lemma plain_add (p q : Probe G j) : symbol j (p+q) = symbol j p + symbol j q := by
  apply equalPol; intro A
  simp [symbol_test]
private lemma plain_zero : symbol j (0 : Probe G j) = 0 := by
  apply equalPol; intro A; simp [symbol_test]
private lemma plain_smul (t : ℝ) (p : Probe G j) : symbol j (t • p) = (t:ℂ) • symbol j p := by
  apply equalPol; intro A
  rw [map_smul,symbol_test,symbol_test]; simp

def actualEntry {x y : E4} (h : x ≠ y) (p : Probe G j) (q : Probe G l) :=
  ((pairing (G:=G) (z:=x-y) (show x-y∈away from sub_ne_zero.mpr h) p q : ℝ):ℂ)

/- The low-leg specialization suffices (all positions separated, arbitrary jet
orders, with the exact derivative kernels / color normalization of `Maxwell`). -/
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1800000 in
theorem double_symbol (x : Points 2) (h : x 0 ≠ x 1) (j k m n : ℕ) :
    ∀ (p : Probe G j) (q : Probe G k) (b : Probe G m) (c : Probe G n),
      wickTwo G x (symbol j p * symbol k q) (symbol m b * symbol n c) =
        actualEntry h p b * actualEntry h q c + actualEntry h p c * actualEntry h q b := by
  refine withProbe _ (fun i => ?_) ?_ (fun a d ha hd => ?_) (fun t a ha => ?_)
  · refine withProbe _ (fun k => ?_) ?_ (fun a d ha hd => ?_) (fun t a ha => ?_)
    · refine withProbe _ (fun m => ?_) ?_ (fun a d ha hd => ?_) (fun t a ha => ?_)
      · refine withProbe _ (fun n => ?_) ?_ (fun a d ha hd => ?_) (fun t a ha => ?_)
        · simp only [show ∀ (j : ℕ) (i : Fin (legDim G j)), symbol j (coordinateLeg ⟨j,i⟩) = MvPolynomial.X ⟨j,i⟩ from fun j i => symbol_coordinate ⟨j,i⟩,letters]
          rfl
        · simp [plain_zero, actualEntry]
        · simp only [plain_add,mul_add,map_add,LinearMap.add_apply]; rw [ha,hd]
          simp [actualEntry]; ring
        · simp only [plain_smul,mul_smul_comm,map_smul,LinearMap.smul_apply,smul_eq_mul]; rw [ha]
          simp only [actualEntry,map_smul,LinearMap.smul_apply,smul_eq_mul,Complex.ofReal_mul]; ring
      · intro c; simp [plain_zero, actualEntry]
      · intro c; simp only [plain_add,add_mul,map_add,LinearMap.add_apply]; rw [ha,hd]
        simp [actualEntry]; ring
      · intro c; simp only [plain_smul,smul_mul_assoc,map_smul,LinearMap.smul_apply,smul_eq_mul]; rw [ha]
        simp only [actualEntry,map_smul,LinearMap.smul_apply,smul_eq_mul,Complex.ofReal_mul]; ring
    · intro b c; simp [plain_zero, actualEntry]
    · intro b c; simp only [plain_add,mul_add,map_add,LinearMap.add_apply]; rw [ha,hd]
      simp [actualEntry]; ring
    · intro b c; simp only [plain_smul,mul_smul_comm,map_smul,LinearMap.smul_apply,smul_eq_mul]; rw [ha]
      simp only [actualEntry,map_smul,LinearMap.smul_apply,smul_eq_mul,Complex.ofReal_mul]; ring
  · intro q b c; simp [plain_zero, actualEntry]
  · intro q b c; simp only [plain_add,add_mul,map_add,LinearMap.add_apply]; rw [ha,hd]
    simp [actualEntry]; ring
  · intro q b c; simp only [plain_smul,smul_mul_assoc,map_smul,LinearMap.smul_apply,smul_eq_mul]; rw [ha]
    simp only [actualEntry,map_smul,LinearMap.smul_apply,smul_eq_mul,Complex.ofReal_mul]; ring

def wickOne (G : Gauge) (x : Points 1) : WickPol G →ₗ[ℂ] ℂ :=
  (moment G x).toLinearMap 0 0

private theorem letter_one (p : WickPol G) (x : Points 1) : wickOne G x p = moment G x (fun _ => p) := by
  change moment G x (update _ (0:Fin 1) p) = _
  congr 1; funext i; rw [Subsingleton.elim i 0,update_self]

open MvPolynomial in
private theorem zero_here (x : Points 1) (i k : Slot G) : wickOne G x (X i * X k)=0 := by
  classical
  let W : Powers G 1 := fun _ => Finsupp.single i 1 + Finsupp.single k 1
  have h : (fun _ : Fin 1 => X i * X k (R:=ℂ)) = fun a => monBasis G (W a) := by
    simp [W,X,monBasis,monomial_mul]
  rw [letter_one,h,moment_basis,Wick.monomial]
  apply Finset.sum_eq_zero; intro p _
  let g : Occ W := atSlot 0 i 0 (by dsimp only [W]; simp)
  exact False.elim (different p g (Subsingleton.elim ..))

theorem mean_symbol (x : Points 1) : ∀ (p : Probe G j) (q : Probe G l),
    moment G x (fun _ => symbol j p * symbol l q) = 0 := by
  intro p q; rw [← letter_one]
  unfold symbol
  simp only [Finset.sum_mul, Finset.mul_sum,map_sum,MvPolynomial.C_mul',smul_mul_assoc, mul_smul_comm,
    map_smul,zero_here,smul_zero,Finset.sum_const_zero]

end YM.UVNext.FreeStress
