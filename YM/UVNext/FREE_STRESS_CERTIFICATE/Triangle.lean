import YM.UVNext.FREE_STRESS_CERTIFICATE.DoubleWick

/-! The exact three-site two-leg sector of the separated Wick moment
for fixing stress normalization (translation test at lowest nontrivial enclosed
weight). The eight cross diagrams even when slots coincide. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Maxwell Wick Wick.Occ Function
variable {G : Gauge}

private abbrev T3 := Fin 3
private abbrev T := Fin 2
private abbrev Grid := T3 × T
private abbrev Sheet (G : Gauge) := T3 → T → Slot G
private def counts (A : Sheet G) : Powers G 3 := fun i => Finsupp.single (A i 0) 1 + Finsupp.single (A i 1) 1

private lemma twoCases (i : T) : i=0 ∨ i=1 := by fin_cases i <;> decide
private def other : Equiv.Perm T := Equiv.swap 0 1
@[simp] private lemma different' (i : T) : other i ≠ i := (by decide : ∀ i : T, other i ≠ i) i
@[simp] private lemma other_swap (i : T) : other (other i)=i := (by decide : ∀ i:T, other (other i)=i) i
private lemma two_other (i k : T) : k=i ∨ k=other i := (by decide : ∀ i k:T, k=i ∨ k=other i) i k

private def indexInto (A : Sheet G) (u : Grid) : Occ (counts A) := by
  classical
  exact if u.2=0 then atSlot u.1 (A u.1 0) 0 (by simp [counts]) else
    atSlot u.1 (A u.1 1) (if A u.1 0 = A u.1 1 then 1 else 0) (by
      simp only [counts, Finsupp.add_apply, Finsupp.single_eq_same]; split_ifs with h
      · simp [h]
      exact Nat.zero_lt_succ _)

@[simp] private lemma pos_into (A : Sheet G) (u : Grid) : (indexInto A u).label = u.1 := by
  unfold indexInto; split <;> rfl
@[simp] private lemma prb_into (A : Sheet G) (u : Grid) : (indexInto A u).probe = A u.1 u.2 := by
  obtain ⟨i,j⟩ := u; rcases twoCases j with rfl|rfl <;> simp [indexInto]

private lemma iso_occ (A : Sheet G) : Bijective (indexInto A) := by
  classical
  constructor
  · rintro ⟨i,j⟩ ⟨b,d⟩ h
    have h1 := congr_arg (fun p : Occ (counts A) => p.label) h
    have h2 := congr_arg (fun p : Occ (counts A) => p.probe) h
    simp only [pos_into,prb_into] at h1 h2
    change i=b at h1; subst b
    have h3 := congr_arg (fun p : Occ (counts A) => p.index) h
    change A i j = A i d at h2
    rcases twoCases j with rfl|rfl <;> rcases twoCases d with rfl|rfl
    all_goals first | rfl | simp [indexInto,h2] at h3
  · intro p
    let i := p.label
    have hp := p.legit
    change p.index < (counts A i) p.probe at hp
    simp only [counts,Finsupp.add_apply,Finsupp.single_apply] at hp
    by_cases hr : A i 0 = A i 1
    · rw [← hr] at hp
      by_cases he : A i 0 = p.probe
      · rw [if_pos he] at hp
        have he' := hr ▸ he
        rcases (show p.index = 0 ∨ p.index=1 by omega) with hd|hd
        · exact ⟨(i,0),Occ.ext (pos_into ..) (by rw [prb_into]; exact he) (by simp [indexInto, hd])⟩
        exact ⟨(i,1),Occ.ext (pos_into ..) (by rw [prb_into]; exact he') (by simp [indexInto,hr,hd])⟩
      rw [if_neg he] at hp; omega
    by_cases he : A i 0 = p.probe
    · rw [if_pos he,if_neg (show A i 1 ≠ p.probe by rw [← he]; exact Ne.symm hr)] at hp
      exact ⟨(i,0),Occ.ext (pos_into ..) (by rw [prb_into]; exact he) (by simp [indexInto]; omega)⟩
    by_cases he' : A i 1 = p.probe
    · rw [if_pos he', if_neg he] at hp
      exact ⟨(i,1),Occ.ext (pos_into ..) (by rw [prb_into]; exact he') (by simp [indexInto,hr]; omega)⟩
    rw [if_neg he',if_neg he] at hp; omega

private def up (i : T3) := i+1
private def dn (i : T3) := i+2
@[simp] private lemma up_ne (i : T3) : up i≠i := (by decide : ∀ i:T3, up i≠i) _
@[simp] private lemma dn_ne (i : T3) : dn i≠i := (by decide : ∀ i:T3, dn i≠i) _
@[simp] private lemma up_dn (i : T3) : up (dn i)=i := (by decide : ∀ i:T3, up (dn i)=i) _
@[simp] private lemma dn_up (i : T3) : dn (up i)=i := (by decide : ∀ i:T3, dn (up i)=i) _
@[simp] private lemma axis_ne (i : T3) : up i≠dn i := (by decide : ∀ i:T3, up i≠dn i) _
private lemma tri (i j : T3) (h : i ≠ j) : i=up j ∨ i=dn j := (by decide : ∀ i j:T3,i≠j → i=up j ∨ i=dn j) i j h
private lemma threeCases (i : T3) : i=0 ∨ i=1 ∨ i=2 := (by decide : ∀ i:T3, i=0 ∨ i=1 ∨ i=2) i

private abbrev Choice := T3→T
private def stepTo (Q : Choice) (v : Grid) : Grid := if v.2=Q v.1 then (up v.1, other (Q (up v.1))) else (dn v.1,Q (dn v.1))
@[simp] private lemma riseTo (Q : Choice) (i : T3) : stepTo Q (i,Q i)=(up i,other (Q (up i))) := by simp [stepTo]
@[simp] private lemma fallTo (Q : Choice) (i : T3) : stepTo Q (i,other (Q i))=(dn i,Q (dn i)) := by simp [stepTo]
@[simp] private lemma step_swap (Q : Choice) (v : Grid) : stepTo Q (stepTo Q v)=v := by
  obtain ⟨i,k⟩ := v; rcases two_other (Q i) k with rfl|rfl <;> simp

section
variable {W : Powers G 3} (e : Grid ≃ Occ W) (he : ∀ u : Grid, (e u).label=u.1)

private def pass (Q : Choice) : Matching W :=
  ⟨{ toFun p := e (stepTo Q (e.symm p))
     invFun p := e (stepTo Q (e.symm p))
     left_inv p := by simp
     right_inv p := by simp },by
    constructor
    · ext1 p; change e (stepTo Q (e.symm (e (stepTo Q (e.symm p))))) = p; simp
    intro p
    obtain ⟨⟨i,j⟩,rfl⟩ := e.surjective p
    change (e (stepTo Q (e.symm _))).label ≠ _
    rcases two_other (Q i) j with rfl|rfl <;> simp [he]⟩

@[simp] private lemma operates (Q : Choice) (u : Grid) : partner (pass e he Q) (e u)=e (stepTo Q u) := by
  change e (stepTo Q (e.symm _))=_; simp

private lemma pass_once : Bijective (pass e he) := by
  classical
  constructor
  · intro s t h
    funext i
    have hp := congr_arg (fun v : Matching W => (e.symm (partner v (e (i,s i)))).1) h
    by_contra! he'
    simp only [operates,Equiv.symm_apply_apply,stepTo,if_neg he'] at hp
    exact axis_ne i hp
  intro p
  let L (u : Grid) := e.symm (partner p (e u))
  have hx u : (L u).1 ≠ u.1 := by simpa [L, ← he] using different p (e u)
  have hl (u) : L (L u)=u := by simp [L]
  have hi : Injective L := (show LeftInverse L L from hl).injective
  have hv (i : T3) : (L (i,0)).1 ≠ (L (i,1)).1 := by
    intro hj
    let j := (L (i,0)).1
    have hn : j≠i := hx _
    let f (a : T) := (L (i,a)).2
    have he (a : T) : L (i,a)=(j,f a) := Prod.ext (by rcases twoCases a with rfl|rfl; rfl; exact hj.symm) rfl
    have ho : Injective f := by
      intro a b hg; exact congr_arg Prod.snd (hi ((he a).trans ((congr_arg (fun z => (j,z)) hg).trans (he b).symm)))
    have hg (z : T) : (L (j,z)).1=i := by
      obtain ⟨t,rfl⟩ := (Finite.surjective_of_injective ho) z
      exact congr_arg Prod.fst ((congr_arg L (he t).symm).trans (hl (i,t)))
    obtain ⟨k,hk,hk'⟩ : ∃ k : T3, k≠i ∧ k≠j := (by decide : ∀ i j : T3, j≠i → ∃ k : T3, k≠i ∧ k≠j) _ _ hn
    let y := L (k,0)
    have hq : y.1≠k := hx _
    have h1 : y.1=i ∨ y.1=j := (by decide : ∀ k i j a : T3, k≠i → k≠j → j≠i → a≠k → a=i ∨ a=j) _ _ _ _ hk hk' hn hq
    have h2 : (L y).1=k := congr_arg Prod.fst (hl (k,0))
    rcases h1 with hw|hw
    · rw [show y=(i,y.2) from Prod.ext hw rfl,he y.2] at h2
      exact hk' h2.symm
    rw [show y=(j,y.2) from Prod.ext hw rfl,hg] at h2; exact hk h2.symm
  have ha (i : T3) : ∃ t : T, (L (i,t)).1=up i ∧ (L (i,other t)).1=dn i := by
    rcases tri _ _ (hx (i,0)) with h|h <;> rcases tri _ _ (hx (i,1)) with h'|h'
    · exact (hv i (h.trans h'.symm)).elim
    exact ⟨0,h,h'⟩
    exact ⟨1,h',by rw [show other 1=0 by decide]; exact h⟩
    exact (hv i (h.trans h'.symm)).elim
  choose Q hQ hD using ha
  have H (i) : L (i,Q i)=(up i,other (Q (up i))) := by
    apply Prod.ext (hQ i)
    rcases two_other (Q (up i)) (L (i,Q i)).2 with hc|hc
    · exfalso
      have h : L (i,Q i)=(up i,Q (up i)) := Prod.ext (hQ i) hc
      have hh := congr_arg Prod.fst ((congr_arg L h).symm.trans (hl (i,Q i)))
      rw [hQ] at hh
      exact (axis_ne (up i)) (hh.trans (dn_up _).symm)
    exact hc
  have h (i) : L (i, other (Q i)) = (dn i,Q (dn i)) := by
    apply hi; rw [hl,H,up_dn]
  refine ⟨Q,Subtype.ext ?_⟩
  ext1 v
  obtain ⟨⟨i,j⟩,rfl⟩ := e.surjective v
  change partner (pass e he Q) _=partner p _
  rw [operates]; apply e.symm.injective
  change e.symm _=L (i,j); rw [e.symm_apply_apply]
  rcases two_other (Q i) j with rfl|rfl
  exacts [(H i).symm |> (riseTo ..).trans,(fallTo ..).trans (h i).symm]
end
private lemma three_product (x : Points 3) (A : Sheet G) :
    Wick.monomial x (counts A) = ∑ Q : Choice,
      Wick.entry (A 0 (Q 0)) (A 1 (other (Q 1))) (x 0) (x 1) *
      Wick.entry (A 0 (other (Q 0))) (A 2 (Q 2)) (x 0) (x 2) *
      Wick.entry (A 1 (Q 1)) (A 2 (other (Q 2))) (x 1) (x 2) := by
  let e := Equiv.ofBijective (indexInto A) (iso_occ A)
  have he u : (e u).label=u.1 := pos_into ..
  have hq u : (e u).probe=A u.1 u.2 := prb_into ..
  rw [Wick.monomial,← Equiv.sum_comp (Equiv.ofBijective _ (pass_once e he))]
  apply Finset.sum_congr rfl; intro Q _
  change graph x (pass e he Q)=_
  let a := e (0,Q 0)
  let b := e (0,other (Q 0))
  let c := e (1,Q 1)
  have h : corners (pass e he Q) = {a,b,c} := by
    ext1 p; obtain ⟨⟨i,j⟩,rfl⟩ := e.surjective p
    rcases two_other (Q i) j with rfl|rfl <;> rcases threeCases i with rfl|rfl|rfl
    all_goals simp [corners,a,b,c,he,riseTo,fallTo, operates,show up 0=1 by decide,show up 1=2 by decide,
      show up 2=0 by decide,show dn 1=0 by decide,show dn 2=1 by decide,show dn 0=2 by decide,Ne.symm (different' _)]
  rw [Occ.graph,h]; simp [a,b,c,edge,hq,he,operates,riseTo,fallTo,show up 0=1 by decide,show up 1=2 by decide,
    show dn 0=2 by decide, Ne.symm (different' _),mul_assoc]

private lemma representation (x : Points 3) (A : Sheet G) :
    moment G x (fun i => MvPolynomial.X (A i 0) * MvPolynomial.X (A i 1)) = ∑ Q : Choice,
      Wick.entry (A 0 (Q 0)) (A 1 (other (Q 1))) (x 0) (x 1) *
      Wick.entry (A 0 (other (Q 0))) (A 2 (Q 2)) (x 0) (x 2) *
      Wick.entry (A 1 (Q 1)) (A 2 (other (Q 2))) (x 1) (x 2) := by
  rw [show (fun i => MvPolynomial.X (A i 0)*MvPolynomial.X (R:=ℂ) (A i 1)) =
      fun i => monBasis G (counts A i) from by funext i; simp [MvPolynomial.X,MvPolynomial.monomial_mul, counts,monBasis],moment_basis]
  exact three_product x A

-- expand the sum for the multilinear calculations
private lemma stations {X : Type*} [AddCommMonoid X] (f : Choice → X) :
    (∑ i : Choice, f i) = ∑ i : T, ∑ j : T, ∑ k : T, f (Fin.cons i (readings j k)) := by
  let L : T × T × T → Choice := fun q => Fin.cons q.1 (readings q.2.1 q.2.2)
  have h (i j k : T) : L (i,j,k) 0 = i ∧ L (i,j,k) 1 = j ∧ L (i,j,k) 2=k := ⟨rfl,rfl,by
    change Fin.cons _ _ (1 : Fin 2).succ = _; rw [Fin.cons_succ,read_one]⟩
  let e : (T × T × T) ≃ Choice := ⟨L, fun f => (f 0,f 1,f 2),by
    rintro ⟨i,j,k⟩; exact Prod.ext (h ..).1 (Prod.ext (h i j k).2.1 (h i j k).2.2),by
    intro f; funext i; rcases threeCases i with rfl|rfl|rfl
    exacts [(h ..).1,(h ..).2.1,(h ..).2.2]⟩
  rw [← Equiv.sum_comp e, Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type]; rfl

-- expose the actual polynomial formula via six linear extension indices.
def triangle {Y : Type*} (a b c : Y) := Fin.cons (α:=fun _ : Fin 3 => Y) a (readings b c)
@[simp] lemma triangle_zero {Y : Type*} (a b c : Y) : triangle a b c 0=a := rfl
@[simp] lemma triangle_one {Y : Type*} (a b c : Y) : triangle a b c 1=b := rfl
@[simp] lemma triangle_two {Y : Type*} (a b c : Y) : triangle a b c 2=c := by change Fin.cons _ _ (1 : Fin 2).succ = _; rw [Fin.cons_succ,read_one]

private lemma wick_at (x : Points 3) (A B C D E F : Slot G) :
    let e (i j : Fin 3) (a b : Slot G) := Wick.entry a b (x i) (x j)
    moment G x (triangle (MvPolynomial.X A * MvPolynomial.X B) (MvPolynomial.X C*MvPolynomial.X D) (MvPolynomial.X E*MvPolynomial.X F)) =
      e 0 1 A D * e 0 2 B E * e 1 2 C F + e 0 1 A D * e 0 2 B F * e 1 2 C E +
      (e 0 1 A C * e 0 2 B E * e 1 2 D F + e 0 1 A C * e 0 2 B F * e 1 2 D E) +
      (e 0 1 B D * e 0 2 A E * e 1 2 C F + e 0 1 B D * e 0 2 A F * e 1 2 C E +
      (e 0 1 B C * e 0 2 A E * e 1 2 D F + e 0 1 B C * e 0 2 A F * e 1 2 D E)) := by
  intro e
  let Q : Sheet G := triangle (readings A B) (readings C D) (readings E F)
  have he := representation x Q
  rw [← show (fun i : Fin 3 => MvPolynomial.X (Q i 0)*MvPolynomial.X (Q i 1)) =
      (triangle (MvPolynomial.X A * MvPolynomial.X B) (MvPolynomial.X C*MvPolynomial.X D)
        (MvPolynomial.X E*MvPolynomial.X F) : Fin 3 → WickPol G) from by
        funext i; rcases threeCases i with rfl|rfl|rfl <;> simp [Q], he,stations]
  have hh (i j k : T) : Fin.cons (α:=fun _ : Fin 3 => T) i (readings j k) = triangle i j k := rfl
  simp only [hh, Fin.sum_univ_two,Q,triangle_zero, triangle_one,triangle_two,read_zero,read_one,show other 0=1 by decide, show other 1=0 by decide,e]

variable (G x) in
def triplet : WickPol G →ₗ[ℂ] WickPol G →ₗ[ℂ] WickPol G →ₗ[ℂ] ℂ where
  toFun A :=
    { toFun B :=
        { toFun C := moment G (x:Points 3) (triangle A B C)
          map_add' C D := by
            let f := (moment G x).toLinearMap (triangle A B 0) 2
            have he u : f u = moment G x (triangle A B u) := by
              change moment G x (update _ _ _) = _
              congr 1; funext i; rcases threeCases i with rfl|rfl|rfl <;> simp
            rw [← he, ← he, ← he,map_add]
          map_smul' t C := by
            let f := (moment G x).toLinearMap (triangle A B 0) 2
            have he u : f u = moment G x (triangle A B u) := by
              change moment G x (update _ _ _) = _
              congr 1; funext i; rcases threeCases i with rfl|rfl|rfl <;> simp
            rw [← he, ← he,map_smul,RingHom.id_apply] }
      map_add' B C := by
        apply LinearMap.ext; intro D
        let f := (moment G x).toLinearMap (triangle A 0 D) 1
        have he u : f u = moment G x (triangle A u D) := by
          change moment G x (update _ _ _) = _
          congr 1; funext i; rcases threeCases i with rfl|rfl|rfl <;> simp
        change moment G x (triangle A (B+C) D) = moment G x (triangle A B D) + moment G x (triangle A C D)
        rw [← he, ← he, ← he,map_add]
      map_smul' t B := by
        apply LinearMap.ext; intro D
        let f := (moment G x).toLinearMap (triangle A 0 D) 1
        have he u : f u = moment G x (triangle A u D) := by
          change moment G x (update _ _ _) = _
          congr 1; funext i; rcases threeCases i with rfl|rfl|rfl <;> simp
        change moment G x (triangle A (t • B) D) = t • moment G x (triangle A B D)
        rw [← he, ← he,map_smul] }
  map_add' A B := by
    apply LinearMap.ext; intro C; apply LinearMap.ext; intro D
    change (moment G x).curryLeft (A+B) (readings C D) = _
    rw [map_add]; rfl
  map_smul' t A := by
    apply LinearMap.ext; intro C; apply LinearMap.ext; intro D
    change (moment G x).curryLeft (t • A) (readings C D) = _
    rw [map_smul]; rfl

private abbrev P (G : Gauge) := Probe G 0
private def m (x : Points 3) (i j : T3) (p q : P G) := (legKernel p q (x i-x j) : ℂ) -- actual no mismatch

private def law3 (x : Points 3) (A B C D E F : P G) :=
    let f := m x
    triplet G x (symbol 0 A * symbol 0 B) (symbol 0 C * symbol 0 D) (symbol 0 E*symbol 0 F) =
      f 0 1 A D * f 0 2 B E * f 1 2 C F + f 0 1 A D * f 0 2 B F * f 1 2 C E +
      (f 0 1 A C * f 0 2 B E * f 1 2 D F + f 0 1 A C * f 0 2 B F * f 1 2 D E) +
      (f 0 1 B D * f 0 2 A E * f 1 2 C F + f 0 1 B D * f 0 2 A F * f 1 2 C E +
      (f 0 1 B C * f 0 2 A E * f 1 2 D F + f 0 1 B C * f 0 2 A F * f 1 2 D E))

-- Mirrors the two-site linear extension. Avoid multiset/factorial rewrites.
private abbrev Light (G : Gauge) := Fin (legDim G 0)
private def atP (i : Light G) := coordinateLeg (⟨0,i⟩ : Slot G)
private theorem inductionP (f : P G → Prop) (k : ∀ i, f (atP i)) (hz : f 0)
    (ha : ∀ p q, f p → f q → f (p+q)) (hs : ∀ c : ℝ, ∀ p, f p → f (c • p)) : ∀ p, f p := by
  let V : Submodule ℝ (P G) := { carrier := {u | f u}, zero_mem' := hz, add_mem' := ha _ _, smul_mem' := fun t => hs t _ }
  intro p; change p∈V
  have he : p = ∑ i : Light G, p (frame G 0 i) • atP i := by
    apply (frame G 0).ext; intro i; simp [atP,coordinateLeg]
  rw [he]
  exact Submodule.sum_mem V fun _ _ => V.smul_mem _ (k _)
private lemma plainA (p q : P G) : symbol 0 (p+q) = symbol 0 p+symbol 0 q := by apply equalPol; intro X; simp [symbol_test]
private lemma plainZ : symbol 0 (0 : P G) = 0 := by apply equalPol; intro X; simp [symbol_test]
private lemma plainS (t : ℝ) (p : P G) : symbol 0 (t • p) = (t:ℂ) • symbol 0 p := by
  apply equalPol; intro A; rw [map_smul,symbol_test,symbol_test]; simp
private lemma from_pair (p q : P G) {x : Points 3} (h : x∈conf 3) (i j : T3) (ht : i≠j) :
    m x i j p q = (pairing (show x i-x j ∈ away from sub_ne_zero.mpr ((show Injective x.ofLp from h).ne ht)) p q : ℝ) := rfl


set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 6000000 in
private lemma signal {x : Points 3} (h : x∈conf 3) : ∀ (a b c d e f : P G), law3 x a b c d e f := by
  have h01 (p q : P G) := from_pair p q h 0 1 (by decide)
  have h02 (p q : P G) := from_pair p q h 0 2 (by decide)
  have h12 (p q : P G) := from_pair p q h 1 2 (by decide)
  refine inductionP _ (fun i0 => ?_) ?_ (fun v w hv hw => ?_) (fun t v hv => ?_)
  · refine inductionP _ (fun i1 => ?_) ?_ (fun v w hv hw => ?_) (fun t v hv => ?_)
    · refine inductionP _ (fun i2 => ?_) ?_ (fun v w hv hw => ?_) (fun t v hv => ?_)
      · refine inductionP _ (fun i3 => ?_) ?_ (fun v w hv hw => ?_) (fun t v hv => ?_)
        · refine inductionP _ (fun i4 => ?_) ?_ (fun v w hv hw => ?_) (fun t v hv => ?_)
          · refine inductionP _ (fun i5 => ?_) ?_ (fun v w hv hw => ?_) (fun t v hv => ?_)
            · dsimp only [law3]
              have he (i : Light G) : symbol 0 (atP i) = MvPolynomial.X (⟨0,i⟩:Slot G) := symbol_coordinate ⟨0,i⟩
              simp only [he]
              exact wick_at x ⟨0,i0⟩ ⟨0,i1⟩ ⟨0,i2⟩ ⟨0,i3⟩ ⟨0,i4⟩ ⟨0,i5⟩
            · simp only [law3, plainZ, mul_zero, zero_mul,map_zero,LinearMap.zero_apply,h01,h02,h12,Complex.ofReal_zero,add_zero]
            · unfold law3 at *
              simp only [plainA,mul_add,map_add,LinearMap.add_apply]; rw [hv,hw]
              simp only [h01,h02,h12,map_add,LinearMap.add_apply,Complex.ofReal_add]; ring
            · unfold law3 at *
              simp only [plainS,mul_smul_comm,map_smul,LinearMap.smul_apply]; rw [hv]
              simp only [h01,h02,h12,map_smul,LinearMap.smul_apply,smul_eq_mul,Complex.ofReal_mul]; ring
          · intro F; simp only [law3, plainZ, mul_zero, zero_mul,map_zero,LinearMap.zero_apply,h01,h02,h12,Complex.ofReal_zero,add_zero]
          · intro F; unfold law3 at *
            simp only [plainA,add_mul,map_add,LinearMap.add_apply]; rw [hv,hw]
            simp only [h01,h02,h12,map_add,LinearMap.add_apply,Complex.ofReal_add]; ring
          · intro F; unfold law3 at *
            simp only [plainS,smul_mul_assoc,map_smul,LinearMap.smul_apply]; rw [hv]
            simp only [h01,h02,h12,map_smul,LinearMap.smul_apply,smul_eq_mul,Complex.ofReal_mul]; ring
        · intro E F; simp only [law3, plainZ, mul_zero, zero_mul,map_zero,LinearMap.zero_apply,h01,h02,h12,Complex.ofReal_zero,add_zero]
        · intro E F; unfold law3 at *
          simp only [plainA,mul_add,map_add,LinearMap.add_apply]; rw [hv,hw]
          simp only [h01,h02,h12,map_add,LinearMap.add_apply,Complex.ofReal_add]; ring
        · intro E F; unfold law3 at *
          simp only [plainS,mul_smul_comm,map_smul,LinearMap.smul_apply]; rw [hv]
          simp only [h01,h02,h12,map_smul,LinearMap.smul_apply,smul_eq_mul,Complex.ofReal_mul]; ring
      · intro D E F; simp only [law3, plainZ, mul_zero, zero_mul,map_zero,LinearMap.zero_apply,h01,h02,h12,Complex.ofReal_zero,add_zero]
      · intro D E F; unfold law3 at *
        simp only [plainA,add_mul,map_add,LinearMap.add_apply]; rw [hv,hw]
        simp only [h01,h02,h12,map_add,LinearMap.add_apply,Complex.ofReal_add]; ring
      · intro D E F; unfold law3 at *
        simp only [plainS,smul_mul_assoc,map_smul,LinearMap.smul_apply]; rw [hv]
        simp only [h01,h02,h12,map_smul,LinearMap.smul_apply,smul_eq_mul,Complex.ofReal_mul]; ring
    · intro c D E F; simp only [law3, plainZ, mul_zero, zero_mul,map_zero,LinearMap.zero_apply,h01,h02,h12,Complex.ofReal_zero,add_zero]
    · intro c D E F; unfold law3 at *
      simp only [plainA,mul_add,map_add,LinearMap.add_apply]; rw [hv,hw]
      simp only [h01,h02,h12,map_add,LinearMap.add_apply,Complex.ofReal_add]; ring
    · intro c D E F; unfold law3 at *
      simp only [plainS,mul_smul_comm,map_smul,LinearMap.smul_apply]; rw [hv]
      simp only [h01,h02,h12,map_smul,LinearMap.smul_apply,smul_eq_mul,Complex.ofReal_mul]; ring
  · intro B c D E F; simp only [law3, plainZ, mul_zero, zero_mul,map_zero,LinearMap.zero_apply,h01,h02,h12,Complex.ofReal_zero,add_zero]
  · intro B c D E F; unfold law3 at *
    simp only [plainA,add_mul,map_add,LinearMap.add_apply]; rw [hv,hw]
    simp only [h01,h02,h12,map_add,LinearMap.add_apply,Complex.ofReal_add]; ring
  · intro B c D E F; unfold law3 at *
    simp only [plainS,smul_mul_assoc,map_smul,LinearMap.smul_apply]; rw [hv]
    simp only [h01,h02,h12,map_smul,LinearMap.smul_apply,smul_eq_mul,Complex.ofReal_mul]; ring

/-- Repeated letters at each of the two probing sites (enclosed, far). -/
theorem triangle_test {x : Points 3} (h : x ∈ conf 3) (A B C Y : Probe G 0) :
    triplet G x (symbol 0 A*symbol 0 B) (symbol 0 C*symbol 0 C) (symbol 0 Y * symbol 0 Y) =
      4 * ((legKernel C Y (x 1-x 2):ℝ):ℂ) *
        ((((legKernel A C (x 0-x 1):ℝ):ℂ)*((legKernel B Y (x 0-x 2):ℝ):ℂ))+
        (((legKernel B C (x 0-x 1):ℝ):ℂ)*((legKernel A Y (x 0-x 2):ℝ):ℂ))) := by
  rw [signal h A B C C Y Y]
  unfold m; ring
end YM.UVNext.FreeStress
