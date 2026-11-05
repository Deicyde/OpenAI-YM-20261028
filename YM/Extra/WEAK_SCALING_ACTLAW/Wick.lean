import YM.Extra.WEAK_SCALING_ACTLAW.Four

/-! # Two-site pair table from the no-internal-contraction moment, including repeated legs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.WeakScaling.Color
open Function Set Labels Maxwell Wick Tensor
open scoped Topology Matrix.Norms.Frobenius
variable {G : Gauge}
open Occ (partner)

private abbrev Grid := Fin 2 × Fin 2
private abbrev Plan := {s : Equiv.Perm Grid // (∀ x, s (s x)=x) ∧ ∀ x, (s x).1 ≠ x.1}
private lemma split_two (a : Fin 2) : a=0 ∨ a=1 := by omega
private def turn := Equiv.swap (0:Fin 2) 1
private def direct : Plan := ⟨Equiv.prodCongr turn (.refl _),by decide,by decide⟩
private def cross : Plan := ⟨Equiv.prodCongr turn turn,by decide,by decide⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private lemma options : ∀ s : Plan, s=direct ∨ s=cross := by
  intro ⟨s,hs,hS⟩
  have he : ∀ s : Grid → Grid, (∀ x, s (s x)=x) → (∀ x, (s x).1 ≠ x.1) → (∀ x, s x=direct.val x) ∨ ∀ x, s x=cross.val x := by decide
  rcases he s hs hS with h|h
  exacts [Or.inl (Subtype.ext (Equiv.ext h)),Or.inr (Subtype.ext (Equiv.ext h))]

private def powers (u : Grid → Maxwell.Slot G) : Powers G 2 := fun i => Finsupp.single (u (i,0)) 1 + Finsupp.single (u (i,1)) 1
private def addr (u : Grid → Maxwell.Slot G) (x : Grid) := if x.2 = 1 ∧ u (x.1,0) = u x then 1 else (0 : ℕ)

private lemma enumerate (u : Grid → Maxwell.Slot G) : ∃ e : Grid ≃ Occ (powers u),
    (∀ x, (e x).label = x.1) ∧ (∀ x, (e x).probe = u x) := by
  have h (w : Occ (powers u)) : w.index < (if u (w.label,0) = w.probe then 1 else 0) +
      (if u (w.label,1) = w.probe then 1 else 0) := by simpa [powers,Finsupp.single_apply] using w.legit
  let f (x : Grid) := Occ.atSlot (W:=powers u) x.1 (u x) (addr u x) (by
    obtain ⟨i,j⟩ := x; rcases split_two j with e|e <;> simp [e,powers,addr,Finsupp.single_apply])
  have hs : Surjective f := by
    intro y; specialize h y
    by_cases he : y.probe = u (y.label,0)
    · by_cases hi : y.index = 0
      · exact ⟨(y.label,0), Occ.ext rfl he.symm (by change addr u (y.label,0) = _; simp [addr,hi])⟩
      have hw : y.probe = u (y.label,1) := by split_ifs at h <;> first | omega | exact Eq.symm (by assumption)
      exact ⟨(y.label,1), Occ.ext rfl hw.symm (by change addr u (y.label,1) = _; rw [addr,if_pos ⟨rfl,he.symm.trans hw⟩]; split_ifs at h <;> omega)⟩
    rw [if_neg (Ne.symm he)] at h
    have hw : y.probe = u (y.label,1) := by split_ifs at h <;> first | omega | exact Eq.symm (by assumption)
    exact ⟨(y.label,1), Occ.ext rfl hw.symm (by change addr u (y.label,1) = _; rw [addr,if_neg (fun h => he (hw.trans h.2.symm))]; split_ifs at h <;> omega)⟩
  have hi i (e : f (i,0)=f (i,1)) : False := by
    have h := congrArg Occ.probe e
    have he := congrArg Occ.index e
    change addr u (i,0)=addr u (i,1) at he
    simp [addr,show u (i,0)=u (i,1) from h] at he
  have ht : Injective f := by
    rintro ⟨i,j⟩ ⟨k,l⟩ h
    have e : i=k := congrArg Occ.label h
    subst k
    rcases split_two j with h₁|h₁ <;> rcases split_two l with h₂|h₂ <;> subst j <;> subst l <;> first | rfl | exact (hi i h).elim | exact (hi i h.symm).elim
  exact ⟨Equiv.ofBijective f ⟨ht,hs⟩,fun _ => rfl,fun _ => rfl⟩

private lemma matching {w : Powers G 2} (e : Grid ≃ Occ w) (he : ∀ x, (e x).label = x.1) :
    ∃ t : Plan ≃ Occ.Matching w, ∀ s x, partner (t s) (e x) = e (s.val x) := by
  let t := e.permCongr
  have ht (s : Equiv.Perm Grid) x : t s (e x)=e (s x) := by simp [t]
  refine ⟨t.subtypeEquiv ?_,fun s x => ht _ _⟩
  intro s
  constructor
  · rintro ⟨h₁,h₂⟩
    refine ⟨Equiv.ext fun i => ?_, fun i => ?_⟩ <;> obtain ⟨x,rfl⟩ := e.surjective i
    · simp [Equiv.Perm.mul_apply,ht,h₁ x]
    rw [ht,he,he]; exact h₂ x
  rintro ⟨h₁,h₂⟩
  refine ⟨fun x => e.injective ?_, fun x => ?_⟩
  · rw [← ht,← ht]; exact congrFun (congrArg DFunLike.coe h₁) (e x)
  have h := h₂ (e x); rwa [ht,he,he] at h

private def vertex (u : Grid → Maxwell.Slot G) (x : Points 2) (j : Grid) := entry (u (0,j.1)) (u (1,j.2)) (x 0) (x 1)

private lemma wick_diagram (u : Grid → Maxwell.Slot G) (x : Points 2) :
    monomial x (powers u) = vertex u x (0,0)*vertex u x (1,1) + vertex u x (0,1)*vertex u x (1,0) := by
  let V := vertex u x
  obtain ⟨e,he,hv⟩ := enumerate u
  obtain ⟨t,ht⟩ := matching e he
  have h (s : Plan) i : (s.val (0,i)).1 = 1 := (split_two _).resolve_left (s.property.2 (0,i))
  have H (s : Plan) : Occ.graph x (t s) = ∏ i : Fin 2, V (i, (s.val (0,i)).2) := by
    symm
    apply Finset.prod_bij' (fun i _ => e (0,i)) (fun v _ => (e.symm v).2)
    · simp [Occ.corners,ht,he,h]
    · simp
    · simp
    · intro a ha
      obtain ⟨⟨i,j⟩,rfl⟩ := e.surjective a
      have hi : i < _ := (show Occ.label (e (i,j)) = i from he _ ) ▸ (Finset.mem_filter.mp ha).2
      rw [e.symm_apply_apply]; exact congrArg (fun k => e (k,j)) (by omega)
    intro a _; rw [Occ.edge, hv, ht, he, he, hv]; rw [h]
    exact congrArg (fun k => entry _ (u k) _ _) (Prod.ext (h s a).symm rfl)
  rw [monomial,← Equiv.sum_comp t]
  simp_rw [H,show (Finset.univ : Finset Plan) = {direct,cross} from Finset.ext fun i => by simpa using options i]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]; simp only [Fin.prod_univ_two]; rfl

lemma entries (x : Points 2) (u v y z : Maxwell.Slot G) :
    Wick.moment G x ![MvPolynomial.X u * MvPolynomial.X v, MvPolynomial.X y * MvPolynomial.X z] =
      entry u y (x 0) (x 1) * entry v z (x 0) (x 1) + entry u z (x 0) (x 1) * entry v y (x 0) (x 1) := by
  let p (i : Grid) := (![![u,v],![y,z]] : Fin 2 → Fin 2 → Maxwell.Slot G) i.1 i.2
  have he : ![MvPolynomial.X u * MvPolynomial.X v, MvPolynomial.X y * MvPolynomial.X z] = fun i => monBasis G (powers p i) := by
    have he (u v : Maxwell.Slot G) : MvPolynomial.X u * MvPolynomial.X v =
        monBasis G (Finsupp.single u 1 + Finsupp.single v 1) := by
          rw [← pow_one (MvPolynomial.X u : WickPol G),← pow_one (MvPolynomial.X v : WickPol G), MvPolynomial.X_pow_eq_monomial,MvPolynomial.X_pow_eq_monomial,MvPolynomial.monomial_mul]
          simp [monBasis]
    funext i; rcases split_two i with h|h <;> simp [p,powers,h,he]
  rw [he,moment_basis, wick_diagram]; rfl

private def first (x : Points 2) (v : WickPol G) := (Wick.moment G x).toLinearMap ![0,v] 0
private def last' (x : Points 2) (v : WickPol G) := (Wick.moment G x).toLinearMap ![v,0] 1

private lemma at_first (x : Points 2) (v u : WickPol G) : Wick.moment G x ![v,u] = first x u v := by
  apply congrArg (Wick.moment ..); funext i; rcases split_two i with h|h <;> simp [h]
private lemma at_last (x : Points 2) (v u : WickPol G) : Wick.moment G x ![v,u] = last' x v u := by
  apply congrArg (Wick.moment ..); funext i; rcases split_two i with h|h <;> simp [h]

private abbrev key (i : Fin (legDim G 0)) : Maxwell.Slot G := ⟨0,i⟩
private abbrev term (p : Maxwell.Probe G 0) (i : Fin (legDim G 0)) : ℝ := p (frame G 0 i)

private lemma termwise (p q : Maxwell.Probe G 0) (f : WickPol G →ₗ[ℂ] ℂ) :
    f (symbol 0 p * symbol 0 q) = ∑ i, ∑ j, (↑(term p i * term q j):ℂ) * f (MvPolynomial.X (key i)*MvPolynomial.X (key j)) := by
  unfold symbol; rw [Finset.sum_mul_sum]; simp_rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_mul_mul_comm,← map_mul,← MvPolynomial.smul_eq_C_mul,map_smul,Complex.ofReal_mul]; rfl

private lemma amounts (p : Maxwell.Probe G 0) : p = ∑ i, term p i • (frame G 0).coord i := by
  apply LinearMap.ext; intro x
  rw [LinearMap.sum_apply]; nth_rw 1 [← (frame G 0).sum_repr x, map_sum]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]; exact mul_comm _ _

private lemma pairing_frame {x : Points 2} {P Q : Maxwell.Probe G 0} (h : x 0-x 1 ∈ away) :
    (↑(pairing h P Q) : ℂ) = ∑ i, ∑ j, (↑(term P i*term Q j):ℂ) * entry (key i) (key j) (x 0) (x 1) := by
  conv_lhs => rw [amounts P]
  simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,Complex.ofReal_sum,Complex.ofReal_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [amounts Q]; simp only [map_sum,map_smul,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_sum,Finset.mul_sum, ← mul_assoc]
  rfl

lemma pair_table (x : Points 2) {P Q R S : Maxwell.Probe G 0} (h : x 0-x 1∈away) :
    let v := pairing h (G:=G) (j:=0) (l:=0)
    Wick.moment G x ![symbol 0 P * symbol 0 Q,symbol 0 R * symbol 0 S] = (↑(v P R * v Q S + v P S * v Q R) : ℂ) := by
  intro v
  rw [at_first,termwise]; simp_rw [← at_first,at_last,termwise,← at_last,entries, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  dsimp only [v]; rw [Complex.ofReal_add]; simp_rw [Complex.ofReal_mul,pairing_frame h, Finset.sum_mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    push_cast; ring
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => arg 2; intro j; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  push_cast; ring

def two (x : Points 2) (a b i j p q c d : Axis) :=
    bareCurl a b p q (x 0-x 1) * bareCurl i j c d (x 0-x 1) + bareCurl a b c d (x 0-x 1) * bareCurl i j p q (x 0-x 1)

lemma paired_eval (L : Register G) (x : Points 2) (hx : x∈conf 2) (a b i j p q c d : Axis) :
    let tag := fun s t u v => (⟨4,pinned L s t u v⟩ : (Spin.comparator L).Tag)
    Ward.disc ![tag a b i j,tag p q c d] x = (↑(G.lieDim * two x a b i j p q c d : ℝ) : ℂ) := by
  intro tag
  let Y := Spin.comparator L
  let r := fun a b i j => ((Maxwell.standard L.grid).coord 4).coords (pairLabel G a b i j)
  let R := (![⟨4,r a b i j⟩,⟨4,r p q c d⟩] : Fin 2 → (Maxwell.standard L.grid).Token)
  have he : ![tag a b i j,tag p q c d] = Y.classTokens ∘ R := by funext i; fin_cases i <;> rfl
  let f (t : (Maxwell.standard L.grid).Token) := observable G t.1 (((Maxwell.standard L.grid).coord _).coords.symm t.2)
  rw [he,Ward.disc,Y.at_project Y (table_sym _) (fun _ => le_rfl) hx]
  change Wick.moment G x (f ∘ R) = _
  have ht a b c d : f ⟨4,r a b c d⟩ = reduceEq (pairPol G a b c d) := by
    change observable G 4 (((standard L.grid).coord 4).coords.symm (((standard L.grid).coord 4).coords (pairLabel ..))) = _
    rw [LinearEquiv.symm_apply_apply]; rfl
  rw [show f ∘ R = ![reduceEq (pairPol G a b i j), reduceEq (pairPol G p q c d)] from funext (fun z => by
    rcases split_two z with h|h <;> rw [h] <;> simp [R,ht])]
  have haway : x 0 - x 1 ∈ away := sub_ne_zero.mpr ((show Injective x.ofLp from hx).ne (by decide))
  have hh (i j a b : Axis) (u v : G.ColorIndex) : pairing haway (leg i j u) (leg a b v) =
      if u=v then bareCurl i j a b (x 0-x 1) else 0 := by simpa [Tensor.coeff] using raw_mixed (fun _ => 0) (fun _ => 0) i j a b u v (G:=G) (j:=0) (l:=0) haway
  rw [at_first]; simp_rw [pairPol,map_sum,map_mul,reduced,← at_first,at_last,map_sum,← at_last,pair_table x haway,hh]
  calc
    _ = ∑ _ : G.ColorIndex, (two x a b i j p q c d : ℂ) := by
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_eq_single_of_mem u (Finset.mem_univ u)]
      · simp [two]
      intro v _ hv; simp [Ne.symm hv]
    _ = _ := by simp
end YM.Extra.WeakScaling.Color
