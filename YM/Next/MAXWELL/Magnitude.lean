import YM.Next.MAXWELL.Racers
import YM.Next.MAXWELL.Shelves
import YM.Next.MAXWELL.Silt


/-! # At bounded exterior capacity, the global vector Ward kernel -/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick Climb
open MvPolynomial hiding monomial
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder
variable {G : Gauge} {j k n d : ℕ}

abbrev magnet (k : ℕ) := gloss (G:=G) (fun i => i+2) k
abbrev grams (G : Gauge) := rewired (metric G)

theorem polarity_X (i : Slot G) : grams G (X i)=(scaleW i:ℂ) • X i := by
  obtain ⟨L,hL⟩ := symbol_linear (G:=G) i.1
  rw [← symbol_coordinate]; unfold grams; rw [rewired_symbol]; unfold metric
  change symbol i.1 (((i.1:ℝ)+2) • coordinateLeg i) = _
  simp_rw [← hL]
  change L (((i.1:ℝ)+2) • coordinateLeg i)=(scaleW i:ℂ) • L _
  rw [map_smul,← volumes, scaleW]; norm_cast

/-- Simultaneous Euler and parity calculation. -/
theorem weight_own (p : Slot G→₀ ℕ) (c : ℂ) :
    grams G (MvPolynomial.monomial p c)=(degree p:ℂ) • MvPolynomial.monomial p c ∧
      reflectPol oppositeFrame.ortho (MvPolynomial.monomial p c)=((-1:ℂ)^degree p) • MvPolynomial.monomial p c := by
  classical
  induction ht : degree p using Nat.strong_induction_on generalizing p with
  | h n ih =>
    subst n; by_cases hp:p=0
    · subst p; change grams G (C c)=_ ∧ reflectPol _ (C c)=_; simp [degree,algHom_C,MvPolynomial.algebraMap_eq]
    obtain ⟨i,hi⟩ : p.support.Nonempty := by simpa using hp
    let u := p-Finsupp.single i 1
    have he : u+Finsupp.single i 1=p := tsub_add_cancel_of_le (single_le hi)
    have hh : degree p=degree u+scaleW i := by
      conv_lhs => rw [← he,weight_next,add_assoc]
      rfl
    have hv : degree u < degree p := by rw [hh]; unfold scaleW; omega
    obtain ⟨h,hK⟩ := ih (degree u) hv u rfl
    let A := MvPolynomial.monomial u c
    change grams G A=_ at h
    have hl : MvPolynomial.monomial p c=A* X i := by rw [X,MvPolynomial.monomial_mul,he,mul_one]
    constructor
    · rw [hl, Derivation.leibniz, polarity_X,h]
      change A*((scaleW i:ℂ) • X i)+ X i *((degree u:ℂ) • A)=(degree p:ℂ) • _
      rw [mul_smul_comm,mul_smul_comm,mul_comm (X i) A, ← add_smul, add_comm,← Nat.cast_add,hh]
    have hw : reflectPol oppositeFrame.ortho (X (R:=ℂ) i)=((-1:ℂ)^scaleW i) • X (R:=ℂ) i := by
      rw [← symbol_coordinate,inversion,scaleW,pow_add]; push_cast; norm_num
    rw [hl,map_mul,hw, show reflectPol _ A = _ from hK, smul_mul_assoc,mul_smul_comm,smul_smul,hh,pow_add]

theorem weight_mono (p : WickPol G) (k : ℕ) :
    let q := magnet k p
    grams G q=(k:ℂ) • q ∧ reflectPol oppositeFrame.ortho q=((-1:ℂ)^k) • q ∧ magnet k (grams G p)=grams G q := by
  classical
  intro q
  induction p using MvPolynomial.induction_on' with
  | add p v hp hv =>
    simp only [q,map_add,smul_add];
    dsimp only at hp hv
    rw [hp.1,hv.1,hp.2.1,hv.2.1,hp.2.2,hv.2.2,hp.1,hv.1]; trivial
  | monomial s c =>
    obtain ⟨h,h'⟩ := weight_own s c
    let A := MvPolynomial.monomial s c
    have ht : IsWeightedHomogeneous scaleW A (degree s) := isWeightedHomogeneous_monomial _ _ _ rfl
    rw [h]
    change grams G (magnet k A)=_ ∧ reflectPol _ (magnet k A)= _ ∧ magnet k ((degree s:ℂ) • A)=grams G (magnet k A)
    unfold q; by_cases hh:k=degree s
    · subst k; rw [map_smul,show magnet (degree s) A=A from ht.weightedHomogeneousComponent_same]; exact ⟨h,h',h.symm⟩
    rw [map_smul, show magnet k A=0 from ht.weightedHomogeneousComponent_ne _ hh]; simp

lemma weights_done (p : WickPol G) : ∃ S : Finset ℕ, ∑ i∈S,magnet i p=p := by
  classical
  have he := MvPolynomial.sum_weightedHomogeneousComponent scaleW p
  rw [finsum_eq_sum _ (MvPolynomial.weightedHomogeneousComponent_finsupp (w:=scaleW) p)] at he
  exact ⟨_,he⟩

lemma off_pole (Q : Module.End ℂ (WickPol G)) (p : WickPol G) (hp : p∈shellSector G d)
    (H : ∀ p∈shellSector G d, grams G (Q p)=Q (grams G p))
    (hx : ∀ p∈shellSector G d, reflectPol oppositeFrame.ortho (Q p) = - Q (reflectPol oppositeFrame.ortho p)) : Q p=0 := by
  classical
  obtain ⟨s,hs⟩ := weights_done p
  have he (i : ℕ) : Q (magnet i p)=0 := by
    let k := magnet i p
    let K := Q k
    have ht : k∈ shellSector G d := colors_grade _ _ hp
    obtain ⟨hK,ho,Hr⟩ := weight_mono p i
    change grams G k = _ at hK
    have hh : grams G K=(i:ℂ) • K := by unfold K; rw [H k ht,hK,map_smul]
    obtain ⟨s,h⟩ := weights_done K
    change K=0
    rw [← h]; refine Finset.sum_eq_zero fun l hl => ?_
    obtain ⟨hq,hq',H⟩ := weight_mono K l
    by_cases hi:l=i
    · subst l
      have heq : reflectPol oppositeFrame.ortho K= -(((-1:ℂ)^i) • K) := by unfold K; rw [hx k ht,show reflectPol _ k=_ from ho,map_smul]
      rw [← gloss_mirror (fun l => l+2) i oppositeFrame.ortho K,heq,map_neg,map_smul] at hq'
      let z := magnet i K
      let c : ℂ := (-1)^i
      change -(c • z)=c • z at hq'
      by_contra hv
      exact (show (-c) ≠ c from fun hw => pow_ne_zero i (neg_ne_zero.mpr (one_ne_zero : (1:ℂ)≠0)) (neg_eq_self.mp hw))
        (smul_left_injective ℂ (show z≠0 from hv) (by dsimp only; rw [neg_smul]; assumption))
    rw [hh,map_smul,hq] at H
    by_contra he; exact hi (by exact_mod_cast (smul_left_injective ℂ he H).symm)
  rw [← hs,map_sum]; exact Finset.sum_eq_zero fun i _ => he i

section apparatus
variable (F : Labels.Frames G)

def quiet (t : Vector d (Model F)) := ∀ n (a : Axis) (v : Fin n → (Model F).Field d) x,x∈conf _ → diagram v (t a) x=0
lemma droning (t : Vector d (Model F)) : quiet F t ↔ ∀ a, silence G d (motor F t a) :=
  ⟨fun h a => (branded F _).mp fun n v x hx=> h n a v x hx,fun h n a v x hx => (branded F (t a).toLinearMap).mpr (h a) n v x hx⟩

lemma quiet_runs (d : ℕ) : quiet F (leaves (scheme F).deriv d) := by
  rw [droning]; intro a n p x hp hx
  let q (k) := update p k (rewired (glide G (basis a)) (p k))
  have he := moment_across x p
  let u := ∑ i : Fin n, Points.direction i a
  have hw (j : Fin n) : u j=basis a := by simp [u,Points.direction]
  let v := fun t : ℝ => x+t • u
  have hh : HasDerivAt v u 0 := by
    exact (show HasDerivAt _ _ _ from (by simpa [v] using! ((ContinuousLinearMap.toSpanSingleton ℝ u).hasDerivAt (x := 0)).const_add x))
  let f (y : Points n) := moment G y p
  have hu : v 0=x := by simp [v]
  have hi : DifferentiableAt ℝ f (v 0) := by rw [hu]; exact (kernel_analytic p hx).differentiableAt (by simp)
  have hD := hi.hasFDerivAt.comp_hasDerivAt 0 hh
  rw [show (f ∘ v)= fun t : ℝ => moment G x p from ?_,hu] at hD
  · have hs := hD.unique (hasDerivAt_const ..)
    rw [← hs]; unfold u; rw [map_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [show motor F (leaves (scheme F).deriv d) a (p i)=_ from ?_]
    · exact (positionD p hx i a).symm
    have he := brand_eval F ((leaves (scheme F).deriv d) a).toLinearMap (wrap F (hp i))
    change motor F _ _ _=address F (d+1) ((scheme F).deriv d a (wrap F (hp i))) at he
    rw [address_derive,shed] at he; exact he
  funext t; change moment G (x + t • u) p= _
  rw [show x+t • u= Points.across (t • basis a) x from ?_,he]
  ext1 j; change x j+t • u j=x j+t • basis a; rw [hw]

lemma charges_quiet (h : G.Simple) {d : ℕ} (hd : 4≤d) (hz : ∀ w,∀ p∈shellSector G w,p ∈ ghost G d→p=0) (t : Vector d (Model F))
    (v : t∈Colors (scheme F) (hierarchy F).spin d) : quiet F t ↔ ∃ c : ℝ,t=c • leaves (scheme F).deriv d := by
  classical
  let P := scheme F
  let D := leaves P.deriv d
  have ht := quiet_runs F d
  constructor
  · intro H
    obtain ⟨c,hc⟩ := racer F h t v hd ((droning F _).mp H)
    let A := t - c • D
    have hv : quiet F A := by
      intro n a v x hx; unfold A; rw [Pi.sub_apply,Pi.smul_apply,← observation,map_sub,
        show Climb.observed v x (d+1) (c • D a) = c • Climb.observed v x (d+1) (D a) from map_smul ((Climb.observed v x (d+1)).restrictScalars ℝ) c (D a), observation,observation]
      change diagram v _ x - c • diagram v (leaves _ d a) x=_
      rw [H n a v x hx,ht n a v x hx,smul_zero,sub_zero]
    have hD : D ∈ Colors (scheme F) (hierarchy F).spin d := (native _ (hierarchy F) (scheme_filters F) (scheme_derives F) (phase_orientation F)).sight d
    refine ⟨c,sub_eq_zero.mp ?_⟩
    change A=0
    ext1 a; ext1 q
    have hm (s : WickPol G) (hS : s∈shellSector G 4) : motor F A a s=0 := by
      let x := wrap F (chain hd hS)
      have he : address F d x=s := shed F _
      have hh := brand_eval F (A a).toLinearMap x
      change motor F A a _ = address F (d+1) (t a x-c • (scheme F).deriv d a x) at hh
      rw [map_sub,show address F (d+1) (c • _) = c • address F (d+1) ((scheme F).deriv d a x) from
        ((address F (d+1)).restrictScalars ℝ).map_smul c _, address_derive,← show motor F t a (address F d x)=address F (d+1) (t a x) from brand_eval F (t a).toLinearMap x,he] at hh
      rw [hh]; exact sub_eq_zero.mpr (hc a _ hS)
    have hw : A∈Colors (scheme F) (hierarchy F).spin d := Submodule.sub_mem _ v (Submodule.smul_mem _ _ hD)
    have hL n (x : Points (n+1)) (hx : x∈conf _) : ∃ χ v, Table.Window x χ ∧ Motion (x:=x 0) v (metric G) χ := by
      obtain ⟨χ,hχ⟩ := Work.A01.exists_window x hx
      exact ⟨χ,_,hχ,radial_motion hχ.1 hχ.2.1 hχ.2.2.1⟩
    have hf S (hg : S∈ shellSector G d) : grams G (motor F A a S)=motor F A a (grams G S) :=
      sub_eq_zero.mp (hz (d+1) _ (Submodule.sub_mem _ (metric_holds (brand_fit F (A a).toLinearMap _))
        (brand_fit F (A a).toLinearMap _)) (commute_ghost hd ((droning F _).1 hv a) (fun i j => hm _ (stress_label G i j)) hL S hg (metric_holds hg)))
    have he := off_pole (motor F A a) _ (address_in F d q) hf (fun p hp => motor_inverse F hw a hp)
    rw [motor,brand_eval] at he; exact address_inj F (d+1) (he.trans (map_zero (address F (d+1))).symm)
  rintro ⟨c,rfl⟩; intro n a v x hx
  rw [← observation, Pi.smul_apply]; change Climb.observed v x _ (c • D a)=_
  rw [show Climb.observed v x (d+1) (c • D a)=c • Climb.observed v x (d+1) (leaves (scheme F).deriv d a) from map_smul ((Climb.observed v x (d+1)).restrictScalars ℝ) c (D a), observation]
  rw [ht n a v x hx]; simp
end apparatus
end YM.Maxwell.Free
