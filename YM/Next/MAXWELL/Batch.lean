import YM.Next.MAXWELL.Leading
import YM.Next.MAXWELL.Living


/-!
# Coalescence with no exterior-surplus

Lowest length component p[k]. Cluster precisely k exterior legs. Then
no mutual contractions are left inside the cluster. This is not a
coincidence prescription at a diagonal.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick
open MvPolynomial hiding monomial
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder
variable {G : Gauge} {j k w d n : ℕ}

private lemma bags_exact (p : Powers G n) : ∃ r : List (Fin n × Factor G), bag Prod.fst Prod.snd r = (fun i => monBasis G (p i)) ∧ r.length=∑ i,bulk (p i) := by
  classical
  choose L he H hl using fun i => mon_list (p i)
  let t (i : Fin n) := (L i).map fun s => (i,coordF s)
  have ht (i j) : bag Prod.fst Prod.snd (t i) j = if j=i then monBasis G (p j) else 1 := by
    unfold t; by_cases h : j=i
    · subst j; simpa [bag,letter_coord,List.map_map, Function.comp_def, monBasis] using (he i).symm
    simp [bag,List.map_map,Function.comp_def,h]
  have h (s : Finset (Fin n)) : ∃ r : List (Fin n × Factor G), (∀ j, bag Prod.fst Prod.snd r j=
      if j∈s then monBasis G (p j) else 1) ∧ r.length=∑ i∈s,bulk (p i) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨[],fun j => by simp [bag],by simp⟩
    | @insert i s hi ih =>
      obtain ⟨r,h,h'⟩ := ih
      refine ⟨t i++r,fun j => ?_,?_⟩
      · by_cases H : j=i <;> simp_all [bag_merge]
      simp [t,hl,hi,h',bulk,Finsupp.weight_apply]
  obtain ⟨v,hv,H⟩ := h Finset.univ
  exact ⟨v,funext fun i => by simpa using hv i,H⟩

private lemma all_bag {ι : Type*} (r : List ι) (s : ι→Fin n) (p : ι→Factor G) : ∏ i, bag s p r i = (r.map (letter ∘ p)).prod := by
  induction r with
  | nil => simp [bag]
  | cons a r ih => simp only [bag_cons,Finset.prod_mul_distrib, ih]; simp

private lemma no_bond (x : E4) (p : Factor G) (u : List (Factor G)) (v : List (Limb G)) :
    pairCost linkEntry ((x,p)::((u.map fun i => (x,i)) ++ v)) =
      pulls v (fun b w => linkEntry (x,p) b*pairCost linkEntry ((u.map fun i => (x,i)) ++ w)) := by
  rw [pair_step,pulls_append,pulls_map]; simp_rw [link_zero,zero_mul]
  simp only [pulls_zero,zero_add]

private lemma lacks (x : E4) (u : List (Factor G)) (v : List (Limb G)) (h : u.length > v.length) :
    pairCost linkEntry ((u.map fun i => (x,i)) ++ v) = 0 := by
  induction u generalizing v with
  | nil => simp at h
  | cons a u ih =>
    simp only [List.map_cons,List.cons_append,no_bond]
    apply Finset.sum_eq_zero; intro i _
    change _ * pairCost linkEntry _=_; rw [ih]
    · rw [mul_zero]
    have := List.length_eraseIdx_add_one i.isLt
    rw [List.length_cons] at h; omega

private lemma all_path {ι σ : Type*} (F : Filter ι) {x y : E4} (hx : x≠y) {v : σ → ι → E4}
    (ht : ∀ a, Tendsto (v a) F (𝓝 y)) (u : List (Factor G)) (r : List σ) (w : σ → Factor G)
    (h : u.length ≥ r.length) :
    Tendsto (fun t => pairCost linkEntry ((u.map fun i => (x,i)) ++ r.map (fun i => (v i t,w i)))) F
      (𝓝 (pairCost linkEntry ((u.map fun i => (x,i)) ++ r.map (fun i => (y,w i))))) := by
  induction u generalizing r with
  | nil => obtain rfl := List.eq_nil_of_length_eq_zero (show r.length=0 by simp_all); exact tendsto_const_nhds
  | cons a u ih =>
    simp only [List.map_cons, List.cons_append,no_bond,pulls_map]
    unfold pulls; apply tendsto_finsetSum; intro i _
    let j := r.get i
    have hu : ContinuousAt (fun z => linkEntry (x,a) (z,w j)) y := by
      refine ContinuousAt.congr_of_eventuallyEq (f:=fun z => (↑(K a.2 (w j).2 x z):ℂ)) ?_ ?_
      · apply Complex.continuous_ofReal.continuousAt.comp
        exact (K_smooth a.2 (w j).2 (x,y) hx).continuousAt.comp
          (show ContinuousAt (fun z : E4 => (x,z)) y from continuousAt_const.prodMk continuousAt_id)
      filter_upwards [isOpen_ne.mem_nhds hx.symm] with z hz
      exact link_eq x z _ _ (Ne.symm hz)
    refine (hu.tendsto.comp (ht j)).mul (ih (r.eraseIdx i.val) ?_)
    have := List.length_eraseIdx_add_one i.isLt
    rw [List.length_cons] at h; omega

variable {ι : Type*} {F : Filter ι} {x y : E4}

private lemma strict_bags (hx : x≠y) {v : ι → Points n} (H : ∀ᶠ t in F,Points.cons x (v t)∈conf _) (ht : ∀ i, Tendsto (fun t => v t i) F (𝓝 y))
    (p : Slot G→₀ ℕ) (q : Powers G n) (h : bulk p ≥ ∑ i, bulk (q i)) :
    let B := fun i => monBasis G (q i)
    let A := monBasis G p
    Tendsto (fun t => moment G (Points.cons x (v t)) (Fin.cons (α:=fun _ => WickPol G) A B)) F
      (𝓝 (bond G x y (distill (∑ i,bulk (q i)) A) (∏ i, B i))) := by
  classical
  intro B A
  obtain ⟨r,hr,hK⟩ := bags_exact q
  obtain ⟨L,hL,Hl,l⟩ := mon_list p
  let u := L.map coordF
  have hp : A=(u.map letter).prod := by unfold u; simp [hL,A,monBasis,List.map_map,letter_coord,Function.comp_def]
  have hN : u.length=bulk p := by simp [l,u,bulk,Finsupp.weight_apply]
  let a (P : List (Limb G)) := pairCost linkEntry ((u.map (fun i => (x,i))) ++ P)
  have ht' := all_path F hx (v:=fun (j : Fin n × Factor G) t => v t j.1) (fun i => ht i.1) u r Prod.snd (by omega)
  let Q t := r.map (fun i => (v t i.1,i.2))
  let R := r.map (fun i => (y,i.2))
  suffices hv : bond G x y (distill (∑ i,bulk (q i)) A) (∏ i, B i)=a R by
    rw [hv]; apply ht'.congr'
    filter_upwards [H] with t hx
    change a (Q t)=_
    rw [hp, ← show bag Prod.fst Prod.snd r=B from hr, planted _ _ _ _ _ hx]; rfl
  by_cases he : (∑ i,bulk (q i))=bulk p
  · have HH : Pure (bulk p) A := by unfold A monBasis; rw [coe_basisMonomials]; exact isWeightedHomogeneous_monomial _ _ _ rfl
    rw [he,(distilled_eq _ _).mp HH,hp,← show bag Prod.fst Prod.snd r=B from hr,all_bag,bond_eval]
    let k : Fin n × Factor G → Fin 1 := fun _ => 0
    have hw : (fun _ : Fin 1 => (r.map (letter ∘ Prod.snd)).prod)=bag k Prod.snd r := by
      ext1 i; fin_cases i; simp [k,bag,Function.comp_def]
    rw [hw,pairPoints,planted _ _ _ _ _ (pair_ok hx)]; rfl
  have HH : Pure (bulk p) A := by unfold A monBasis; rw [coe_basisMonomials]; exact isWeightedHomogeneous_monomial _ _ _ rfl
  rw [show distill (∑ i,bulk (q i)) A=0 from HH.weightedHomogeneousComponent_ne _ he,map_zero]; exact (lacks x u R (by simp only [R,List.length_map]; omega)).symm

private lemma strictly (hx : x≠y) {v : ι → Points n} (H : ∀ᶠ t in F,Points.cons x (v t)∈conf _) (ht : ∀ i, Tendsto (fun t => v t i) F (𝓝 y))
    (p : WickPol G) (q : Fin n → WickPol G) (r : Fin n → ℕ) (hh : ∀ i,Pure (r i) (q i)) (h : ∀ l,l < ∑ i,r i → distill l p=0) :
    Tendsto (fun t => moment G (Points.cons x (v t)) (Fin.cons (α:=fun _ => WickPol G) p q)) F
      (𝓝 (bond G x y (distill (∑ i,r i) p) (∏ i, q i))) := by
  classical
  let k := ∑ i,r i
  let B := MultilinearMap.mkPiAlgebra ℂ (Fin n) (WickPol G)
  let b (p) := bond G x y (distill k p)
  let Z : WickPol G →ₗ[ℂ] MultilinearMap ℂ (fun _ : Fin n => WickPol G) ℂ :=
    { toFun p := (b p).compMultilinearMap B
      map_add' p q := by ext1 x; simp [b]
      map_smul' c p := by ext1 x; simp [b] }
  let J : MultilinearMap ℂ (fun _ : Fin (n+1) => WickPol G) ℂ := LinearMap.uncurryLeft (M:=fun _ : Fin (n+1) => WickPol G) Z
  let W := Fin.cons (α:=fun _ : Fin (n+1) => WickPol G) p q
  change Tendsto _ F (𝓝 ((b p) (B q)))
  rw [show b p (B q)=J W by unfold W J; simp [Z], Multilabel.expansion (fun _ => monBasis G) J]
  have he t := Multilabel.expansion (fun _ => monBasis G) (moment G (Points.cons x (v t))) W
  change Tendsto (fun t => moment G _ W) _ _; simp_rw [he]; apply tendsto_finsetSum; intro i hi
  have hl (j) : MvPolynomial.coeff (i j) (W j)≠0 := Finsupp.mem_support_iff.mp (Fintype.mem_piFinset.mp hi j)
  have hk (j : Fin n) : bulk (i j.succ)=r j := hh j (hl j.succ)
  let Y := fun j => monBasis G (i j)
  let l := bulk (i 0)
  have hv : l ≥ k := by
    by_contra! ht
    have hp : (distill l p).coeff (i 0)≠0 := by
      rw [distill,gloss,MvPolynomial.coeff_weightedHomogeneousComponent,if_pos rfl]; exact hl 0
    rw [h l ht] at hp; exact hp (MvPolynomial.coeff_zero _)
  have hg := strict_bags hx H ht (i 0) (fun j => i j.succ) (by simp only [hk]; exact hv)
  simp_rw [hk] at hg
  apply Tendsto.const_smul
  convert! hg using 1
  ext1 t; congr 1; exact (Fin.cons_self_tail Y).symm

lemma collapses (p : WickPol G) (h : p∈ghost G d) (r : ℕ) (hp : ∀ j, j<r → distill j p=0) {x y : E4} (hx : x≠y) :
    ∀ q∈Host G d r,bond G x y (distill r p) q=0 := by
  intro q hq
  induction hq using Submodule.span_induction with
  | mem q hf =>
    obtain ⟨n,b,q,ha,rfl,rfl⟩ := hf
    let A (i : Fin n) := (↑i.val:ℝ) • basis timeAxis
    let v := fun t : ℝ => points fun i => y+t • A i
    have ht (i) : Tendsto (fun t : ℝ => v t i) little (𝓝 y) := by
      have ht : Tendsto (id : ℝ → ℝ) little (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
      change Tendsto (fun t => y + id t • A i) _ _
      simpa using tendsto_const_nhds (x := y) |>.add (ht.smul_const (A i))
    have hw (i) : ∀ᶠ t in little,x≠ v t i := ((ht i).eventually (isOpen_ne.mem_nhds hx.symm)).mono (fun t ht => Ne.symm ht)
    have he : ∀ᶠ t in little,Points.cons x (v t)∈conf _ := by
      filter_upwards [eventually_all.mpr hw,self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t he ht
      have hi : Injective A := fun i j h => by
        have hh := congr_arg (fun x : E4 => x timeAxis) h; simp [A] at hh; exact Fin.ext hh
      have hk : Injective (v t).ofLp := fun i j h => hi (smul_right_injective E4 (show t≠0 from (show t>0 from ht).ne') (add_left_cancel (a:=y) h))
      rw [show Points.cons x (v t)∈conf _ ↔ Injective (Fin.cons (α:=fun _ => E4) x (v t).ofLp) from Iff.rfl]
      intro i j; refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · exact fun _ => rfl
        intro hs; exact ((he j) hs).elim
      refine Fin.cases ?_ (fun j => ?_) j
      · intro hs; exact ((he i) hs.symm).elim
      exact fun h => congr_arg Fin.succ (hk h)
    apply tendsto_nhds_unique (strictly hx he ht p q b (fun i => (ha i).1) hp)
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with t H; exact (h n _ _ (fun i => (ha i).2) H).symm
  | zero => simp
  | add x y _ _ h h' => rw [map_add,h,h',add_zero]
  | smul c x _ h => rw [map_smul,h,smul_zero]

lemma hosted_out (p : WickPol G) (h : p∈ghost G d) (hh : ∀ j {p : WickPol G}, p ∈ shelf G k→ Pure j p → Painted p → p∈Host G d j)
    (hw : p∈shelf G k) (hp : p∈shellSector G w) : p=0 := by
  classical
  suffices hs : ∀ j : ℕ, distill j p=0 by
    rw [← MvPolynomial.sum_weightedHomogeneousComponent (fun _ : Slot G => (1:ℕ)) p]; change (finsum fun j => distill j p) = 0
    simp_rw [hs]; exact finsum_zero
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    let P := distill j p
    by_contra! hv
    let s := Signed.reflect timeAxis
    let K := mirrorBar s P
    have he : mirrorBar s K=P := by
      unfold K mirrorBar; simp only [LinearMap.coe_mk,AddHom.coe_mk,real_orient,← pol_mul]
      rw [show s*s=1 by unfold s; nth_rw 1 [← mirrored_inv timeAxis]; exact inv_mul_cancel _,pol_one]
      apply equalPol; intro A; rw [real_eval,real_eval,star_star]
    have hk : K≠0 := fun H => hv (he.symm.trans (by rw [H,map_zero]))
    have ht := detects timeAxis (basis timeAxis) (by simp) K hk
    let x := basis timeAxis
    let v := points (fun _ : Fin 1 => x)
    have hx : Ortho.move s x=-x := by ext1 i; by_cases hi:i=timeAxis <;> simp_all [x,s]
    change 0 < moment G (Table.Pairing.closedUp timeAxis v v) (Fin.append (mirrorBar s ∘ (fun _ : Fin 1 => K)) (fun _ => K)) at ht
    rw [show Table.Pairing.closedUp timeAxis v v = pairPoints (-x) x from ?_,
      show Fin.append (mirrorBar s ∘ (fun _ : Fin 1 => K)) (fun _ : Fin 1 => K) = Fin.cons P fun _ => K from ?_,← bond_eval] at ht
    · have hu : -x ≠ x := by intro ha; have H := congr_arg (fun x : E4 => x timeAxis) ha; simp [x] at H; linarith
      have hl : Pure j P := weightedHomogeneousComponent_isWeightedHomogeneous j p
      have ho : P∈shelf G k := gloss_shelf (fun _ => (1:ℕ)) j p hw
      have hw' : P∈shellSector G w := colors_grade (fun _ => (1:ℕ)) j hp
      have hq : K∈Host G d j := hh j (spaced_mirror s (spaced_real ho)) (pure_mirror s _ (pure_real _ hl))
        ((sector.mp (closed_sector (closed_sector hw' s).2 s).1).2)
      rw [show bond G (-x) x P K=0 from collapses p h j ih hu K hq] at ht
      exact lt_irrefl _ ht
    · ext1 i; fin_cases i
      exact he
      rfl
    ext1 i; refine Fin.addCases ?_ ?_ i
    · intro i; fin_cases i; rw [Table.Pairing.enter]; exact hx
    intro i; fin_cases i; rw [Table.Pairing.leave]; rfl
end YM.Maxwell.Free
