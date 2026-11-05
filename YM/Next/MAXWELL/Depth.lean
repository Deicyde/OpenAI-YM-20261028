import YM.Next.MAXWELL.Ends
import YM.Next.MAXWELL.Statistic

/-!
# Weight-4 point-pair metric direction

Internal tests cannot infer rotations from arbitrary mixed-jet metric
at higher weights. Use anchored p on whole zero-order curvature sector,
and include House reflection on that tensor, *then* change direction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder
variable {G : Gauge} {j l d n : ℕ}

def pairPoints (x y : E4) : Points 2 := Points.cons x (points fun _ => y)

def bond (G : Gauge) (x y : E4) : WickPol G →ₗ[ℂ] WickPol G →ₗ[ℂ] ℂ where
  toFun p := ((moment G (pairPoints x y)).curryLeft p).toLinearMap (fun _ => 0) 0
  map_add' p q := by apply LinearMap.ext; intro z; simp
  map_smul' p q := by apply LinearMap.ext; intro z; simp

lemma bond_eval (x y : E4) (p q : WickPol G) : bond G x y p q = moment G (pairPoints x y)
    (Fin.cons (α:=fun _ => WickPol G) p (fun _ => q)) := by
  unfold bond; simp only [LinearMap.coe_mk, AddHom.coe_mk, MultilinearMap.toLinearMap_apply,MultilinearMap.curryLeft_apply]; congr 1
  ext1 i; fin_cases i <;> simp

lemma pair_ok {x y : E4} (h : x≠y) : pairPoints x y∈conf _ := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [pairPoints,h,h.symm,Points.cons]

lemma pair_flow (x y z : E4) : bond G (x+z) (y+z) = bond G x y := by
  apply LinearMap.ext; intro p; apply LinearMap.ext; intro q; rw [bond_eval,bond_eval]
  have he : pairPoints (x+z) (y+z)=Points.across z (pairPoints x y) := by ext1 i; fin_cases i <;> simp [pairPoints,Points.cons]
  rw [he,moment_across]

lemma closed_sector {p : WickPol G} (h : p∈shellSector G d) (s : Ortho) :
    reflectPol s p ∈ shellSector G d ∧ realForm p∈ shellSector G d := by
  obtain ⟨A,rfl⟩ := h; rw [← real_eats, ← pulls_label]; exact ⟨⟨_,rfl⟩,_,rfl⟩

lemma real_orient (s : Ortho) (p : WickPol G) : realForm (reflectPol s p)=reflectPol s (realForm p) := by
  apply equalPol; intro A; rw [real_eval, reflects_eval, reflects_eval,real_eval]

/-- Use axis separation of length r. -/
lemma pair_nonzero (a : Axis) (p : WickPol G) {r : ℝ} (hr : 0 < r) (hp : p∈ shellSector G d)
    (h : ∀ q ∈ shellSector G d, bond G ((-r) • basis a) 0 p q=0) : p=0 := by
  let q := mirrorBar (Signed.reflect a) p
  have hu : mirrorBar (Signed.reflect a) q = p := by
    unfold q mirrorBar
    simp only [LinearMap.coe_mk,AddHom.coe_mk,real_orient,← pol_mul]
    rw [show Signed.reflect a * Signed.reflect a=1 by nth_rw 1 [← mirrored_inv a]; exact inv_mul_cancel _,pol_one]
    apply equalPol; intro A; rw [real_eval,real_eval,star_star]
  by_contra he
  have hq : q≠0 := fun H => he (hu.symm.trans (by rw [H,map_zero]))
  let z := (r/2) • basis a
  have hv : 0 < z a := by simp [z]; linarith
  have hs : Table.Pairing.closedUp a (points fun _ : Fin 1 => z) (points fun _ : Fin 1 => z)=pairPoints (-z) z := by
    ext1 i; refine Fin.addCases ?_ ?_ i
    · intro i; fin_cases i; apply PiLp.ext; intro k
      rw [Table.Pairing.enter];
      change through a z k=(-z) k
      by_cases ht:k=a <;> simp_all [through,z]
    intro i; fin_cases i; rw [Table.Pairing.leave]; rfl
  have hc := detects a z hv q hq
  unfold score cabinet at hc; rw [hs] at hc
  have ht : (bond G (-z) z p q) = 0 := by
    rw [← pair_flow (-z) z (-z)]; simp only [add_neg_cancel]
    rw [show -z + -z = (-r) • basis a from ?_]
    · exact h q ((closed_sector (closed_sector hp 1).2 _).1)
    unfold z; rw [← neg_smul,← add_smul]; ring_nf
  exfalso; apply lt_irrefl (0:ℂ)
  rw [bond_eval] at ht
  have hh : Fin.append (mirrorBar (Signed.reflect a) ∘ (fun _ : Fin 1 => q)) (fun _ : Fin 1 => q) = Fin.cons p (fun _ => q) := by
    ext1 i; fin_cases i
    exact hu
    rfl
  rwa [hh,ht] at hc

/-- Point sectors with no jet-shift indices don't depend on House direction
once the corresponding index reflection acted. -/
private def stock (p : List (Probe G 0)) := (p.map (symbol 0)).prod

private def Floor (G : Gauge) := Submodule.span ℂ (Set.range (stock (G:=G)))

private lemma fits_floor (h : G.Simple) : shellSector G 4 ≤ Floor G := by
  rw [low_support h]; apply sup_le
  · rw [BottomOnly,Submodule.span_le]; rintro p hp; obtain rfl : p=(1:WickPol G) := hp; exact Submodule.subset_span ⟨[],rfl⟩
  rw [Teams,Submodule.span_le]; rintro p ⟨a,b,rfl⟩; apply Submodule.sum_mem; intro i _
  exact Submodule.subset_span (show _∈range stock from ⟨[flavor 0 i a,flavor 0 i b],by simp [stock,bit]⟩)

private lemma house_cost (p q : Probe G 0) {x y : E4} (hx : x≠0) (hy : y≠0) (he : ‖x‖=‖y‖) :
    K (probeTurn (house x) p) q x 0 = K (probeTurn (house y) p) q y 0 := by
  induction q using leg_probe_induction with
  | vars u c i m =>
    rw [show leg u c i m = omegaLeg c i m from congr_arg (fun v : Fin 0 → E4 => leg v c i m) (Subsingleton.elim ..)]
    rw [probe_formula _ i m c hx,probe_formula _ i m c hy]
    have ht x (A : Shell G 0) : probeTurn (house x) p (solutionTurn (house x) A)=p A := by
      change p (solutionTurn (house x)⁻¹ (solutionTurn (house x) A))=p A; rw [← solution_rep, inv_mul_cancel,solution_id]
    rw [sub_zero,sub_zero,ht,ht,he]
  | zero => rw [K_pairing _ _ hx,K_pairing _ _ hy]; simp
  | add a b hp hq => rw [K_pairing _ _ hx,K_pairing _ _ hy] at *; simp only [map_add,hp,hq]
  | smul t v h => rw [K_pairing _ _ hx,K_pairing _ _ hy] at *; rw [map_smul,map_smul,h]

private lemma bond_rotate_same_list (p q : List (Probe G 0)) {x y : E4} (hx : x≠0) (hy : y≠0) (he : ‖x‖=‖y‖) :
    bond G x 0 (reflectPol (house x) (stock p)) (stock q)=bond G y 0 (reflectPol (house y) (stock p)) (stock q) := by
  let Q (x : E4) (s : Probe G 0) : Factor G := ⟨0,probeTurn (house x) s⟩
  let f : Probe G 0 → Factor G := fun u => ⟨0,u⟩
  let K (x : E4) := Sum.elim (fun s : Probe G 0 => ((x,Q x s):Limb G)) (fun s => ((0,f s) : Limb G))
  let L := p.map Sum.inl ++ q.map Sum.inr
  have hp z (p) : reflectPol (house z) (stock p) = ((p.map (Q z)).map letter).prod := by
    induction p with
    | nil => exact map_one _
    | cons a b ih => unfold stock; rw [List.map_cons,List.prod_cons,map_mul, reflect_symbol]; change _ * reflectPol (house z) (stock b)=_; rw [ih]; rfl
  have heq (x : E4) (hx : x≠0) : bond G x 0 (reflectPol (house x) (stock p)) (stock q)=pairCost linkEntry (L.map (K x)) := by
    rw [bond_eval,hp x p];
    let Y := points fun _ : Fin 1 => (0:E4)
    rw [show (fun _ : Fin 1 => stock q)=bag (fun _ => (0:Fin 1)) f q from ?_,show pairPoints x 0 = Points.cons x Y from rfl, planted Y f _ _ _ (pair_ok hx)]
    · simp only [L,List.map_append, List.map_map]; rfl
    ext1 i; fin_cases i; simp [stock,bag]; rfl
  rw [heq x hx,heq y hy,pair_transfer,pair_transfer]; congr 1; funext i j
  rcases i with i|i <;> rcases j with j|j
  · simp [K,link_zero]
  · change linkEntry (x,Q x i) _ = linkEntry (y,Q y i) _; unfold K; simp only [Sum.elim_inr]
    rw [link_eq _ _ _ _ hx,link_eq _ _ _ _ hy]; exact congr_arg ((↑) : ℝ→ℂ) (house_cost i j hx hy he)
  · unfold K; simp only [Sum.elim_inr,Sum.elim_inl,link_eq 0 x _ _ (Ne.symm hx),link_eq 0 y _ _ (Ne.symm hy)]
    rw [K_symmetric _ _ (Ne.symm hx),K_symmetric _ _ (Ne.symm hy)]; exact congr_arg ((↑) : ℝ→ℂ) (house_cost j i hx hy he)
  rfl

lemma corridor (h : G.Simple) {x y : E4} (hx : x≠0) (hy : y≠0) (he : ‖x‖=‖y‖) (p q : WickPol G)
    (hp : p ∈ shellSector G 4) (hq : q ∈ shellSector G 4) :
    bond G x 0 p q=bond G y 0 (reflectPol (house y * house x) p) q := by
  have H : ∀ p∈Floor G,∀ q∈Floor G, bond G x 0 (reflectPol (house x) p) q=bond G y 0 (reflectPol (house y) p) q := by
    intro p hp; induction hp using Submodule.span_induction with
    | mem u h =>
      obtain ⟨p,rfl⟩ := h
      intro v hv; induction hv using Submodule.span_induction with
      | mem v h => obtain ⟨q,rfl⟩ := h; exact bond_rotate_same_list p q hx hy he
      | zero => simp
      | add p q _ _ h k => rw [map_add,map_add,h,k]
      | smul c p _ h => rw [map_smul,map_smul,h]
    | zero => simp
    | add p q _ _ h k => intro u hu; rw [map_add,map_add,map_add,map_add,LinearMap.add_apply,LinearMap.add_apply,h u hu,k u hu]
    | smul t p _ h => intro u hu; rw [map_smul,map_smul,map_smul,map_smul,LinearMap.smul_apply,LinearMap.smul_apply,h u hu]
  have hr := H _ (fits_floor h (closed_sector hp (house x)).1) _ (fits_floor h hq)
  rw [← pol_mul, ← pol_mul, show house x * house x=1 by nth_rw 1 [← house_inv]; exact inv_mul_cancel _,pol_one] at hr
  exact hr

lemma two_stat {x : E4} (hx : x≠0) {T : Module.End ℂ (WickPol G)} (hT : silence G d T) {p q}
    (hp : p ∈ shellSector G d) (hq : q ∈ shellSector G d) :
    bond G x 0 (T p) q + bond G x 0 p (T q)=0 := by
  let V := Fin.cons (α:=fun _ : Fin 2 => WickPol G) p (fun _ => q)
  have he := hT 2 V _ (fun i => Fin.cases hp (fun j => hq) i) (pair_ok hx)
  rw [Fin.sum_univ_two] at he
  rw [bond_eval,bond_eval];
  rw [show Fin.cons (α:=fun _ : Fin 2 => WickPol G) (T p) (fun _ => q) = update V 0 (T (V 0)) from
    (Fin.update_cons_zero ..).symm,
    show Fin.cons (α:=fun _ : Fin 2 => WickPol G) p (fun _ => T q) = update V 1 (T (V 1)) from ?_]; exact he
  ext1 i; fin_cases i <;> simp [V]

lemma low_motion (h : G.Simple) {d} (hd : 4≤d) {T : Module.End ℂ (WickPol G)} (H : silence G d T)
    (ht : ∀ p ∈ shellSector G 4,T p∈shellSector G 4)
    (a : Axis) {r : ℝ} (hr : 0 < r) {v : E4} (hv : ‖v‖=r) {p : WickPol G} (hp : p∈shellSector G 4) :
    let x := (-r) • basis a
    reflectPol (house x * house v) (T p) = T (reflectPol (house x * house v) p) := by
  intro x
  have he : ‖x‖=r := by simp [x,norm_smul,abs_of_pos hr]
  have hx : x ≠ 0 := norm_pos_iff.mp (by rw [he]; assumption)
  have hw : v ≠ 0 := norm_pos_iff.mp (by rw [hv]; assumption)
  let s := house x * house v
  let A := reflectPol s p
  have hp' : A∈shellSector G 4 := (closed_sector hp _).1
  change reflectPol s (T p)=T A; apply sub_eq_zero.mp
  have hg := ht _ hp
  apply pair_nonzero a _ hr (Submodule.sub_mem _ ((closed_sector hg s).1) (ht _ hp'))
  intro q hq
  have hi := two_stat hw H (chain hd hp) (chain hd hq)
  rw [corridor h hw hx (hv.trans he.symm) _ _ hg hq, corridor h hw hx (hv.trans he.symm) _ _ hp (ht _ hq)] at hi
  have hA := two_stat hx H (chain hd hp') (chain hd hq)
  rw [map_sub,LinearMap.sub_apply,sub_eq_zero]; exact add_right_cancel (hi.trans hA.symm)
end YM.Maxwell.Free
