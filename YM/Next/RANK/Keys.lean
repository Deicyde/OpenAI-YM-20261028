import YM.Next.RANK.Foils

/-!
# Newton on separated endpoints, real cochain Taylor version

Extract highest coefficient from *ordered forward differences* at the vertex.
It is automatically a closed continuous form, even from discrete closure. Subtract
its actual cell-test cochain before using the next degree.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.CellsInt
open Tensor Maxwell Labels Function ContinuousMultilinearMap Lattice Equiv Submodule Analysis Filter Set
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

-- reuse sym-proof decomposition from Analysis.Jet

omit [NormedSpace ℝ V] in
theorem jump_sym {n : ℕ} (f : Cover → V) : ∀ t (s : Perm (Fin n)), jumps n (t ∘ s) f= jumps n t f := by
  induction n generalizing f with
  | zero => exact fun _ _ => rfl
  | succ n H =>
    cases n with
    | zero =>
      intro t s; exact congr_arg (fun x => jumps 1 x f) (funext (fun k => congr_arg t (@Subsingleton.elim (Fin 1) _ _ _)))
    | succ k =>
      let B (s : Perm (Fin (k+1))) := Perm.decomposeFin.symm (0,s)
      let P (s : Perm (Fin (k+2))) := ∀ t, jumps (k+2) (t ∘ s) f=jumps (k+2) t f
      have T (s) : P (B s) := by
        intro v; let w := Fin.tail v
        rw [show v ∘ B s=Fin.cons (v 0) (w ∘ s) by
          ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [w,B,Fin.tail]]
        conv_rhs => rw [← Fin.cons_self_tail v]
        rw [steps, steps]; exact H _ w s
      let i₁ := (0 : Fin (k+1)).succ
      have U : P (swap 0 i₁) := by
        intro v; let w:= Fin.tail (Fin.tail v)
        conv_rhs => rw [show v= Fin.cons (v 0) (Fin.cons (v i₁) w) by
          change v = Fin.cons (v 0) (Fin.cons (Fin.tail v 0) (Fin.tail (Fin.tail v)))
          rw [Fin.cons_self_tail, Fin.cons_self_tail]]
        rw [show v ∘ swap 0 i₁ = Fin.cons (v i₁) (Fin.cons (v 0) w) by
          ext i; refine Fin.cases ?_ (fun j => ?_) i
          · simp
          refine Fin.cases ?_ (fun n => ?_) j
          · dsimp only [i₁]; simp
          simp only [w, Function.comp, swap_apply_def, i₁, Fin.succ_ne_zero, Fin.succ_inj,↓reduceIte,Fin.cons_succ]; rfl]
        rw [steps,steps,steps,steps, hop]
      have M (s t : Perm (Fin (k+2))) (hx : P s) (hy : P t) : P (s*t) := fun v => (hy (v ∘ s)).trans (hx v)
      have V (i : Fin (k+2)) : P (swap 0 i) := by
        refine Fin.cases (by intro v;simp) ?_ i
        intro j
        let t := swap 0 j
        have he := swap_apply_apply (B t) 0 i₁; rw [show B t 0=0 by simp [B],show B t i₁=j.succ by simp [B,t,i₁]] at he
        rw [he]; refine M _ _ (M _ _ (T _) U) ?_
        intro v; rw [← T t]; rw [show (v ∘ ⇑(B t)⁻¹) ∘ ⇑(B t) = v by ext; simp]
      intro v s; obtain ⟨⟨i,q⟩,rfl⟩ := Perm.decomposeFin.symm.surjective s
      have he : Perm.decomposeFin.symm (i,q) = swap 0 i*B q := by ext a; refine Fin.cases ?_ (fun j => ?_) a <;> simp [B]
      rw [he]; exact M _ _ (V i) (T q) v

-- component Taylor coefficient; fill symmetric by basis values

private def base := (EuclideanSpace.basisFun Axis ℝ).toBasis
private lemma based (i : Axis) : base i=basis i := EuclideanSpace.basisFun_apply ..

private lemma cultivate {n : ℕ} (f : (Fin n → Axis) → V) : ∃ F : T E4 V n, ∀ i,F (basis ∘ i)= f i := by
  induction n with
  | zero => exact ⟨ContinuousMultilinearMap.uncurry0 _ _ (f 0),fun i => congr_arg f (Subsingleton.elim ..)⟩
  | succ n H =>
    choose A H using fun i => H (fun t => f (Fin.cons i t))
    let F := (base.constr ℝ A).toContinuousLinearMap
    refine ⟨F.uncurryLeft,fun i => ?_⟩
    have hx : F (basis (i 0))=A (i 0) := by
      rw [← based]; exact base.constr_basis ℝ A _
    change F (basis (i 0)) (basis ∘ Fin.tail i)=_; rw [hx,H,Fin.cons_self_tail]

def seed {n : ℕ} (f : (Fin n → Axis) → V) := (cultivate f).choose
lemma fertile {n : ℕ} (f : (Fin n→Axis)→V) (i) : seed f (basis ∘ i)= f i := by unfold seed; exact (cultivate f).choose_spec i
lemma seedEq {n : ℕ} (S U : T E4 V n) (h : ∀ i : Fin n → Axis,S (basis ∘ i)=U (basis ∘ i)) : S=U := by
  apply toMultilinearMap_injective; apply Module.Basis.ext_multilinear (fun _ => base)
  intro v; simp_rw [based]; exact h v

-- Cartesian cochains antisymmetric
abbrev C2 (V : Type*) := Axis → Axis → Cover → V
structure Secure (f : C2 V) : Prop where
  ax i j : f i j= - f j i
  holds a b c : stepValue (f b c) a+stepValue (f c a) b+stepValue (f a b) c=0

variable {F H : C2 V}
abbrev leaf (j : ℕ) (F : C2 V) := fun (i l : Axis) => seed (fun t : Fin j → Axis => (j.factorial:ℝ)⁻¹ • jumps j t (F i l) 0)

omit [NormedSpace ℝ V] in
lemma jumps_add (n : ℕ) (t) (x y : Cover → V) : jumps n t (x+y)= jumps n t x+jumps n t y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n h => rw [jumps, jumps,jumps,show stepValue (x+y) (t 0) = stepValue x (t 0)+stepValue y (t 0) from funext (fun z => add_sub_add_comm ..),h]
lemma jumps_scale (n : ℕ) (t) (x : Cover → V) (a : ℝ) : jumps n t (a • x) = a • jumps n t x := by
  induction n generalizing x with
  | zero => rfl
  | succ n h => rw [jumps,jumps, show stepValue (a • x) (t 0)=a • stepValue x (t 0) from funext (fun z => (smul_sub a (x (z+ _)) (x z)).symm),h]
omit [NormedSpace ℝ V] in
lemma jumps_zero (n : ℕ) (t : Fin n → Axis) : jumps n t (0 : Cover→V)=0 := by
  have ht := jumps_add n t (0:Cover→V) 0; rw [add_zero] at ht; exact (left_eq_add.mp ht)
omit [NormedSpace ℝ V] in
lemma jumps_neg (n : ℕ) (t : Fin n → Axis) (x : Cover→V) : jumps n t (-x)= - jumps n t x := by simpa only [zero_sub, jumps_zero] using! jumps_sub n t (0:Cover→V) x

lemma sprout (j : ℕ) (h : Secure F) : ClosedJet (leaf j F) := by
  have hs (i l : Axis) : Sym (leaf j F i l) := by
    let P := leaf j F i l
    intro v s
    have hx : P.domDomCongr s=P := by
      apply seedEq; intro t
      change leaf j F i l (YM.basis ∘ (t ∘ s))=leaf j F i l _
      simp only [leaf,fertile,jump_sym]
    exact congr_arg (fun Z : T E4 V j => Z v) hx
  refine ⟨hs,fun i l => ?_,fun a b c x => ?_⟩
  · apply seedEq; intro t; rw [leaf,_root_.neg_apply,fertile,leaf,fertile]; simp_rw [h.ax i l, jumps_neg, Pi.neg_apply,smul_neg]
  cases j with
  | zero =>
    have he (A : T E4 V 0) (a) : grad a (Tensor.diagonal A) x = 0 := by
      rw [show Tensor.diagonal A = fun _ => Tensor.diagonal A 0 from funext fun _ => congr_arg A (Subsingleton.elim ..)]
      simp [grad,D]
    rw [he,he,he]; simp
  | succ n =>
    let P i l := leaf (n+1) F i l
    let R (a i l) := (P i l).curryLeft (basis a)
    have he : R a b c + R b c a + R c a b=0 := by
      apply seedEq; intro t
      have hc (a b c : Axis) : R a b c (basis ∘ t)=(↑(n+1).factorial:ℝ)⁻¹ • jumps n t (stepValue (F b c) a) 0 := by
        unfold R P; rw [curryLeft_apply,leaf, show Fin.cons (basis a) (basis ∘ t)=basis ∘ Fin.cons a t by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl, fertile,steps]
      rw [add_apply,add_apply,hc,hc,hc, ← smul_add,← smul_add]
      have hh := jumps_zero (V:=V) n t; nth_rw 1 [← h.holds a b c,jumps_add,jumps_add] at hh
      rw [show jumps n t (stepValue (F b c) a) 0 + jumps n t (stepValue (F c a) b) 0 + jumps n t (stepValue (F a b) c) 0 = (0:V) from congr_fun hh (0:Cover),smul_zero]; rfl
    have hc (a b c : Axis) : grad a (Tensor.diagonal (P b c)) x=(n+1) • (R a b c) (fun _ => x) := differential_diagonal _ (hs b c) x _
    change grad a (Tensor.diagonal (P b c)) _+grad b (Tensor.diagonal (P c a)) _+grad c (Tensor.diagonal (P a b)) _=0
    rw [hc,hc,hc,← smul_add,← smul_add,← add_apply, ← add_apply,he,zero_apply,smul_zero]
end YM.Next.Rank.CellsInt
