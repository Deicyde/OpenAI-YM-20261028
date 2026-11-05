import YM.Next.BOUNDARY.Alias
import YM.Push.STRESS_FLUX.Orbits
import YM.Push.STRESS_FLUX.Polynomial
import YM.Work.B04


/-!
upper bounds for the signed-coordinate equivariant spaces at each of the
relevant low weights on the actual radial-jet labels (before Maxwell projection).
-/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux
open Labels Function Gauge
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace

variable {G : Gauge} {d : ℕ}

def spinR {d : ℕ} (s : Signed) : Module.End ℝ (Label G d) := (tensor s.ortho).restrictScalars ℝ
def conjR {d : ℕ} : Module.End ℝ (Label G d) where
  toFun := realBar
  map_add' := map_add _
  map_smul' _ _ := realBar_scale ..

section Spaces
variable {V : Type*} [AddCommGroup V] [Module ℝ V] (K : Signed → Module.End ℝ V) (J : Module.End ℝ V)

def tensors : Submodule ℝ (Axis → Axis → V) where
  carrier := { T | (∀ a b, T a b=T b a) ∧ (∀ a b, J (T a b) = T a b) ∧
    ∀ s a b, K s (T a b) = (sign s a*sign s b) • T (s.perm a) (s.perm b) }
  zero_mem' := by simp
  add_mem' := by
    intro x y ⟨A,B,C⟩ ⟨D,E,F⟩
    simp only [Set.mem_setOf_eq,Pi.add_apply, map_add,B,C,E,F,smul_add]
    exact ⟨fun a b => congr_arg₂ _ (A a b) (D a b),fun _ _ => trivial, fun _ _ _ => trivial⟩
  smul_mem' := by
    intro c x ⟨A,B,C⟩
    simp only [Set.mem_setOf_eq,Pi.smul_apply, map_smul, B,C]
    exact ⟨fun a b => congr_arg _ (A a b),fun _ _ => trivial, fun _ _ _ => smul_comm ..⟩

def vectors : Submodule ℝ (Axis → V) where
  carrier := { T | (∀ a, J (T a) = T a) ∧ ∀ s a, K s (T a) = sign s a • T (s.perm a) }
  zero_mem' := by simp
  add_mem' := by
    intro x y ⟨A,B⟩ ⟨C,D⟩
    simp only [Set.mem_setOf_eq,Pi.add_apply, map_add,B,C,A,D,smul_add, implies_true,and_self]
  smul_mem' := by
    intro c x ⟨A,B⟩
    simp only [Set.mem_setOf_eq,Pi.smul_apply,map_smul,A,B,smul_comm c,implies_true,and_self]
end Spaces

abbrev RawTwo (G : Gauge) := tensors (V:=Label G 4) spinR conjR
abbrev RawOne (G : Gauge) := vectors (V:=Label G 5) spinR conjR

lemma stress_rows (G : Gauge) (w : Coeff) : stress G w ∈ RawTwo G :=
  ⟨stress_symm w,stress_real w,fun s => stress_tensor s w⟩
lemma eom_rows (G : Gauge) : eom G ∈ RawOne G := ⟨eom_real, fun s a => eom_vector a s⟩

private lemma low_moves {A B : Low G} (ha : A.Sym) (hb : B.Sym) {v w : Label G d}
    (hA : ∀ J, read J v.val=A.eval J) (hB : ∀ J, read J w.val=B.eval J) (s : Signed) (c : ℝ)
    (hv : tensor s.ortho v = c • w) : A = B.comp (c • LinearMap.id) (fun _ => Taylor.turn s.ortho) := by
  refine Low.ext _ _ ha (B.comp_sym hb _ _) (fun J => ?_)
  let J' := axesMove (fun _ => Taylor.turn s.ortho) J
  have he : shifted s J' = J := by
    funext i; change Taylor.turn s.ortho⁻¹ (Taylor.turn s.ortho (J i)) = J i
    rw [← Taylor.turn_mul,inv_mul_cancel,Taylor.oneTurn]
  rw [Low.comp_eval,← hA,← hB]
  change read J v.val = c • read J' w.val
  rw [← he,← eval_changed, show changed _ v.val = c • w.val from congr_arg Subtype.val hv,read_smul]

private lemma low_real {A : Low G} (ha : A.Sym) {v : Label G d} (hA : ∀ J, read J v.val=A.eval J)
    (hr : realBar v=v) : A = A.comp ((starL' ℝ : ℂ ≃L[ℝ] ℂ).toLinearEquiv.toLinearMap) (fun _ => LinearMap.id) := by
  apply Low.ext _ _ ha (A.comp_sym ha _ _) (fun J => ?_)
  rw [Low.comp_eval, ← hA, ← hA]
  change read J v.val = star (read J v.val)
  rw [← conj_value]; exact congr_arg (fun p => Labels.read J (p : Label G d).val) hr.symm

private lemma of_real_zero {x : ℂ} (hx : x = star x) (hr : x.re = 0) : x = 0 := by
  exact Complex.ext hr (Complex.conj_eq_iff_im.mp hx.symm)

private lemma vanish_sq {A : Low G} (H : G.Simple) (hA : ∀ g, A.comp LinearMap.id (fun _ => Taylor.paint g) = A)
    (e : G.Color) (he : ‖e‖=1) (hz : ∀ i j k l, A.sq (leg0 i j e) (leg0 k l e) = 0) : A.sq = 0 := by
  have h (i j k l : Axis) (x y : G.Color) : A.sq (leg0 i j x) (leg0 k l y) = 0 := by
    let B := A.sq.compl₁₂ (leg0 i j) (leg0 k l)
    have he := bilinear_invariant H B (fun g u w => show A.sq (leg0 _ _ _) (leg0 _ _ _) = _ by
      rw [← paint_leg0,← paint_leg0]; exact congr_arg (fun A => Low.sq A (leg0 i j u) (leg0 k l w)) (hA g)) he x y
    change _ = (_:ℝ) • A.sq _ _ at he
    rw [hz,smul_zero] at he; exact he
  apply LinearMap.ext₂; intro x y
  have hx (x : Taylor G 0) : x = (2:ℝ)⁻¹ • (∑ i, ∑ j, leg0 i j (curl0 i j x)) := by rw [sum_legs0, smul_smul]; norm_num
  change A.sq x y=0; rw [hx x,hx y]; simp [h]

private lemma vanish_mix {A : Low G} (H : G.Simple) (hA : ∀ g, A.comp LinearMap.id (fun _ => Taylor.paint g) = A)
    (e : G.Color) (he : ‖e‖=1) (hz : ∀ r i j k l, A.mix (leg0 i j e) (leg1 r k l e) = 0) : A.mix = 0 := by
  have h (i j r k l : Axis) (x y : G.Color) : A.mix (leg0 i j x) (leg1 r k l y) = 0 := by
    let B := A.mix.compl₁₂ (leg0 i j) (leg1 r k l)
    have he := bilinear_invariant H B (fun g u w => show A.mix (leg0 _ _ _) (leg1 _ _ _ _) = _ by
      rw [← paint_leg0,← paint_leg1]; exact congr_arg (fun A => Low.mix A (leg0 i j u) (leg1 r k l w)) (hA g)) he x y
    change _ = (_:ℝ) • A.mix _ _ at he; rw [hz,smul_zero] at he; exact he
  apply LinearMap.ext₂; intro x y
  have hx : x = (2:ℝ)⁻¹ • (∑ i, ∑ j, leg0 i j (curl0 i j x)) := by rw [sum_legs0, smul_smul]; norm_num
  have hy : y = (2:ℝ)⁻¹ • (∑ k, ∑ l, ∑ r, leg1 r k l (curl1 r k l y)) := by rw [sum_legs1, smul_smul]; norm_num
  change A.mix x y=0; rw [hx,hy]; simp [h]

private def realProbe (J : Jet G) : Label G d →ₗ[ℝ] ℝ := Complex.reCLM.toLinearMap.comp
    (((read J).toLinearMap.comp (localFields G d).subtype).restrictScalars ℝ)

private def squareProbe (e : G.Color) (i j k l : Axis) : Label G d →ₗ[ℝ] ℝ :=
  let p : Jet G := Pi.single 0 (leg0 i j e)
  let q : Jet G := Pi.single 0 (leg0 k l e)
  (2:ℝ)⁻¹ • (realProbe (p+q) - realProbe p - realProbe q + realProbe 0)

private lemma squareProbe_eval {v : Label G d} {A : Low G} (h : ∀ J, read J v.val = A.eval J) (ha : A.Sym)
    (e : G.Color) (i j k l : Axis) : squareProbe e i j k l v = (A.sq (leg0 i j e) (leg0 k l e)).re := by
  simp only [squareProbe,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sub_apply,
    show ∀ J, realProbe J v = (A.eval J).re from fun J => congr_arg Complex.re (h J),Low.eval]
  simp [ha (leg0 k l e) (leg0 i j e)]; ring

private def tensorTest (e : G.Color) : RawTwo G →ₗ[ℝ] Fin 4 → ℝ :=
  let read (a b : Axis) : RawTwo G →ₗ[ℝ] Label G 4 := LinearMap.proj b ∘ₗ LinearMap.proj a ∘ₗ (RawTwo G).subtype
  LinearMap.pi ![realProbe 0 ∘ₗ read 0 0, squareProbe e 0 1 0 1 ∘ₗ read 0 0,
    squareProbe e 1 2 1 2 ∘ₗ read 0 0,squareProbe e 0 1 2 1 ∘ₗ read 0 2]

lemma has_color (H : G.Simple) : ∃ e : G.Color, ‖e‖ = 1 := by
  haveI := H.nontrivial_color
  obtain ⟨e,he⟩ := exists_ne (0:G.Color)
  exact ⟨‖e‖⁻¹ • e, by simp [norm_smul, he]⟩

theorem finrank_two (H : G.Simple) : Module.finrank ℝ (RawTwo G) ≤ 4 := by
  obtain ⟨e,he⟩ := has_color H
  conv_rhs => rw [← Module.finrank_fin_fun ℝ (n:=4)]
  refine LinearMap.finrank_le_finrank_of_injective (f := tensorTest e) ?_
  refine (LinearMap.ker_eq_bot (R:=ℝ) (R₂:=ℝ) (M:=RawTwo G) (M₂:=Fin 4 → ℝ) (f:=(tensorTest (G:=G) e))).mp ?_
  refine LinearMap.ker_eq_bot'.mpr ?_
  rintro ⟨v, hS, hR, hT⟩ h0
  change (tensorTest e ⟨v,hS,hR,hT⟩) = 0 at h0
  choose A ha hm hA using fun i j => low (by decide : 4 ≤ 5) (v i j)
  have hG i j := (A i j).covariance (ha i j) (hA i j)
  let t (p q i j k l : Axis) := (A p q).sq (leg0 i j e) (leg0 k l e)
  have ho : Orbit t := by
    refine ⟨fun s p q i j k l => ?_,fun p q i j k l => ?_,fun p q i j k l => ?_⟩
    · have h := low_moves (ha p q) (ha (s.perm p) (s.perm q)) (hA p q) (hA (s.perm p) (s.perm q)) s _ (hT s p q)
      calc
        t p q i j k l = (sign s p * sign s q) • (A (s.perm p) (s.perm q)).sq (Taylor.turn s.ortho (leg0 i j e)) (Taylor.turn s.ortho (leg0 k l e)) :=
          congr_arg (fun A => Low.sq A (leg0 i j e) (leg0 k l e)) h
        _ = _ := by rw [turn_leg0,turn_leg0,map_smul (A _ _).sq, LinearMap.smul_apply,map_smul, smul_smul, smul_smul]; simp only [mul_assoc,t]
    · unfold t; nth_rw 1 [leg0_swap i j]; simp
    unfold t; nth_rw 1 [leg0_swap k l]; simp
  have hs (p q i j k l : Axis) (h : squareProbe e i j k l (v p q) = 0) : t p q i j k l = 0 := by
    refine of_real_zero (congr_arg (fun A => Low.sq A (leg0 i j e) (leg0 k l e)) (low_real (ha p q) (hA p q) (hR p q))) ?_
    exact (squareProbe_eval (hA p q) (ha p q) ..).symm.trans h
  have h1 := hs 0 0 0 1 0 1 (congr_fun h0 1); have h2 := hs 0 0 1 2 1 2 (congr_fun h0 2); have h3 := hs 0 2 0 1 2 1 (congr_fun h0 3)
  have hv i j := vanish_sq H (hG i j) e he (ho.test h1 h2 h3 ((ha 0 2 ..).trans h3) i j)
  have hl (s : Signed) (p q : Axis) := congr_arg Low.c (low_moves (ha p q) (ha (s.perm p) (s.perm q)) (hA p q)
      (hA (s.perm p) (s.perm q)) s _ (hT s p q))
  have hc (p q : Axis) : (A p q).c = 0 := by
    by_cases hpq : p=q
    · have h' := hl ⟨Equiv.swap 0 p,fun _ => false⟩ 0 0
      simp only [Low.comp, Equiv.swap_apply_left,LinearMap.id_coe, id_eq,sign,
        Bool.false_eq_true,if_false,one_mul,one_smul] at h'
      rw [← hpq,← h']; refine of_real_zero (congr_arg Low.c (low_real (ha 0 0) (hA 0 0) (hR 0 0))) ?_
      have hr := congr_fun h0 0; change (Labels.read (0 : Jet G) (v 0 0).val).re = 0 at hr; simpa [hA,Low.eval] using hr
    have hc : (A p q).c = - (A p q).c := by simpa [sign,Signed.mirror,hpq, Low.comp] using hl (Signed.mirror p) p q
    linear_combination hc/2
  apply Subtype.ext; funext a b; apply label_ext; intro J
  change read J (v a b).val = read J (0 : Label G 4).val
  simp [hA,Low.eval,hv,(A a b).linear_invariant H (hG a b),hm a b le_rfl, hc]

private def mixProbe (e : G.Color) (r i j k l : Axis) : Label G d →ₗ[ℝ] ℝ :=
  let p : Jet G := Pi.single 0 (leg0 i j e)
  let q : Jet G := Pi.single 1 (leg1 r k l e)
  realProbe (p+q) - realProbe p - realProbe q + realProbe 0

private lemma mixProbe_eval {v : Label G d} {A : Low G} (h : ∀ J, read J v.val = A.eval J)
    (e : G.Color) (r i j k l : Axis) : mixProbe e r i j k l v = (A.mix (leg0 i j e) (leg1 r k l e)).re := by
  simp only [mixProbe,LinearMap.add_apply,LinearMap.sub_apply,
    show ∀ J, realProbe J v = (A.eval J).re from fun J => congr_arg Complex.re (h J),Low.eval]; simp; abel

private def vectorTest (e : G.Color) : RawOne G →ₗ[ℝ] Fin 3 → ℝ :=
  let read := LinearMap.proj (0:Axis) ∘ₗ (RawOne G).subtype
  LinearMap.pi ![mixProbe e 0 0 1 0 1 ∘ₗ read, mixProbe e 2 0 1 2 1 ∘ₗ read,mixProbe e 2 2 1 0 1 ∘ₗ read]

lemma sign_invert (a : Axis) : sign (⟨Equiv.refl _,fun _ => true⟩ : Signed) a = -1 := rfl
@[simp] lemma inverted_turn (A : Taylor G 0) : Taylor.turn (⟨Equiv.refl _,fun _ => true⟩ : Signed).ortho A=A := by
  let s : Signed := ⟨Equiv.refl _,fun _ => true⟩
  have hi (i j : Axis) (x : G.Color) : Taylor.turn s.ortho (leg0 i j x)=leg0 i j x := by simp only [turn_leg0,s,sign_invert,neg_mul_neg,one_mul,one_smul]; rfl
  change Taylor.turn s.ortho A=A
  rw [show A = (2:ℝ)⁻¹ • (∑ i, ∑ j, leg0 i j (curl0 i j A)) by rw [sum_legs0,smul_smul]; norm_num]; simp only [map_smul,map_sum,hi]

theorem finrank_one (H : G.Simple) : Module.finrank ℝ (RawOne G) ≤ 3 := by
  obtain ⟨e,he⟩ := has_color H
  conv_rhs => rw [← Module.finrank_fin_fun ℝ (n:=3)]
  refine LinearMap.finrank_le_finrank_of_injective (f := vectorTest e) ?_
  refine (LinearMap.ker_eq_bot (R:=ℝ) (R₂:=ℝ) (M:=RawOne G) (M₂:=Fin 3 → ℝ) (f:=vectorTest (G:=G) e)).mp ?_
  refine LinearMap.ker_eq_bot'.mpr ?_
  rintro ⟨v,hR,hT⟩ h0
  change vectorTest e ⟨v,hR,hT⟩ = 0 at h0
  choose A ha _hm hA using fun i => low le_rfl (v i)
  have hG i := (A i).covariance (ha i) (hA i)
  let t (p r i j k l : Axis) := (A p).mix (leg0 i j e) (leg1 r k l e)
  have hl (s : Signed) p := low_moves (ha p) (ha (s.perm p)) (hA p) (hA (s.perm p)) s _ (hT s p)
  have ho : Orbit t := by
    refine ⟨fun s p q i j k l => ?_,fun p q i j k l => ?_,fun p q i j k l => ?_⟩
    · calc
        _ = sign s p • (A (s.perm p)).mix (Taylor.turn s.ortho (leg0 i j e)) (Taylor.turn s.ortho (leg1 q k l e)) :=
          congr_arg (fun A => Low.mix A (leg0 i j e) (leg1 q k l e)) (hl s p)
        _ = _ := by rw [turn_leg0,turn_leg1,map_smul (A _).mix, LinearMap.smul_apply,map_smul]; unfold t; simp_rw [smul_smul]; congr 1; ring
    · unfold t; nth_rw 1 [leg0_swap i j]; simp
    unfold t; nth_rw 1 [leg1_swap q k l]; simp
  have hs (q i j k l : Axis) (h : mixProbe e q i j k l (v 0) = 0) : t 0 q i j k l = 0 := by
    apply of_real_zero (congr_arg (fun A => Low.mix A (leg0 i j e) (leg1 q k l e)) (low_real (ha 0) (hA 0) (hR 0)))
    exact (mixProbe_eval (hA 0) ..).symm.trans h
  have h1 := hs 0 0 1 0 1 (congr_fun h0 0); have h3 := hs 2 0 1 2 1 (congr_fun h0 1); have h4 := hs 2 2 1 0 1 (congr_fun h0 2)
  have h2 : t 0 0 1 2 1 2 = 0 := by
    have ht := congr_arg ((A 0).mix (leg0 1 2 e)) (leg1_cycle 0 1 2 e)
    change _ = ((A 0).mix (leg0 1 2 e)) 0 at ht
    rw [map_zero, map_add,map_add,leg1_swap (1:Axis) 2 0] at ht
    have hw := ho.law (⟨Equiv.swap 1 2, fun _ => false⟩) 0 1 1 2 0 2
    norm_num [Equiv.swap_apply_of_ne_of_ne, sign, Fin.ext_iff] at hw
    rw [map_neg] at ht
    change t 0 0 1 2 1 2 + -(t 0 1 1 2 0 2) + t 0 2 1 2 0 1 = 0 at ht
    rw [hw,h4,neg_zero,ho.swap 0 2,h4] at ht; simpa using ht
  have hv p := vanish_mix H (hG p) e he (ho.test h1 h2 h3 h4 p)
  apply Subtype.ext; funext p; apply label_ext; intro J
  let s : Signed := ⟨Equiv.refl _, fun _ => true⟩
  have hz {x : ℂ} (hx : x = -x) : x=0 := by linear_combination hx/2
  have hc : (A p).c=0 := hz (by simpa [s,Low.comp,sign] using congr_arg Low.c (hl s p))
  have hZ : (A p).sq (J 0) (J 0)=0 := by
    apply hz; simpa [Low.comp,s,sign] using congr_arg (fun A => Low.sq A (J 0) (J 0)) (hl s p)
  change read J (v p).val = read J (0 : Label G 5).val
  simp [hA,Low.eval,hv,(A p).linear_invariant H (hG p),hc,hZ]
end YM.StressFlux
