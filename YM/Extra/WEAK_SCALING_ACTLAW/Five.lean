import YM.Extra.WEAK_SCALING_ACTLAW.Mixed

/-!
# Bound on real polar-vector labels through Maxwell weight five

Finite symmetry reduction and the actual quotient Bianchi/divergence
constraints on the same projected generators. Numbers use each
antisymmetric curl pair once in the nonincident squares. No assumption of
independence of unconstrained jets in the quotient. Only an upper bound on
this polar-vector rank is needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.WeakScaling.Five
open Function Set Filter Table Maxwell Climb Color Cube
open Work.A01 (eps)
variable {G : Gauge} {L : Register G}

private abbrev S (L : Register G) := Bel L
private abbrev C (L : Register G) := (S L).Field 5
private abbrev v (L : Register G) := mixedPin L
variable {H : (S L).RealSpin} {x : Axis → C L}

private def χ (t a : Axis) := eps (Signed.mirror t) a
private def pair (t : Axis) (i : Fin 6) := χ t (left i)*χ t (right i)
private def screen (t : Axis) : C L →ₗ[ℝ] C L :=
    (2:ℝ)⁻¹ • (LinearMap.id + χ t 0 • ((S L).mirror H 5 (Signed.mirror t)).restrictScalars ℝ)
private def delta (t a : Axis) (i j : Fin 6) :=
    (2:ℝ)⁻¹*(1+χ t 0 * (pair t i * pair t j * χ t a))
private def gate (i j : Fin 6) (a : Axis) := delta 0 a i j * delta 1 a i j * delta 2 a i j
private lemma kept (h : x∈polar H) t : screen (H:=H) t (x 0) = x 0 := by
  have ht := (show _ ∧ ∀ k j, _ from h).2 (Signed.mirror t) 0
  change (S L).mirror H _ _ (x 0) = (↑(χ t 0):ℂ) • x 0 at ht
  rw [show (↑(χ t 0):ℂ) • x 0 = χ t 0 • x 0 from (RCLike.real_smul_eq_coe_smul (K:=ℂ) ..).symm] at ht
  change (2:ℝ)⁻¹ • (x 0 + χ t 0 • _) = _
  change (2:ℝ)⁻¹ • (x 0 + χ t 0 • ((S L).mirror H _ _ (x 0))) = _
  rw [ht,smul_smul,χ,Work.A01.eps_self,one_smul]; module
private lemma coef (i j : Fin 6) (t a : Axis) : screen (H:=H) t (mixedAt L i j a) = delta t a i j • mixedAt L i j a := by
  change (2:ℝ)⁻¹ • (_ + χ t 0 • ((S L).mirror H _ _ _)) = _
  rw [mixedAt,mixedPin_action]; simp only [delta,pair,χ,Signed.mirror,Equiv.refl_apply]; module
private lemma selects (h : x ∈ polar H) (p : Fin 6 → Fin 6 → Axis → ℝ)
    (he : x 0 = ∑ i, ∑ j, ∑ a, p i j a • mixedAt L i j a) : x 0 = ∑ i, ∑ j, ∑ a, p i j a • gate i j a • mixedAt L i j a := by
  calc
    x 0 = screen (H:=H) 2 (screen (H:=H) 1 (screen (H:=H) 0 (x 0))) := by rw [kept h,kept h,kept h]
    _ = _ := by rw [he]; simp only [_root_.map_sum,map_smul,coef,smul_smul,gate,mul_assoc]

private def tA (L : Register G) (a : Axis) := v L 0 a 0 a 0
private def tB (L : Register G) (a b : Axis) := v L a b a b 0
private def tC (L : Register G) (a b : Axis) := v L 0 b a b a
private def tD (L : Register G) (a b : Axis) := v L a b 0 b a
private lemma symmetric (a b : Axis) : tB L a b = tB L b a := by
  unfold tB v; rw [mixedPin_left a b, mixedPin_right b a a b,neg_neg]

set_option maxHeartbeats 3000000 in
private lemma table_gate (i j : Fin 6) (a : Axis) : gate i j a = if (i=j ∧ a=0) ∨
(a=1 ∧ (i=1 ∧ j=3)) ∨
    (a=2 ∧ (i=2 ∧ j=5)) ∨
    (a=3 ∧ (i=0 ∧ j=4)) ∨
    (a=2 ∧ (i=0 ∧ j=3)) ∨
    (a=3 ∧ (i=1 ∧ j=5)) ∨
    (a=1 ∧ (i=2 ∧ j=4)) ∨
    (a=1 ∧ (i=3 ∧ j=1)) ∨
    (a=2 ∧ (i=5 ∧ j=2)) ∨
    (a=3 ∧ (i=4 ∧ j=0)) ∨
    (a=2 ∧ (i=3 ∧ j=0)) ∨
    (a=3 ∧ (i=5 ∧ j=1)) ∨
    (a=1 ∧ (i=4 ∧ j=2)) then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases a <;> norm_num [gate,delta,pair,χ,eps,Signed.mirror,Signed.matrix_at,left,right,Fin.ext_iff]

private def comb {V : Type*} [AddCommGroup V] [Module ℝ V] (w : Fin 3 → V) (c : Fin 3 → ℝ) := ∑ i, c i • w i
private abbrev wA (L : Register G) := ![tA L 1,tA L 2,tA L 3]
private abbrev tri {V : Type*} (w : Axis → Axis → V) := ![w 1 2,w 2 3,w 3 1]
private abbrev tri' {V : Type*} (w : Axis → Axis → V) := ![w 2 1,w 3 2,w 1 3]
private abbrev wB (L : Register G) := tri (tB L)
private abbrev wC (L : Register G) := tri (tC L)
private abbrev wC' (L : Register G) := tri' (tC L)
private abbrev wD (L : Register G) := tri (tD L)
private abbrev wD' (L : Register G) := tri' (tD L)

@[simp] private lemma at_two {V : Type*} (x y z : V) : ![x,y,z] (2:Fin 3) = z := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private lemma shape (h : x∈polar H) (p : Fin 6 → Fin 6 → Axis → ℝ) (he : x 0 = ∑ i, ∑ j, ∑ a, p i j a • mixedAt L i j a) :
    ∃ a b c d e f : Fin 3 → ℝ, x 0 = comb (wA L) a + comb (wB L) b + comb (wC L) c + comb (wC' L) d + comb (wD L) e + comb (wD' L) f := by
  refine ⟨![p 0 0 0,p 1 1 0,p 2 2 0],![p 3 3 0,p 5 5 0,p 4 4 0],
    ![p 1 3 1, p 2 5 2, -p 0 4 3],![-p 0 3 2, -p 1 5 3, p 2 4 1],
    ![p 3 1 1, p 5 2 2, -p 4 0 3],![-p 3 0 2, -p 5 1 3, p 4 2 1],
    ?_⟩
  rw [selects h p he]
  simp only [Fin.sum_univ_six,Fin.sum_univ_four, comb, Fin.sum_univ_three, table_gate]; norm_num [Fin.ext_iff,wA,wB,wC,wC',wD,wD',tri,tri',neg_smul]
  have h₁ : ∀ i : Fin 6, left i = if i=0 ∨ i=1 ∨ i=2 then 0 else if i=3 ∨ i=4 then 1 else 2 := by decide
  have h₂ : ∀ i : Fin 6, right i = if i=0 then 1 else if i=1 ∨ i=3 then 2 else 3 := by decide
  rw [symmetric (L:=L) 3 1]; norm_num [mixedAt,tA,tB,tC,tD,v,h₁,h₂,Fin.ext_iff]
  rw [mixedPin_right (L:=L) 0 1 3 1 3, mixedPin_left (L:=L) 3 1 0 1 3,
    mixedPin_right (L:=L) 0 1 2 1 2, mixedPin_left (L:=L) 2 1 0 1 2,
    mixedPin_right (L:=L) 0 2 3 2 3, mixedPin_left (L:=L) 3 2 0 2 3]
  module

private def plain (s : Equiv.Perm Axis) : Signed := ⟨s,fun _ => false⟩
private def maps (s : Equiv.Perm Axis) := ((S L).mirror H 5 (plain s)).restrictScalars ℝ
private def rot := Equiv.swap (1:Axis) 2 * Equiv.swap (2:Axis) 3
private lemma fixed (h : x∈polar H) (s : Equiv.Perm Axis) (a : Axis) : maps (H:=H) s (x a) = x (s a) := by
  have ht := (show _ ∧ ∀ k i, _ from h).2 (plain s) a; simpa [maps,plain,eps,Signed.matrix_at] using ht
private lemma moved (s : Equiv.Perm Axis) (i j a b k : Axis) : maps (H:=H) s (v L i j a b k) = v L (s i) (s j) (s a) (s b) (s k) := by
  simp [maps,v,mixedPin_action,plain,eps,Signed.matrix_at]

private def average (m : C L →ₗ[ℝ] C L) := (3:ℝ)⁻¹ • (LinearMap.id + m + m.comp m)
private lemma symmetrize (m : C L →ₗ[ℝ] C L) (w : Fin 3 → C L) (p : Fin 3 → ℝ)
    (h : ∀ i, m (w i) = w (i+1)) : average m (comb w p) = ((3:ℝ)⁻¹ * ∑ i, p i) • (∑ i, w i) := by
  have he i j (he : i+1=j) : m (w i) = w j := he ▸ h i
  simp only [average,LinearMap.smul_apply,LinearMap.add_apply, LinearMap.id_coe,id_eq,LinearMap.comp_apply,comb,
    Fin.sum_univ_three,map_add,map_smul,he 0 1 (by decide),he 1 2 (by decide),he 2 0 (by decide)]
  module

set_option maxHeartbeats 1000000 in
private lemma sums (hG : G.Simple) (h : x∈polar H) : ∃ a b c d : ℝ, x 0 =
    a • (∑ i, wA L i) + b • (∑ i, wB L i) + c • ((∑ i, wC L i) + (∑ i, wC' L i)) + d • ((∑ i, wD L i)+(∑ i, wD' L i)) := by
  obtain ⟨p,hp⟩ := odd_center hG H x h
  obtain ⟨a,b,c,d,e,f,he⟩ := shape h p hp
  let r := maps (H:=H) rot
  let s := maps (H:=H) (Equiv.swap 1 2)
  have h₁ : rot (0:Axis)=0 := by decide
  have h₂ : rot (1:Axis)=2 := by decide
  have h₃ : rot (2:Axis)=3 := by decide
  have h₄ : rot (3:Axis)=1 := by decide
  have hr := fixed h rot 0; rw [h₁] at hr
  have hi : ∀ i : Fin 3, i=0 ∨ i=1 ∨ i=2 := by decide
  have hrA (i) : r (wA L i)= wA L (i+1) := by
    rcases hi i with h|h|h <;> subst i <;>
      first | rw [show (0:Fin 3)+1=1 from rfl] | rw [show (1:Fin 3)+1=2 from rfl] | rw [show (2:Fin 3)+1=0 from rfl]
    all_goals
      norm_num [r,moved,rot, Equiv.swap_apply_def,Fin.ext_iff,tA,tri,tri',wA]
  have hrB (i) : r (wB L i)= wB L (i+1) := by
    rcases hi i with h|h|h <;> subst i <;>
      first | rw [show (0:Fin 3)+1=1 from rfl] | rw [show (1:Fin 3)+1=2 from rfl] | rw [show (2:Fin 3)+1=0 from rfl]
    all_goals
      norm_num [r,moved,rot, Equiv.swap_apply_def,Fin.ext_iff,tB,tri,tri',wB]
  have hrC (i) : r (wC L i)= wC L (i+1) := by
    rcases hi i with h|h|h <;> subst i <;>
      first | rw [show (0:Fin 3)+1=1 from rfl] | rw [show (1:Fin 3)+1=2 from rfl] | rw [show (2:Fin 3)+1=0 from rfl]
    all_goals
      norm_num [r,moved,rot, Equiv.swap_apply_def,Fin.ext_iff,tC,tri,tri',wC]
  have hrC' (i) : r (wC' L i)= wC' L (i+1) := by
    rcases hi i with h|h|h <;> subst i <;>
      first | rw [show (0:Fin 3)+1=1 from rfl] | rw [show (1:Fin 3)+1=2 from rfl] | rw [show (2:Fin 3)+1=0 from rfl]
    all_goals
      norm_num [r,moved,rot, Equiv.swap_apply_def,Fin.ext_iff,tC,tri,tri',wC']
  have hrD (i) : r (wD L i)= wD L (i+1) := by
    rcases hi i with h|h|h <;> subst i <;>
      first | rw [show (0:Fin 3)+1=1 from rfl] | rw [show (1:Fin 3)+1=2 from rfl] | rw [show (2:Fin 3)+1=0 from rfl]
    all_goals
      norm_num [r,moved,rot, Equiv.swap_apply_def,Fin.ext_iff,tD,tri,tri',wD]
  have hrD' (i) : r (wD' L i)= wD' L (i+1) := by
    rcases hi i with h|h|h <;> subst i <;>
      first | rw [show (0:Fin 3)+1=1 from rfl] | rw [show (1:Fin 3)+1=2 from rfl] | rw [show (2:Fin 3)+1=0 from rfl]
    all_goals
      norm_num [r,moved,rot, Equiv.swap_apply_def,Fin.ext_iff,tD,tri,tri',wD']
  have hs := congrArg (average r) he; simp only [map_add] at hs
  rw [show average r (x 0) = x 0 by change (3:ℝ)⁻¹ • (x 0 + r (x 0) + r (r (x 0))) = _; simp only [r,hr]; module,
    symmetrize r _ a hrA,
    symmetrize r _ b hrB,
    symmetrize r _ c hrC,
    symmetrize r _ d hrC',
    symmetrize r _ e hrD,
    symmetrize r _ f hrD'] at hs
  have hA : s (∑ i, wA L i) = ∑ i, wA L i := by
    norm_num [s,Fin.sum_univ_three,map_add,wA,tA,moved,Equiv.swap_apply_def,Fin.ext_iff]
    abel
  have hB : s (∑ i, wB L i) = ∑ i, wB L i := by
    norm_num [s,Fin.sum_univ_three,map_add,wB,tB,tri,moved,Equiv.swap_apply_def,Fin.ext_iff]
    rw [show v L 2 1 2 1 0 = v L 1 2 1 2 0 from symmetric .., show v L 1 3 1 3 0 = v L 3 1 3 1 0 from symmetric ..,show v L 3 2 3 2 0 = v L 2 3 2 3 0 from symmetric ..]
    abel
  have hC : s (∑ i, wC L i) = ∑ i, wC' L i := by
    norm_num [s,Fin.sum_univ_three,map_add,wC,tC,wC',tri,tri',moved,Equiv.swap_apply_def,Fin.ext_iff]
    abel
  have hC' : s (∑ i, wC' L i) = ∑ i, wC L i := by
    norm_num [s,Fin.sum_univ_three,map_add,wC',tC,wC,tri,tri',moved,Equiv.swap_apply_def,Fin.ext_iff]
    abel
  have hD : s (∑ i, wD L i) = ∑ i, wD' L i := by
    norm_num [s,Fin.sum_univ_three,map_add,wD,tD,wD',tri,tri',moved,Equiv.swap_apply_def,Fin.ext_iff]
    abel
  have hD' : s (∑ i, wD' L i) = ∑ i, wD L i := by
    norm_num [s,Fin.sum_univ_three,map_add,wD',tD,wD,tri,tri',moved,Equiv.swap_apply_def,Fin.ext_iff]
    abel
  let mean (a : Fin 3 → ℝ) := (3:ℝ)⁻¹*(∑ i, a i)
  refine ⟨mean a,mean b,(2:ℝ)⁻¹*(mean c+mean d),(2:ℝ)⁻¹*(mean e+mean f),?_⟩
  have ht : s (x 0) = x 0 := (fixed h (Equiv.swap 1 2) 0).trans (by rfl)
  have hx : x 0 = (2:ℝ)⁻¹ • (x 0 + s (x 0)) := by rw [ht]; module
  rw [hx,hs]; dsimp only [mean]; simp only [map_add,map_smul,hA,hB,hC,hC',hD,hD']; module

private lemma dropped (a b i k : Axis) : v L a b i i k = 0 := by
  apply smul_right_injective _ (two_ne_zero (α:=ℝ)); change (2:ℝ) • mixedPin L _ _ _ _ _ = (2:ℝ) • 0
  rw [two_smul,smul_zero,add_eq_zero_iff_eq_neg]; exact mixedPin_right ..
private lemma via_equation : ((∑ i, wC L i)+(∑ i, wC' L i)) = -∑ i, wA L i := by
  have h i : ∑ j : Axis, v L 0 i j i j = 0 := mixedPin_delta ..
  have h₁ := h 1; have h₂ := h 2; have h₃ := h 3
  simp only [Fin.sum_univ_four, dropped] at h₁ h₂ h₃
  simp only [Fin.sum_univ_three,wC,wC',wA,tC,tA,tri,tri']; dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one,at_two]
  apply eq_neg_of_add_eq_zero_left
  conv_rhs => rw [← h₁, ← h₂, ← h₃]
  abel

private lemma via_bianchi : ((∑ i, wD L i)+(∑ i, wD' L i)) = ∑ i, wB L i := by
  have ht (a b : Axis) : tD L a b + tD L b a = tB L a b := by
    have he := mixedPin_closed (L:=L) a b 0 b a
    rw [mixedPin_right a b b a, mixedPin_right a b a 0, ← mixedPin_left b a 0 a b] at he
    change tD L a b + -tB L a b + tD L b a = 0 at he
    exact sub_eq_zero.mp (by rw [← he]; abel)
  simp [Fin.sum_univ_three,tri,tri',wB,wD,wD']; rw [← ht 1 2,← ht 2 3,← ht 3 1]; abel

lemma rank_polar (hG : G.Simple) (H : (Bel L).RealSpin) : Module.finrank ℝ (polar H) ≤ 2 := by
  let T : (Fin 2 → ℝ) →ₗ[ℝ] C L := (LinearMap.proj 0).smulRight (∑ i, wA L i) + (LinearMap.proj 1).smulRight (∑ i, wB L i)
  have he (x : Axis → C L) (hx : x∈polar H) : x 0 ∈ T.range := by
    obtain ⟨a,b,c,d,h⟩ := sums hG hx
    refine ⟨![a-c,b+d],?_⟩
    rw [via_equation,via_bianchi] at h; rw [h]
    change (a-c) • (∑ i, wA L i) + (b+d) • (∑ i, wB L i) = _
    module
  let P := LinearMap.codRestrict T.range ((LinearMap.proj (φ:=fun _:Axis => C L) 0).domRestrict (polar H)) (fun x => he x x.property)
  refine (LinearMap.finrank_le_finrank_of_injective (f:=P) (fun a b he => Subtype.ext ?_)).trans
    ((LinearMap.finrank_le_finrank_of_surjective T.surjective_rangeRestrict).trans_eq (Module.finrank_fin_fun ℝ))
  funext i
  simpa only [Equiv.swap_apply_left] using ((fixed a.property (Equiv.swap 0 i) 0).symm.trans
    ((congrArg (maps (H:=H) (Equiv.swap 0 i)) (congrArg Subtype.val he)).trans (fixed b.property _ _)))
end YM.Extra.WeakScaling.Five
