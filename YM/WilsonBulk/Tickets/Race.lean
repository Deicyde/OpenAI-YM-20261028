import YM.WilsonBulk.Tickets.Ally

/-!
# `TicketNull` rank two and all higher, for NORMALIZED density differences

Parity of rotations proved, do not drop paths. `optic`,`pulse` use full ν_false,
so THIS output has correct inverseX reset convention. χ isolates entire
transverse Taylor moment normalized to unit rank. Export rank-derivative.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet
open Lattice Laurent Function Filter Bloch Equiv Matrix Precision Exterior Wilson Pert.Bulk Sheet Atelier Finset
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {V U : Text (Cloth G) 2} {c : Side} {e : ℕ} {σ p : ℝ} {I J : Library G}
open Sheet.Taylor (lineRead league)
open MvPolynomial (X C)
variable (h : Whisper I) (hs : G.Simple) (k : G.ColorIndex) (hz : subdue k (I e 2)=0)
include h hs
local notation "lens" => signalK (h.palm e 2)
-- Extract second-momentum diagonal
omit h hs in
lemma offbeat {x₁ y₁ x y : Axis} (H : x₁≠y₁) (h' : x ≠ y) : ∃ s: Perm Axis,s x₁=x∧s y₁=y := by -- add params & omit
  let T:= swap x₁ x; let e:= swap (T y₁) y; let s:=T.trans e
  refine ⟨s,by rw [Equiv.trans_apply,show T x₁=x from Equiv.swap_apply_left _ _]; apply Equiv.swap_apply_of_ne_of_ne _ h'; rw [← show T x₁=x from Equiv.swap_apply_left _ _]; exact T.injective.ne H,by rw [Equiv.trans_apply,Equiv.swap_apply_left]⟩
include k hz
lemma onsite (i j : G.ColorIndex) (a b : Axis) (hp : a≠b) : lens a a i j (noteP b*noteP b)=0 := by
  obtain ⟨s,hA,hB⟩ := offbeat (by decide : (1:Axis)≠0) hp
  have he:= optics_two h hs (e:=e) k k 1 1 0 0 (publicArk s)
  rw [show (publicArk s).perm 1=a from hA, show (publicArk s).perm 0=b from hB] at he; simp [publicArk,flagFee] at he; -- simp expands?
  have ht : lens 1 1 k k (noteP 0*noteP 0)=0:= neg_eq_zero.mp hz
  change surge ..=0; rw [color_price h hs k i j a a _ e]; split; next _=> exact he.trans ht
  rfl
-- parallel direction from cubic or parity
omit k hz in
lemma onset (i j : G.ColorIndex) (a : Axis) : lens a a i j (noteP a*noteP a)=0 := by
  let v:=noteP a; have he:= pulseK (h.palm _ _) (quad_empty (I:=I) h hs e) (v^3) a i j
  have hv (y : Axis) : remote y (v^3)= if y=a then -(3:ℝ) • (v*v) + (3:ℝ) • v-1 else 0 := by
    unfold remote; rw [map_pow]; by_cases h:y=a
    · rw [if_pos h]; have hm : outset (regionShift 1 y) v=v-1:= by simp [v,outset,cage,regionShift,noteP,h,μ]; ring
      rw [hm, ← MvPolynomial.C_mul', ← MvPolynomial.C_mul']; simp only [map_neg,map_ofNat]; ring
    rw [if_neg h]; have hm : outset (regionShift 1 y) v=v:= by simp [v,outset,cage,regionShift,noteP,Ne.symm h, μ]
    rw [hm,sub_self]
  simp_rw [hv,apply_ite (signalK _ _ _ _ _),map_zero, sum_ite_eq',if_pos (mem_univ a)] at he; unfold v at he; rw [map_sub,map_add,map_smul,map_smul, smul_eq_mul,optic h hs,pulse_empty _ (quad_empty h hs e)] at he; simp only [smul_zero, add_zero,sub_zero, mul_eq_zero] at he; exact he.resolve_left (by norm_num)
lemma flee (i j : G.ColorIndex) (a b : Axis) (hz' : a≠b) : lens a b i j (noteP a * noteP b)=0 := by
  let x:=noteP a; let y:=noteP b; have he:=pulseK (h.palm _ _) (quad_empty (I:=I) h hs e) (x*x*y) b i j
  have hx (b v : Axis) : outset (regionShift 1 b) (noteP v) =if b=v then noteP v-1 else noteP v:= by
    by_cases he:b=v
    · simp [he,outset,cage,regionShift,noteP,μ]; ring
    simp [he,outset,cage,regionShift,noteP,Ne.symm he,μ]
  have ht (k): remote k (x*x*y)=(if k=a then y-(2:ℝ) • (x*y) else 0)+(if k=b then -(x*x) else 0):= by
      unfold remote x y; simp_rw [map_mul,hx]; by_cases hp:k=a
      · rw [hp]; simp only [if_neg hz',↓reduceIte, add_zero,← MvPolynomial.C_mul']; simp only [map_ofNat]; ring
      rcases eq_or_ne k b with rfl|hh
      · simp only [if_neg hp,↓reduceIte,zero_add]; ring
      simp only [if_neg hp,if_neg hh,add_zero,sub_self]
  simp_rw [ht,map_add, apply_ite (signalK _ _ _ _ _),map_zero,sum_add_distrib, sum_ite_eq', if_pos (mem_univ _)] at he
  unfold x y at he; rw [map_neg,map_sub,map_smul, onsite h hs k hz _ _ b a hz'.symm, optic h hs] at he; simp only [neg_zero,add_zero,smul_eq_mul,zero_sub,neg_eq_zero,mul_eq_zero] at he; exact he.resolve_left (by norm_num)
lemma levyNote (i j : G.ColorIndex) (a b x y : Axis) : lens a b i j (noteP x * noteP y)=0 := by
  have H (t : Axis) := optics_two h hs (e:=e) i j a b x y (singleArk t)
  change ∀ t:Axis,lens a b i j (noteP x * noteP y)= _ at H -- _ metastates
  let v:= lens a b i j (noteP x * noteP y)
  by_cases hh : a=b
  · subst b; rcases eq_or_ne x y with hy|hy
    · subst y; rcases eq_or_ne x a with rfl|he; exact onset h hs i j x; exact onsite h hs k hz i j a x he.symm
    have ht:= H x; unfold singleArk flagFee at ht; by_cases hb:a=x
    · rw [hb]; simp [hb, Ne.symm hy] at ht; linarith only [ht]
    simp [hb, Ne.symm hy] at ht ; linarith only [ht]
  have hx:a=x ∨ a=y ∨ v=0:= by
    by_contra! hb; have ht:= H a; simp [singleArk,flagFee,Ne.symm hh,Ne.symm hb.1,Ne.symm hb.2.1] at ht; exact hb.2.2 (by unfold v; linarith only [ht])
  have hy:b=x ∨ b=y ∨ v=0:= by
    by_contra! hb; have ht:= H b; simp [singleArk,flagFee,hh,Ne.symm hb.1,Ne.symm hb.2.1] at ht; exact hb.2.2 (by unfold v; linarith only [ht])
  rcases hx with Hx|Hx|Hx
  · rcases hy with hh'|rfl|hr; · exact False.elim (hh (Hx.trans hh'.symm))
    · rw [← Hx]; exact flee h hs k hz i j a b hh
    exact hr
  · rcases hy with hh'|hh'|hh'
    · rw [← hh',mul_comm,← Hx]; exact flee h hs k hz i j a b hh
    · exact False.elim (hh (Hx.trans hh'.symm))
    exact hh'
  exact Hx
lemma lifted_quadratic : TicketNull 3 (I e (1+1)) := by
  refine TicketNull.issue (h.palm _ _) ?_; rintro ⟨a,u⟩ p l hl; let w:=p 0; obtain ⟨i,hi⟩ := axisEquiv.surjective a; obtain ⟨j,hj⟩:= axisEquiv.surjective w.1
  change journal _ (a,u) p (league l)=0; rw [← hi,show p=(fun _=> (coord j,w.2)) from funext (fun i=> Fin.fin_one_eq_zero i ▸ (Prod.ext (show w.1= _ from hj.symm) rfl))]; change lens i j u w.2 (league l)=0
  match l with
  | []=> exact pulse_empty _ (quad_empty h hs e) ..
  | [⟨i',a⟩]=> rw [Taylor.league_p,Taylor.league_empty,mul_one, Fin.fin_one_eq_zero i']; exact optic h hs ..
  | [⟨i',a⟩,⟨j',b⟩]=> rw [Taylor.league_p,Taylor.league_p,Taylor.league_empty,mul_one, Fin.fin_one_eq_zero i',Fin.fin_one_eq_zero j']; exact levyNote h hs k hz ..
  | _::_::_::_=> simp only [List.length_cons] at hl; omega
end YM.WilsonBulk.Parapet
